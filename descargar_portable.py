#!/usr/bin/env python3
"""
Descargador de canciones desde CSV con selección inteligente del resultado de YouTube.

Mejoras frente a la versión original:
- Admite CSV con columnas tipo Spotify Exportify y tipo miplaylist.csv.
- Busca varios resultados y los puntúa por título, artista y duración.
- Penaliza versiones Live/Remix/Slowed/Cover/etc. cuando no se pidieron.
- No descarga una canción si no puede verificar con suficiente confianza título, artista y duración.
- Usa filtros duros para evitar confundir canciones del mismo artista.
- Revalida con metadatos completos los mejores resultados antes de descargar.
- Cuando existe ISRC, lo usa como búsqueda adicional de alta precisión.
- Mantiene el nombre de archivo "Artista - Canción.mp3".
- Reescribe las etiquetas ID3 con los datos del CSV para que el coche/reproductor
  no muestre el título del vídeo de YouTube.
- Puede corregir las etiquetas de MP3 ya descargados sin volver a descargarlos.

Requisitos para esta versión .py:
    - Python 3.11+ en Windows 10/11 o Linux (glibc, x86_64/aarch64).
    - No requiere instalar yt-dlp, FFmpeg ni Deno.
      La primera ejecución descarga copias portables verificadas dentro de ./_portable_tools.
    - No necesita permisos de administrador/sudo: las herramientas se guardan junto al script.
    - Cuando se empaquete como ejecutable, tampoco será necesario instalar Python.

Ejemplos:
    python descargar.py coche.csv
    python descargar.py miplaylist.csv -o ./musica
    python descargar.py coche.csv --limit 10 --show-candidates
    python descargar.py coche.csv --min-score 70
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import logging
import os
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import tarfile
import time
import unicodedata
import urllib.parse
import urllib.request
import zipfile
from dataclasses import dataclass
from difflib import SequenceMatcher
from pathlib import Path
from typing import Iterable


# ── Herramientas portables ───────────────────────────────────────────────────
# Esta versión NO depende de yt-dlp/FFmpeg/Deno instalados en el sistema.
# Descarga y conserva copias locales verificadas junto al script.
# Plataformas soportadas actualmente:
#   - Windows x64
#   - Linux x86_64 (glibc)
#   - Linux aarch64/arm64 (glibc)


def _base_dir() -> Path:
    """Carpeta persistente junto al script (y, más adelante, junto al ejecutable)."""
    if getattr(sys, "frozen", False):
        return Path(sys.executable).resolve().parent
    return Path(__file__).resolve().parent


def _arquitectura() -> str:
    maquina = platform.machine().lower()
    if maquina in {"amd64", "x86_64", "x64"}:
        return "x64"
    if maquina in {"arm64", "aarch64"}:
        return "arm64"
    return maquina or "desconocida"


SISTEMA = platform.system()
ARQUITECTURA = _arquitectura()
BASE_DIR = _base_dir()
TOOLS_DIR = BASE_DIR / "_portable_tools"
DENO_DIR = TOOLS_DIR / "deno"
FFMPEG_ROOT = TOOLS_DIR / "ffmpeg"
FFMPEG_EXE: Path | None = None
FFPROBE_EXE: Path | None = None
FFMPEG_DIR: Path | None = None

YTDLP_REPO = "yt-dlp/yt-dlp"
DENO_REPO = "denoland/deno"
BTBN_REPO = "BtbN/FFmpeg-Builds"
FFMPEG_WINDOWS_ZIP_URL = "https://www.gyan.dev/ffmpeg/builds/ffmpeg-release-essentials.zip"
FFMPEG_WINDOWS_SHA_URL = "https://www.gyan.dev/ffmpeg/builds/ffmpeg-release-essentials.zip.sha256"
USER_AGENT = "DescargadorMusicaPortable/2.0 (+Python urllib)"


def _nombres_herramientas() -> tuple[str, str]:
    if SISTEMA == "Windows":
        if ARQUITECTURA != "x64":
            raise RuntimeError(
                "Windows portable está soportado actualmente en x64. "
                f"Arquitectura detectada: {platform.machine()}"
            )
        return "yt-dlp.exe", "deno.exe"

    if SISTEMA == "Linux":
        if ARQUITECTURA == "x64":
            return "yt-dlp_linux", "deno"
        if ARQUITECTURA == "arm64":
            return "yt-dlp_linux_aarch64", "deno"
        raise RuntimeError(
            "Linux portable está soportado actualmente en x86_64 y aarch64/arm64. "
            f"Arquitectura detectada: {platform.machine()}"
        )

    raise RuntimeError(
        f"Sistema no compatible todavía: {SISTEMA}. "
        "Actualmente se admiten Windows x64 y Linux x86_64/aarch64."
    )


YTDLP_NOMBRE, DENO_NOMBRE = _nombres_herramientas()
YTDLP_EXE = TOOLS_DIR / YTDLP_NOMBRE
DENO_EXE = DENO_DIR / DENO_NOMBRE


def _hacer_ejecutable(ruta: Path) -> None:
    """Añade permisos de ejecución en sistemas Unix sin necesitar sudo."""
    if os.name != "nt" and ruta.exists():
        ruta.chmod(ruta.stat().st_mode | 0o111)


def _validar_linux_runtime() -> None:
    if SISTEMA != "Linux":
        return

    libc, version = platform.libc_ver()
    libc_norm = (libc or "").casefold()
    if "musl" in libc_norm:
        raise RuntimeError(
            "Esta versión portable para Linux usa binarios glibc y no es compatible con musl/Alpine todavía."
        )

    # Las builds Linux de FFmpeg-Builds requieren glibc >= 2.28. Si Python puede
    # detectar una versión inferior, abortamos antes de descargar más de 100 MB.
    if libc_norm in {"glibc", "libc"} and version:
        try:
            partes = tuple(int(x) for x in version.split(".")[:2])
            if partes < (2, 28):
                raise RuntimeError(
                    f"glibc {version} detectada; la build portable de FFmpeg requiere glibc >= 2.28."
                )
        except ValueError:
            pass


def _peticion(url: str) -> urllib.request.Request:
    return urllib.request.Request(url, headers={"User-Agent": USER_AGENT})


def _leer_url(url: str, timeout: int = 120, intentos: int = 4) -> bytes:
    """Lee una URL con reintentos para conexiones lentas/inestables."""
    ultimo_error: Exception | None = None
    for intento in range(1, intentos + 1):
        try:
            with urllib.request.urlopen(_peticion(url), timeout=timeout) as r:
                return r.read()
        except Exception as e:
            ultimo_error = e
            if intento < intentos:
                espera = min(3 * intento, 10)
                log.warning(
                    "Conexión lenta/fallida (%s/%s): %s. Reintento en %ss...",
                    intento, intentos, e, espera,
                )
                time.sleep(espera)
    assert ultimo_error is not None
    raise ultimo_error


def _sha256_archivo(ruta: Path) -> str:
    h = hashlib.sha256()
    with ruta.open("rb") as f:
        for bloque in iter(lambda: f.read(1024 * 1024), b""):
            h.update(bloque)
    return h.hexdigest().lower()


def _descargar(url: str, destino: Path, etiqueta: str, sha256: str | None = None) -> None:
    """Descarga con reintentos; usa curl como respaldo en Linux si urllib falla."""
    destino.parent.mkdir(parents=True, exist_ok=True)
    temporal = destino.with_suffix(destino.suffix + ".part")
    temporal.unlink(missing_ok=True)

    log.info("Preparando %s...", etiqueta)
    ultimo_error: Exception | None = None

    for intento in range(1, 5):
        try:
            temporal.unlink(missing_ok=True)
            with urllib.request.urlopen(_peticion(url), timeout=180) as r, temporal.open("wb") as f:
                total = int(r.headers.get("Content-Length") or 0)
                descargado = 0
                ultimo_pct = -10
                while True:
                    bloque = r.read(1024 * 1024)
                    if not bloque:
                        break
                    f.write(bloque)
                    descargado += len(bloque)
                    if total:
                        pct = int(descargado * 100 / total)
                        if pct >= ultimo_pct + 10:
                            ultimo_pct = pct
                            log.info("   %s: %s%%", etiqueta, min(100, pct))
            ultimo_error = None
            break
        except Exception as e:
            ultimo_error = e
            temporal.unlink(missing_ok=True)
            if intento < 4:
                espera = min(4 * intento, 15)
                log.warning(
                    "Descarga de %s falló (%s/4): %s. Reintento en %ss...",
                    etiqueta, intento, e, espera,
                )
                time.sleep(espera)

    if ultimo_error is not None and SISTEMA == "Linux":
        curl = shutil.which("curl")
        if curl:
            log.warning("urllib no pudo descargar %s; pruebo con curl...", etiqueta)
            temporal.unlink(missing_ok=True)
            cmd = [
                curl, "-L", "--fail", "--silent", "--show-error",
                "--connect-timeout", "30",
                "--max-time", "900",
                "--retry", "4",
                "--retry-delay", "3",
                "-o", str(temporal),
                url,
            ]
            try:
                subprocess.run(cmd, check=True)
                ultimo_error = None
            except Exception as e:
                ultimo_error = e
                temporal.unlink(missing_ok=True)

    if ultimo_error is not None:
        raise RuntimeError(
            f"No se pudo descargar {etiqueta} tras varios intentos: {ultimo_error}"
        ) from ultimo_error

    if not temporal.exists() or temporal.stat().st_size == 0:
        temporal.unlink(missing_ok=True)
        raise RuntimeError(f"La descarga de {etiqueta} quedó vacía.")

    if sha256:
        real = _sha256_archivo(temporal)
        esperado = sha256.strip().lower()
        if real != esperado:
            temporal.unlink(missing_ok=True)
            raise RuntimeError(
                f"SHA-256 incorrecto para {etiqueta}. Esperado {esperado}, obtenido {real}."
            )

    os.replace(temporal, destino)


def _github_release_latest(repo: str) -> dict:
    url = f"https://api.github.com/repos/{repo}/releases/latest"
    return json.loads(_leer_url(url).decode("utf-8"))


def _asset_release(release: dict, nombre: str) -> tuple[str, str | None]:
    for asset in release.get("assets") or []:
        if asset.get("name") == nombre:
            digest = asset.get("digest")
            sha = digest.split(":", 1)[1] if isinstance(digest, str) and digest.startswith("sha256:") else None
            return str(asset["browser_download_url"]), sha
    raise RuntimeError(f"No encuentro el recurso {nombre!r} en la última versión publicada.")


def _sha_asset_companion(release: dict, nombre_asset: str) -> str | None:
    """Lee un asset compañero .sha256sum cuando GitHub no expone digest."""
    nombre_checksum = nombre_asset + ".sha256sum"
    try:
        url, _ = _asset_release(release, nombre_checksum)
        texto = _leer_url(url).decode("ascii", errors="ignore").strip()
        if texto:
            return texto.split()[0].lower()
    except Exception:
        pass
    return None


def _sha_ytdlp_desde_sumas(nombre_asset: str) -> str | None:
    """Obtiene el checksum oficial si la API de GitHub no devuelve 'digest'."""
    try:
        texto = _leer_url(
            "https://github.com/yt-dlp/yt-dlp/releases/latest/download/SHA2-256SUMS"
        ).decode("utf-8", errors="replace")
        for linea in texto.splitlines():
            partes = linea.strip().split()
            if len(partes) >= 2 and partes[-1].lstrip("*") == nombre_asset:
                return partes[0].lower()
    except Exception:
        pass
    return None


def _asegurar_ytdlp(forzar: bool = False) -> None:
    if forzar:
        YTDLP_EXE.unlink(missing_ok=True)
    if YTDLP_EXE.exists() and YTDLP_EXE.stat().st_size > 1_000_000:
        _hacer_ejecutable(YTDLP_EXE)
        return

    release = _github_release_latest(YTDLP_REPO)
    url, sha = _asset_release(release, YTDLP_NOMBRE)
    sha = sha or _sha_ytdlp_desde_sumas(YTDLP_NOMBRE)
    _descargar(url, YTDLP_EXE, "yt-dlp", sha256=sha)
    _hacer_ejecutable(YTDLP_EXE)


def _deno_asset_name() -> str:
    if SISTEMA == "Windows" and ARQUITECTURA == "x64":
        return "deno-x86_64-pc-windows-msvc.zip"
    if SISTEMA == "Linux" and ARQUITECTURA == "x64":
        return "deno-x86_64-unknown-linux-gnu.zip"
    if SISTEMA == "Linux" and ARQUITECTURA == "arm64":
        return "deno-aarch64-unknown-linux-gnu.zip"
    raise RuntimeError(f"No hay build portable de Deno configurada para {SISTEMA}/{ARQUITECTURA}.")


def _extraer_zip_seguro(zip_path: Path, destino: Path) -> None:
    destino.mkdir(parents=True, exist_ok=True)
    destino_real = destino.resolve()
    with zipfile.ZipFile(zip_path) as z:
        for miembro in z.infolist():
            objetivo = (destino / miembro.filename).resolve()
            try:
                objetivo.relative_to(destino_real)
            except ValueError:
                raise RuntimeError(f"ZIP inseguro: ruta fuera del destino: {miembro.filename}")
        z.extractall(destino)


def _asegurar_deno(forzar: bool = False) -> None:
    if forzar:
        shutil.rmtree(DENO_DIR, ignore_errors=True)
    if DENO_EXE.exists() and DENO_EXE.stat().st_size > 1_000_000:
        _hacer_ejecutable(DENO_EXE)
        return

    release = _github_release_latest(DENO_REPO)
    nombre = _deno_asset_name()
    url, sha = _asset_release(release, nombre)
    sha = sha or _sha_asset_companion(release, nombre)
    DENO_DIR.mkdir(parents=True, exist_ok=True)
    zip_path = TOOLS_DIR / nombre
    _descargar(url, zip_path, "Deno", sha256=sha)
    try:
        _extraer_zip_seguro(zip_path, DENO_DIR)
    finally:
        zip_path.unlink(missing_ok=True)
    if not DENO_EXE.exists():
        raise RuntimeError(f"Deno se descargó, pero no apareció {DENO_NOMBRE} tras descomprimirlo.")
    _hacer_ejecutable(DENO_EXE)


def _nombres_ffmpeg() -> tuple[str, str]:
    if SISTEMA == "Windows":
        return "ffmpeg.exe", "ffprobe.exe"
    return "ffmpeg", "ffprobe"


def _localizar_ffmpeg() -> tuple[Path, Path, Path] | None:
    if not FFMPEG_ROOT.exists():
        return None
    ffmpeg_nombre, ffprobe_nombre = _nombres_ffmpeg()
    for ffmpeg in FFMPEG_ROOT.rglob(ffmpeg_nombre):
        carpeta = ffmpeg.parent
        ffprobe = carpeta / ffprobe_nombre
        if ffprobe.exists():
            _hacer_ejecutable(ffmpeg)
            _hacer_ejecutable(ffprobe)
            return carpeta, ffmpeg, ffprobe
    return None


def _ffmpeg_linux_asset_name() -> str:
    if ARQUITECTURA == "x64":
        return "ffmpeg-master-latest-linux64-gpl.tar.xz"
    if ARQUITECTURA == "arm64":
        return "ffmpeg-master-latest-linuxarm64-gpl.tar.xz"
    raise RuntimeError(f"FFmpeg Linux no configurado para arquitectura {ARQUITECTURA}.")


def _extraer_ffmpeg_linux(archivo: Path) -> None:
    """Extrae únicamente ffmpeg y ffprobe de la build estática de BtbN."""
    destino = FFMPEG_ROOT / "bin"
    destino.mkdir(parents=True, exist_ok=True)
    encontrados: dict[str, tarfile.TarInfo] = {}

    with tarfile.open(archivo, mode="r:xz") as tar:
        for miembro in tar.getmembers():
            if not miembro.isfile():
                continue
            base = Path(miembro.name).name
            if base in {"ffmpeg", "ffprobe"} and "/bin/" in miembro.name.replace("\\", "/"):
                encontrados[base] = miembro

        if set(encontrados) != {"ffmpeg", "ffprobe"}:
            raise RuntimeError("La build Linux de FFmpeg no contiene ffmpeg y ffprobe donde se esperaba.")

        for nombre, miembro in encontrados.items():
            origen = tar.extractfile(miembro)
            if origen is None:
                raise RuntimeError(f"No se pudo extraer {nombre} de la build de FFmpeg.")
            salida = destino / nombre
            with salida.open("wb") as f:
                shutil.copyfileobj(origen, f)
            _hacer_ejecutable(salida)


def _asegurar_ffmpeg(forzar: bool = False) -> None:
    global FFMPEG_DIR, FFMPEG_EXE, FFPROBE_EXE

    if forzar:
        shutil.rmtree(FFMPEG_ROOT, ignore_errors=True)

    localizado = _localizar_ffmpeg()
    if localizado:
        FFMPEG_DIR, FFMPEG_EXE, FFPROBE_EXE = localizado
        return

    if SISTEMA == "Windows":
        if ARQUITECTURA != "x64":
            raise RuntimeError("La build portable de FFmpeg usada actualmente requiere Windows x64.")

        checksum = _leer_url(FFMPEG_WINDOWS_SHA_URL).decode("ascii", errors="ignore").strip().split()[0]
        zip_path = TOOLS_DIR / "ffmpeg-release-essentials.zip"
        _descargar(FFMPEG_WINDOWS_ZIP_URL, zip_path, "FFmpeg", sha256=checksum)

        temporal = Path(tempfile.mkdtemp(prefix="ffmpeg_", dir=str(TOOLS_DIR)))
        try:
            _extraer_zip_seguro(zip_path, temporal)
            shutil.rmtree(FFMPEG_ROOT, ignore_errors=True)
            os.replace(temporal, FFMPEG_ROOT)
        finally:
            zip_path.unlink(missing_ok=True)
            if temporal.exists() and temporal != FFMPEG_ROOT:
                shutil.rmtree(temporal, ignore_errors=True)

    elif SISTEMA == "Linux":
        _validar_linux_runtime()
        release = _github_release_latest(BTBN_REPO)
        nombre = _ffmpeg_linux_asset_name()
        url, sha = _asset_release(release, nombre)
        archivo = TOOLS_DIR / nombre
        _descargar(url, archivo, "FFmpeg", sha256=sha)
        try:
            shutil.rmtree(FFMPEG_ROOT, ignore_errors=True)
            _extraer_ffmpeg_linux(archivo)
        finally:
            archivo.unlink(missing_ok=True)
    else:
        raise RuntimeError(f"FFmpeg portable no configurado para {SISTEMA}.")

    localizado = _localizar_ffmpeg()
    if not localizado:
        raise RuntimeError("FFmpeg se descargó, pero no encuentro ffmpeg y ffprobe.")
    FFMPEG_DIR, FFMPEG_EXE, FFPROBE_EXE = localizado


def asegurar_herramientas_portables(forzar: bool = False) -> None:
    """Deja yt-dlp + Deno + FFmpeg listos localmente, sin sudo ni instalación global."""
    _nombres_herramientas()  # valida sistema/arquitectura
    _validar_linux_runtime()

    TOOLS_DIR.mkdir(parents=True, exist_ok=True)
    _asegurar_ytdlp(forzar=forzar)
    _asegurar_deno(forzar=forzar)
    _asegurar_ffmpeg(forzar=forzar)

    comprobaciones = [
        ([str(YTDLP_EXE), "--version"], "yt-dlp"),
        ([str(DENO_EXE), "--version"], "Deno"),
        ([str(FFMPEG_EXE), "-version"], "FFmpeg"),
        ([str(FFPROBE_EXE), "-version"], "FFprobe"),
    ]
    for cmd, nombre in comprobaciones:
        r = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=20)
        if r.returncode != 0:
            raise RuntimeError(f"{nombre} portable no responde correctamente.")

    log.info(
        "Herramientas portables listas en: %s (%s/%s)",
        TOOLS_DIR,
        SISTEMA,
        ARQUITECTURA,
    )


def _args_ytdlp_comunes(browser: str | None = None) -> list[str]:
    if not (YTDLP_EXE.exists() and DENO_EXE.exists() and FFMPEG_DIR):
        raise RuntimeError("Las herramientas portables todavía no están inicializadas.")
    args = [
        str(YTDLP_EXE),
        "--ignore-config",
        "--no-warnings",
        "--js-runtimes", f"deno:{DENO_EXE}",
        "--ffmpeg-location", str(FFMPEG_DIR),
    ]
    if browser:
        args += ["--cookies-from-browser", browser]
    return args


def _ejecutar_ytdlp_json(
    url: str,
    browser: str | None = None,
    flat: bool = False,
    playlist_end: int | None = None,
) -> dict:
    cmd = _args_ytdlp_comunes(browser)
    cmd += ["--quiet", "--skip-download", "--dump-single-json"]
    if flat:
        cmd += ["--flat-playlist"]
    if playlist_end:
        cmd += ["--playlist-end", str(playlist_end)]
    cmd.append(url)

    r = subprocess.run(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        encoding="utf-8",
        errors="replace",
        timeout=90,
    )
    if r.returncode != 0:
        detalle = (r.stderr or r.stdout).strip()
        raise RuntimeError(detalle.splitlines()[-1] if detalle else "yt-dlp terminó con error")

    salida = r.stdout.strip()
    if not salida:
        return {}
    try:
        return json.loads(salida)
    except json.JSONDecodeError:
        for linea in reversed(salida.splitlines()):
            linea = linea.strip()
            if linea.startswith("{"):
                try:
                    return json.loads(linea)
                except json.JSONDecodeError:
                    pass
        raise RuntimeError("yt-dlp devolvió una respuesta que no pude interpretar como JSON.")


logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s  %(levelname)-8s  %(message)s",
    datefmt="%H:%M:%S",
)
log = logging.getLogger(__name__)


def opciones_cookies(browser: str | None) -> dict:
    """Opciones comunes para usar cookies del navegador cuando el usuario lo pide."""
    return {"cookiesfrombrowser": (browser,)} if browser else {}


VERSIONES_ESPECIALES = {
    "live", "en vivo", "directo", "concert", "concierto",
    "remix", "remastered", "remaster", "sped up", "speed up",
    "slowed", "reverb", "nightcore", "cover", "karaoke",
    "instrumental", "acoustic", "acustico", "acústico", "8d",
    "mashup", "mix", "edit", "version extendida", "extended",
}

RUIDO_TITULO = {
    "official audio", "official video", "official music video",
    "audio oficial", "video oficial", "music video", "visualizer",
    "lyric video", "lyrics", "letra", "video lyrics", "topic",
    "hq", "hd", "4k",
}


@dataclass
class Cancion:
    titulo: str
    artistas: list[str]
    artista_mostrar: str
    album: str = ""
    duracion_s: float | None = None
    isrc: str = ""


@dataclass
class Candidato:
    url: str
    titulo: str
    canal: str
    duracion_s: float | None
    score: float
    razones: list[str]
    origen: str = ""


# ── Lectura del CSV ────────────────────────────────────────────────────────────

def _normalizar_cabecera(nombre: str) -> str:
    """Normaliza cabeceras para admitir variantes como Track Name / Track name."""
    nombre = unicodedata.normalize("NFKD", str(nombre or ""))
    nombre = "".join(c for c in nombre if not unicodedata.combining(c))
    nombre = nombre.casefold().strip()
    # Ignora espacios, guiones, paréntesis y otros signos en los nombres de columna.
    return re.sub(r"[^a-z0-9]+", "", nombre)


def _valor(fila: dict, *nombres: str) -> str:
    """Obtiene un campo sin depender de mayúsculas, espacios o signos de la cabecera."""
    mapa = {
        _normalizar_cabecera(k): str(v).strip()
        for k, v in fila.items()
        if k is not None and v is not None and str(v).strip()
    }
    for nombre in nombres:
        valor = mapa.get(_normalizar_cabecera(nombre))
        if valor:
            return valor
    return ""


def _separar_artistas(texto: str) -> list[str]:
    if not texto:
        return []
    # Los dos CSV adjuntos usan ';' o ',' como separador de artistas.
    partes = re.split(r"\s*[;,]\s*", texto)
    return [p.strip() for p in partes if p.strip()]


def _parsear_duracion(fila: dict) -> float | None:
    ms = _valor(fila, "Duration (ms)")
    if ms:
        try:
            return float(ms) / 1000.0
        except ValueError:
            pass

    texto = _valor(fila, "Duration")
    if texto:
        try:
            partes = [float(x) for x in texto.split(":")]
            if len(partes) == 2:
                return partes[0] * 60 + partes[1]
            if len(partes) == 3:
                return partes[0] * 3600 + partes[1] * 60 + partes[2]
        except ValueError:
            pass
    return None


def fila_a_cancion(fila: dict) -> Cancion | None:
    # Admite, entre otros:
    #   Track name, Artist name, Album, ISRC
    #   Track Name, Artist Name(s), Album Name
    #   Song, Artist, Album
    titulo = _valor(fila, "Track Name", "Track name", "Song", "Title", "Track")
    artista_raw = _valor(
        fila,
        "Artist Name(s)", "Artist name", "Artist Name", "Artist", "Artists"
    )
    album = _valor(fila, "Album Name", "Album name", "Album")
    isrc = _valor(fila, "ISRC")

    if not titulo:
        return None

    artistas = _separar_artistas(artista_raw)
    artista_mostrar = ", ".join(artistas) if artistas else artista_raw

    return Cancion(
        titulo=titulo,
        artistas=artistas,
        artista_mostrar=artista_mostrar,
        album=album,
        duracion_s=_parsear_duracion(fila),
        isrc=isrc,
    )


def leer_csv(ruta: str) -> list[Cancion]:
    canciones: list[Cancion] = []
    with open(ruta, newline="", encoding="utf-8-sig") as f:
        reader = csv.DictReader(f)

        if not reader.fieldnames:
            raise ValueError("El CSV no tiene cabeceras reconocibles.")

        log.info("Columnas detectadas: %s", ", ".join(reader.fieldnames))

        sin_titulo = 0
        for numero, fila in enumerate(reader, start=2):
            cancion = fila_a_cancion(fila)
            if cancion:
                canciones.append(cancion)
            else:
                sin_titulo += 1
                log.error(
                    "Fila %s sin título reconocible. Cabeceras: %s",
                    numero,
                    ", ".join(reader.fieldnames),
                )

        if not canciones:
            raise ValueError(
                "No se ha podido leer ninguna canción del CSV. "
                f"Cabeceras encontradas: {', '.join(reader.fieldnames)}"
            )

        if sin_titulo:
            log.warning("Filas sin título: %s", sin_titulo)

    return canciones


# ── Normalización y puntuación ────────────────────────────────────────────────

def normalizar(texto: str) -> str:
    texto = unicodedata.normalize("NFKD", texto or "")
    texto = "".join(c for c in texto if not unicodedata.combining(c))
    texto = texto.casefold()
    texto = texto.replace("&", " and ")
    texto = re.sub(r"[\[\](){}|_/\\:;,.!?¿¡'\"`´+*=~^-]+", " ", texto)
    texto = re.sub(r"\s+", " ", texto)
    return texto.strip()


def tokens(texto: str) -> set[str]:
    return {t for t in normalizar(texto).split() if len(t) > 1}


def contiene_frase(texto_norm: str, frase: str) -> bool:
    frase_norm = normalizar(frase)
    return bool(frase_norm and frase_norm in texto_norm)


def limpiar_titulo_candidato(titulo: str, artistas: Iterable[str]) -> str:
    limpio = normalizar(titulo)
    for artista in artistas:
        a = normalizar(artista)
        if a:
            limpio = re.sub(rf"\b{re.escape(a)}\b", " ", limpio)
    for ruido in RUIDO_TITULO:
        limpio = limpio.replace(normalizar(ruido), " ")
    return re.sub(r"\s+", " ", limpio).strip()


def similitud(a: str, b: str) -> float:
    a, b = normalizar(a), normalizar(b)
    if not a or not b:
        return 0.0
    return SequenceMatcher(None, a, b).ratio()


def _frase_completa_en(texto_norm: str, frase_norm: str) -> bool:
    """Coincidencia por palabras completas para evitar falsos positivos por subcadenas."""
    if not texto_norm or not frase_norm:
        return False
    return f" {frase_norm} " in f" {texto_norm} "


def _numeros(texto: str) -> set[str]:
    return set(re.findall(r"\b\d+\b", normalizar(texto)))


def _marcadores_especiales_no_pedidos(cancion: Cancion, titulo_video: str) -> list[str]:
    titulo_norm = normalizar(titulo_video)
    esperado = normalizar(f"{cancion.titulo} {cancion.album}")
    encontrados: list[str] = []
    for marcador in VERSIONES_ESPECIALES:
        m = normalizar(marcador)
        if _frase_completa_en(titulo_norm, m) and not _frase_completa_en(esperado, m):
            encontrados.append(marcador)
    return encontrados


def validar_candidato(
    cancion: Cancion,
    info: dict,
    *,
    estricto: bool = True,
) -> tuple[bool, list[str]]:
    """Aplica filtros duros. Un resultado que no los supera jamás se descarga."""
    titulo_video = str(info.get("title") or "")
    canal = str(info.get("channel") or info.get("uploader") or "")
    if not titulo_video:
        return False, ["sin título"]

    titulo_norm = normalizar(titulo_video)
    titulo_limpio = limpiar_titulo_candidato(titulo_video, cancion.artistas)
    esperado = normalizar(cancion.titulo)

    esperados = set(esperado.split())
    candidatos = set(titulo_limpio.split()) | set(titulo_norm.split())
    cobertura = len(esperados & candidatos) / len(esperados) if esperados else 0.0
    sim_limpia = similitud(cancion.titulo, titulo_limpio)
    exacto_limpio = titulo_limpio == esperado

    # Regla crítica para títulos como "125", "911", "2:50", etc.
    # Si el número del título no aparece, no puede ser la canción correcta.
    numeros_esperados = _numeros(cancion.titulo)
    numeros_video = _numeros(titulo_video)
    if numeros_esperados and not numeros_esperados.issubset(numeros_video):
        return False, ["faltan números del título"]

    # Un título corto necesita coincidencia especialmente fuerte.
    if len(esperados) <= 2:
        titulo_ok = exacto_limpio or (cobertura == 1.0 and sim_limpia >= 0.78)
    else:
        titulo_ok = exacto_limpio or cobertura >= 0.80 or sim_limpia >= 0.78

    if not titulo_ok:
        return False, [f"título incompatible (cobertura {cobertura:.0%}, sim {sim_limpia:.2f})"]

    especiales = _marcadores_especiales_no_pedidos(cancion, titulo_video)
    if especiales:
        return False, [f"versión no pedida: {', '.join(especiales)}"]

    if estricto and cancion.artistas:
        principal = normalizar(cancion.artistas[0])
        texto_artista = normalizar(f"{titulo_video} {canal}")
        if principal and not _frase_completa_en(texto_artista, principal):
            return False, ["no aparece el artista principal"]

    duracion = info.get("duration")
    try:
        duracion = float(duracion) if duracion is not None else None
    except (TypeError, ValueError):
        duracion = None

    # Con duración conocida, una diferencia grande es una señal muy fuerte de error.
    if estricto and cancion.duracion_s and duracion:
        diferencia = abs(cancion.duracion_s - duracion)
        if diferencia > 22:
            return False, [f"duración incompatible ({diferencia:.0f}s de diferencia)"]

    return True, []


def puntuar_candidato(cancion: Cancion, info: dict) -> tuple[float, list[str]]:
    titulo_video = str(info.get("title") or "")
    canal = str(info.get("channel") or info.get("uploader") or "")
    duracion = info.get("duration")
    try:
        duracion = float(duracion) if duracion is not None else None
    except (TypeError, ValueError):
        duracion = None

    valido, motivos = validar_candidato(cancion, info, estricto=False)
    if not valido:
        return 0.0, [f"RECHAZADO: {m}" for m in motivos]

    titulo_norm = normalizar(titulo_video)
    canal_norm = normalizar(canal)
    titulo_limpio = limpiar_titulo_candidato(titulo_video, cancion.artistas)
    esperado_norm = normalizar(cancion.titulo)

    score = 0.0
    razones: list[str] = []

    # 1) Título: pesa más que todo lo demás.
    sim = similitud(cancion.titulo, titulo_limpio)
    score += 45.0 * sim

    esperado_tokens = set(esperado_norm.split())
    video_tokens = set(titulo_limpio.split()) | tokens(titulo_video)
    cobertura = len(esperado_tokens & video_tokens) / len(esperado_tokens) if esperado_tokens else 0.0
    score += 20.0 * cobertura

    if titulo_limpio == esperado_norm:
        score += 15.0
        razones.append("título limpio exacto")
    elif cobertura == 1.0:
        razones.append("todos los términos del título presentes")

    # 2) Artista.
    if cancion.artistas:
        principal = normalizar(cancion.artistas[0])
        texto_artista = normalizar(f"{titulo_video} {canal}")
        if principal and _frase_completa_en(texto_artista, principal):
            score += 12.0
            razones.append("artista principal coincide")
        else:
            score -= 20.0
            razones.append("falta artista principal")

        for extra in cancion.artistas[1:]:
            extra_norm = normalizar(extra)
            if extra_norm and _frase_completa_en(texto_artista, extra_norm):
                score += 2.0

    # 3) Duración.
    if cancion.duracion_s and duracion:
        diferencia = abs(cancion.duracion_s - duracion)
        if diferencia <= 2.5:
            score += 12.0
            razones.append(f"duración ±{diferencia:.1f}s")
        elif diferencia <= 5:
            score += 10.0
            razones.append(f"duración ±{diferencia:.1f}s")
        elif diferencia <= 10:
            score += 6.0
        elif diferencia <= 15:
            score += 2.0
        elif diferencia > 22:
            score -= 25.0
            razones.append(f"duración incorrecta ({diferencia:.0f}s)")

    # 4) Fuentes habitualmente fiables.
    if any(x in titulo_norm for x in ("official audio", "audio oficial")):
        score += 3.0
    if "topic" in canal_norm or "vevo" in canal_norm:
        score += 3.0
        razones.append("canal musical fiable")
    if cancion.album and contiene_frase(titulo_norm, cancion.album):
        score += 2.0

    return max(0.0, min(100.0, score)), razones


# ── Búsqueda ──────────────────────────────────────────────────────────────────

def construir_queries(cancion: Cancion) -> list[str]:
    """Genera búsquedas precisas; nunca usa título solo como primera opción."""
    principal = cancion.artistas[0] if cancion.artistas else cancion.artista_mostrar
    todos = " ".join(cancion.artistas) if cancion.artistas else cancion.artista_mostrar

    queries: list[str] = []

    if cancion.isrc:
        queries.extend([
            f'"{cancion.isrc}"',
            f'"{cancion.isrc}" "{principal}"',
        ])

    queries.extend([
        f'"{principal}" "{cancion.titulo}"',
        f'"{principal}" "{cancion.titulo}" official audio',
        f'{principal} {cancion.titulo} Topic',
        f'{principal} {cancion.titulo} audio',
        f'{principal} {cancion.titulo}',
        f'{todos} {cancion.titulo}',
    ])

    if cancion.album:
        queries.extend([
            f'"{principal}" "{cancion.titulo}" "{cancion.album}"',
            f'{principal} {cancion.titulo} {cancion.album}',
        ])

    resultado: list[str] = []
    vistos: set[str] = set()
    for q in queries:
        q = re.sub(r"\s+", " ", q).strip()
        clave = normalizar(q)
        if q and clave not in vistos:
            vistos.add(clave)
            resultado.append(q)
    return resultado


def _info_a_candidato(cancion: Cancion, info: dict, origen: str) -> Candidato | None:
    if not info:
        return None
    video_id = info.get("id")
    url = info.get("webpage_url") or info.get("url")
    if video_id and (not url or not str(url).startswith("http")):
        url = f"https://www.youtube.com/watch?v={video_id}"
    if not url:
        return None

    # En fase preliminar ya descartamos incompatibilidades de título evidentes.
    valido, _ = validar_candidato(cancion, info, estricto=False)
    if not valido:
        return None

    score, razones = puntuar_candidato(cancion, info)
    duracion = info.get("duration")
    try:
        duracion = float(duracion) if duracion is not None else None
    except (TypeError, ValueError):
        duracion = None

    if cancion.isrc and cancion.isrc.casefold() in origen.casefold():
        score = min(100.0, score + 3.0)
        razones.append("búsqueda por ISRC")

    return Candidato(
        url=str(url),
        titulo=str(info.get("title") or ""),
        canal=str(info.get("channel") or info.get("uploader") or ""),
        duracion_s=duracion,
        score=score,
        razones=razones,
        origen=origen,
    )


def _buscar_query(cancion: Cancion, query: str, cantidad: int, browser: str | None = None) -> list[Candidato]:
    search_url = f"ytsearch{cantidad}:{query}"
    resultado = _ejecutar_ytdlp_json(
        search_url, browser=browser, flat=True, playlist_end=cantidad
    )

    candidatos: list[Candidato] = []
    for info in (resultado or {}).get("entries") or []:
        candidato = _info_a_candidato(cancion, info, origen=f"YouTube: {query}")
        if candidato:
            candidatos.append(candidato)
    return candidatos


def _buscar_youtube_music(cancion: Cancion, query: str, cantidad: int, browser: str | None = None) -> list[Candidato]:
    """Busca en la sección 'Songs' de YouTube Music antes que en YouTube general."""
    q = urllib.parse.quote_plus(query)
    # Filtro oficial de la sección Songs usado por el extractor de YouTube Music de yt-dlp.
    search_url = (
        "https://music.youtube.com/search?q=" + q
        + "&sp=EgWKAQIIAWoKEAoQAxAEEAkQBQ%3D%3D"
    )
    resultado = _ejecutar_ytdlp_json(
        search_url, browser=browser, flat=True, playlist_end=cantidad
    )

    candidatos: list[Candidato] = []
    for info in (resultado or {}).get("entries") or []:
        candidato = _info_a_candidato(cancion, info, origen=f"YouTube Music: {query}")
        if candidato:
            candidatos.append(candidato)
    return candidatos


def _enriquecer_candidato(cancion: Cancion, candidato: Candidato, browser: str | None = None) -> Candidato | None:
    """Obtiene metadatos completos del vídeo y aplica los filtros estrictos."""
    try:
        info = _ejecutar_ytdlp_json(candidato.url, browser=browser, flat=False)
    except Exception as e:
        log.debug("No pude revalidar %s: %s", candidato.url, e)        # Si la búsqueda plana ya trae metadatos suficientes, todavía podemos validarla.
        info = {
            "title": candidato.titulo,
            "channel": candidato.canal,
            "duration": candidato.duracion_s,
        }

    valido, motivos = validar_candidato(cancion, info, estricto=True)
    if not valido:
        log.debug("Rechazado %r: %s", candidato.titulo, "; ".join(motivos))
        return None

    score, razones = puntuar_candidato(cancion, info)
    duracion = info.get("duration")
    try:
        duracion = float(duracion) if duracion is not None else candidato.duracion_s
    except (TypeError, ValueError):
        duracion = candidato.duracion_s

    return Candidato(
        url=str(info.get("webpage_url") or candidato.url),
        titulo=str(info.get("title") or candidato.titulo),
        canal=str(info.get("channel") or info.get("uploader") or candidato.canal),
        duracion_s=duracion,
        score=score,
        razones=razones,
        origen=candidato.origen,
    )


def buscar_candidatos(cancion: Cancion, cantidad: int, browser: str | None = None) -> list[Candidato]:
    """Busca en dos fases para reducir peticiones y evitar bloqueos de YouTube."""
    queries = construir_queries(cancion)
    por_query = max(3, min(5, cantidad))
    mejores_por_url: dict[str, Candidato] = {}
    revalidadas: set[str] = set()

    def guardar(encontrados: list[Candidato]) -> None:
        for c in encontrados:
            anterior = mejores_por_url.get(c.url)
            if anterior is None or c.score > anterior.score:
                mejores_por_url[c.url] = c

    principal = cancion.artistas[0] if cancion.artistas else cancion.artista_mostrar
    music_query = f'{principal} {cancion.titulo}'.strip()
    if music_query:
        try:
            guardar(_buscar_youtube_music(cancion, music_query, por_query, browser=browser))
        except Exception as e:
            log.debug("YouTube Music no disponible para %r: %s", music_query, e)

    # Primera fase: solo las búsquedas más precisas. En la mayoría de canciones
    # esto basta y evita lanzar 8-10 búsquedas innecesarias por pista.
    primarias = queries[:3]
    secundarias = queries[3:]
    for query in primarias:
        try:
            guardar(_buscar_query(cancion, query, por_query, browser=browser))
        except Exception as e:
            log.debug("Falló búsqueda %r: %s", query, e)

    def revalidar_mejores(limite: int) -> list[Candidato]:
        preliminares = sorted(mejores_por_url.values(), key=lambda c: c.score, reverse=True)
        verificados: list[Candidato] = []
        for candidato in preliminares:
            if candidato.url in revalidadas:
                continue
            revalidadas.add(candidato.url)
            completo = _enriquecer_candidato(cancion, candidato, browser=browser)
            if completo:
                verificados.append(completo)
            if len(revalidadas) >= limite:
                break
        return verificados

    verificados = revalidar_mejores(min(4, max(3, cantidad)))
    if verificados and max(c.score for c in verificados) >= 90:
        return sorted(verificados, key=lambda c: c.score, reverse=True)

    # Segunda fase: solo se amplía la búsqueda cuando la primera no produce una
    # coincidencia muy sólida. Así reducimos mucho el volumen de peticiones.
    for query in secundarias:
        try:
            guardar(_buscar_query(cancion, query, por_query, browser=browser))
        except Exception as e:
            log.debug("Falló búsqueda secundaria %r: %s", query, e)

    verificados.extend(revalidar_mejores(min(8, max(5, cantidad + 2))))
    return sorted(verificados, key=lambda c: c.score, reverse=True)


def elegir_candidato(
    cancion: Cancion,
    cantidad: int,
    min_score: float,
    show_candidates: bool,
) -> Candidato | None:
    candidatos = buscar_candidatos(cancion, cantidad, browser=None)
    if not candidatos:
        log.warning("Sin coincidencias verificadas para: %s — %s", cancion.artista_mostrar, cancion.titulo)
        return None

    if show_candidates:
        for pos, c in enumerate(candidatos[:8], start=1):
            dur = f"{c.duracion_s:.0f}s" if c.duracion_s else "?s"
            log.info("   %s) %5.1f  %s  [%s]  %s", pos, c.score, c.titulo, dur, c.canal)
            log.info("      query: %s", c.origen)

    mejor = candidatos[0]
    if mejor.score < min_score:
        log.warning(
            "Ningún candidato alcanza la confianza mínima (mejor %.1f < %.1f). No se descarga para evitar una canción incorrecta.",
            mejor.score, min_score,
        )
        return None
    return mejor


# ── Nombre de archivo y etiquetas ─────────────────────────────────────────────

def nombre_archivo_seguro(nombre: str) -> str:
    nombre = re.sub(r'[\\/:*?"<>|]', "_", nombre)
    nombre = re.sub(r"\s+", " ", nombre).strip(" .")
    # Evita problemas con rutas demasiado largas, especialmente en Windows.
    return nombre[:180].rstrip(" .")


def ruta_mp3(cancion: Cancion, carpeta_salida: Path) -> Path:
    # Mantiene compatibilidad con tu script original: para el nombre del archivo
    # usa el primer artista. Las etiquetas ID3 sí guardan todos los artistas.
    artista_archivo = cancion.artistas[0] if cancion.artistas else cancion.artista_mostrar
    base = f"{artista_archivo} - {cancion.titulo}" if artista_archivo else cancion.titulo
    return carpeta_salida / f"{nombre_archivo_seguro(base)}.mp3"


def audio_reproducible(ruta: Path) -> bool:
    """Comprueba que el fichero existe y contiene una pista de audio legible."""
    if not ruta.exists() or ruta.stat().st_size < 4096:
        return False

    if not FFPROBE_EXE or not FFPROBE_EXE.exists():
        return False

    cmd = [
        str(FFPROBE_EXE), "-v", "error",
        "-select_streams", "a:0",
        "-show_entries", "stream=codec_type,duration",
        "-of", "default=noprint_wrappers=1:nokey=1",
        str(ruta),
    ]
    try:
        r = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=20)
        return r.returncode == 0 and bool(r.stdout.strip())
    except Exception:
        return False


def fijar_metadatos(ruta: Path, cancion: Cancion) -> bool:
    """Elimina metadatos heredados de YouTube y escribe los del CSV sin recodificar audio."""
    if not FFMPEG_EXE or not FFMPEG_EXE.exists():
        log.error("La copia portable de ffmpeg no está disponible.")
        return False

    temporal = ruta.with_name(f"{ruta.stem}.__etiquetas__.mp3")
    cmd = [
        str(FFMPEG_EXE), "-hide_banner", "-loglevel", "error", "-y",
        "-i", str(ruta),
        "-map_metadata", "-1",
        "-c:a", "copy",
        "-id3v2_version", "3",
        "-metadata", f"title={cancion.titulo}",
    ]
    if cancion.artista_mostrar:
        cmd += ["-metadata", f"artist={cancion.artista_mostrar}"]
    if cancion.album:
        cmd += ["-metadata", f"album={cancion.album}"]
    cmd.append(str(temporal))

    try:
        subprocess.run(cmd, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
        os.replace(temporal, ruta)
        return True
    except subprocess.CalledProcessError as e:
        if temporal.exists():
            temporal.unlink(missing_ok=True)
        detalle = e.stderr.decode("utf-8", errors="replace").strip() if e.stderr else str(e)
        log.error("No se pudieron escribir metadatos en '%s': %s", ruta.name, detalle)
        return False


# ── Descarga ──────────────────────────────────────────────────────────────────

def descargar_cancion(
    cancion: Cancion,
    candidato: Candidato,
    carpeta_salida: Path,
    browser: str | None = None,
) -> bool:
    destino = ruta_mp3(cancion, carpeta_salida)

    if destino.exists():
        if audio_reproducible(destino):
            log.info("Ya existe y es reproducible: %s", destino.name)
            if not fijar_metadatos(destino, cancion):
                log.warning("El audio existe y se puede reproducir, aunque no pude corregir sus etiquetas.")
            return True
        log.warning("El archivo existente no es reproducible; se elimina y se vuelve a descargar: %s", destino.name)
        destino.unlink(missing_ok=True)

    # Usamos una plantilla fija basada SOLO en el CSV. El título de YouTube nunca decide el nombre.
    plantilla = str(destino.with_suffix(".%(ext)s"))

    cmd = _args_ytdlp_comunes(browser) + [
        "--quiet",
        "--no-playlist",
        "--format", "bestaudio/best",
        "--output", plantilla,
        "--retries", "3",
        "--fragment-retries", "3",
        "--extract-audio",
        "--audio-format", "mp3",
        "--audio-quality", "320K",
        candidato.url,
    ]

    try:
        r = subprocess.run(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=300,
        )
        if r.returncode != 0:
            detalle = (r.stderr or r.stdout).strip()
            raise RuntimeError(detalle.splitlines()[-1] if detalle else "yt-dlp terminó con error")

        if not destino.exists():
            log.error("La descarga terminó pero no aparece el MP3 esperado: %s", destino)
            return False

        if not audio_reproducible(destino):
            log.error("El MP3 creado no es reproducible; probaré otra fuente: %s", destino.name)
            destino.unlink(missing_ok=True)
            return False

        if not fijar_metadatos(destino, cancion):
            log.warning("El audio está bien y se conserva, aunque falló el cambio de etiquetas: %s", destino.name)

        log.info("Descargado y reproducible: %s  <-  %s (score %.1f)", destino.name, candidato.titulo, candidato.score)
        return True
    except Exception as e:
        log.error("Error inesperado con '%s': %s", destino.name, e)
        return False


def resolver_y_descargar(
    cancion: Cancion,
    carpeta_salida: Path,
    cantidad: int,
    min_score: float,
    show_candidates: bool,
    browser: str | None = None,
) -> bool:
    """Descarga únicamente candidatos previamente verificados."""
    try:
        candidatos = buscar_candidatos(cancion, cantidad, browser=browser)
    except Exception as e:
        log.error("Falló la búsqueda de %s — %s: %s", cancion.artista_mostrar, cancion.titulo, e)
        return False

    if show_candidates:
        for pos, c in enumerate(candidatos[:10], start=1):
            dur = f"{c.duracion_s:.0f}s" if c.duracion_s else "?s"
            log.info("   %s) %5.1f  %s  [%s]  %s", pos, c.score, c.titulo, dur, c.canal)
            log.info("      query: %s", c.origen)
            if c.razones:
                log.info("      señales: %s", ", ".join(c.razones))

    candidatos = [c for c in candidatos if c.score >= min_score]
    if not candidatos:
        log.warning(
            "No hay una coincidencia suficientemente segura para %s — %s. Se omite en vez de descargar otra canción.",
            cancion.artista_mostrar,
            cancion.titulo,
        )
        return False

    # Si una fuente correcta está bloqueada o falla la descarga, se prueba otra,
    # pero siempre dentro del conjunto previamente verificado.
    for pos, candidato in enumerate(candidatos[:12], start=1):
        if pos > 1:
            log.warning(
                "La fuente anterior falló; pruebo otra coincidencia verificada %s/%s: %s",
                pos,
                min(12, len(candidatos)),
                candidato.titulo,
            )
        if descargar_cancion(cancion, candidato, carpeta_salida, browser=browser):
            return True

    return False


# ── Main ──────────────────────────────────────────────────────────────────────

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Descarga canciones desde CSV usando yt-dlp, Deno y FFmpeg portables, sin instalación global en Windows o Linux."
    )
    parser.add_argument("csv", help="Ruta al CSV")
    parser.add_argument("--output", "-o", default="./musica", help="Carpeta de salida")
    parser.add_argument("--limit", "-l", type=int, default=None, help="Máximo de canciones")
    parser.add_argument("--delay", "-d", type=float, default=5.0, help="Pausa entre canciones (default: 5s para reducir bloqueos de YouTube)")
    parser.add_argument(
        "--candidates", "-c", type=int, default=6,
        help="Máximo orientativo de candidatos por búsqueda (default: 6)",
    )
    parser.add_argument(
        "--min-score", type=float, default=78.0,
        help="Confianza mínima para descargar; por debajo se omite la canción (default: 78)",
    )
    parser.add_argument(
        "--show-candidates", action="store_true",
        help="Muestra los mejores candidatos y su puntuación",
    )
    parser.add_argument(
        "--retag-only", action="store_true",
        help="Solo corrige las etiquetas de MP3 ya existentes; no busca ni descarga",
    )
    parser.add_argument(
        "--cookies-from-browser",
        metavar="NAVEGADOR",
        help="Usa cookies del navegador con yt-dlp (por ejemplo: chrome, edge o firefox) si YouTube bloquea búsquedas/descargas",
    )
    parser.add_argument(
        "--update-tools",
        action="store_true",
        help="Vuelve a descargar las últimas copias portables de yt-dlp, Deno y FFmpeg",
    )
    args = parser.parse_args()

    if not os.path.exists(args.csv):
        log.error("No se encontró el archivo CSV: %s", args.csv)
        sys.exit(1)
    if args.candidates < 1:
        parser.error("--candidates debe ser >= 1")
    if not (0 <= args.min_score <= 100):
        parser.error("--min-score debe estar entre 0 y 100")

    try:
        asegurar_herramientas_portables(forzar=args.update_tools)
    except Exception as e:
        log.error("No pude preparar las herramientas portables: %s", e)
        sys.exit(2)

    carpeta_salida = Path(args.output)
    carpeta_salida.mkdir(parents=True, exist_ok=True)

    canciones = leer_csv(args.csv)
    if args.limit is not None:
        canciones = canciones[: args.limit]

    log.info("Carpeta de salida: %s", carpeta_salida.resolve())
    log.info("Canciones a procesar: %s", len(canciones))

    exitosas = 0
    fallidas: list[str] = []

    for i, cancion in enumerate(canciones, start=1):
        etiqueta = f"{cancion.artista_mostrar} - {cancion.titulo}" if cancion.artista_mostrar else cancion.titulo
        log.info("[%s/%s] %s", i, len(canciones), etiqueta)

        destino = ruta_mp3(cancion, carpeta_salida)

        if args.retag_only:
            if destino.exists() and fijar_metadatos(destino, cancion):
                exitosas += 1
            else:
                fallidas.append(etiqueta)
            continue

        # Si ya existe, primero comprobamos que realmente se pueda reproducir.
        if destino.exists() and audio_reproducible(destino):
            if not fijar_metadatos(destino, cancion):
                log.warning("El MP3 es reproducible, pero no pude corregir sus etiquetas: %s", destino.name)
            else:
                log.info("Etiquetas corregidas: %s", destino.name)
            exitosas += 1
            continue
        elif destino.exists():
            log.warning("MP3 existente corrupto/no reproducible; lo vuelvo a descargar: %s", destino.name)
            destino.unlink(missing_ok=True)

        if resolver_y_descargar(
            cancion,
            carpeta_salida,
            cantidad=args.candidates,
            min_score=args.min_score,
            show_candidates=args.show_candidates,
            browser=args.cookies_from_browser,
        ):
            exitosas += 1
        else:
            fallidas.append(etiqueta)

        if i < len(canciones) and args.delay > 0:
            time.sleep(args.delay)

    print("\n" + "=" * 64)
    print(f"OK / corregidas : {exitosas}/{len(canciones)}")
    print(f"Sin audio        : {len(fallidas)}")

    if fallidas:
        ruta = carpeta_salida / "_errores.txt"
        ruta.write_text("\n".join(fallidas), encoding="utf-8")
        print(f"Sin audio guardadas en: {ruta}")

    print("=" * 64)


if __name__ == "__main__":
    main()