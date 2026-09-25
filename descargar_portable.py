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
    - Python 3.11+ en Windows 10/11.
    - No requiere instalar yt-dlp, FFmpeg ni Deno.
      La primera ejecución descarga copias portables verificadas dentro de .\\_portable_tools.
    - Cuando lo empaquetemos como .exe, tampoco será necesario instalar Python.

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
# Esta versión NO depende de yt-dlp/FFmpeg/Deno instalados en Windows.
# Descarga y conserva copias locales verificadas junto al script.


def _base_dir() -> Path:
    """Carpeta persistente junto al script (y, más adelante, junto al .exe)."""
    if getattr(sys, "frozen", False):
        return Path(sys.executable).resolve().parent
    return Path(__file__).resolve().parent


BASE_DIR = _base_dir()
TOOLS_DIR = BASE_DIR / "_portable_tools"
YTDLP_EXE = TOOLS_DIR / "yt-dlp.exe"
DENO_DIR = TOOLS_DIR / "deno"
DENO_EXE = DENO_DIR / "deno.exe"
FFMPEG_ROOT = TOOLS_DIR / "ffmpeg"
FFMPEG_EXE: Path | None = None
FFPROBE_EXE: Path | None = None
FFMPEG_DIR: Path | None = None

YTDLP_REPO = "yt-dlp/yt-dlp"
DENO_REPO = "denoland/deno"
FFMPEG_ZIP_URL = "https://www.gyan.dev/ffmpeg/builds/ffmpeg-release-essentials.zip"
FFMPEG_SHA_URL = "https://www.gyan.dev/ffmpeg/builds/ffmpeg-release-essentials.zip.sha256"
USER_AGENT = "DescargadorMusicaPortable/1.0 (+Python urllib)"


def _peticion(url: str) -> urllib.request.Request:
    return urllib.request.Request(url, headers={"User-Agent": USER_AGENT})


def _leer_url(url: str, timeout: int = 45) -> bytes:
    with urllib.request.urlopen(_peticion(url), timeout=timeout) as r:
        return r.read()


def _sha256_archivo(ruta: Path) -> str:
    h = hashlib.sha256()
    with ruta.open("rb") as f:
        for bloque in iter(lambda: f.read(1024 * 1024), b""):
            h.update(bloque)
    return h.hexdigest().lower()


def _descargar(url: str, destino: Path, etiqueta: str, sha256: str | None = None) -> None:
    destino.parent.mkdir(parents=True, exist_ok=True)
    temporal = destino.with_suffix(destino.suffix + ".part")
    temporal.unlink(missing_ok=True)

    log.info("Preparando %s...", etiqueta)
    try:
        with urllib.request.urlopen(_peticion(url), timeout=60) as r, temporal.open("wb") as f:
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
    except Exception:
        temporal.unlink(missing_ok=True)
        raise

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


def _sha_ytdlp_desde_sumas() -> str | None:
    """Obtiene el checksum oficial si la API de GitHub no devuelve 'digest'."""
    try:
        texto = _leer_url(
            "https://github.com/yt-dlp/yt-dlp/releases/latest/download/SHA2-256SUMS"
        ).decode("utf-8", errors="replace")
        for linea in texto.splitlines():
            partes = linea.strip().split()
            if len(partes) >= 2 and partes[-1].lstrip("*") == "yt-dlp.exe":
                return partes[0].lower()
    except Exception:
        pass
    return None


def _asegurar_ytdlp(forzar: bool = False) -> None:
    if forzar:
        YTDLP_EXE.unlink(missing_ok=True)
    if YTDLP_EXE.exists() and YTDLP_EXE.stat().st_size > 1_000_000:
        return

    release = _github_release_latest(YTDLP_REPO)
    url, sha = _asset_release(release, "yt-dlp.exe")
    sha = sha or _sha_ytdlp_desde_sumas()
    _descargar(url, YTDLP_EXE, "yt-dlp", sha256=sha)


def _deno_asset_name() -> str:
    maquina = platform.machine().lower()
    if maquina in {"amd64", "x86_64", "x64"}:
        return "deno-x86_64-pc-windows-msvc.zip"
    if maquina in {"arm64", "aarch64"}:
        return "deno-aarch64-pc-windows-msvc.zip"
    raise RuntimeError(f"Arquitectura de Windows no compatible todavía: {platform.machine()}")


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
        return

    release = _github_release_latest(DENO_REPO)
    nombre = _deno_asset_name()
    url, sha = _asse