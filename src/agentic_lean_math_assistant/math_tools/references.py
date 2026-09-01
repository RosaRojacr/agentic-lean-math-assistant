"""Content-addressed acquisition helpers for openly accessible publications."""

from __future__ import annotations

import hashlib
import os
import tempfile
import urllib.request
from dataclasses import dataclass
from pathlib import Path
from urllib.parse import urlparse


def _require_absolute_https(url: str, *, label: str) -> None:
    parsed = urlparse(url)
    if parsed.scheme != "https" or not parsed.netloc:
        raise ValueError(f"{label} must be absolute HTTPS")


class _HttpsRedirectHandler(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        _require_absolute_https(newurl, label="reference redirect URL")
        return super().redirect_request(req, fp, code, msg, headers, newurl)


@dataclass(frozen=True, slots=True)
class DownloadedReference:
    path: Path
    sha256: str
    size: int
    url: str


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def download_reference(
    url: str,
    destination: Path,
    *,
    expected_sha256: str | None = None,
    max_bytes: int = 50 * 1024 * 1024,
    timeout: float = 30.0,
) -> DownloadedReference:
    """Download one HTTPS source atomically with size and optional digest checks."""

    _require_absolute_https(url, label="reference URL")
    if max_bytes < 1:
        raise ValueError("max_bytes must be positive")
    if timeout <= 0:
        raise ValueError("timeout must be positive")
    if expected_sha256 is not None and (
        len(expected_sha256) != 64
        or any(character not in "0123456789abcdef" for character in expected_sha256)
    ):
        raise ValueError("expected_sha256 must be lowercase hexadecimal")
    destination.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{destination.name}.", suffix=".part", dir=destination.parent
    )
    temporary = Path(temporary_name)
    digest = hashlib.sha256()
    size = 0
    try:
        request = urllib.request.Request(
            url, headers={"User-Agent": "agentic-lean-math-assistant/1"}
        )
        opener = urllib.request.build_opener(_HttpsRedirectHandler())
        with (
            os.fdopen(descriptor, "wb") as output,
            opener.open(request, timeout=timeout) as response,
        ):
            while chunk := response.read(1024 * 1024):
                size += len(chunk)
                if size > max_bytes:
                    raise ValueError(f"reference exceeds {max_bytes} bytes")
                digest.update(chunk)
                output.write(chunk)
            output.flush()
            os.fsync(output.fileno())
        observed = digest.hexdigest()
        if expected_sha256 is not None and observed != expected_sha256:
            raise ValueError(
                f"reference digest mismatch: expected {expected_sha256}, got {observed}"
            )
        os.replace(temporary, destination)
        return DownloadedReference(destination, observed, size, url)
    finally:
        temporary.unlink(missing_ok=True)
