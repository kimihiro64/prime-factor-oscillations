"""Verify the same immutable artifact view used by the Windows proof probes."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
from typing import Any, cast

from scripts.artifact_extensions import (
    AnalyticEnvironment,
    extension_files,
    verify_extension_companions,
)
from scripts.artifact_extensions import (
    artifact_path as artifact_path,
)
from scripts.artifact_extensions import (
    verify_files as verify_files,
)
from scripts.prebuilt_dependency import COMMIT, TOOLCHAIN, digest

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "data/analytic-artifacts.json"
MANIFEST_SHA256 = "4541992ff6cd517ee585ece627b68c066bffed704bc13dbb4205c2b943da072c"
MATHLIB_COMMIT = "5ed2965256430c3649e86755f9576b54eca72435"
EXTENSION_PINS = (
    (
        "data/analytic-artifacts-rh-mathlib.json",
        "8b8b62c21dd74d9f8d7f4061a82aa94012d71121044418195392871ded9d3684",
    ),
    (
        "data/analytic-artifacts-qrh-mathlib.json",
        "fa3a46a69825af348fd86b3ef67b303946e382ab34a165be83d14ff6129707a9",
    ),
    (
        "data/analytic-artifacts-qrh-source-mathlib.json",
        "a7ec6aeb882bc149ad762cff09d27e0c2a3433e8b58c6711d2d447bff253e615",
    ),
    (
        "data/analytic-artifacts-qrh-port.json",
        "ff49ffed2ca3e8e39a9d6888ca36d2805a4e26ef2ce8b9f8153c636aeae9e64a",
    ),
)


def load_artifact_manifests() -> tuple[dict[str, Any], list[dict[str, Any]], dict[str, str]]:
    """Read only immutable pinned manifests; also usable before cache installation."""
    if not MANIFEST.is_file() or digest(MANIFEST) != MANIFEST_SHA256:
        raise ValueError("analytic artifact manifest is missing or differs from the audited pin")
    manifest = cast(dict[str, Any], json.loads(MANIFEST.read_text(encoding="utf-8")))
    if manifest["toolchain"] != TOOLCHAIN or manifest["erdos690_commit"] != COMMIT:
        raise ValueError("analytic artifact toolchain/dependency mismatch")
    files = dict(cast(dict[str, str], manifest["files"]))
    extensions: list[dict[str, Any]] = []
    for relative, expected_hash in EXTENSION_PINS:
        path = artifact_path(ROOT, relative)
        if not path.is_file() or digest(path) != expected_hash:
            raise ValueError(f"extension manifest differs from its immutable pin: {relative}")
        extension = cast(dict[str, Any], json.loads(path.read_text(encoding="utf-8")))
        files.update(
            extension_files(
                extension,
                files,
                base_sha256=MANIFEST_SHA256,
                toolchain=TOOLCHAIN,
                compiler=manifest["compiler"],
                mathlib_commit=MATHLIB_COMMIT,
            )
        )
        extensions.append(extension)
    return manifest, extensions, files


def configured_artifact_root() -> Path:
    """Resolve the existing single provider without modifying its pointer."""
    configured = os.environ.get("PFO_ANALYTIC_CACHE")
    if configured is None:
        pointer = ROOT / ".lake/analytic-cache.json"
        if not pointer.is_file():
            raise ValueError("set PFO_ANALYTIC_CACHE to the audited existing artifact view")
        data = cast(dict[str, str], json.loads(pointer.read_text(encoding="utf-8")))
        if data.get("manifest_sha256") != MANIFEST_SHA256:
            raise ValueError("local artifact pointer has stale manifest provenance")
        configured = data["root"]
    return Path(configured).resolve()


def verify_environment() -> AnalyticEnvironment:
    """Verify the entire additive view; no fetch, port or compile fallback."""
    manifest, extensions, files = load_artifact_manifests()
    root = configured_artifact_root()
    verify_files(root, files)
    for name, row in manifest["modules"].items():
        required = row["artifacts"]
        if not required or any(relative not in files for relative in required):
            raise ValueError(f"incomplete artifact companions: {name}")
    for extension in extensions:
        verify_extension_companions(root, extension)
    print(
        f"Verified existing analytic view: {len(files)} artifacts; dependency builds: 0", flush=True
    )
    return AnalyticEnvironment(
        root, MANIFEST_SHA256, EXTENSION_PINS, TOOLCHAIN, manifest["compiler"], MATHLIB_COMMIT
    )


def verify() -> Path:
    """Keep existing consumers on the same fully verified additive environment."""
    return verify_environment().root


def source_digest(path: Path) -> str:
    """Hash the exact source bytes for incremental owned-module checks."""
    return hashlib.sha256(path.read_bytes()).hexdigest()
