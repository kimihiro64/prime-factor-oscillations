"""Verify the same immutable artifact view used by the Windows proof probes."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path, PurePosixPath
from typing import Any, cast

from scripts.prebuilt_dependency import COMMIT, TOOLCHAIN, digest

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "data/analytic-artifacts.json"
MANIFEST_SHA256 = "4541992ff6cd517ee585ece627b68c066bffed704bc13dbb4205c2b943da072c"


def artifact_path(root: Path, relative: str) -> Path:
    """Reject paths outside the selected artifact view."""
    parts = PurePosixPath(relative).parts
    if not parts or ".." in parts or ":" in relative or "\\" in relative:
        raise ValueError(f"unsafe artifact path: {relative}")
    target = (root / relative).resolve()
    if not target.is_relative_to(root.resolve()):
        raise ValueError(f"artifact path escapes its root: {relative}")
    return target


def verify_files(root: Path, files: dict[str, str]) -> None:
    """Check every supplied artifact, including runtime/signature companions."""
    if not files:
        raise ValueError("empty analytic artifact inventory")
    for relative, expected in files.items():
        path = artifact_path(root, relative)
        if not path.is_file() or digest(path) != expected:
            raise ValueError(
                f"missing or altered artifact: {relative}; dependency rebuild forbidden"
            )


def verify() -> Path:
    """Return the existing verified view; never fetch, port, or compile anything."""
    if not MANIFEST.is_file() or digest(MANIFEST) != MANIFEST_SHA256:
        raise ValueError("analytic artifact manifest is missing or differs from the audited pin")
    manifest = cast(dict[str, Any], json.loads(MANIFEST.read_text(encoding="utf-8")))
    if manifest["toolchain"] != TOOLCHAIN or manifest["erdos690_commit"] != COMMIT:
        raise ValueError("analytic artifact toolchain/dependency mismatch")
    configured = os.environ.get("PFO_ANALYTIC_CACHE")
    if configured is None:
        pointer = ROOT / ".lake/analytic-cache.json"
        if not pointer.is_file():
            raise ValueError("set PFO_ANALYTIC_CACHE to the audited existing artifact view")
        data = cast(dict[str, str], json.loads(pointer.read_text(encoding="utf-8")))
        if data.get("manifest_sha256") != MANIFEST_SHA256:
            raise ValueError("local artifact pointer has stale manifest provenance")
        configured = data["root"]
    root = Path(configured).resolve()
    files = cast(dict[str, str], manifest["files"])
    verify_files(root, files)
    for name, row in manifest["modules"].items():
        required = row["artifacts"]
        if not required or any(relative not in files for relative in required):
            raise ValueError(f"incomplete artifact companions: {name}")
    print(
        f"Verified existing analytic view: {len(files)} artifacts; dependency builds: 0", flush=True
    )
    return root


def source_digest(path: Path) -> str:
    """Hash the exact source bytes for incremental owned-module checks."""
    return hashlib.sha256(path.read_bytes()).hexdigest()
