"""Restore verified Erdos 690 oleans; never invoke a dependency build."""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import sys
import tarfile
import urllib.request
from pathlib import Path, PurePosixPath
from typing import Any, cast

COMMIT = "ef3c9311d42b61db59f81d99741b5819d1986436"
TOOLCHAIN = "leanprover/lean4:v4.34.0"
TAG = "v0.1.0-conditional.ef3c9311d42b"
BASE = f"https://github.com/kimihiro64/erdos-690-prime-factor-unimodality/releases/download/{TAG}"
MANIFEST = "conditional-build-manifest.json"
MANIFEST_SHA256 = "ca4c8a053dc86ec0acf8f641ffaf69a3354157ff184a2e7a8564db3b09e2f470"
ROOT = Path(__file__).resolve().parents[1]
CACHE = ROOT / ".lake" / "prebuilt" / "erdos690"
VENDORED_PREFIX = ".lake/build/lib/lean/VendorPrimeNumberTheoremAnd/"
REQUIRED_VENDORED_OLEANS = (
    VENDORED_PREFIX + "EulerMaclaurin.olean",
    VENDORED_PREFIX + "Mertens.olean",
)


def digest(path: Path) -> str:
    """Hash a file without loading the whole release into memory."""
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def safe_target(root: Path, relative: str) -> Path:
    """Accept only regular build-library paths contained in the cache."""
    parts = PurePosixPath(relative).parts
    if "\\" in relative or ":" in relative or ".." in parts:
        raise ValueError(f"unsafe archive path: {relative}")
    if not parts or parts[0] != ".lake" or "/build/lib/lean/" not in relative:
        raise ValueError(f"not a build-library path: {relative}")
    target = (root / relative).resolve()
    if not target.is_relative_to(root.resolve()):
        raise ValueError(f"archive path escapes cache: {relative}")
    return target


def wanted(relative: str) -> bool:
    """Select reusable leaves and their released third-party library closure."""
    if "/build/lib/lean/" not in relative:
        return False
    if relative.startswith(".lake/packages/"):
        return True
    if relative.startswith(VENDORED_PREFIX):
        return True
    prefix = ".lake/build/lib/lean/PrimeFactorUnimodality/"
    return relative.startswith((prefix + "Definitions/", prefix + "Helpers/")) and (
        "/FiniteCertificates/" not in relative
    )


def fetch(assets: Path, name: str, expected: str) -> Path:
    """Download a pinned public asset and verify it before use."""
    if Path(name).name != name:
        raise ValueError("asset must be a basename")
    assets.mkdir(parents=True, exist_ok=True)
    target = assets / name
    if not target.is_file():
        temporary = target.with_suffix(target.suffix + ".partial")
        print(f"Downloading {name}", flush=True)
        with (
            urllib.request.urlopen(f"{BASE}/{name}", timeout=120) as response,
            temporary.open("wb") as output,
        ):
            shutil.copyfileobj(response, output)
        if digest(temporary) != expected:
            raise ValueError(f"download hash mismatch: {name}")
        temporary.replace(target)
    if digest(target) != expected:
        raise ValueError(f"asset hash mismatch: {name}")
    return target


def restore(assets: Path, cache: Path = CACHE) -> dict[str, str]:
    """Restore a selected, checksum-verified subset without executing source code."""
    manifest_path = fetch(assets, MANIFEST, MANIFEST_SHA256)
    manifest = cast(dict[str, Any], json.loads(manifest_path.read_text(encoding="utf-8")))
    if manifest["commit"] != COMMIT or manifest["toolchain"] != TOOLCHAIN:
        raise ValueError("release identity does not match the dependency pin")
    restored: dict[str, str] = {}
    for part in manifest["parts"]:
        selected = {name: sha for name, sha in part["files"].items() if wanted(name)}
        if not selected:
            continue
        archive = fetch(assets, part["asset"], part["sha256"])
        pending = {
            name
            for name, sha in selected.items()
            if not (path := safe_target(cache, name)).is_file() or digest(path) != sha
        }
        if pending:
            print(f"Restoring {archive.name}: {len(pending)} artifacts", flush=True)
            with tarfile.open(archive, "r|gz") as bundle:
                for member in bundle:
                    if member.name not in pending:
                        continue
                    if not member.isfile():
                        raise ValueError(f"nonregular archive member: {member.name}")
                    destination = safe_target(cache, member.name)
                    destination.parent.mkdir(parents=True, exist_ok=True)
                    stream = bundle.extractfile(member)
                    if stream is None:
                        raise ValueError(f"unreadable archive member: {member.name}")
                    with stream, destination.open("wb") as output:
                        shutil.copyfileobj(stream, output)
                    if digest(destination) != selected[member.name]:
                        raise ValueError(f"artifact hash mismatch: {member.name}")
                    pending.remove(member.name)
            if pending:
                raise ValueError(f"archive omitted {len(pending)} required members")
        restored.update(selected)
    cache.mkdir(parents=True, exist_ok=True)
    receipt = {
        "commit": COMMIT,
        "toolchain": TOOLCHAIN,
        "manifest_sha256": MANIFEST_SHA256,
        "dependency_builds": 0,
        "scope": "Erdos leaves, vendored Mertens closure, released dependency libraries",
        "files": restored,
    }
    (cache / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print(f"Restored {len(restored)} verified artifacts; dependency builds: 0", flush=True)
    return restored


def verify(cache: Path = CACHE) -> list[Path]:
    """Reject absent or altered artifacts, with no compilation fallback."""
    receipt_path = cache / "receipt.json"
    if not receipt_path.is_file():
        raise ValueError("missing prebuilt cache; run scripts/prebuilt_dependency.py first")
    receipt = cast(dict[str, Any], json.loads(receipt_path.read_text(encoding="utf-8")))
    if receipt.get("commit") != COMMIT or receipt.get("toolchain") != TOOLCHAIN:
        raise ValueError("prebuilt cache identity mismatch")
    if receipt.get("manifest_sha256") != MANIFEST_SHA256 or not receipt.get("files"):
        raise ValueError("missing pinned manifest provenance or empty artifact inventory")
    if any(name not in receipt["files"] for name in REQUIRED_VENDORED_OLEANS):
        raise ValueError("incomplete vendored artifact closure; rerun cache restoration")
    for name, expected in receipt["files"].items():
        path = safe_target(cache, name)
        if not path.is_file() or digest(path) != expected:
            raise ValueError(f"missing or altered prebuilt artifact: {name}; rebuild forbidden")
    roots = [cache / ".lake/build/lib/lean"]
    roots.extend(sorted((cache / ".lake/packages").glob("*/.lake/build/lib/lean")))
    return roots


def main() -> int:
    """Restore or verify the pinned artifact cache."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--assets", type=Path, default=ROOT / ".lake/downloads")
    parser.add_argument("--verify", action="store_true")
    options = parser.parse_args()
    try:
        if options.verify:
            roots = verify()
            print(f"Verified cache with {len(roots)} library roots; dependency builds: 0")
        else:
            restore(options.assets)
    except (OSError, ValueError, KeyError, tarfile.TarError) as error:
        print(f"prebuilt dependency error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
