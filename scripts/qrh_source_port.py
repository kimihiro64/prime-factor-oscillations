"""Reconstruct the exact audited QRH sources from pinned upstream checkouts."""

from __future__ import annotations

import argparse
import hashlib
import sys
from collections.abc import Mapping
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if __package__ in {None, ""}:
    sys.path.insert(0, str(ROOT))

from scripts.analytic_dependency import load_artifact_manifests  # noqa: E402
from scripts.artifact_extensions import artifact_path  # noqa: E402


def ported_source(name: str, raw: bytes, manifest: Mapping[str, Any]) -> bytes:
    """Apply only the published adaptations and require the final source hash."""
    row = manifest["source_modules"][name]
    if hashlib.sha256(raw).hexdigest() != row["source_sha256"]:
        raise ValueError(f"original source differs from the pinned revision: {name}")
    text = raw.decode("utf-8")
    patch = manifest["compatibility_adaptations"].get(name)
    if patch is not None:
        if patch["source_sha256"] != row["source_sha256"]:
            raise ValueError(f"adaptation has a different source pin: {name}")
        for replacement in patch["replacements"]:
            old, new = replacement["old"], replacement["new"]
            if not new.isascii() or "!=" in new:
                raise ValueError(f"adaptation violates source policy: {name}")
            if text.count(old) != replacement.get("expected_count", 1):
                raise ValueError(f"adaptation context is missing or ambiguous: {name}")
            text = text.replace(old, new)
    if row["synchronous_elaboration"]:
        boundary = "\nnamespace OAI\n"
        if text.count(boundary) != 1:
            raise ValueError(f"synchronous elaboration boundary differs: {name}")
        text = text.replace(boundary, "\nset_option Elab.async false\n\nnamespace OAI\n")
    result = text.encode("utf-8")
    if hashlib.sha256(result).hexdigest() != row["port_source_sha256"]:
        raise ValueError(f"adapted source differs from the audited proof: {name}")
    return result


def main() -> int:
    """Write sources only; never build, download, or modify dependency checkouts."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checkout", action="append", required=True, metavar="OWNER/REPO=PATH")
    parser.add_argument("--output", required=True, type=Path)
    options = parser.parse_args()
    try:
        checkouts: dict[str, Path] = {}
        for item in options.checkout:
            repository, separator, raw_path = item.partition("=")
            path = Path(raw_path).resolve()
            if not separator or repository in checkouts or not path.is_dir():
                raise ValueError(f"invalid or duplicate source checkout: {item}")
            checkouts[repository] = path
        _, extensions, _ = load_artifact_manifests()
        manifest = extensions[-1]
        if manifest["kind"] != "append_only_verified_source_port":
            raise ValueError("the verified source-port manifest is absent")
        required = {row["repository"] for row in manifest["source_modules"].values()}
        if set(checkouts) != required:
            raise ValueError(f"provide exactly these source checkouts: {sorted(required)}")
        output = options.output.resolve()
        if any(output.is_relative_to(path) for path in checkouts.values()):
            raise ValueError("output must be outside the supplied source checkouts")
        count = 0
        for name, row in sorted(manifest["source_modules"].items()):
            source = artifact_path(checkouts[row["repository"]], row["path"])
            data = ported_source(name, source.read_bytes(), manifest)
            target = artifact_path(output, name.replace(".", "/") + ".lean")
            target.parent.mkdir(parents=True, exist_ok=True)
            if target.exists():
                if target.read_bytes() != data:
                    raise ValueError(f"different output preserved: {target}")
            else:
                with target.open("xb") as stream:
                    stream.write(data)
            count += 1
        print(f"Reconstructed {count} audited sources; no dependencies compiled.")
    except (OSError, ValueError, KeyError) as error:
        print(f"source reconstruction failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
