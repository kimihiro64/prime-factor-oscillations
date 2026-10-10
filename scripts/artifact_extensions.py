"""Validate immutable additive artifacts and preserve compatible owned caches."""

from __future__ import annotations

import hashlib
import json
import os
import re
from collections.abc import Mapping, Sequence
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from itertools import islice
from pathlib import Path, PurePosixPath
from typing import Any, cast

from scripts.prebuilt_dependency import digest
from scripts.qrh_source_extension import validate_source_port


def artifact_path(root: Path, relative: str) -> Path:
    """Reject escaping paths and Windows aliases before resolving a provider."""
    parts = PurePosixPath(relative).parts
    reserved = {"con", "prn", "aux", "nul", "clock$"}
    reserved.update(f"{prefix}{i}" for prefix in ("com", "lpt") for i in range(1, 10))
    if (
        not parts
        or PurePosixPath(relative).as_posix() != relative
        or PurePosixPath(relative).is_absolute()
        or ":" in relative
        or "\\" in relative
        or any(
            part in {".", ".."}
            or part.endswith((".", " "))
            or part.split(".")[0].casefold() in reserved
            for part in parts
        )
    ):
        raise ValueError(f"unsafe artifact path: {relative}")
    target = (root / relative).resolve()
    if not target.is_relative_to(root.resolve()):
        raise ValueError(f"artifact path escapes its root: {relative}")
    return target


def verify_files(root: Path, files: Mapping[str, str]) -> None:
    """Check every supplied companion; never fetch or compile on a miss."""
    if not files:
        raise ValueError("empty analytic artifact inventory")

    def check(item: tuple[str, str]) -> None:
        relative, expected = item
        path = artifact_path(root, relative)
        if not path.is_file() or digest(path) != expected:
            raise ValueError(
                f"missing or altered artifact: {relative}; dependency rebuild forbidden"
            )

    # Hash every file as before, with bounded I/O concurrency and queue size.
    # Exhaust each batch so an error cannot be mistaken for completed validation.
    remaining = iter(files.items())
    with ThreadPoolExecutor(max_workers=4) as pool:
        while batch := list(islice(remaining, 64)):
            for _ in pool.map(check, batch):
                pass


def extension_files(
    extension: Mapping[str, Any],
    known_files: Mapping[str, str],
    *,
    base_sha256: str,
    toolchain: str,
    compiler: str,
    mathlib_commit: str,
) -> dict[str, str]:
    """Check a complete new-module set, not merely disjoint filenames."""
    expected = {
        "schema_version": 1,
        "base_manifest_sha256": base_sha256,
        "toolchain": toolchain,
        "compiler": compiler,
        "mathlib_commit": mathlib_commit,
    }
    if any(extension.get(key) != value for key, value in expected.items()):
        raise ValueError("extension provenance differs from the immutable pins")
    kind = extension.get("kind")
    if kind not in {"append_only_artifact_extension", "append_only_verified_source_port"}:
        raise ValueError("extension provenance has an unknown artifact kind")
    files = cast(dict[str, str], extension["files"])
    modules = cast(dict[str, dict[str, Any]], extension["modules"])
    if not files or not modules:
        raise ValueError("empty extension inventory")
    known_folded = {name.casefold() for name in known_files}
    folded: set[str] = set()
    for relative, expected_hash in files.items():
        artifact_path(Path.cwd(), relative)
        key = relative.casefold()
        if key in known_folded or key in folded:
            raise ValueError(f"overlapping or case-colliding artifact: {relative}")
        if re.fullmatch(r"[0-9a-f]{64}", expected_hash) is None:
            raise ValueError(f"invalid artifact digest: {relative}")
        folded.add(key)
    supplied: set[str] = set()
    for module, row in modules.items():
        namespace = (
            "Mathlib"
            if kind == "append_only_artifact_extension"
            else "(?:OAI|RellichKondrachov|PrimeNumberTheoremAnd)"
        )
        if re.fullmatch(namespace + r"(?:\.[A-Za-z0-9_']+)+", module) is None:
            raise ValueError(f"extension is outside its approved provider: {module}")
        stem = module.replace(".", "/")
        if (stem + ".olean").casefold() in known_folded:
            raise ValueError(f"extension adds companions to an existing module: {module}")
        required = cast(list[str], row["artifacts"])
        if (
            row.get("module") != module
            or row.get("relative_path") != stem + ".lean"
            or not required
            or len(required) != len(set(required))
            or stem + ".olean" not in required
            or any(not path.startswith(stem + ".") for path in required)
            or supplied.intersection(required)
        ):
            raise ValueError(f"invalid module companion inventory: {module}")
        supplied.update(required)
    if supplied != set(files):
        raise ValueError("module companions do not equal the complete extension file map")
    if kind == "append_only_verified_source_port":
        validate_source_port(extension, known_files)
    return dict(files)


def verify_extension_companions(root: Path, extension: Mapping[str, Any]) -> None:
    """Compare all supplied regular companions, with no suffix selection list."""
    for module, row in extension["modules"].items():
        stem = module.replace(".", "/")
        path = artifact_path(root, stem)
        actual = {
            item.relative_to(root).as_posix()
            for item in path.parent.glob(path.name + ".*")
            if item.is_file()
        }
        if actual != set(row["artifacts"]):
            raise ValueError(f"incomplete or unexpected artifact companions: {module}")


@dataclass(frozen=True)
class AnalyticEnvironment:
    """The actual pins, separately from their compatible fingerprint anchor."""

    root: Path
    base_sha256: str
    extension_pins: tuple[tuple[str, str], ...]
    toolchain: str
    compiler: str
    mathlib_commit: str

    def pin_record(self) -> dict[str, Any]:
        """Return the portable, complete environment identity."""
        return {
            "schema_version": 1,
            "base_manifest_sha256": self.base_sha256,
            "extension_pins": [{"path": path, "sha256": sha} for path, sha in self.extension_pins],
            "toolchain": self.toolchain,
            "compiler": self.compiler,
            "mathlib_commit": self.mathlib_commit,
        }

    def snapshot(self, owned_root: Path, compiler_executable: str) -> dict[str, Any]:
        """Record exact providers; reject any earlier external namespace shadow."""
        for name in ("Mathlib", "OAI", "RellichKondrachov", "PrimeNumberTheoremAnd"):
            if (owned_root / name).exists() or (owned_root / (name + ".olean")).exists():
                raise ValueError(f"owned artifact root shadows the verified {name} provider")
        if not (self.root / "Mathlib").is_dir():
            raise ValueError("verified Mathlib namespace root is absent")
        pins = self.pin_record()
        return {
            **pins,
            "analytic_environment_sha256": hashlib.sha256(
                json.dumps(pins, sort_keys=True).encode("utf-8")
            ).hexdigest(),
            "compatibility_anchor": self.base_sha256,
            "ordered_roots": [str(owned_root.resolve()), str(self.root.resolve())],
            "compiler_executable": str(Path(compiler_executable).resolve()),
        }


def require_installation_evidence(
    current: Mapping[str, Any],
    previous_pins: Sequence[dict[str, str]],
    report_sha256: str | None,
    installation: Mapping[str, Any] | None,
) -> None:
    """Every extension addition needs its preserved, exclusive-copy receipt."""
    if (
        not report_sha256
        or installation is None
        or installation.get("status") != "complete"
        or installation.get("base_manifest_sha256") != current["base_manifest_sha256"]
        or installation.get("extension_pins") != current["extension_pins"]
        or installation.get("previous_extension_pins") != list(previous_pins)
        or installation.get("root") != current["ordered_roots"][1]
        or installation.get("base_build_report_sha256") != report_sha256
        or installation.get("new_paths_previously_absent") is not True
        or installation.get("original_artifacts_unchanged") is not True
    ):
        raise ValueError("cache migration lacks verified additive installation evidence")


def validate_cache_transition(
    previous: Mapping[str, Any] | None,
    current: Mapping[str, Any],
    *,
    has_cached_modules: bool,
    legacy_report: Mapping[str, Any] | None = None,
    legacy_report_sha256: str | None = None,
    installation: Mapping[str, Any] | None = None,
) -> None:
    """License baseline fingerprints only for verified append-only transitions."""
    if not has_cached_modules:
        return
    if previous is not None:
        for key in (
            "base_manifest_sha256",
            "compatibility_anchor",
            "toolchain",
            "compiler",
            "mathlib_commit",
            "ordered_roots",
            "compiler_executable",
        ):
            if previous.get(key) != current.get(key):
                raise ValueError(f"incompatible cached environment: {key}")
        prior = cast(list[dict[str, str]], previous["extension_pins"])
        now = cast(list[dict[str, str]], current["extension_pins"])
        if len(prior) > len(now) or now[: len(prior)] != prior:
            raise ValueError("extension history is not an immutable append-only prefix")
        if len(prior) < len(now):
            require_installation_evidence(current, prior, legacy_report_sha256, installation)
        return
    if legacy_report is None:
        raise ValueError("legacy cache requires its successful baseline build report")
    roots = cast(Sequence[str], current["ordered_roots"])
    if (
        legacy_report.get("analytic_manifest_sha256") != current["base_manifest_sha256"]
        or legacy_report.get("toolchain") != current["toolchain"]
        or legacy_report.get("version") != current["compiler"]
        or legacy_report.get("compiler_executable") != current["compiler_executable"]
        or legacy_report.get("lean_path") != os.pathsep.join(roots)
        or legacy_report.get("dependency_builds") != 0
        or not legacy_report.get("checked_owned_modules")
    ):
        raise ValueError("legacy build does not match the baseline compiler/providers")
    if current["extension_pins"]:
        require_installation_evidence(current, [], legacy_report_sha256, installation)


def require_report_environment(report: Mapping[str, Any], current: Mapping[str, Any]) -> None:
    """A fresh audit requires the actual environment, not just its anchor."""
    if (
        report.get("analytic_environment") != current
        or report.get("lean_path") != os.pathsep.join(current["ordered_roots"])
        or report.get("version") != current["compiler"]
        or report.get("compiler_executable") != current["compiler_executable"]
    ):
        raise ValueError("build environment differs; run the owned build before this audit")
