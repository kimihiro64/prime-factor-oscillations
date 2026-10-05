"""Exercise additive-cache compatibility without touching real artifacts or Lean."""

from __future__ import annotations

import copy
import json
import os
import shutil
import subprocess
from pathlib import Path
from typing import Any

import pytest

from scripts import analytic_dependency, build_project
from scripts.analytic_dependency import MANIFEST_SHA256, source_digest
from scripts.artifact_extensions import (
    AnalyticEnvironment,
    artifact_path,
    extension_files,
    require_report_environment,
    validate_cache_transition,
    verify_extension_companions,
    verify_files,
)
from scripts.prebuilt_dependency import COMMIT, TOOLCHAIN

COMPILER = "Lean (version 4.34.0, pinned Windows test fixture)"


def extension(root: Path, module: str = "Mathlib.New") -> dict[str, Any]:
    stem = module.replace(".", "/")
    files = {}
    for suffix in (".olean", ".ir.sig", ".olean.private"):
        relative = stem + suffix
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(relative.encode())
        files[relative] = source_digest(path)
    return {
        "schema_version": 1,
        "kind": "append_only_artifact_extension",
        "base_manifest_sha256": MANIFEST_SHA256,
        "toolchain": TOOLCHAIN,
        "compiler": COMPILER,
        "mathlib_commit": "mathlib",
        "files": files,
        "modules": {
            module: {"module": module, "relative_path": stem + ".lean", "artifacts": list(files)}
        },
    }


def validate(data: dict[str, Any], known: dict[str, str] | None = None) -> dict[str, str]:
    return extension_files(
        data,
        known or {},
        base_sha256=MANIFEST_SHA256,
        toolchain=TOOLCHAIN,
        compiler=COMPILER,
        mathlib_commit="mathlib",
    )


def environment(root: Path, pins: tuple[tuple[str, str], ...]) -> AnalyticEnvironment:
    (root / "Mathlib").mkdir(parents=True, exist_ok=True)
    return AnalyticEnvironment(root, MANIFEST_SHA256, pins, TOOLCHAIN, COMPILER, "mathlib")


def test_complete_extension_changes_digest_but_keeps_compatible_anchor(tmp_path: Path) -> None:
    data = extension(tmp_path)
    files = validate(data)
    verify_files(tmp_path, files)
    verify_extension_companions(tmp_path, data)
    old = environment(tmp_path, ()).snapshot(tmp_path / "owned", "lean")
    new = environment(tmp_path, (("ext.json", "pin"),)).snapshot(tmp_path / "owned", "lean")
    assert old["analytic_environment_sha256"] != new["analytic_environment_sha256"]
    assert old["compatibility_anchor"] == new["compatibility_anchor"] == MANIFEST_SHA256
    validate_cache_transition(
        old,
        new,
        has_cached_modules=True,
        legacy_report_sha256="report-hash",
        installation=installation(new, "report-hash"),
    )


@pytest.mark.parametrize("mutation", ["missing-signature", "altered-private", "extra-companion"])
def test_companion_failures(tmp_path: Path, mutation: str) -> None:
    data = extension(tmp_path)
    if mutation == "missing-signature":
        (tmp_path / "Mathlib/New.ir.sig").unlink()
    elif mutation == "altered-private":
        (tmp_path / "Mathlib/New.olean.private").write_bytes(b"altered")
    else:
        (tmp_path / "Mathlib/New.future-runtime-companion").write_bytes(b"unexpected")
    with pytest.raises(ValueError):
        verify_files(tmp_path, validate(data))
        verify_extension_companions(tmp_path, data)


@pytest.mark.parametrize(
    "key", ["base_manifest_sha256", "toolchain", "compiler", "mathlib_commit", "kind"]
)
def test_extension_provenance_mismatch(tmp_path: Path, key: str) -> None:
    data = extension(tmp_path)
    data[key] = "different"
    with pytest.raises(ValueError, match="provenance"):
        validate(data)


def test_extension_manifest_must_match_its_saved_pin(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    base = {
        "toolchain": TOOLCHAIN,
        "erdos690_commit": COMMIT,
        "compiler": COMPILER,
        "files": {"Mathlib/Old.olean": "0" * 64},
    }
    manifest = tmp_path / "base.json"
    manifest.write_text(json.dumps(base), encoding="utf-8")
    base_hash = source_digest(manifest)
    data = extension(tmp_path)
    data["base_manifest_sha256"] = base_hash
    ext = tmp_path / "extension.json"
    ext.write_text(json.dumps(data), encoding="utf-8")
    monkeypatch.setattr(analytic_dependency, "ROOT", tmp_path)
    monkeypatch.setattr(analytic_dependency, "MANIFEST", manifest)
    monkeypatch.setattr(analytic_dependency, "MANIFEST_SHA256", base_hash)
    monkeypatch.setattr(analytic_dependency, "MATHLIB_COMMIT", "mathlib")
    monkeypatch.setattr(
        analytic_dependency, "EXTENSION_PINS", (("extension.json", source_digest(ext)),)
    )
    analytic_dependency.load_artifact_manifests()
    ext.write_text(json.dumps(data) + "\n", encoding="utf-8")
    with pytest.raises(ValueError, match="immutable pin"):
        analytic_dependency.load_artifact_manifests()


def test_overlap_and_new_companion_on_old_module_rejected(tmp_path: Path) -> None:
    data = extension(tmp_path)
    with pytest.raises(ValueError, match="overlapping"):
        validate(data, {"Mathlib/New.olean": data["files"]["Mathlib/New.olean"]})
    with pytest.raises(ValueError, match="existing module"):
        altered = copy.deepcopy(data)
        del altered["files"]["Mathlib/New.olean"]
        validate(altered, {"Mathlib/New.olean": "old"})


def test_case_collision_and_file_map_mismatch_rejected(tmp_path: Path) -> None:
    data = extension(tmp_path)
    data["files"]["mathlib/new.olean"] = data["files"]["Mathlib/New.olean"]
    with pytest.raises(ValueError, match="case-colliding"):
        validate(data)
    del data["files"]["mathlib/new.olean"]
    data["modules"]["Mathlib.New"]["artifacts"].pop()
    with pytest.raises(ValueError, match="complete extension file map"):
        validate(data)


@pytest.mark.parametrize("path", ["a//b", "a/./b", "Mathlib/A.", "nul.olean", "a ", "../a"])
def test_windows_aliases_rejected(tmp_path: Path, path: str) -> None:
    with pytest.raises(ValueError, match="unsafe"):
        artifact_path(tmp_path, path)


@pytest.mark.parametrize("pins", [(), (("one", "changed"),), (("two", "2"), ("one", "1"))])
def test_history_removal_mutation_and_reordering_rejected(
    tmp_path: Path, pins: tuple[tuple[str, str], ...]
) -> None:
    old = environment(tmp_path, (("one", "1"), ("two", "2"))).snapshot(tmp_path / "owned", "lean")
    new = environment(tmp_path, pins).snapshot(tmp_path / "owned", "lean")
    with pytest.raises(ValueError, match="prefix"):
        validate_cache_transition(old, new, has_cached_modules=True)


def test_provider_shadow_and_root_change_rejected(tmp_path: Path) -> None:
    owned = tmp_path / "owned"
    env = environment(tmp_path / "external", ())
    old = env.snapshot(owned, "lean")
    changed = env.snapshot(tmp_path / "other-owned", "lean")
    with pytest.raises(ValueError, match="ordered_roots"):
        validate_cache_transition(old, changed, has_cached_modules=True)
    (owned / "Mathlib").mkdir(parents=True)
    with pytest.raises(ValueError, match="shadows"):
        env.snapshot(owned, "lean")


def legacy_report(current: dict[str, Any]) -> dict[str, Any]:
    return {
        "analytic_manifest_sha256": current["base_manifest_sha256"],
        "toolchain": current["toolchain"],
        "version": current["compiler"],
        "compiler_executable": current["compiler_executable"],
        "lean_path": os.pathsep.join(current["ordered_roots"]),
        "dependency_builds": 0,
        "checked_owned_modules": ["A"],
    }


def installation(current: dict[str, Any], report_hash: str) -> dict[str, Any]:
    return {
        "status": "complete",
        "base_manifest_sha256": current["base_manifest_sha256"],
        "extension_pins": current["extension_pins"],
        "previous_extension_pins": [],
        "root": current["ordered_roots"][1],
        "base_build_report_sha256": report_hash,
        "new_paths_previously_absent": True,
        "original_artifacts_unchanged": True,
    }


def test_legacy_migration_requires_matching_success_report_and_receipt(tmp_path: Path) -> None:
    current = environment(tmp_path, (("ext", "pin"),)).snapshot(tmp_path / "owned", "lean")
    report = legacy_report(current)
    with pytest.raises(ValueError, match="successful baseline"):
        validate_cache_transition(None, current, has_cached_modules=True)
    with pytest.raises(ValueError, match="installation evidence"):
        validate_cache_transition(None, current, has_cached_modules=True, legacy_report=report)
    receipt = installation(current, "report-hash")
    validate_cache_transition(
        None,
        current,
        has_cached_modules=True,
        legacy_report=report,
        legacy_report_sha256="report-hash",
        installation=receipt,
    )
    receipt["base_build_report_sha256"] = "stale"
    with pytest.raises(ValueError, match="installation evidence"):
        validate_cache_transition(
            None,
            current,
            has_cached_modules=True,
            legacy_report=report,
            legacy_report_sha256="report-hash",
            installation=receipt,
        )


def test_audit_requires_current_digest_and_actual_provider_path(tmp_path: Path) -> None:
    old = environment(tmp_path, ()).snapshot(tmp_path / "owned", "lean")
    new = environment(tmp_path, (("ext", "pin"),)).snapshot(tmp_path / "owned", "lean")
    report = {**legacy_report(old), "analytic_environment": old}
    with pytest.raises(ValueError, match="owned build"):
        require_report_environment(report, new)
    report["analytic_environment"] = new
    require_report_environment(report, new)
    report["lean_path"] = "unverified-root"
    with pytest.raises(ValueError, match="owned build"):
        require_report_environment(report, new)


@pytest.mark.parametrize("reuse", [False, True])
def test_build_reuses_compatible_rows_and_records_environment_before_failure(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, reuse: bool
) -> None:
    source = tmp_path / "A.lean"
    source.write_text("-- changed source\n", encoding="utf-8")
    (tmp_path / "lean-toolchain").write_text(TOOLCHAIN, encoding="utf-8")
    lean = tmp_path / "lean.exe"
    lean.write_bytes(b"test fixture; never executed")
    env = environment(tmp_path / "external", (("ext", "pin"),))
    current = env.snapshot(tmp_path / ".lake/build/lib/lean", str(lean))
    report = legacy_report(current)
    build = tmp_path / ".lake/build"
    build.mkdir(parents=True)
    report_path = build / "project-build.json"
    report_path.write_text(json.dumps(report), encoding="utf-8")
    cache_path = build / "owned-module-cache.json"
    row: dict[str, Any] = {}
    if reuse:
        obj = build / "lib/lean/A.olean"
        obj.parent.mkdir(parents=True)
        obj.write_bytes(b"existing successful object")
        row = {
            "exit_code": 0,
            "source_sha256": source_digest(source),
            "object_sha256": source_digest(obj),
            "dependencies": {},
            "closure_sha256": build_project.module_fingerprint(
                source_digest(source), {}, COMPILER, MANIFEST_SHA256
            ),
        }
    cache_path.write_text(json.dumps({"modules": {"A": row}}), encoding="utf-8")
    receipt = installation(current, source_digest(report_path))
    (tmp_path / ".lake/analytic-extension-installation.json").write_text(
        json.dumps(receipt), encoding="utf-8"
    )
    monkeypatch.setattr(build_project, "ROOT", tmp_path)
    monkeypatch.setattr(build_project, "verify_environment", lambda: env)
    monkeypatch.setattr(shutil, "which", lambda name: str(lean) if name == "lean" else None)
    monkeypatch.setattr(build_project, "library_namespace", lambda _root: "A")
    monkeypatch.setattr(
        build_project, "owned_graph", lambda _root, _ns: ({"A": source}, {"A": set()})
    )

    def version(command: list[str], **_kwargs: object) -> subprocess.CompletedProcess[str]:
        assert command == [str(lean), "--version"]
        return subprocess.CompletedProcess(command, 0, COMPILER)

    def fail(command: list[str], _environment: dict[str, str]) -> None:
        saved = json.loads(cache_path.read_text(encoding="utf-8"))
        assert saved["analytic_environment"] == current
        raise subprocess.CalledProcessError(1, command)

    monkeypatch.setattr(subprocess, "run", version)
    monkeypatch.setattr(build_project, "compile_owned_module", fail)
    assert build_project.main() == (0 if reuse else 1)
    if reuse:
        completed = json.loads(report_path.read_text(encoding="utf-8"))
        assert completed["analytic_environment"] == current
        assert completed["reused_owned_modules"] == ["A"]
        assert completed["compiled_owned_modules"] == []
        require_report_environment(completed, current)
    else:
        assert json.loads(report_path.read_text(encoding="utf-8")) == report
    saved = json.loads(cache_path.read_text(encoding="utf-8"))
    assert saved["analytic_environment"] == current
    older = environment(tmp_path / "external", ()).snapshot(
        tmp_path / ".lake/build/lib/lean", str(lean)
    )
    with pytest.raises(ValueError, match="prefix"):
        validate_cache_transition(saved["analytic_environment"], older, has_cached_modules=True)
