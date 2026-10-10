"""Synthetic metadata tests, never mathematical proof or real Lean artifacts."""

import copy
import hashlib
from typing import Any

import pytest

from scripts.artifact_extensions import extension_files
from scripts.qrh_source_extension import (
    ENDPOINTS,
    FOUNDATIONS,
    ROOT_MODULE,
    SOURCE_PINS,
    validate_source_port,
)


def sample() -> tuple[dict[str, Any], dict[str, str]]:
    inherited = "PrimeNumberTheoremAnd.Fourier"
    sha = "a" * 64
    canonical_fixture = "synthetic metadata fixture, not a Lean proof"
    known = {inherited.replace(".", "/") + suffix: sha for suffix in (".olean", ".ir.sig")}
    sources: dict[str, Any] = {}
    for name, imports in ((ROOT_MODULE, [inherited, "Mathlib.Test"]), (inherited, [])):
        repo, commit = SOURCE_PINS[name.split(".", 1)[0]]
        sources[name] = {
            "repository": repo,
            "commit": commit,
            "path": name.replace(".", "/") + ".lean",
            "source_sha256": sha,
            "port_source_sha256": sha,
            "fingerprint": sha,
            "imports": imports,
        }
    data: dict[str, Any] = {
        "kind": "append_only_verified_source_port",
        "root_module": ROOT_MODULE,
        "source_commit": SOURCE_PINS["OAI"][1],
        "source_modules": sources,
        "modules": {ROOT_MODULE: {}},
        "files": {ROOT_MODULE.replace(".", "/") + ".olean": sha},
        "inherited_modules": {inherited: dict(known)},
        "endpoint_audit": {
            "source_sha256": sha,
            "log_sha256": sha,
            "object_sha256": sha,
            "root_fingerprint": sha,
            "canonical_specification": {
                "source_text": canonical_fixture,
                "source_sha256": hashlib.sha256(canonical_fixture.encode()).hexdigest(),
                "log_sha256": sha,
                "artifacts": {"QRHMathlibTarget.olean": sha},
            },
            "axiom_reports": [
                {"declaration": name, "axioms": FOUNDATIONS} for name in sorted(ENDPOINTS)
            ],
        },
    }
    known["Mathlib/Test.olean"] = sha
    return data, known


def test_matching_source_closure_and_complete_inherited_companions() -> None:
    data, known = sample()
    validate_source_port(data, known)


def test_transitive_artifact_missing_is_rejected() -> None:
    data, known = sample()
    del known["Mathlib/Test.olean"]
    with pytest.raises(ValueError, match="missing QRH dependency"):
        validate_source_port(data, known)


def test_dropped_inherited_signature_is_rejected() -> None:
    data, known = sample()
    data["inherited_modules"]["PrimeNumberTheoremAnd.Fourier"].pop(
        "PrimeNumberTheoremAnd/Fourier.ir.sig"
    )
    with pytest.raises(ValueError, match="inherited QRH companions"):
        validate_source_port(data, known)


@pytest.mark.parametrize("mutation", ["revision", "cycle", "disconnected", "target-axiom", "stale"])
def test_invalid_source_or_audit_is_rejected(mutation: str) -> None:
    data, known = sample()
    if mutation == "revision":
        data["source_modules"][ROOT_MODULE]["commit"] = "b" * 40
    elif mutation == "cycle":
        data["source_modules"]["PrimeNumberTheoremAnd.Fourier"]["imports"] = [ROOT_MODULE]
    elif mutation == "disconnected":
        row = copy.deepcopy(data["source_modules"][ROOT_MODULE])
        row["imports"] = []
        data["source_modules"]["OAI.Unrelated"] = row
        data["modules"]["OAI.Unrelated"] = {}
        data["files"]["OAI/Unrelated.olean"] = "a" * 64
    elif mutation == "target-axiom":
        data["endpoint_audit"]["axiom_reports"][0]["axioms"] = ["ResearchTarget"]
    else:
        data["endpoint_audit"]["root_fingerprint"] = "b" * 64
    with pytest.raises(ValueError):
        validate_source_port(data, known)


def test_both_actual_endpoints_are_required() -> None:
    data, known = sample()
    data["endpoint_audit"]["axiom_reports"].pop()
    with pytest.raises(ValueError, match="missing actual"):
        validate_source_port(data, known)


def test_changed_canonical_specification_source_is_rejected() -> None:
    data, known = sample()
    data["endpoint_audit"]["canonical_specification"]["source_text"] += " changed"
    with pytest.raises(ValueError, match="canonical specification source"):
        validate_source_port(data, known)


def test_missing_canonical_specification_is_rejected() -> None:
    data, known = sample()
    del data["endpoint_audit"]["canonical_specification"]
    with pytest.raises(ValueError, match="missing independent"):
        validate_source_port(data, known)


def test_source_port_passes_common_checks_and_rejects_target_axiom() -> None:
    data, known = sample()
    stem = ROOT_MODULE.replace(".", "/")
    data.update(
        schema_version=1,
        base_manifest_sha256="d" * 64,
        toolchain="fixture",
        compiler="fixture",
        mathlib_commit="e" * 40,
    )
    data["modules"][ROOT_MODULE] = {
        "module": ROOT_MODULE,
        "relative_path": stem + ".lean",
        "artifacts": [stem + ".olean"],
    }
    options = {
        "base_sha256": "d" * 64,
        "toolchain": "fixture",
        "compiler": "fixture",
        "mathlib_commit": "e" * 40,
    }
    assert extension_files(data, known, **options) == data["files"]
    data["endpoint_audit"]["axiom_reports"][0]["axioms"] = ["ResearchTarget"]
    with pytest.raises(ValueError, match="nonstandard"):
        extension_files(data, known, **options)
