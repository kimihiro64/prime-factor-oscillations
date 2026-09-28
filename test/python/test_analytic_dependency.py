"""Reject corrupted or incomplete artifact sets and research assumptions."""

import subprocess
from pathlib import Path

import pytest

from scripts.analytic_dependency import artifact_path, source_digest, verify_files
from scripts.build_project import compile_owned_module, module_fingerprint
from scripts.proof_audit import THEOREMS, axiom_sets


@pytest.mark.parametrize("relative", ["../bad", "/outside", "C:/outside", "x:stream", "x\\bad"])
def test_artifact_path_rejects_escapes(tmp_path: Path, relative: str) -> None:
    with pytest.raises(ValueError):
        artifact_path(tmp_path, relative)


def test_all_companions_required_and_hash_checked(tmp_path: Path) -> None:
    obj = tmp_path / "Test.olean"
    sig = tmp_path / "Test.ir.sig"
    obj.write_bytes(b"object")
    sig.write_bytes(b"signature")
    files = {p.name: source_digest(p) for p in (obj, sig)}
    verify_files(tmp_path, files)
    sig.unlink()
    with pytest.raises(ValueError, match="missing or altered"):
        verify_files(tmp_path, files)
    sig.write_bytes(b"changed")
    with pytest.raises(ValueError, match="missing or altered"):
        verify_files(tmp_path, files)


def test_empty_inventory_rejected(tmp_path: Path) -> None:
    with pytest.raises(ValueError, match="empty"):
        verify_files(tmp_path, {})


def test_axiom_audit_rejects_holes_and_missing_reports() -> None:
    log = "\n".join(
        f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]" for name in THEOREMS
    )
    assert set(axiom_sets(log)) == set(THEOREMS)
    with pytest.raises(ValueError, match="nonfoundational"):
        axiom_sets(log.replace("propext", "sorryAx"))
    with pytest.raises(ValueError, match="missing"):
        axiom_sets(log.splitlines()[0])


def test_owned_cache_invalidates_transitive_consumers_with_unchanged_sources() -> None:
    """A -> B -> C must invalidate C even when B's exported object bytes are unchanged."""
    old_a = module_fingerprint("old-a", {}, "compiler", "manifest")
    new_a = module_fingerprint("new-a", {}, "compiler", "manifest")
    old_b = module_fingerprint("same-b-source", {"A": old_a}, "compiler", "manifest")
    new_b = module_fingerprint("same-b-source", {"A": new_a}, "compiler", "manifest")
    old_c = module_fingerprint("same-c-source", {"B": old_b}, "compiler", "manifest")
    new_c = module_fingerprint("same-c-source", {"B": new_b}, "compiler", "manifest")
    assert old_b != new_b
    assert old_c != new_c


def test_owned_cache_dependency_order_does_not_change_identity() -> None:
    assert module_fingerprint("s", {"A": "a", "B": "b"}, "v", "m") == module_fingerprint(
        "s", {"B": "b", "A": "a"}, "v", "m"
    )


@pytest.mark.parametrize(
    ("source", "version", "manifest"),
    [("changed", "v", "m"), ("s", "changed", "m"), ("s", "v", "changed")],
)
def test_owned_cache_tracks_source_and_environment(
    source: str, version: str, manifest: str
) -> None:
    assert module_fingerprint(source, {}, version, manifest) != module_fingerprint(
        "s", {}, "v", "m"
    )


def test_owned_compile_retries_only_native_failures(monkeypatch: pytest.MonkeyPatch) -> None:
    attempts: list[list[str]] = []

    def run(command: list[str], **options: object) -> subprocess.CompletedProcess[bytes]:
        assert options["check"] is True
        attempts.append(command)
        if len(attempts) == 1:
            raise subprocess.CalledProcessError(3221225477, command)
        return subprocess.CompletedProcess(command, 0)

    monkeypatch.setattr(subprocess, "run", run)
    compile_owned_module(["verified-lean", "owned.lean"], {})
    assert attempts == [["verified-lean", "owned.lean"]] * 2


@pytest.mark.parametrize(("code", "expected_attempts"), [(1, 1), (2, 1), (3221226505, 3)])
def test_owned_compile_failures_stop_with_bounded_retries(
    monkeypatch: pytest.MonkeyPatch, code: int, expected_attempts: int
) -> None:
    calls = 0

    def run(command: list[str], **options: object) -> subprocess.CompletedProcess[bytes]:
        nonlocal calls
        assert options["check"] is True
        calls += 1
        raise subprocess.CalledProcessError(code, command)

    monkeypatch.setattr(subprocess, "run", run)
    with pytest.raises(subprocess.CalledProcessError) as caught:
        compile_owned_module(["verified-lean", "owned.lean"], {})
    assert caught.value.returncode == code
    assert calls == expected_attempts
