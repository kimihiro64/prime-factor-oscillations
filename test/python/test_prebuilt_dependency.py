"""Regression tests for the dependency no-rebuild boundary."""

import json
from pathlib import Path

import pytest

from scripts.build_project import build_order
from scripts.prebuilt_dependency import (
    COMMIT,
    MANIFEST_SHA256,
    TOOLCHAIN,
    safe_target,
    verify,
    wanted,
)


@pytest.mark.parametrize(
    "path",
    [
        "../outside.olean",
        "/.lake/build/lib/lean/Bad.olean",
        ".lake/build/lib/lean/../../../../outside.olean",
        ".lake/build/lib/lean/Bad.olean:stream",
        ".lake\\build\\lib\\lean\\Bad.olean",
    ],
)
def test_archive_escape_is_rejected(tmp_path: Path, path: str) -> None:
    with pytest.raises(ValueError):
        safe_target(tmp_path, path)


def test_missing_cache_is_a_hard_error(tmp_path: Path) -> None:
    with pytest.raises(ValueError, match="missing prebuilt cache"):
        verify(tmp_path)
    assert list(tmp_path.iterdir()) == []


def test_scope_excludes_classification_certificates() -> None:
    assert wanted(".lake/build/lib/lean/PrimeFactorUnimodality/Definitions/FiniteDensity.olean")
    assert not wanted(".lake/build/lib/lean/PrimeFactorUnimodality/Proof/LargeRange/Big.olean")
    assert not wanted(
        ".lake/build/lib/lean/PrimeFactorUnimodality/Helpers/FiniteCertificates/Big.olean"
    )


def test_owned_build_order_and_cycle_rejection() -> None:
    assert build_order({"Root": {"Leaf"}, "Leaf": set()}) == ["Leaf", "Root"]
    with pytest.raises(ValueError, match="cycle"):
        build_order({"A": {"B"}, "B": {"A"}})


@pytest.mark.parametrize("module", ["EulerMaclaurin", "Mertens"])
def test_mertens_companion_artifacts_are_restored(module: str) -> None:
    prefix = f".lake/build/lib/lean/VendorPrimeNumberTheoremAnd/{module}"
    for suffix in (".olean", ".olean.private", ".olean.server", ".ilean"):
        assert wanted(prefix + suffix)
    assert not wanted(f".lake/build/ir/VendorPrimeNumberTheoremAnd/{module}.c")


def test_stale_receipt_cannot_hide_missing_vendored_closure(tmp_path: Path) -> None:
    provider = ".lake/build/lib/lean/PrimeFactorUnimodality/Helpers/Analytic/MertensProvider.olean"
    receipt = {
        "commit": COMMIT,
        "toolchain": TOOLCHAIN,
        "manifest_sha256": MANIFEST_SHA256,
        "files": {provider: "unused"},
    }
    (tmp_path / "receipt.json").write_text(json.dumps(receipt), encoding="utf-8")
    with pytest.raises(ValueError, match="incomplete vendored artifact closure"):
        verify(tmp_path)
