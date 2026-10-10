"""Source-byte reconstruction tests; these do not assert a Lean theorem."""

import hashlib
from typing import Any

import pytest

from scripts.qrh_source_port import ported_source


def fixture() -> tuple[bytes, bytes, dict[str, Any]]:
    original = b"import Mathlib.Test\n\nnamespace OAI\n-- original\nend OAI\n"
    result = original.replace(b"-- original", b"-- adapted").replace(
        b"\nnamespace OAI\n", b"\nset_option Elab.async false\n\nnamespace OAI\n"
    )
    sha = hashlib.sha256(original).hexdigest()
    manifest: dict[str, Any] = {
        "source_modules": {
            "OAI.Test": {
                "source_sha256": sha,
                "port_source_sha256": hashlib.sha256(result).hexdigest(),
                "synchronous_elaboration": True,
            }
        },
        "compatibility_adaptations": {
            "OAI.Test": {
                "source_sha256": sha,
                "replacements": [{"old": "-- original", "new": "-- adapted"}],
            }
        },
    }
    return original, result, manifest


def test_exact_adaptation_and_synchronous_elaboration() -> None:
    original, expected, manifest = fixture()
    assert ported_source("OAI.Test", original, manifest) == expected


@pytest.mark.parametrize("mutation", ["original", "context", "final"])
def test_changed_proof_bytes_or_context_rejected(mutation: str) -> None:
    original, _, manifest = fixture()
    if mutation == "original":
        original += b" "
    elif mutation == "context":
        manifest["compatibility_adaptations"]["OAI.Test"]["replacements"][0]["old"] = "missing"
    else:
        manifest["source_modules"]["OAI.Test"]["port_source_sha256"] = "a" * 64
    with pytest.raises(ValueError):
        ported_source("OAI.Test", original, manifest)
