from __future__ import annotations

import json
import subprocess
from pathlib import Path

import pytest

from scripts.check import (
    CheckFailure,
    check_metadata,
    check_submission_link,
    is_private_path,
    public_candidate_paths,
    tracked_public_size,
)
from scripts.import_graph import (
    detect_cycles,
    module_layer,
    transitive_dependents,
)
from scripts.lean_source import (
    LeanSourceError,
    check_comparator_boundary,
    check_lean_sources,
    lean_imports,
    strip_lean_comments,
)
from scripts.mathlib_candidates import (
    is_mathlib_candidate,
    mathlib_candidate_failures,
    mathlib_manifest_failures,
)


def test_private_path_boundary_is_component_aware() -> None:
    assert is_private_path(".research/GOAL.json")
    assert is_private_path("AGENTS.md")
    assert not is_private_path("scripts/research_experiment.py")
    assert not is_private_path("AGENTS.md.example")


def test_nested_lean_comments_are_removed() -> None:
    source = "theorem ok : True := by\n  /- sorry /- admit -/ -/ trivial\n"
    stripped = strip_lean_comments(source)
    assert "sorry" not in stripped
    assert "admit" not in stripped
    assert "trivial" in stripped
    assert stripped.count("\n") == source.count("\n")


def test_import_parser_ignores_comments() -> None:
    source = strip_lean_comments("/- import Mathlib -/\nimport Mathlib.Data.Nat.Basic\n")
    assert lean_imports(source) == ["Mathlib.Data.Nat.Basic"]


def test_dependency_cycle_detection() -> None:
    graph = {"A": {"B"}, "B": {"C"}, "C": {"A"}}
    assert detect_cycles(graph) == [["A", "B", "C", "A"]]


def test_transitive_blast_radius() -> None:
    graph = {"A": set(), "B": {"A"}, "C": {"B"}, "D": {"A"}}
    impact = transitive_dependents(graph)
    assert impact["A"] == {"B", "C", "D"}
    assert impact["B"] == {"C"}


def test_mathlib_candidate_layer_is_innermost_and_extractable() -> None:
    namespace = "ExampleTheorem"
    candidate = "ExampleTheorem.Mathlib.NumberTheory.Helper"
    owned = {
        "ExampleTheorem.Mathlib",
        candidate,
        "ExampleTheorem.Definitions.Core",
    }
    assert is_mathlib_candidate(candidate, namespace)
    assert module_layer(candidate, namespace) == -1
    source = """/-
Copyright (c) 2026 Ada Example. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ada Example
-/
import Mathlib.Data.Nat.Basic

/-! Candidate module. -/
namespace Nat
end Nat
"""
    allowed = mathlib_candidate_failures(
        candidate,
        source,
        strip_lean_comments(source),
        ["Mathlib.Data.Nat.Basic"],
        owned,
        namespace,
    )
    assert allowed == []


def test_mathlib_candidate_rejects_project_and_third_party_dependencies() -> None:
    namespace = "ExampleTheorem"
    candidate = "ExampleTheorem.Mathlib.NumberTheory.Helper"
    owned = {candidate, "ExampleTheorem.Definitions.Core"}
    failures = mathlib_candidate_failures(
        candidate,
        "namespace ExampleTheorem\nend ExampleTheorem\n",
        "namespace ExampleTheorem\nend ExampleTheorem\n",
        ["ExampleTheorem.Definitions.Core", "PrimeGapsLib.Basic"],
        owned,
        namespace,
    )
    assert any("imports project module" in failure for failure in failures)
    assert any("imports non-Mathlib dependency" in failure for failure in failures)
    assert any("references project namespace" in failure for failure in failures)


def test_mathlib_candidate_manifest_requires_destination_and_readiness() -> None:
    namespace = "ExampleTheorem"
    candidate = "ExampleTheorem.Mathlib.NumberTheory.Helper"
    valid = (
        "| `ExampleTheorem.Mathlib.NumberTheory.Helper` | "
        "`Mathlib/NumberTheory/Helper.lean` | mathlib-ready | None |"
    )
    assert mathlib_manifest_failures([f"{namespace}.Mathlib", candidate], namespace, valid) == []
    failures = mathlib_manifest_failures(
        [candidate], namespace, f"| `{candidate}` | Not assigned | unknown | None |"
    )
    assert any("proposed Mathlib path" in failure for failure in failures)
    assert any("recognized readiness" in failure for failure in failures)


def test_ignored_artifact_does_not_affect_tracked_size(tmp_path: Path) -> None:
    tracked = tmp_path / "tracked.txt"
    ignored = tmp_path / ".lake" / "large.bin"
    ignored.parent.mkdir()
    tracked.write_bytes(b"abc")
    ignored.write_bytes(b"x" * 10000)
    assert tracked_public_size(tmp_path, ["tracked.txt"]) == 3


def test_ignored_private_lean_does_not_affect_public_policy(tmp_path: Path) -> None:
    (tmp_path / ".gitignore").write_text(".research/\n", encoding="utf-8")
    (tmp_path / "Example.lean").write_text(
        "/-! Public module. -/\nimport Mathlib.Data.Nat.Basic\n",
        encoding="utf-8",
    )
    deleted = tmp_path / "Deleted.lean"
    deleted.write_text("axiom obsolete : False\n", encoding="utf-8")
    private = tmp_path / ".research" / "Private.lean"
    private.parent.mkdir()
    private.write_text("axiom privateLeak : False\n", encoding="utf-8")
    subprocess.run(["git", "init", "--quiet"], cwd=tmp_path, check=True)
    subprocess.run(
        ["git", "add", ".gitignore", "Example.lean", "Deleted.lean"],
        cwd=tmp_path,
        check=True,
    )
    deleted.unlink()
    candidates = public_candidate_paths(tmp_path)
    assert ".research/Private.lean" not in candidates
    assert "Deleted.lean" not in candidates
    check_lean_sources(tmp_path, public_candidate_paths(tmp_path))


def write_boundary_fixture(tmp_path: Path, challenge: str, solution: str) -> None:
    (tmp_path / "Challenge.lean").write_text(challenge, encoding="utf-8")
    (tmp_path / "Solution.lean").write_text(solution, encoding="utf-8")
    subprocess.run(["git", "init", "--quiet"], cwd=tmp_path, check=True)
    subprocess.run(["git", "add", "Challenge.lean", "Solution.lean"], cwd=tmp_path, check=True)


def test_boundary_sources_require_explicit_implicit_policy(tmp_path: Path) -> None:
    write_boundary_fixture(
        tmp_path,
        "import Mathlib.Logic.Basic\ntheorem Example.result : True := by\n  sorry\n",
        "import Mathlib.Logic.Basic\ntheorem Example.result : True := by\n  trivial\n",
    )
    with pytest.raises(LeanSourceError, match="must set_option autoImplicit false"):
        check_lean_sources(tmp_path, public_candidate_paths(tmp_path))


def test_challenge_rejects_project_imports(tmp_path: Path) -> None:
    boundary = (
        "import Mathlib.Logic.Basic\n"
        "set_option autoImplicit false\n"
        "theorem Example.result : True := by\n"
    )
    write_boundary_fixture(
        tmp_path,
        boundary.replace("import Mathlib.Logic.Basic\n", "import Example.Definitions\n")
        + "  sorry\n",
        boundary + "  trivial\n",
    )
    with pytest.raises(LeanSourceError, match="non-Mathlib direct imports"):
        check_lean_sources(tmp_path, public_candidate_paths(tmp_path))


def test_boundary_sources_accept_exact_mathlib_surface(tmp_path: Path) -> None:
    boundary = (
        "import Mathlib.Logic.Basic\n"
        "set_option autoImplicit false\n"
        "theorem Example.result : True := by\n"
    )
    write_boundary_fixture(tmp_path, boundary + "  sorry\n", boundary + "  trivial\n")
    check_lean_sources(tmp_path, public_candidate_paths(tmp_path))


def test_comparator_boundary_enumerates_every_theorem_pair(tmp_path: Path) -> None:
    (tmp_path / "Challenge.lean").write_text(
        "theorem Example.first : True := by\n  sorry\n", encoding="utf-8"
    )
    (tmp_path / "Solution.lean").write_text(
        "theorem Example.first : True := by\n  trivial\n", encoding="utf-8"
    )
    (tmp_path / "comparator.json").write_text(
        '{"challenge_module":"Challenge","solution_module":"Solution",'
        '"theorem_names":["Example.first","Example.missing"]}\n',
        encoding="utf-8",
    )
    with pytest.raises(LeanSourceError, match="Example.missing"):
        check_comparator_boundary(tmp_path)


def test_open_targets_are_definitions_and_block_release(tmp_path: Path) -> None:
    config = {
        "status": "research",
        "challenge_module": "Challenge",
        "solution_module": "Solution",
        "theorem_names": [],
        "open_targets": [{"module": "Targets", "name": "OpenQuestion"}],
    }
    (tmp_path / "comparator.json").write_text(json.dumps(config), encoding="utf-8")
    (tmp_path / "Targets.lean").write_text("def OpenQuestion : Prop := False\n", encoding="utf-8")
    (tmp_path / "Challenge.lean").write_text("set_option autoImplicit false\n", encoding="utf-8")
    check_comparator_boundary(tmp_path)
    with pytest.raises(CheckFailure, match="headline targets remain open"):
        check_metadata(tmp_path, release=True)
    (tmp_path / "Targets.lean").write_text("", encoding="utf-8")
    with pytest.raises(LeanSourceError, match="missing unique open target"):
        check_comparator_boundary(tmp_path)


def test_research_boundary_rejects_an_assumed_headline(tmp_path: Path) -> None:
    config = {
        "status": "research",
        "challenge_module": "Challenge",
        "solution_module": "Solution",
        "theorem_names": [],
        "open_targets": [{"module": "Targets", "name": "OpenQuestion"}],
    }
    (tmp_path / "comparator.json").write_text(json.dumps(config), encoding="utf-8")
    (tmp_path / "Targets.lean").write_text("def OpenQuestion : Prop := False\n", encoding="utf-8")
    (tmp_path / "Challenge.lean").write_text(
        "theorem claimed : False := by sorry\n", encoding="utf-8"
    )
    with pytest.raises(LeanSourceError, match="must not advertise assumed theorems"):
        check_comparator_boundary(tmp_path)


def test_submission_link_accepts_current_form(tmp_path: Path) -> None:
    (tmp_path / "README.md").write_text(
        "Submit at https://submit.palomar-registry.org/.\n", encoding="utf-8"
    )
    subprocess.run(["git", "init", "--quiet"], cwd=tmp_path, check=True)
    subprocess.run(["git", "add", "README.md"], cwd=tmp_path, check=True)
    check_submission_link(tmp_path)


def test_submission_link_rejects_missing_current_form(tmp_path: Path) -> None:
    (tmp_path / "README.md").write_text("No submission link.\n", encoding="utf-8")
    with pytest.raises(CheckFailure, match="README.md must link"):
        check_submission_link(tmp_path)


def test_submission_link_rejects_retired_form(tmp_path: Path) -> None:
    (tmp_path / "README.md").write_text(
        "https://submit.palomar-registry.org/\nPalomarSubmission/issues/new\n",
        encoding="utf-8",
    )
    subprocess.run(["git", "init", "--quiet"], cwd=tmp_path, check=True)
    subprocess.run(["git", "add", "README.md"], cwd=tmp_path, check=True)
    with pytest.raises(CheckFailure, match="retired Palomar form"):
        check_submission_link(tmp_path)


def test_submission_link_ignores_untracked_binary_markdown(tmp_path: Path) -> None:
    (tmp_path / "README.md").write_text("https://submit.palomar-registry.org/\n", encoding="utf-8")
    subprocess.run(["git", "init", "--quiet"], cwd=tmp_path, check=True)
    subprocess.run(["git", "add", "README.md"], cwd=tmp_path, check=True)
    (tmp_path / "generated.md").write_bytes(b"generated\xffartifact")
    check_submission_link(tmp_path)
