"""Validate Lean source policy and Palomar boundary declarations."""

from __future__ import annotations

import json
import re
from collections.abc import Sequence
from pathlib import Path
from typing import Final

FORBIDDEN_LEAN: Final[re.Pattern[str]] = re.compile(
    r"(?m)^\s*(?:axiom|constant|opaque)\b|\b(?:sorry|admit|native_decide)\b"
)
FORBIDDEN_CHALLENGE: Final[re.Pattern[str]] = re.compile(
    r"(?m)^\s*(?:axiom|constant|opaque)\b|\b(?:admit|native_decide)\b"
)
DISCOVERY_LEAN: Final[re.Pattern[str]] = re.compile(
    r"(?m)^\s*#(?:check|print|eval|reduce)\b|"
    r"\b(?:exact|apply|simp|rw|aesop)\?|\blibrary_search\b"
)
BROAD_IMPORT: Final[re.Pattern[str]] = re.compile(r"(?m)^\s*import\s+(?:Batteries|Mathlib)\s*$")
AUTO_IMPLICIT_FALSE: Final[re.Pattern[str]] = re.compile(
    r"(?m)^\s*set_option\s+autoImplicit\s+false\s*$"
)


class LeanSourceError(RuntimeError):
    """Raised when Lean source or a boundary declaration violates policy."""


def strip_lean_comments(source: str) -> str:
    """Remove nested Lean comments while preserving line structure."""
    output: list[str] = []
    index = 0
    depth = 0
    in_string = False
    escaped = False
    while index < len(source):
        pair = source[index : index + 2]
        character = source[index]
        if depth > 0:
            if pair == "/-":
                depth += 1
                output.extend("  ")
                index += 2
                continue
            if pair == "-/":
                depth -= 1
                output.extend("  ")
                index += 2
                continue
            output.append("\n" if character == "\n" else " ")
            index += 1
            continue
        if not in_string and pair == "/-":
            depth = 1
            output.extend("  ")
            index += 2
            continue
        if not in_string and pair == "--":
            while index < len(source) and source[index] != "\n":
                output.append(" ")
                index += 1
            continue
        output.append(character)
        if in_string:
            if escaped:
                escaped = False
            elif character == "\\":
                escaped = True
            elif character == '"':
                in_string = False
        elif character == '"':
            in_string = True
        index += 1
    if depth != 0:
        raise LeanSourceError("unterminated Lean block comment")
    return "".join(output)


def lean_imports(code: str) -> list[str]:
    """Return direct import names from a Lean source."""
    return re.findall(r"(?m)^\s*import\s+([A-Za-z0-9_'.]+)\s*$", code)


def check_lean_sources(root: Path, candidates: Sequence[str]) -> None:
    """Check public Lean source policy without requiring a Lean runtime."""
    failures: list[str] = []
    files = [
        root / relative
        for relative in candidates
        if relative.endswith(".lean") and (root / relative).is_file()
    ]
    for path in files:
        relative = path.relative_to(root).as_posix()
        source = path.read_text(encoding="utf-8")
        try:
            code = strip_lean_comments(source)
        except LeanSourceError as error:
            failures.append(f"{relative}: {error}")
            continue
        forbidden = FORBIDDEN_CHALLENGE if relative == "Challenge.lean" else FORBIDDEN_LEAN
        if match := forbidden.search(code):
            failures.append(f"{relative}: forbidden Lean source `{match.group(0).strip()}`")
        if match := DISCOVERY_LEAN.search(code):
            failures.append(f"{relative}: discovery command `{match.group(0).strip()}`")
        if match := BROAD_IMPORT.search(code):
            failures.append(f"{relative}: broad import `{match.group(0).strip()}`")
        imports = lean_imports(code)
        if imports != sorted(imports):
            failures.append(f"{relative}: imports are not in ordinal order")
        if len(imports) != len(set(imports)):
            failures.append(f"{relative}: duplicate direct import")
        if relative in {"Challenge.lean", "Solution.lean"} and not AUTO_IMPLICIT_FALSE.search(code):
            failures.append(f"{relative}: must set_option autoImplicit false")
        if relative == "Challenge.lean":
            non_mathlib = [module for module in imports if not module.startswith("Mathlib.")]
            if non_mathlib:
                failures.append(
                    "Challenge.lean: non-Mathlib direct imports: " + ", ".join(non_mathlib)
                )
        if relative not in {"Challenge.lean", "Solution.lean"} and "/-!" not in source:
            failures.append(f"{relative}: missing module documentation")
    challenge = root / "Challenge.lean"
    if challenge.exists():
        size = challenge.stat().st_size
        lines = len(challenge.read_text(encoding="utf-8").splitlines())
        if size > 100 * 1024 or lines > 1000:
            failures.append(f"Challenge.lean exceeds 100 KiB or 1,000 lines ({size}, {lines})")
        elif size > 32 * 1024 or lines > 300:
            print(f"warning: Challenge.lean exceeds the preferred audit size ({size}, {lines})")
    if failures:
        raise LeanSourceError("Lean source policy failed:\n" + "\n".join(failures))
    print(f"Lean source policy: clean ({len(files)} files)")


def check_comparator_boundary(root: Path) -> None:
    """Require every configured theorem to occur once on each source boundary."""
    config_path = root / "comparator.json"
    try:
        config = json.loads(config_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise LeanSourceError(f"invalid comparator.json: {error}") from error
    if not isinstance(config, dict):
        raise LeanSourceError("comparator.json must contain an object")
    challenge_module = config.get("challenge_module")
    solution_module = config.get("solution_module")
    theorem_names = config.get("theorem_names")
    if not isinstance(challenge_module, str) or not isinstance(solution_module, str):
        raise LeanSourceError("comparator.json boundary modules must be strings")
    if config.get("status") == "research" and theorem_names == []:
        targets = config.get("open_targets")
        if not isinstance(targets, list) or not targets:
            raise LeanSourceError("research boundary must list actual open target definitions")
        for target in targets:
            if not isinstance(target, dict):
                raise LeanSourceError("invalid open target entry")
            module, name = target.get("module"), target.get("name")
            if not isinstance(module, str) or not re.fullmatch(r"[A-Za-z0-9_.]+", module):
                raise LeanSourceError("invalid target module")
            if not isinstance(name, str) or not re.fullmatch(r"[A-Za-z0-9_]+", name):
                raise LeanSourceError("invalid target definition name")
            source = root.joinpath(*module.split(".")).with_suffix(".lean")
            if not source.is_file():
                raise LeanSourceError(f"missing open target source: {module}")
            code = strip_lean_comments(source.read_text(encoding="utf-8"))
            if len(re.findall(rf"(?m)^def {re.escape(name)}\b", code)) != 1:
                raise LeanSourceError(f"missing unique open target definition: {name}")
        challenge = root / "Challenge.lean"
        code = strip_lean_comments(challenge.read_text(encoding="utf-8"))
        if re.search(r"\b(?:theorem|lemma|sorry|axiom|constant|opaque)\b", code):
            raise LeanSourceError("an open research boundary must not advertise assumed theorems")
        print(f"Research boundary: {len(targets)} explicit open targets; no completed headline")
        return
    if (
        not isinstance(theorem_names, list)
        or not theorem_names
        or not all(isinstance(name, str) and name for name in theorem_names)
    ):
        raise LeanSourceError("comparator.json theorem_names must be a nonempty string list")

    failures: list[str] = []
    for label, module in (("Challenge", challenge_module), ("Solution", solution_module)):
        path = root.joinpath(*module.split(".")).with_suffix(".lean")
        if not path.is_file():
            failures.append(f"{label}: configured module source is missing: {module}")
            continue
        code = strip_lean_comments(path.read_text(encoding="utf-8"))
        for theorem_name in theorem_names:
            declaration = re.compile(
                rf"(?m)^\s*(?:theorem|lemma)\s+{re.escape(theorem_name)}(?:\s|:)"
            )
            count = len(declaration.findall(code))
            if count != 1:
                failures.append(f"{label}: {theorem_name} occurs {count} times in {path.name}")
    if failures:
        raise LeanSourceError("Comparator boundary source audit failed:\n" + "\n".join(failures))
    print(f"Comparator boundary source: clean ({len(theorem_names)} theorem pairs)")
