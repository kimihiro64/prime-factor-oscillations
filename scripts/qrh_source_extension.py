"""Validate a pinned QRH cache record; metadata is not a mathematical proof."""

import hashlib
import re
from collections.abc import Mapping
from pathlib import PurePosixPath
from typing import Any

SOURCE_PINS = {
    "OAI": ("openai/math", "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"),
    "RellichKondrachov": (
        "abenenson/rellich-kondrachov",
        "70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23",
    ),
    "PrimeNumberTheoremAnd": (
        "AlexKontorovich/PrimeNumberTheoremAnd",
        "c39a751132c88b6e8080b74c74023fd95b3d8be0",
    ),
}
ROOT_MODULE = "OAI.NumberTheory.DirichletL.Nonvanishing"
ENDPOINTS = {
    "OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re",
    "OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re",
}
FOUNDATIONS = ["Classical.choice", "Quot.sound", "propext"]


def require_sha(value: Any) -> None:
    if not isinstance(value, str) or re.fullmatch(r"[0-9a-f]{64}", value) is None:
        raise ValueError("invalid QRH provenance digest")


def validate_source_port(extension: Mapping[str, Any], known_files: Mapping[str, str]) -> None:
    """Run after the common immutable-pin, platform and companion-map checks.

    The immutable manifest must be produced by the successful theorem audit.
    This function checks distribution consistency; it does not replace Lean.
    """
    if (
        extension.get("kind") != "append_only_verified_source_port"
        or extension.get("root_module") != ROOT_MODULE
        or extension.get("source_commit") != SOURCE_PINS["OAI"][1]
    ):
        raise ValueError("QRH source provenance differs from the frozen endpoint")
    modules = extension["modules"]
    files = extension["files"]
    sources = extension["source_modules"]
    inherited = extension["inherited_modules"]
    if (
        not modules
        or ROOT_MODULE not in modules
        or set(modules) & set(inherited)
        or set(sources) != set(modules) | set(inherited)
    ):
        raise ValueError("QRH source closure differs from its new and inherited modules")
    available = set(known_files) | set(files)
    dependencies = {}
    for module, row in sources.items():
        if re.fullmatch(r"[A-Za-z0-9_]+(?:\.[A-Za-z0-9_]+)+", module) is None:
            raise ValueError("invalid QRH source module")
        pin = SOURCE_PINS.get(module.split(".", 1)[0])
        if pin is None or (row.get("repository"), row.get("commit")) != pin:
            raise ValueError(f"unexpected QRH source revision: {module}")
        path = row["path"]
        if (
            not isinstance(path, str)
            or PurePosixPath(path).is_absolute()
            or PurePosixPath(path).as_posix() != path
            or ":" in path
            or "\\" in path
            or ".." in PurePosixPath(path).parts
            or not path.endswith(".lean")
        ):
            raise ValueError(f"unsafe QRH source path: {module}")
        for key in ("source_sha256", "port_source_sha256", "fingerprint"):
            require_sha(row.get(key))
        imports = row["imports"]
        if (
            not isinstance(imports, list)
            or any(not isinstance(x, str) for x in imports)
            or len(imports) != len(set(imports))
        ):
            raise ValueError(f"invalid QRH import inventory: {module}")
        dependencies[module] = set(imports) & set(sources)
        for dependency in imports:
            if dependency.split(".", 1)[0] in {"Init", "Lean", "Std", "Lake"}:
                continue
            if dependency.replace(".", "/") + ".olean" not in available:
                raise ValueError(f"missing QRH dependency artifact: {module} -> {dependency}")
    for module, supplied in inherited.items():
        stem = module.replace(".", "/")
        expected = {path: sha for path, sha in known_files.items() if path.startswith(stem + ".")}
        if not expected or stem + ".olean" not in expected or supplied != expected:
            raise ValueError(f"incomplete or altered inherited QRH companions: {module}")
    # Reject an unreachable extra source or a cycle, not merely missing filenames.
    reached = set()
    queue = [ROOT_MODULE]
    while queue:
        module = queue.pop()
        if module not in reached:
            reached.add(module)
            queue.extend(dependencies[module])
    if reached != set(sources):
        raise ValueError("QRH inventory is not the exact endpoint import closure")
    pending = {name: set(deps) for name, deps in dependencies.items()}
    while pending:
        ready = {name for name, deps in pending.items() if not deps}
        if not ready:
            raise ValueError("cyclic QRH import inventory")
        pending = {name: deps - ready for name, deps in pending.items() if name not in ready}
    audit = extension["endpoint_audit"]
    for key in ("source_sha256", "log_sha256", "object_sha256", "root_fingerprint"):
        require_sha(audit.get(key))
    if audit["root_fingerprint"] != sources[ROOT_MODULE]["fingerprint"]:
        raise ValueError("stale QRH endpoint fingerprint")
    canonical = audit.get("canonical_specification")
    if not isinstance(canonical, Mapping) or not isinstance(canonical.get("source_text"), str):
        raise ValueError("missing independent canonical specification")
    for key in ("source_sha256", "log_sha256"):
        require_sha(canonical.get(key))
    if (
        hashlib.sha256(canonical["source_text"].encode("utf-8")).hexdigest()
        != canonical["source_sha256"]
    ):
        raise ValueError("canonical specification source differs from its audit")
    artifacts = canonical.get("artifacts", {})
    if not artifacts or "QRHMathlibTarget.olean" not in artifacts:
        raise ValueError("missing canonical specification artifact")
    for path, sha in artifacts.items():
        if re.fullmatch(r"QRHMathlibTarget\.[A-Za-z0-9_.]+", path) is None:
            raise ValueError("unexpected canonical specification namespace")
        require_sha(sha)
    names = set()
    for row in audit["axiom_reports"]:
        if row["declaration"] in names or row["axioms"] != FOUNDATIONS:
            raise ValueError("nonstandard or duplicate QRH axiom report")
        names.add(row["declaration"])
    if not names >= ENDPOINTS:
        raise ValueError("missing actual zeta or Dirichlet endpoint audit")
