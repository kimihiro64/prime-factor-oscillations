"""Compile project-owned Lean only, using verified prebuilt dependencies."""

from __future__ import annotations

import hashlib
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any, cast

ROOT = Path(__file__).resolve().parents[1]
if __package__ in {None, ""}:
    sys.path.insert(0, str(ROOT))

from scripts.analytic_dependency import MANIFEST_SHA256, source_digest  # noqa: E402
from scripts.analytic_dependency import verify as verify_analytic  # noqa: E402
from scripts.import_graph import library_namespace, owned_graph  # noqa: E402
from scripts.prebuilt_dependency import COMMIT, TOOLCHAIN  # noqa: E402


def build_order(graph: dict[str, set[str]]) -> list[str]:
    """Topologically order project modules and reject cycles."""
    result: list[str] = []
    remaining = {name: set(imports) for name, imports in graph.items()}
    while remaining:
        ready = sorted(name for name, imports in remaining.items() if not imports)
        if not ready:
            raise ValueError("cycle in owned Lean modules")
        for name in ready:
            result.append(name)
            del remaining[name]
        for imports in remaining.values():
            imports.difference_update(ready)
    return result


def module_fingerprint(
    source_sha256: str,
    dependency_fingerprints: dict[str, str],
    version: str,
    manifest_sha256: str,
) -> str:
    """Identify the full owned input closure, even if an intermediate object is unchanged."""
    payload = {
        "schema_version": 1,
        "source_sha256": source_sha256,
        "dependencies": dependency_fingerprints,
        "compiler": version,
        "analytic_manifest": manifest_sha256,
        "options": ["-j", "1", "-s", "65536", "-M", "8192"],
    }
    return hashlib.sha256(json.dumps(payload, sort_keys=True).encode("utf-8")).hexdigest()


def compile_owned_module(command: list[str], environment: dict[str, str]) -> None:
    """Retry at most three times on native crashes; never retry a Lean proof error."""
    native_codes = {3221225477, 3221226505, -1073741819, -1073740791}
    for attempt in range(1, 4):
        try:
            subprocess.run(command, cwd=ROOT, env=environment, check=True)
            return
        except subprocess.CalledProcessError as error:
            if error.returncode not in native_codes or attempt == 3:
                raise
            print(f"Native compiler exit {error.returncode}; retry {attempt + 1}/3", flush=True)


def main() -> int:
    """Compile changed owned modules in the exact verified probe environment."""
    try:
        if (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip() != TOOLCHAIN:
            raise ValueError("the project toolchain differs from the audited artifact pin")
        lean = shutil.which("lean")
        elan = shutil.which("elan")
        environment = os.environ.copy()
        environment["ELAN_TOOLCHAIN"] = TOOLCHAIN
        if elan is not None:
            resolved = subprocess.run(
                [elan, "which", "lean"],
                cwd=ROOT,
                env=environment,
                check=True,
                capture_output=True,
                text=True,
                encoding="utf-8",
            ).stdout.splitlines()
            if len(resolved) != 1:
                raise ValueError("elan did not resolve exactly one compiler")
            lean = resolved[0].strip()
        if lean is None or not Path(lean).is_absolute() or not Path(lean).is_file():
            raise ValueError("the pinned Lean executable is unavailable")
        version = subprocess.run(
            [lean, "--version"],
            cwd=ROOT,
            env=environment,
            check=True,
            capture_output=True,
            text=True,
            encoding="utf-8",
        ).stdout.strip()
        if "version 4.34.0," not in version:
            raise ValueError(f"unexpected compiler: {version}")
        # The pinned shared view includes the released Erdos artifacts actually imported.
        # Do not rehash a second, unused copy of the same release cache.
        analytic_root = verify_analytic()
        destination = ROOT / ".lake/build/lib/lean"
        destination.mkdir(parents=True, exist_ok=True)
        environment["LEAN_PATH"] = os.pathsep.join([str(destination), str(analytic_root)])
        modules, graph = owned_graph(ROOT, library_namespace(ROOT))
        order = build_order(graph)
        cache_path = ROOT / ".lake/build/owned-module-cache.json"
        cache = (
            cast(dict[str, Any], json.loads(cache_path.read_text(encoding="utf-8")))
            if cache_path.exists()
            else {"modules": {}}
        )
        rows = cast(dict[str, Any], cache["modules"])
        compiled: list[str] = []
        reused: list[str] = []
        fingerprints: dict[str, str] = {}
        for name in order:
            source = modules[name].resolve()
            if not source.is_relative_to(ROOT) or ".lake" in source.relative_to(ROOT).parts:
                raise ValueError(f"refusing non-owned source: {source}")
            output = destination / (name.replace(".", "/") + ".olean")
            dependencies = {
                dep: source_digest(destination / (dep.replace(".", "/") + ".olean"))
                for dep in sorted(graph[name])
            }
            old = cast(dict[str, Any], rows.get(name, {}))
            digest = source_digest(source)
            fingerprint = module_fingerprint(
                digest,
                {dep: fingerprints[dep] for dep in sorted(graph[name])},
                version,
                MANIFEST_SHA256,
            )
            fingerprints[name] = fingerprint
            if (
                old.get("exit_code") == 0
                and old.get("closure_sha256") == fingerprint
                and old.get("source_sha256") == digest
                and old.get("dependencies") == dependencies
                and output.is_file()
                and old.get("object_sha256") == source_digest(output)
            ):
                reused.append(name)
                continue
            output.parent.mkdir(parents=True, exist_ok=True)
            print(f"Checking {name}", flush=True)
            compile_owned_module(
                [lean, "-j", "1", "-s", "65536", "-M", "8192", "-o", str(output), str(source)],
                environment,
            )
            rows[name] = {
                "exit_code": 0,
                "closure_sha256": fingerprint,
                "source_sha256": digest,
                "object_sha256": source_digest(output),
                "dependencies": dependencies,
            }
            cache_path.write_text(json.dumps(cache, indent=2) + "\n", encoding="utf-8")
            compiled.append(name)
        report = {
            "toolchain": TOOLCHAIN,
            "version": version,
            "compiler_executable": lean,
            "dependency_commit": COMMIT,
            "analytic_manifest_sha256": MANIFEST_SHA256,
            "dependency_builds": 0,
            "compiler_threads": 1,
            "compiled_owned_modules": compiled,
            "reused_owned_modules": reused,
            "checked_owned_modules": order,
            "lean_path": environment["LEAN_PATH"],
            "headline_audit": "run scripts/proof_audit.py after this successful build",
        }
        (ROOT / ".lake/build/project-build.json").write_text(
            json.dumps(report, indent=2) + "\n", encoding="utf-8"
        )
        print(
            f"Checked {len(order)} owned modules ({len(reused)} unchanged reused); "
            "dependency builds: 0"
        )
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f"project build failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
