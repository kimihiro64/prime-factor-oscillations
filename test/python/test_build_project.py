from __future__ import annotations

from pathlib import Path

import pytest

from scripts import build_project


def test_owned_compile_command_keeps_the_same_target_with_a_short_argument(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    root = tmp_path / ("long-repository-" * 6)
    source = root / "Example" / "Parity.lean"
    output = root / ".lake" / "build" / "lib" / "lean" / "Example" / "Parity.olean"
    compiler = str(tmp_path / "pinned-lean.exe")
    monkeypatch.setattr(build_project, "ROOT", root)
    command = build_project.owned_compile_command(compiler, source, output)
    assert command[:8] == [compiler, "-j", "1", "-s", "65536", "-M", "8192", "-o"]
    assert command[-2] == ".lake/build/lib/lean/Example/Parity.olean"
    assert not Path(command[-2]).is_absolute()
    assert (root / command[-2]).resolve() == output.resolve()
    assert command[-1] == str(source)


def test_owned_compile_command_rejects_an_output_outside_the_repository(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    root = tmp_path / "repository"
    monkeypatch.setattr(build_project, "ROOT", root)
    with pytest.raises(ValueError):
        build_project.owned_compile_command(
            "pinned-lean.exe", root / "Example.lean", tmp_path / "outside.olean"
        )


def test_owned_compile_command_rejects_parent_path_escape(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    root = tmp_path / "repository"
    monkeypatch.setattr(build_project, "ROOT", root)
    with pytest.raises(ValueError):
        build_project.owned_compile_command(
            "pinned-lean.exe", root / "Example.lean", root / ".." / "outside.olean"
        )
