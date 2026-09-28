# Build and verification

The supported environment is native Windows, Lean 4.34.0, and the artifact
revisions pinned in this repository. The builder compiles project-owned
modules only. It never builds Erdos 690 or another dependency.

## Prerequisites

Install Git, Python 3.11 or later, Ruby with Minitest, and elan with the
toolchain in `lean-toolchain`. In a Python virtual environment, install:

```powershell
python -m pip install -e ".[dev]"
```

The owned proofs use narrow modules from
[Erdos 690](https://github.com/kimihiro64/erdos-690-prime-factor-unimodality)
at `ef3c9311d42b61db59f81d99741b5819d1986436`.
That project publishes its own
[cache release](https://github.com/kimihiro64/erdos-690-prime-factor-unimodality/releases/tag/v0.1.0-conditional.ef3c9311d42b).
This repository does not package another copy. The optional restoration
utility downloads the pinned upstream assets, verifies their hashes and
extracts the selected reusable closure:

```powershell
python scripts/prebuilt_dependency.py
python scripts/prebuilt_dependency.py --verify
```

This restores the Erdos subset, not the entire analytic environment. The
full headline additionally consumes analytic ports from the exact source
commits in [DEPENDENCY_REUSE.md](DEPENDENCY_REUSE.md). Their source and
artifact hashes are recorded in
[data/analytic-artifacts.json](data/analytic-artifacts.json). Upstream
publication of those compatibility ports remains deferred. Consequently,
this initial source publication does not yet provide an automated complete
fresh-machine bootstrap.

## Use an existing matching analytic view

Set `PFO_ANALYTIC_CACHE` to the absolute root of a matching complete artifact
view. Alternatively, create an ignored `.lake/analytic-cache.json` with
`root` and `manifest_sha256` fields. The required manifest SHA-256 is:

```text
4541992ff6cd517ee585ece627b68c066bffed704bc13dbb4205c2b943da072c
```

The verifier checks every required artifact, including signature companions.
It rejects missing or altered files. Do not point it at the restored Erdos
subset and assume the additional analytic modules are present.

## Checks

From the repository root, using that environment:

```powershell
python scripts/build_project.py
python scripts/proof_audit.py
python scripts/check.py --profile research
```

The first command checks owned module source and transitive dependency
fingerprints, reusing unchanged compiled objects. The second checks the two
compiled public statement identities and twelve theorem axiom closures.
The research profile also runs repository boundaries, architecture,
metadata, Python formatting, lint, typing and tests.

On Windows installations where optional RubyGems startup fails, the same
checks can run with `RUBYOPT=--disable-gems` and `RUBYLIB` pointing to the
installed Minitest `lib` directory. This changes Ruby startup only; no check
is skipped. Use an existing installation's actual path.

Build receipts are written under `.lake/build/`; detailed proof-audit logs
are under ignored `.research/audits/public-integration/`. A sanitized
initial-publication record is in [paper/VERIFICATION.md](paper/VERIFICATION.md).

Do not substitute `lake build`, `lake lint`, or legacy API/release helpers
that schedule dependency builds. Official Comparator/NanoDa replay has not
been run and is separate from the local compiled-type comparison. There is
no CI or automated dependency-update workflow in this initial publication.

## Paper

The standalone source is [paper/research-paper.tex](paper/research-paper.tex).
It uses standard LaTeX packages: amsmath, amssymb, amsthm and hyperref.
Compile it with the built-in LaTeX editor or an existing LaTeX installation.
Its fixed date is 28 September 2026. No private probe or numerical evidence
is used as a proof of its asymptotic theorems.
