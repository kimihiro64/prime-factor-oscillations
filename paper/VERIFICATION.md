# Paper verification

## RH and spectrum revision — 4 October 2026

The existing paper and README now describe **Prime-factor densities:
bounded-gap spectra and a Riemann hypothesis criterion**. The 30-page paper
distinguishes classical Nicolas and mod-Poisson inputs from the potentially
new spectrum and moving-coefficient transfer. It adds the proved RH
criteria and their quantitative consequences, and compares these with
the earlier conditional Hardy–Littlewood location result. Exploratory RH
attacks and the unfinished LCM-power extension are excluded.

The same TeX source was edited in place and the tracked PDF was refreshed.
Two final native Windows MiKTeX passes completed with package installation
disabled and a fixed source date. There are no undefined references or
citations and no overfull or underfull boxes. All pages were rendered and
visually checked; text extraction, label uniqueness and reference closure
also passed.

- [Revision report and hashes](verification/rh-editorial-revision.json).
- [Final compiler output](verification/rh-paper-revision-build.log).
- [Primary sources and novelty boundaries](SOURCE_REVIEW.md).
- [Theorem/proof crosswalk](THEOREM_STATUS.md).

No Lean source or dependency was changed by this editorial revision.
The immediately preceding proof audit checked two public statement
identities and 218 theorem closures with only propext, Classical.choice
and Quot.sound, reusing 58,065 verified external artifacts and rebuilding
no dependency. That audit is separate from this documentation check.
The normalized coefficient wave is an ordinary consequence of compiled
inputs; the relative Hardy–Littlewood location theorem is compiled in a
private probe, with maintained public export still pending.

The built-in editor remains on the existing source. Its compiler reports
that standard platform directories cannot be initialized. The tracked PDF
was successfully produced by the existing native Windows compiler instead.
No new CI, OS switch or dependency-cache redistribution was introduced.
Official Comparator/NanoDa replay and independent novelty certification
remain unperformed.

## Expanded research-paper revision — 28 September 2026

The tracked PDF now contains the 15-page paper **Prime-factor density reversals
and the spectrum of bounded prime gaps**. It includes a plain-English argument
guide, detailed proofs with consistent notation, primary-source history, and
the precise implications for bounded prime gaps and affine prime sums.
Unfinished exploratory work is excluded.

The same existing TeX file was edited in place. Two native Windows MiKTeX
passes completed with package installation disabled and a fixed source date.
There are no undefined references or citations, overfull boxes, or underfull
boxes. All 15 rendered pages were inspected. After the title change, page 1
was inspected again; extracted pages 2–15 were unchanged. The built PDF is
included in the commit, without adding CI.

- [Editorial report and final source/PDF hashes](verification/editorial-revision.json).
- [Final paper compiler output](verification/paper-revision-build.log).
- [Primary-source review](SOURCE_REVIEW.md).
- [Expanded theorem/proof crosswalk](THEOREM_STATUS.md).

This is a documentation revision. It changes no proof source, dependency pin,
or public theorem statement. Pre-existing staged research proofs are excluded
from its commit. The proof checks below remain an explicitly historical record,
not a claim of fresh recompilation for the editorial revision.

The built-in editor remains open on the same source. Its compiler still reports
that standard platform directories cannot be initialized. The included PDF was
successfully compiled with the existing Windows installation instead.

## Initial-publication verification

Validation date: 28 September 2026. The checks used native Windows and the
project's pinned Lean 4.34.0 environment. No dependency was rebuilt, and no
dependency cache is redistributed in this repository.

| Check | Result |
|---|---|
| Owned Lean build | 167 modules checked; all 167 unchanged objects reused after recursive source/dependency fingerprint checks |
| Analytic artifact integrity | 57,142 pinned files verified; zero dependency builds |
| Public theorem boundary | Two compiled Challenge/Solution types and universe parameter lists identical |
| Theorem dependency assumptions | Twelve closures; only Classical.choice, Quot.sound and propext |
| Python | 51 tests passed; Ruff formatting/lint and strict MyPy passed |
| Metadata | 16 Ruby tests, 83 assertions; no failures, errors or skips |
| Repository | Public/private boundary, Lean source policy, import architecture and dependency manifest checks passed |
| Paper | Seven pages; two successful native Windows LaTeX passes, no unresolved citations/references or overfull boxes; all pages visually inspected and extracted text checked |

The build reused previously compiled owned objects only after checking the
complete transitive owned-source fingerprints. The statement and axiom
checks were freshly executed. These are different kinds of verification;
the log does not claim 167 fresh recompilations.

Evidence:

- [Machine-readable report and source hashes](verification/report.json).
- [Research-profile output](verification/research-check.log).
- [Exact theorem types and axiom reports](verification/theorem-types-and-axioms.log).
- [Compiled public-type comparison](verification/compiled-public-types.log).
- [Paper compiler output](verification/paper-build.log).

Logs replace local checkout and user-directory paths with generic markers.
The research-profile log records the checked proof-bearing snapshot before
this documentation and its log copies were added. Proof sources and the
paper are identified by SHA-256 in the report; documentation additions do
not change those inputs. The final staged surface is checked again before
the initial commit.

The official Comparator/NanoDa replay has not been run. A local comparison
of compiled types is not advertised as that external validation. Independent
expert review and novelty assessment are also not claimed.

The existing analytic view makes the recorded build reproducible in that
environment. Erdos 690's cache is publicly released upstream; the additional
analytic compatibility artifacts still require an existing matching view.
The initial source publication is therefore not a complete fresh-machine
bootstrap. See [BUILD.md](../BUILD.md) for the exact prerequisites and commands.

The built-in LaTeX editor was opened but its compiler failed to initialize
standard directories. The PDF was instead compiled with the already installed
Windows MiKTeX, with package installation disabled, and rendered for inspection
using the existing Poppler installation. No OS or toolchain switch occurred.
