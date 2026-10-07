# Paper verification

## Paper and power-degree completion — 6 October 2026

The same source document was edited in place and its tracked PDF rebuilt.
The revision incorporates the complete growing-family calculations, the
conditional power-degree zero-free implication and square-root RH corollary,
and the unconditional modified-LCM critical window. The title, abstract,
introduction, argument guide, detailed proofs, implications, bibliography and
formalization crosswalk are aligned with that scope.

The power-degree proof was already implemented in
`Helpers/ConsecutiveRootZeroFree.lean`. Its source is unchanged in this
revision. A fresh kernel check imports the maintained family owners and
Solution and audits 18 statements, including all four power-degree
declarations. The eventual complete-sign hypothesis is still explicit:
neither the editorial work nor an axiom audit proves it.

| Check | Result |
|---|---|
| Compiler | Native Windows Lean 4.34.0, pinned shared artifact environment |
| Fresh statement/axiom audit | 18 statements; every complete axiom set is exactly Classical.choice, Quot.sound, propext |
| Cache reuse | Recursive owned-source/dependency fingerprints checked by the focused runner; zero dependency builds |
| Lean source changes | None; existing proof implementation and public consumers retained |
| PDF | 56 pages; native Windows MiKTeX, package installation disabled |
| TeX checks | 117 unique labels, 154 reference occurrences, 14 bibliography keys; no unresolved references/citations or layout warnings |
| Visual check | All-page contact sheets and enlarged checks of the title and new theorem/proof pages |

Evidence is retained in
[the revision report](verification/paper-nalpha-revision.json),
[the exact theorem types and axioms](verification/paper-nalpha-theorem-types-and-axioms.log),
and [the final compiler log](verification/paper-nalpha-build.log).
The report contains the focused audit source and target list for replay in
the documented pinned environment. The full maintained build recorded before
this documentation-only pass checked 488 owned modules; it is not described
as a fresh full rebuild here.

The built-in editor remains on the original TeX source. Its compiler could
not initialize its standard platform directories, so the PDF was built with
the already installed Windows compiler. No dependency rebuild, new runtime
installation, OS switch, worktree, commit or push was performed.
The earlier verification sections below refer to their historical snapshots.

## General family RH transfer — 5 October 2026

The family extension adds 35 maintained Lean modules and 98 audit targets.
It proves the quadratic local-law qualification, product and moving-rank RH
criteria, exact probability-mass interpretation with forced coordinates,
affine-family consumers, generalized reference constants and finite weighted
family combinations. The full criteria retain their explicit local-law
hypotheses and do not assume RH or a prime-gap supply theorem.

| Check | Result |
|---|---|
| Windows Lean 4.34.0 build | 456 owned modules; 38 checked afresh, 418 unchanged objects reused |
| Dependency cache | 58,065 pinned artifacts verified; zero dependency builds |
| Public statements | Two compiled Challenge/Solution types and universe lists identical |
| Axiom audit | 539 selected closures, including all 441 earlier targets; only Classical.choice, Quot.sound and propext |
| Python | 77 tests; Ruff formatting/lint and strict MyPy passed on 20 source files |
| Metadata | 16 Ruby tests, 83 assertions, no failures |
| Repository | Source policy, public/private boundary, architecture, documentation and metadata checks passed |
| Paper | 46 pages; all pages rendered and reviewed, no undefined references/citations or overfull/underfull boxes |

The research profile passed on the final Lean sources and public exports.
The final staged fast profile checks the completed documentation and evidence
surface. Full Lake lint and official Comparator/NanoDa were not run; the
compiled statement comparison and named axiom audit are the checks reported
here. The two deliberate Challenge placeholders are unchanged.

Two final-check replays without CPU affinity ended in Ruby FrozenError
exceptions during runtime initialization or test-plugin loading. Their logs
are retained privately. The unchanged final check passed with the same
single-CPU setting as the successful research build; the cause of the
earlier runtime failures is not established.

- [Full family proof audit](verification/family-rh-proof-audit.json).
- [Research-profile build and check log](verification/family-rh-research-check.log).
- [Theorem statements and dependency axioms](verification/family-rh-theorem-types-and-axioms.log).
- [Paper and source hashes](verification/family-rh-editorial-review.json).
- [Final native paper compilation](verification/family-rh-paper-build.log).
- [Final staged repository check](verification/family-rh-final-staged-check.log).

The built-in LaTeX compiler could not initialize its platform directories.
The tracked PDF was compiled from the same source using the existing native
Windows MiKTeX installation, with package installation disabled. The open
document and editor were retained. Nothing was committed or pushed.

The qualification theorem is sufficient, not a classification of every
possible family. An arithmetic ensemble also needs the independent limiting
finite-prime law. Sparse supports, moving families, and extensions of the
ordinary area/count criteria require additional arguments. RH and improved
prime-gap bounds remain unproved.

## Post-paper formalization and expanded paper — 5 October 2026

All fifteen post-paper theorem groups are maintained and publicly exported.
This includes both localized separated-reversal count equivalences, the
ascent-only variants, the area criteria, the sharp growing-tilt correction,
general gap capacities, and local-coverage tracking of the actual last ascent
with its full conditional RH wave. The paper and README distinguish these
proved implications from their unproved arithmetic or moment hypotheses.

| Check | Result |
|---|---|
| Owned Lean build | 421 modules checked; 16 freshly checked and 405 unchanged objects reused in the completion build |
| Dependencies | 58,065 pinned artifacts verified; zero dependency builds |
| Public statement comparison | Two compiled Challenge/Solution types and universe parameter lists identical |
| Theorem assumptions | 441 selected closures; only Classical.choice, Quot.sound and propext |
| Python | 77 tests passed; Ruff formatting/lint and strict MyPy passed on 19 source files |
| Metadata | 16 Ruby tests, 83 assertions; no failures, errors or skips |
| Repository | Public/private boundary, source policy, import architecture and documentation manifest passed |

The audit preserves the original 218 targets and adds 223 post-paper targets.
The full theorem types and axiom closures are recorded below. The two intended
Challenge placeholders remain confined to Challenge; no research-target axiom
was added. The Alweiss–Luo all-short-interval input remains an explicit formal
premise. The separate local exact-gap hypothesis and proposed moment estimates
are not asserted as theorems about primes.

- [Full proof-audit report](verification/post-paper-proof-audit.json).
- [Full research-profile log](verification/post-paper-formalization-check.log).
- [Theorem types and axiom closures](verification/post-paper-theorem-types-and-axioms.log).
- [Paper revision and hashes](verification/post-paper-editorial-revision.json).
- [Final paper compiler output](verification/post-paper-build.log).

The existing TeX source and editor are retained. The built-in compiler could
not initialize its standard platform directories; the built PDF uses the
existing native Windows MiKTeX installation with package installation disabled.
The editorial report records the final page count, layout checks and hashes.
No CI, dependency-cache redistribution, new worktree, commit or push is part
of this completion pass. Official Comparator/NanoDa replay and independent
expert review remain separate.

The strict Python check excludes only the unused optional NumPy stubs pulled
in by pytest: the installed research NumPy uses Python 3.12 syntax while the
project code is checked against Python 3.11. No repository Python source imports
NumPy, and all project modules and tests retain strict type checking.

The earlier records below describe their own historical snapshots.

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
