# Initial-publication verification

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
