# Erdos 690 dependency reuse

Repository: https://github.com/kimihiro64/erdos-690-prime-factor-unimodality

Pinned commit: `ef3c9311d42b61db59f81d99741b5819d1986436`.
Toolchain: `leanprover/lean4:v4.34.0`. Licence: Apache-2.0.
Release: `v0.1.0-conditional.ef3c9311d42b`.
Build-manifest SHA-256:
`ca4c8a053dc86ec0acf8f641ffaf69a3354157ff184a2e7a8564db3b09e2f470`.

The pinned manifest identifies each archive and each artifact by SHA-256.
The restore selects Definitions, non-certificate Helpers, and third-party
library artifacts. It excludes the enormous generated classification
certificates and does not claim to restore or check the entire classification.
No dependency sources are compiled. Missing imports are errors, never build
requests. The local receipt records the exact restored subset.

| Module | Reused interface | Hypotheses to preserve |
|---|---|---|
| `Definitions.KthPrimeFactor` | `primeAt`, `primesBelow`, `primeFactorDensity` | Prime indices are zero-based; mathematical ranks are positive. |
| `Helpers.FirstDifference.Threshold` | `densityStep_iff_symmetricRatio_gap` | Positive p and positive finite density; the rank convention is r+2. |
| Same | `densityStep_lt_iff_symmetricRatio_lt_gap` | Same positivity conditions, strict descent direction. |
| `Helpers.SymmetricBounds.Main` | `degree_div_weightSum_le_densityRatio` | All entries >1, r <= length, positive weight sum. |
| Same | `densityRatio_le_degree_div_weightSum_sub_leading` | Also descending weights, r>=1, positive complementary sum. |

Names above have namespace `PrimeFactorUnimodality`. Inspect their full types
and `#print axioms` output at the pinned commit. Standard foundational Lean
axioms must be distinguished from assumptions encoding an analytic target.
The narrow interface contains no assertion that the dependency's complete
classification is unconditional. Its release boundary retains a theta-error
hypothesis; do not import the root or Solution and erase that condition.

The new repository pins the same mathlib and transitive source revisions in
both Lake manifests. Its research builder intentionally avoids Lake scheduling:
it verifies released artifacts, places their library roots in `LEAN_PATH`, and
calls Lean only on this repository's own modules. This also avoids rebuilding
the dependency because of timestamp or platform-specific Lake traces.

The release assets were produced on Linux. The local import/build check is
the portability test for the current machine; it does not certify native
executables, plugins, full Lake lint, or every unused release artifact. Use
the exact toolchain. Any future cache-coverage expansion must restore further
verified artifacts, never compile missing dependency modules automatically.

## Shared analytic view

The supported builder uses one external artifact view pinned by
`data/analytic-artifacts.json`, alongside this repository's owned object
root. This view includes the verified Erdos artifacts and the Windows 4.34.0
analytic ports used by both research and public builds. Every supplied
companion, including .ir.sig files, is included by hash. It is an artifact
cache, not an alternate checkout for owned proofs.

The external source commits include PrimeGapsLib
ff4fbdcd13d9eeeba06ede80593974531dfe34b6, BombieriVinogradov
afbcbb5959ad22f86ede6b3a53d5d396142fd32b, Robin1984
bfa72aec0c25c8ee29cefe4449d778ff30412bee, PrimeNumberTheoremAnd
f6147e7572ab3abe5428101bc0b13627bcb005df and LeanArchitect
d9013cc08bd2b5483e837368dfa4cc7ead92a5c2. Original source toolchains and
Windows port execution are distinct. The full manifest records source
hashes and the selected artifact closure; it is not evidence of upstream
publication of these compatibility changes.

Use Erdos 690's [published release cache](https://github.com/kimihiro64/erdos-690-prime-factor-unimodality/releases/tag/v0.1.0-conditional.ef3c9311d42b)
directly. This repository does not package or upload another copy.

Set PFO_ANALYTIC_CACHE to an existing matching complete view, or use the local
ignored pointer. The full analytic view also contains the listed Windows
compatibility ports; do not assume that the Erdos release supplies those
additional artifacts. Upstream publication of those compatibility changes
remains deferred. The current build is reproducible with the pinned artifacts,
but clean-machine bootstrap of the complete analytic view is not supplied
by this initial source publication. See BUILD.md. A missing artifact must
never trigger a rebuild of the pinned Erdos dependency. The proof audit
checks assumptions in the actual theorem closures.

## Seven-eighths source port

`data/analytic-artifacts-qrh-port.json` pins the complete source closure of
`OAI.NumberTheory.DirichletL.Nonvanishing` at OpenAI's
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Its source declares Lean 4.34.1;
this repository's port was compiled on Windows with Lean 4.34.0 and the
existing Mathlib pin. The manifest records original and adapted source
hashes, exact replacements, synchronous-elaboration settings, all imports,
and compiled artifact hashes. It also pins the required RellichKondrachov
and PrimeNumberTheoremAnd source revisions.

The complete closure contains 2,945 modules. Four PNT modules reuse the
existing verified artifacts; 2,941 new modules are appended to the same
external view. Existing artifacts are never replaced. The supported owned
build verifies the complete view and does not compile these dependencies.

The source endpoints assert nonvanishing of zeta and Dirichlet L-functions
for real part strictly greater than 7/8, with the explicit Dirichlet pole
exclusion retained. They were compared to separately elaborated Mathlib-only
targets and audited for axioms. The actual endpoint closures use only
`Classical.choice`, `Quot.sound`, and `propext`; no zero-free-region
assumption remains. This is an attributed compatibility port and reuse of
the OAI proof, not an independently discovered proof of that region.

`PrimeFactorOscillations.Helpers.QRHSevenEighths` supplies the maintained
interface and discharges the strip hypothesis in this project's two
modified-LCM margin theorems. Their height-log and cutoff-log conventions
remain distinct. These applications do not establish full RH or an
improvement in the bounded prime-gap constant.

For source inspection, `scripts/qrh_source_port.py` reconstructs all 2,945
adapted files from checkouts of the three pinned upstream revisions.
Pass one `--checkout OWNER/REPO=PATH` for each repository named in the
manifest and an independent `--output` directory. Every original and
adapted file must match its published hash; existing different outputs
are preserved. This command performs no downloads or compilation. The
complete source reconstruction was checked against the files used for
the successful port.

After the supported build, `scripts/proof_audit.py` checks the maintained
7/8 statements against a separately compiled Mathlib-only specification
and includes the 78 new strip-transfer and application declarations in
its axiom audit. The exact source port's cache artifacts are required;
source reconstruction alone is not a compiled cache or proof audit.
