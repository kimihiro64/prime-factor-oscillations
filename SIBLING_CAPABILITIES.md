# Sibling repository capability catalog

This catalog is copied into every generated child so a new formalization can
check sibling repositories before reproving infrastructure that is not yet in
Mathlib. It lists every direct public child known to the template maintainers
as of 2026-09-05. Private research worktrees, experiments, and uncommitted
changes are deliberately excluded.

## Borrowing protocol

1. Check the pinned Mathlib revision first; use an upstream declaration when
   it already exists.
2. Open the sibling module at an exact commit and verify the declaration,
   hypotheses, namespace, licence, toolchain, direct imports, proof
   placeholders, and axiom surface. A catalog row is a discovery aid, not a
   substitute for that audit.
3. Prefer a sibling's `MATHLIB_PORTING.md` candidate when one exists. Otherwise
   either depend on the pinned sibling commit or extract the minimum transitive
   source closure into the new child's Mathlib candidate layer.
4. Record the source repository, full commit SHA, original declaration names,
   any renaming, and all required attribution. Never borrow from a dirty or
   unpublished worktree.
5. Build the borrowed module in isolation, then build its first project
   consumer. Recheck forbidden placeholders and the final advertised theorem's
   axiom surface.

Capability status in this file is local to the named declarations. An open
headline theorem does not invalidate an independently proved leaf, and a
complete headline theorem does not make every internal module portable.

## Repository index

| Repository | Reviewed commit | Toolchain | Headline status | Reuse posture |
| --- | --- | --- | --- | --- |
| [Robin1984](https://github.com/kimihiro64/Robin1984) | `bfa72aec0c25c8ee29cefe4449d778ff30412bee` | Lean `v4.33.1` | Complete Robin equivalence; no RH proof claimed | Several proved analytic and finite modules; inspect transitive `PrimeNumberTheoremAnd` dependencies |
| [PrimeNumberTheoremAnd fork](https://github.com/kimihiro64/PrimeNumberTheoremAnd) | `0f15a38c619298b5cd786d39a84dd4bb8997324c` | Lean `v4.33.1` | PNT development plus module-compatible analytic APIs | Use this reviewed fork when its added zero-shift or xi-divisor modules are required; pin the exact commit |
| [bombieri-vinogradov](https://github.com/kimihiro64/bombieri-vinogradov) | `7a1748306e026825ed6a5555516cc2f28989b2ac` | Lean `v4.33.1` | Complete Bombieri-Vinogradov theorem with released Comparator/NanoDa evidence | Headline theorem and proved analytic, sieve, and conversion layers are reusable at the exact release commit |

These repositories license their project-authored Lean source under Apache-2.0.
Always inspect the source module and dependency notices for material derived
from or imported through another repository.

## PrimeNumberTheoremAnd fork capabilities

| Capability | Stable module | Status at reviewed commit | Borrowing notes |
| --- | --- | --- | --- |
| Shifted zero-bound API needed by analytic consumers | `PrimeNumberTheoremAnd.StrongPNT.ShiftZeroBound` | Proved and used by Bombieri-Vinogradov | Public fork adaptation; inspect its exact imported StrongPNT surface |
| Riemann-xi divisor-zero vocabulary | `PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannXiDivisorZeros` | Proved and used by Bombieri-Vinogradov | General analytic bridge maintained in the fork's Mathlib-style layer |

The fork exists to expose APIs missing or unsuitable in the original PNT
repository. Do not recreate those fixes in a new child or silently pin an older
PNT revision when these declarations are required.

## Robin1984 capabilities

| Capability | Stable module or declaration | Status at reviewed commit | Borrowing notes |
| --- | --- | --- | --- |
| Prime-log Abel summation against Chebyshev theta | `Robin1984.Finite.PrimeLogAbelSummation`; `Robin1984.FiniteSupport.primeLogCoeff_abel` | Proved and used | Standard mathematics; a strong extraction candidate |
| Reciprocal-square prime Abel identity and positive tail kernel | `Robin1984.Finite.PrimeSquareAbel`; `Robin1984.FiniteSupport.primeSquareKernel_abel_tailKernel_form_finite` | Proved and used | Depends on the prime-log Abel module |
| Support of `Chebyshev.lcmUpto` factorization | `Robin1984.Helpers.LCMPrimeSupport`; `Robin1984.factorization_lcmUpto_support_eq_primesUpToSet` | Proved and used | Small number-theory helper; inspect its project helper dependency before extraction |
| Real zeta nonvanishing on `0 < s < 1` | `Robin1984.Analytic.RiemannZetaRealNonzero`; `Robin1984.riemannZeta_real_ne_zero_of_mem_Ioo_zero_one` | Proved and used | Large analytic import closure; not a drop-in leaf |
| Landau positive-transform continuation principle | `Robin1984.NicolasLandau.LandauMellinPrinciple` | Proved and used | General analytic statements live beside project-specialized applications; extract selectively |
| Weighted explicit-formula and xi-zero infrastructure | `Robin1984.NicolasLandau.WeightedExplicitFormula` and adjacent `Weighted*` modules | Proved and used | Relies on the pinned public `PrimeNumberTheoremAnd` fork |
| Exact finite-certificate patterns for large bounded ranges | `Robin1984.Finite.FiniteRowCertificate`, `FinitePacketProducts`, and `Finite.Certificates.*` | Kernel checked and used | Reuse the certificate format or generator pattern, not theorem-specific data blindly |
| Robin/RH and colossally-abundant equivalences | `Robin1984.Equivalence.Theorem` | Complete advertised result | Reference theorem and architecture; normally not infrastructure to copy |

## Bombieri-Vinogradov capabilities

| Capability | Stable module or declaration | Status at reviewed commit | Borrowing notes |
| --- | --- | --- | --- |
| Corrected finite Vaughan identity | `BombieriVinogradov.Proof.VaughanIdentity.Main`; `BombieriVinogradov.VaughanIdentity.vaughanIdentity` | Proved leaf | Source-specific statement with corrected cutoff/sign conventions |
| Additive and primitive-character large sieve | `BombieriVinogradov.Proof.LargeSieve.All`; `BombieriVinogradov.LargeSieve.additiveLargeSieve`; `characterLargeSieve` | Proved leaf library | Includes Farey separation, Fejer smoothing, packing, duality, Gauss sums, and character reduction |
| Generic finite Schur and complex Gram bounds | `BombieriVinogradov.Proof.LargeSieve.Schur` and `.Duality`; `schurBoundFinset`; `complexGramSchurBoundFinset` | Proved leaves | Especially suitable for extraction after namespace/import review |
| Dirichlet-character Abel integral and partial-sum control | `BombieriVinogradov.Helpers.DirichletCharacter.*`; `characterAbelIntegral_eq_LFunction_of_one_lt_re`; `characterPartialSum_isBigO_one` | Proved leaf family | Covers complete periods, endpoint decay, derivative majorants, and L-function agreement |
| Normalized Cauchy coefficient estimate | `BombieriVinogradov.Helpers.ComplexAnalysis.CauchyTaylor`; `norm_taylorCoefficient_le` | Proved leaf | Small general complex-analysis helper and strong extraction candidate |
| Explicit logarithmic Fourier cutoff | `BombieriVinogradov.Helpers.LogCutoff.*`; `logTrapezoid_fourier_inversion`; `integral_norm_fourier_integerLogCutoff_le_log` | Proved leaf family | Reusable Fourier cutoff with explicit `L1` estimates and integer indicator representation |
| Vaughan mean-value and Siegel-Walfisz infrastructure | `BombieriVinogradov.Assembly.VaughanMeanValue.*` and `BombieriVinogradov.Proof.SiegelWalfisz.*` | Proved and consumed by the headline theorem | Inspect the exact leaf and its source-aligned quantifiers before reuse |
| Weighted-to-prime-counting conversion | `BombieriVinogradov.PrimeCountingConversion.weighted_to_prime_counting` | Proved and consumed | Bridges the centered weighted estimate to the exact public prime-counting statement |
| Bombieri-Vinogradov theorem | `BombieriVinogradov.bombieriVinogradov` | Proved and released | Public headline theorem; assumption audit reports only `propext`, `Classical.choice`, and `Quot.sound` |

## Maintenance rule

Update this catalog when a direct child is added or retired, a capability is
renamed or upstreamed, a reviewed revision/toolchain changes, or a new
candidate inventory becomes publicly available. Keep claims declaration-level
and status-qualified; do not publish private obligations or speculative work.

## Prime-factor oscillation dependency

- Repository: https://github.com/kimihiro64/erdos-690-prime-factor-unimodality
- Exact revision: `ef3c9311d42b61db59f81d99741b5819d1986436`; Apache-2.0; Lean 4.34.0.
- Reuse `PrimeFactorUnimodality.Helpers.FirstDifference.Threshold` and
  `PrimeFactorUnimodality.Helpers.SymmetricBounds.Main`, plus the canonical
  `Definitions.KthPrimeFactor` density.
- Detailed declarations and assumptions: [DEPENDENCY_REUSE.md](DEPENDENCY_REUSE.md).
- Import the matching released oleans only. Never rebuild this dependency.
- The full-classification release is conditional; this catalog does not
  remove its theta-error hypothesis.
