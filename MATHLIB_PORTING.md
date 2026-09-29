# Mathlib candidate layer

Reusable mathematics intended for possible upstreaming lives under
`PrimeFactorOscillations/Mathlib/` and is exported by `PrimeFactorOscillations/Mathlib.lean`.
The child generator replaces `PrimeFactorOscillations` with the configured project
namespace.

## Hard boundary

A Mathlib candidate module may import only:

- narrow `Mathlib.*`, `Batteries.*`, `Init.*`, `Lean.*`, or `Std.*` modules;
- another module inside the same `<Project>.Mathlib` candidate layer.

It may not import project definitions, helpers, proof branches, assembly,
`Challenge`, `Solution`, or a third-party project library. Its declarations
must use the namespace they would have after upstreaming, never the project's
namespace. The architecture audit enforces these dependency and namespace
rules.

## File and declaration standards

Each real candidate file should:

1. mirror its proposed Mathlib destination after the `<Project>/Mathlib/`
   prefix is removed;
2. use Mathlib's copyright, Apache-2.0 licence, author, module-documentation,
   declaration-documentation, naming, and formatting conventions;
3. state results at reusable generality without headline-theorem terminology;
4. use narrow, sorted, nonredundant imports and avoid project-only dependencies;
5. build independently before the project modules that consume it;
6. include focused regression examples or tests when behavior is not captured
   by a theorem statement alone;
7. contain no `sorry`, local axioms, discovery commands, or generated proof
   shortcuts.

## Candidate inventory

| Project module | Proposed Mathlib path | Readiness | Upstream reference |
| --- | --- | --- | --- |
| `PrimeFactorOscillations.Mathlib.Algebra.Field.FiniteAffineRoots` | `Mathlib/Algebra/Field/FiniteAffineRoots.lean` | extracting | Distinct affine-root cardinality and exact nonzero-pair product residue formula proved with standard foundations; maintained audit pending |
| `PrimeFactorOscillations.Mathlib.Data.ZMod.UnitPairCRT` | `Mathlib/Data/ZMod/UnitPairCRT.lean` | extracting | Exact unit-pair pattern cardinalities factor over pairwise coprime moduli; private proof and foundational-axiom audit passed, maintained audit pending |
| `PrimeFactorOscillations.Mathlib.Algebra.Group.FiniteSumFibers` | `Mathlib/Algebra/Group/FiniteSumFibers.lean` | extracting | Exact finite additive-pair fiber and arbitrary-root counts proved with standard foundations; maintained audit pending; consumer is the affine prime-pair local law |
| `PrimeFactorOscillations.Mathlib.Algebra.All` | `Mathlib/Algebra/All.lean` | extracting | Import-only export group preserves every existing algebra candidate while respecting facade capacity; bookkeeping only |
| `PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliMass` | `Mathlib/Probability/Distributions/FiniteBernoulliMass.lean` | project-verified | Maintained 112-module Windows 4.34.0 build and direct public audits passed; exact forced/excluded-coordinate identities over commutative rings use only propext and Quot.sound |
| `PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliPatterns` | `Mathlib/Probability/Distributions/FiniteBernoulliPatterns.lean` | extracting | Exact polynomial coefficient and finite cardinality-pattern expansions over every commutative ring, including zero and one coordinates; focused proof and axiom checks passed |
| `PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliOdds` | `Mathlib/Probability/Distributions/FiniteBernoulliOdds.lean` | project-verified | Maintained 113-module Windows 4.34.0 build and both direct public axiom audits passed with standard foundations only |
| `PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliInterior` | `Mathlib/Probability/Distributions/FiniteBernoulliInterior.lean` | extracting | Existing bounds verified; new exact-sum/excess extension proved in the same environment; extended maintained audit pending |
| `PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliBounds` | `Mathlib/Probability/Distributions/FiniteBernoulliBounds.lean` | project-verified | Actual finite coefficient ratios with support, positive denominator and exact forced shift; maintained 122-module build and direct public axiom audits passed with standard foundations only |
| `PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliAsymptotics` | `Mathlib/Probability/Distributions/FiniteBernoulliAsymptotics.lean` | extracting | Uniform normalized actual coefficient ratio from total-odds and logarithmic largest-weight bounds, with bounded exact forced count; private theorem and axiom audit passed; maintained check pending |
| `PrimeFactorOscillations.Mathlib.RingTheory.MvPolynomial.Symmetric.OrderedBounds` | `Mathlib/RingTheory/MvPolynomial/Symmetric/OrderedBounds.lean` | project-verified | Ordered-field generalization of the existing rational finite-weight induction; maintained 115-module build and three direct public axiom audits passed with standard foundations only |
| `PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Exp.All` | `Mathlib/Analysis/SpecialFunctions/Exp/All.lean` | project-verified | Import-only export group retaining the three existing exponential modules within the facade capacity; maintained 115-module build passed; bookkeeping only |
| `PrimeFactorOscillations.Mathlib.RingTheory.MvPolynomial.Symmetric.LargestWeightBounds` | `Mathlib/RingTheory/MvPolynomial/Symmetric/LargestWeightBounds.lean` | project-verified | Exact descending permutation, symmetric ratio bounds and cap/excess estimate; maintained 116-module build and four direct public foundational-only audits passed |
| `PrimeFactorOscillations.Mathlib.RingTheory.MvPolynomial.Symmetric.LargestWeightHarmonic` | `Mathlib/RingTheory/MvPolynomial/Symmetric/LargestWeightHarmonic.lean` | extracting | Existing bounds verified; new exact-sum/excess extension proved in the same environment; extended maintained audit pending |
| `PrimeFactorOscillations.Mathlib.Algebra.Order.BigOperators.Group.InverseSquare` | `Mathlib/Algebra/Order/BigOperators/Group/InverseSquare.lean` | project-verified | Maintained 119-module build and both direct public consumer axiom audits passed with standard foundations only |
| `PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Exp.DoubleExpGrowth` | `Mathlib/Analysis/SpecialFunctions/Exp/DoubleExpGrowth.lean` | project-verified | Maintained Windows 4.34.0 build and consuming foundational-only axiom audit passed; elementary fixed-loss comparison for the sharp rate passage |
| `PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Exp.DoubleExpFiniteSum` | `Mathlib/Analysis/SpecialFunctions/Exp/DoubleExpFiniteSum.lean` | project-verified | Maintained Windows 4.34.0 build and direct public-module foundational-only axiom audit passed; finite thresholds synchronized explicitly |
| `PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.DoubleLogRate` | `Mathlib/Analysis/SpecialFunctions/Log/DoubleLogRate.lean` | project-verified | Maintained Windows 4.34.0 build and direct public theorem axiom audit passed; denominator and limsup side conditions explicit |
| `PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.DoubleLogGauge` | `Mathlib/Analysis/SpecialFunctions/Log/DoubleLogGauge.lean` | project-verified | Maintained build and both public upper/frequent-lower axiom audits passed with standard foundations only |
| `PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.CountingRate` | `Mathlib/Analysis/SpecialFunctions/Log/CountingRate.lean` | project-verified | Maintained Windows 4.34.0 build and actual prime-gap exponent consumer axiom audit passed; [0,1] and bounded-count zero results use only standard foundations |
| `PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Pow.PowerLogCount` | `Mathlib/Analysis/SpecialFunctions/Pow/PowerLogCount.lean` | project-verified | Maintained Windows 4.34.0 build passed; consumed by the public quantitative supply and headline, whose full axiom closures use only standard foundations |
| `PrimeFactorOscillations.Mathlib.RingTheory.MvPolynomial.Symmetric.RationalBounds` | `Mathlib/RingTheory/MvPolynomial/Symmetric/RationalBounds.lean` | project-verified | Generalizes the finite-weight induction in Erdos 690, commit `ef3c9311d42b61db59f81d99741b5819d1986436`; Apache-2.0; no dependency import |
| `PrimeFactorOscillations.Mathlib.Algebra.Order.BigOperators.Group.FiniteCutoff` | `Mathlib/Algebra/Order/BigOperators/Group/FiniteCutoff.lean` | project-verified | Elementary finite-support decomposition; maintained source compiled and consumed by the audited upper theorem |
| `PrimeFactorOscillations.Mathlib.Algebra.Order.BigOperators.Ring.WeightedCount` | `Mathlib/Algebra/Order/BigOperators/Ring/WeightedCount.lean` | project-verified | Independent signed finite-sum counting inequality; maintained source compiled |
| `PrimeFactorOscillations.Mathlib.Algebra.Order.BigOperators.Ring.WeightedReweighting` | `Mathlib/Algebra/Order/BigOperators/Ring/WeightedReweighting.lean` | project-verified | Maintained 167-module Windows 4.34.0 build and four direct public declaration/axiom audits passed with standard foundations; exact finite second-moment reweighting, no new asymptotic estimate |
| `PrimeFactorOscillations.Mathlib.Data.Nat.Prime.CompositeBlocks` | `Mathlib/Data/Nat/Prime/CompositeBlocks.lean` | project-verified | Elementary periodic factorial construction; exact endpoints compiled |
| `PrimeFactorOscillations.Mathlib.Data.Nat.Prime.RoughCofactor` | `Mathlib/Data/Nat/Prime/RoughCofactor.lean` | project-verified | Strict cube-root least-factor criterion for prime cofactors; maintained 169-module Windows 4.34.0 build and direct public audit passed with standard foundations only |
| `PrimeFactorOscillations.Mathlib.Data.Nat.Prime.All` | `Mathlib/Data/Nat/Prime/All.lean` | extracting | Import-only group preserves factorial-cell exports and adds the prime cofactor criterion; bookkeeping only |
| `PrimeFactorOscillations.Mathlib.Data.Nat.Prime.FactorialCells` | `Mathlib/Data/Nat/Prime/FactorialCells.lean` | project-verified | All 58 maintained modules freshly checked in Windows Lean 4.34.0; maintained conditional headline audit uses only standard foundations |
| `PrimeFactorOscillations.Mathlib.Data.Nat.Prime.FactorialCellCount` | `Mathlib/Data/Nat/Prime/FactorialCellCount.lean` | project-verified | All 58 maintained modules freshly checked in Windows Lean 4.34.0; maintained conditional headline audit uses only standard foundations |
| `PrimeFactorOscillations.Mathlib.Data.Nat.Prime.FactorialCrossing` | `Mathlib/Data/Nat/Prime/FactorialCrossing.lean` | project-verified | All 58 maintained modules freshly checked in Windows Lean 4.34.0; maintained conditional headline audit uses only standard foundations |
| `PrimeFactorOscillations.Mathlib.Data.Nat.Prime.FactorialCellSelection` | `Mathlib/Data/Nat/Prime/FactorialCellSelection.lean` | project-verified | All 58 maintained modules freshly checked in Windows Lean 4.34.0; maintained conditional headline audit uses only standard foundations |
| `PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.DoubleExpWindow` | `Mathlib/Analysis/SpecialFunctions/Log/DoubleExpWindow.lean` | project-verified | All 58 maintained modules freshly checked in Windows Lean 4.34.0; maintained conditional headline audit uses only standard foundations |
| `PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Exp.CeilDoubleExp` | `Mathlib/Analysis/SpecialFunctions/Exp/CeilDoubleExp.lean` | project-verified | All 58 maintained modules freshly checked in Windows Lean 4.34.0; maintained conditional headline audit uses only standard foundations |
| `PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Pow.CeilDoubleExpCount` | `Mathlib/Analysis/SpecialFunctions/Pow/CeilDoubleExpCount.lean` | project-verified | All 58 maintained modules freshly checked in Windows Lean 4.34.0; maintained conditional headline audit uses only standard foundations |

| `PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.DoubleExpWindowAdditive` | `Mathlib/Analysis/SpecialFunctions/Log/DoubleExpWindowAdditive.lean` | project-verified | Maintained Windows Lean 4.34.0 build passed for all 67 owned modules, with zero dependency builds; exact sharp consumer axiom audit passed in the private prototype |
| `PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Exp.CeilDoubleExpAdditive` | `Mathlib/Analysis/SpecialFunctions/Exp/CeilDoubleExpAdditive.lean` | project-verified | Maintained Windows Lean 4.34.0 build passed for all 67 owned modules, with zero dependency builds; exact sharp consumer axiom audit passed in the private prototype |
| `PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Pow.CeilDoubleExpPowerCount` | `Mathlib/Analysis/SpecialFunctions/Pow/CeilDoubleExpPowerCount.lean` | project-verified | Maintained Windows Lean 4.34.0 build passed for all 67 owned modules, with zero dependency builds; exact sharp consumer axiom audit passed in the private prototype |

| `PrimeFactorOscillations.Mathlib.NumberTheory.ArithmeticFunction.LeastPrimeOwner` | `Mathlib/NumberTheory/ArithmeticFunction/LeastPrimeOwner.lean` | project-verified | Exact least-factor Mobius exclusion and full product-modulus identity; maintained 170-module Windows Lean 4.34.0 build and public foundational-only axiom audit passed; no dependency builds |
| `PrimeFactorOscillations.Mathlib.NumberTheory.ArithmeticFunction.MoebiusHyperbola` | `Mathlib/NumberTheory/ArithmeticFunction/MoebiusHyperbola.lean` | project-verified | Complementary-divisor symmetry and exact lower-hyperbola cancellation for Mobius value one; maintained 172-module Windows 4.34.0 build, three direct public foundational-only axiom audits and existing public statement/axiom audit passed; no dependency builds |
| `PrimeFactorOscillations.Mathlib.NumberTheory.ArithmeticFunction.All` | `Mathlib/NumberTheory/ArithmeticFunction/All.lean` | extracting | Import-only group preserves least-owner exports and adds the complementary-divisor identities; bookkeeping only |

Readiness should be one of: `extracting`, `project-verified`, `mathlib-ready`,
`submitted`, or `upstreamed`. A module is `mathlib-ready` only after it has an
identified destination, no project dependency, focused tests, and a clean
standalone build against the project's pinned Mathlib revision.
