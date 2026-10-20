/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.PrimeProfileSharedExcursions
import PrimeFactorOscillations.Helpers.PrimeConstellationCycles

/-!
# RH and recurrence of any prescribed finite prime-constellation shape

An arbitrary injective bounded offset list is encoded by recurring full-shape
prime cycles. The actual bounded-permutation coefficient ratio reads RH
against the one fixed canonical reference, including noninvolutive cycles.
The conclusion is RH AND shape recurrence, not recurrence supplied by RH.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open Filter Robin1984

/-- The exact arbitrary-shape extension of the constellation/RH witness equivalence. -/
theorem recurrent_prime_shape_and_rh_iff_canonical_cycle_transport
    {k : Nat} (h : Fin k -> Nat) (hinj : Function.Injective h)
    (W : Nat) (hW : forall i, h i <= W) (alpha : Real) (ha : 0 < alpha) :
    (RiemannHypothesis /\ RecurrentPrimeShape h) <->
      (exists sigma : Equiv.Perm Nat.Primes,
        exists hdispl : forall p : Nat.Primes,
          abs (((sigma p : Nat) : Real) - ((p : Nat) : Real)) <= (W : Real),
        (forall N : Nat, exists q : Nat, N <= q /\ PrimeShapeCycleAt h sigma q) /\
        Filter.Eventually (fun N : Nat =>
          let r := Nat.floor (alpha * canonicalPrimeOddsLaw.referenceClock N)
          (boundedPrimePermutationLaw sigma W hdispl).densityRatio N r <
            canonicalPrimeOddsLaw.referenceRatio r (canonicalPrimeOddsLaw.referenceClock N))
          atTop) := by
  constructor
  . intro hBoth
    choose sigma hdispl hCycles using
      hBoth.2.exists_bounded_cycle_permutation h hinj W hW
    refine Exists.intro sigma (Exists.intro hdispl (And.intro hCycles ?_))
    exact (riemannHypothesis_iff_bounded_permutation_canonical_sign
      sigma W hdispl alpha ha).mp hBoth.1
  . intro hex
    let sigma := hex.choose
    have hs := hex.choose_spec
    let hdispl := hs.choose
    have hWitness := hs.choose_spec
    refine And.intro ?_ ?_
    . exact (riemannHypothesis_iff_bounded_permutation_canonical_sign
        sigma W hdispl alpha ha).mpr hWitness.2
    . intro N
      choose q hq hc using hWitness.1 N
      exact Exists.intro q (And.intro hq hc.prime_offsets)

end PrimeFactorOscillations
