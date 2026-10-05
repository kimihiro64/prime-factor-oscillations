/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.RHAscentAsymptoticCapacity
import PrimeFactorOscillations.Helpers.PrimeProfileRootShift

/-!
# Sharp reference displacement for the actual RH last-ascent envelope

The estimate is applied to the same root, reversal maximum and last ascent
already supplied by the RH capacity theorem. Its constants precede epsilon.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

theorem exists_ordinary_last_ascent_sharp_reference_of_RH (hRH : RiemannHypothesis) :
    exists c A C : Real, 0 < c /\ 0 < A /\ 0 <= C /\
      forall epsilon : Real, 0 < epsilon -> exists K : Nat, 2 <= K /\
        forall k : Nat, K <= k -> exists N i : Nat, exists u : Real,
          HasReversalNumber (ordinaryDensity k) N /\
          Real.exp (Real.exp (c * (k : Real))) <= (N : Real) /\
          ordinaryDensity k i < ordinaryDensity k (i + 1) /\
          (forall j : Nat, ordinaryDensity k j < ordinaryDensity k (j + 1) -> j <= i) /\
          Set.Ioo (((k - 1 : Nat) : Real) / 3 - A)
            (((k - 1 : Nat) : Real) / 3 + A) u /\
          Nat.factorialConvolution primeProfileRealCoefficient (k - 2) u /
            Nat.factorialConvolution primeProfileRealCoefficient (k - 1) u = 3 /\
          (1 - epsilon) * (N : Real) * Real.log (N : Real) <=
            Chebyshev.theta ((PrimeFactorUnimodality.primeAt i - 1 : Nat) : Real) /\
          Chebyshev.theta ((PrimeFactorUnimodality.primeAt i - 1 : Nat) : Real) <
            Real.exp (Real.exp (u - Real.eulerMascheroniConstant)) /\
          N <= Nat.primeCounting (PrimeFactorUnimodality.primeAt i) /\
          Nat.primeCounting (PrimeFactorUnimodality.primeAt i) <=
            primeThetaEndpointCount (Real.exp (Real.exp (u - Real.eulerMascheroniConstant))) /\
          (N : Real) <= (1 + epsilon) *
            (Real.exp (Real.exp (u - Real.eulerMascheroniConstant)) /
              Real.log (Real.exp (Real.exp (u - Real.eulerMascheroniConstant)))) /\
          abs (u - ((k - 1 : Nat) : Real) / 3 +
            deriv (fun x : Real => (primeProfile (x : Complex)).re) 3 /
              (primeProfile (3 : Complex)).re) <= C / ((k - 1 : Nat) : Real) := by
  choose c A hc hA hbase using exists_ordinary_last_ascent_asymptotic_capacity_of_RH hRH
  choose C rD hC hrD hbound using
    exists_primeProfile_reference_root_shift_bound 3 A (by norm_num) hA.le
  choose n0 hn0 using exists_nat_gt (6 * A)
  refine Exists.intro c (Exists.intro A (Exists.intro C
    (And.intro hc (And.intro hA (And.intro hC ?_)))))
  intro epsilon he
  choose K0 hK0 hdata using hbase epsilon he
  refine Exists.intro (max K0 (max (rD + 1) (n0 + 2)))
    (And.intro (hK0.trans (le_max_left _ _)) ?_)
  intro k hk
  have hk0 : K0 <= k := (le_max_left _ _).trans hk
  have hkD : rD + 1 <= k := (le_max_left _ _).trans ((le_max_right _ _).trans hk)
  have hkn : n0 + 2 <= k := (le_max_right _ _).trans ((le_max_right _ _).trans hk)
  have hk2 : 2 <= k := hK0.trans hk0
  have hrD' : rD <= k - 1 := by omega
  have hnR : (n0 : Real) < ((k - 1 : Nat) : Real) := by
    exact_mod_cast (show n0 < k - 1 by omega)
  have hrlarge : 6 * A < ((k - 1 : Nat) : Real) := hn0.trans hnR
  choose N i u hN hlo hi hlast hu heq hLower htheta hcount hcapacity hupper using hdata k hk0
  have hu0 : 0 < u := by linarith [hu.1]
  have hRu : ((k - 1 : Nat) : Real) / u <= 6 := by
    have hcancel : ((k - 1 : Nat) : Real) / u * u = ((k - 1 : Nat) : Real) := by
      field_simp
    by_contra hnot
    have hmul := mul_lt_mul_of_pos_right (lt_of_not_ge hnot) hu0
    nlinarith [hu.1]
  have hnear : abs (((k - 1 : Nat) : Real) / 3 - u) <= A := by
    apply abs_le.mpr
    constructor <;> linarith [hu.1, hu.2]
  have hroot : Nat.factorialConvolution primeProfileRealCoefficient ((k - 1) - 1) u /
      Nat.factorialConvolution primeProfileRealCoefficient (k - 1) u = 3 := by
    have hsub : (k - 1) - 1 = k - 2 := by omega
    simpa only [hsub] using heq
  have hshift := hbound (k - 1) hrD' u hu0
    (by simpa only [show (2 : Real) * 3 = 6 by norm_num] using hRu) hnear hroot
  refine Exists.intro N (Exists.intro i (Exists.intro u ?_))
  refine And.intro hN (And.intro hlo (And.intro hi (And.intro hlast ?_)))
  refine And.intro hu (And.intro heq (And.intro hLower ?_))
  exact And.intro htheta (And.intro hcount (And.intro hcapacity (And.intro hupper hshift)))

end PrimeFactorOscillations
