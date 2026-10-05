/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.Headline
import PrimeFactorOscillations.Assembly.RHAscentEnvelope
import PrimeFactorOscillations.Helpers.AscentEndpoints
import PrimeFactorOscillations.Proof.Upper.UniformTail

/-!
# Actual last-ascent and reversal-count capacity

The established reversal supply and terminal descent produce a last actual
ordinary ascent at every sufficiently large rank. Under RH, its prime endpoint
and the attained reversal maximum obey the exact reference capacity sandwich.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

theorem ordinary_eventually_last_ascent_with_reversal_number :
    exists (c : Real) (K : Nat), 0 < c /\ 2 <= K /\
      forall k : Nat, K <= k -> exists N i : Nat,
        HasReversalNumber (ordinaryDensity k) N /\
        Real.exp (Real.exp (c * (k : Real))) <= (N : Real) /\
        ordinaryDensity k i < ordinaryDensity k (i + 1) /\
        (forall j : Nat, ordinaryDensity k j < ordinaryDensity k (j + 1) -> j <= i) /\
        N <= Nat.primeCounting (PrimeFactorUnimodality.primeAt i) := by
  choose c hc hsupply using doubleExponentialReversalBounds
  choose Ks hKs hs using hsupply (1 : Real) (by norm_num)
  choose Kt hKt ht using both_densities_eventually_strict_tail (1 : Real) (by norm_num)
  refine Exists.intro c (Exists.intro (max Ks Kt)
    (And.intro hc (And.intro (hKt.trans (le_max_right _ _)) ?_)))
  intro k hk
  have hks : Ks <= k := (le_max_left _ _).trans hk
  have hkt : Kt <= k := (le_max_right _ _).trans hk
  choose N hN hlo hhi using (hs k hks).1
  have hNpos : 0 < N := by
    have hpos : (0 : Real) < N := (Real.exp_pos _).trans_le hlo
    exact_mod_cast hpos
  have htail (j : Nat) (hj : upperCutoffIndex 1 k <= j) :
      ordinaryDensity k (j + 1) <= ordinaryDensity k j :=
    ((ht k hkt).2 j hj).1.le
  choose i hi hlast using exists_last_ascent_of_nonincreasing_tail
    (ordinaryDensity k) (upperCutoffIndex 1 k) N hNpos htail hN.1
  exact Exists.intro N (Exists.intro i (And.intro hN (And.intro hlo
    (And.intro hi (And.intro hlast
      (reversal_count_le_primeCounting_of_ascent_bound (ordinaryDensity k) i N hlast hN.1))))))

theorem exists_ordinary_last_ascent_and_capacity_of_RH (hRH : RiemannHypothesis) :
    exists (c A : Real) (K : Nat), 0 < c /\ 0 < A /\ 2 <= K /\
      forall k : Nat, K <= k -> exists N i : Nat, exists u : Real,
        HasReversalNumber (ordinaryDensity k) N /\
        Real.exp (Real.exp (c * (k : Real))) <= (N : Real) /\
        ordinaryDensity k i < ordinaryDensity k (i + 1) /\
        (forall j : Nat, ordinaryDensity k j < ordinaryDensity k (j + 1) -> j <= i) /\
        Set.Ioo (((k - 1 : Nat) : Real) / 3 - A)
          (((k - 1 : Nat) : Real) / 3 + A) u /\
        Nat.factorialConvolution primeProfileRealCoefficient (k - 2) u /
          Nat.factorialConvolution primeProfileRealCoefficient (k - 1) u = 3 /\
        Chebyshev.theta ((PrimeFactorUnimodality.primeAt i - 1 : Nat) : Real) <
          Real.exp (Real.exp (u - Real.eulerMascheroniConstant)) /\
        N <= Nat.primeCounting (PrimeFactorUnimodality.primeAt i) /\
        Nat.primeCounting (PrimeFactorUnimodality.primeAt i) <=
          primeThetaEndpointCount (Real.exp (Real.exp (u - Real.eulerMascheroniConstant))) := by
  choose c Kl hc hKl hlast using ordinary_eventually_last_ascent_with_reversal_number
  choose A Kr hA hKr hroot using exists_ordinary_ascent_theta_envelope_of_RH hRH
  refine Exists.intro c (Exists.intro A (Exists.intro (max Kl Kr)
    (And.intro hc (And.intro hA (And.intro (hKl.trans (le_max_left _ _)) ?_)))))
  intro k hk
  have hkl : Kl <= k := (le_max_left _ _).trans hk
  have hkr : Kr <= k := (le_max_right _ _).trans hk
  choose N i hN hlo hi hmax hcount using hlast k hkl
  choose u hu heq hcover using hroot k hkr
  have htheta := hcover i hi
  exact Exists.intro N (Exists.intro i (Exists.intro u
    (And.intro hN (And.intro hlo (And.intro hi (And.intro hmax
      (And.intro hu (And.intro heq (And.intro htheta (And.intro hcount
        (primeCounting_le_primeThetaEndpointCount (PrimeFactorUnimodality.primeAt i)
          (Real.exp (Real.exp (u - Real.eulerMascheroniConstant))) htheta)))))))))))

end PrimeFactorOscillations
