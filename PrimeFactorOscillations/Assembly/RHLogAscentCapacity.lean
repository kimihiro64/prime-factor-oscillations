/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.RHSharpAscentReference
import PrimeFactorOscillations.Helpers.PrimeProfileReferenceCapacity

/-!
# The sharp double-logarithm bound for the actual reversal maximum under RH

The actual count, last ascent and reference root remain the same objects.
No endpoint supply is deduced from the conditional upper envelope.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

theorem exists_ordinary_last_ascent_loglog_capacity_of_RH (hRH : RiemannHypothesis) :
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
              (primeProfile (3 : Complex)).re) <= C / ((k - 1 : Nat) : Real) /\
          abs (Real.log (Real.log (primeThetaEndpointCount
            (Real.exp (Real.exp (u - Real.eulerMascheroniConstant))) : Real)) -
              (((k - 1 : Nat) : Real) / 3 - Real.eulerMascheroniConstant -
                deriv (fun x : Real => (primeProfile (x : Complex)).re) 3 /
                  (primeProfile (3 : Complex)).re)) <= (C + 96) / ((k - 1 : Nat) : Real) /\
          Real.log (Real.log (N : Real)) <=
            ((k - 1 : Nat) : Real) / 3 - Real.eulerMascheroniConstant -
              deriv (fun x : Real => (primeProfile (x : Complex)).re) 3 /
                (primeProfile (3 : Complex)).re + (C + 96) / ((k - 1 : Nat) : Real) := by
  choose c A C hc hA hC hbase using exists_ordinary_last_ascent_sharp_reference_of_RH hRH
  choose rB hrB hcountB using
    exists_primeThetaEndpointCount_near_rank_loglog_error 3 A (by norm_num) hA.le
  refine Exists.intro c (Exists.intro A (Exists.intro C
    (And.intro hc (And.intro hA (And.intro hC ?_)))))
  intro epsilon he
  choose K0 hK0 hdata using hbase epsilon he
  refine Exists.intro (max K0 (rB + 1)) (And.intro (hK0.trans (le_max_left _ _)) ?_)
  intro k hk
  have hk0 : K0 <= k := (le_max_left _ _).trans hk
  have hkB : rB + 1 <= k := (le_max_right _ _).trans hk
  have hrB' : rB <= k - 1 := by omega
  choose N i u hN hlo hi hlast hu heq hLower htheta hcount hcapacity hupper hshift using hdata k hk0
  have hnear : abs (u - ((k - 1 : Nat) : Real) / 3) <= A := by
    apply abs_le.mpr
    constructor <;> linarith [hu.1, hu.2]
  have hb := hcountB (k - 1) hrB' u hnear
  have hfactor : (32 : Real) * 3 = 96 := by norm_num
  rw [hfactor] at hb
  let T := Real.exp (Real.exp (u - Real.eulerMascheroniConstant))
  let center := ((k - 1 : Nat) : Real) / 3 - Real.eulerMascheroniConstant -
    deriv (fun x : Real => (primeProfile (x : Complex)).re) 3 /
      (primeProfile (3 : Complex)).re
  have hcenter : (u - Real.eulerMascheroniConstant) - center =
      u - ((k - 1 : Nat) : Real) / 3 +
        deriv (fun x : Real => (primeProfile (x : Complex)).re) 3 /
          (primeProfile (3 : Complex)).re := by dsimp [center]; ring
  have hBerror : abs (Real.log (Real.log (primeThetaEndpointCount T : Real)) - center) <=
      (C + 96) / ((k - 1 : Nat) : Real) := by
    calc
      abs (Real.log (Real.log (primeThetaEndpointCount T : Real)) - center) <=
          abs (Real.log (Real.log (primeThetaEndpointCount T : Real)) -
            (u - Real.eulerMascheroniConstant)) +
            abs ((u - Real.eulerMascheroniConstant) - center) := abs_sub_le _ _ _
      _ <= 96 / ((k - 1 : Nat) : Real) + C / ((k - 1 : Nat) : Real) := by
        rw [hcenter]
        exact add_le_add hb.2 hshift
      _ = (C + 96) / ((k - 1 : Nat) : Real) := by ring
  have hNpos : 1 < (N : Real) := by
    have h := Real.exp_lt_exp.mpr (Real.exp_pos (c * (k : Real)))
    have h1 : 1 < Real.exp (Real.exp (c * (k : Real))) := by
      simpa only [Real.exp_zero] using h
    exact h1.trans_le hlo
  have hNB : (N : Real) <= primeThetaEndpointCount T := by
    exact_mod_cast hcount.trans hcapacity
  have hlog := Real.log_le_log (zero_lt_one.trans hNpos) hNB
  have hloglog := Real.log_le_log (Real.log_pos hNpos) hlog
  have hNbound : Real.log (Real.log (N : Real)) <=
      center + (C + 96) / ((k - 1 : Nat) : Real) := by
    have htop := (abs_le.mp hBerror).2
    linarith only [hloglog, htop]
  refine Exists.intro N (Exists.intro i (Exists.intro u ?_))
  refine And.intro hN (And.intro hlo (And.intro hi (And.intro hlast ?_)))
  refine And.intro hu (And.intro heq (And.intro hLower ?_))
  exact And.intro htheta (And.intro hcount (And.intro hcapacity
    (And.intro hupper (And.intro hshift (And.intro hBerror hNbound)))))

end PrimeFactorOscillations
