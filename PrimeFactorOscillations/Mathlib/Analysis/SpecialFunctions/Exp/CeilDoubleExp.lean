/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Order.Floor.Ring
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Exp.DoubleExpGrowth
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.DoubleExpWindow

/-! # Natural ceilings and double-exponential logarithmic bands -/

namespace Real

/-- Every actual prefix in the natural double-exponential window has the required band. -/
theorem ceil_double_exp_prime_prefix_band {t : Real} (ht : 8 <= t) {p : Nat}
    (hlo : Nat.ceil (Real.exp (Real.exp t)) <= p)
    (hhi : p <= 4 * Nat.ceil (Real.exp (Real.exp t))) :
    ((3 : Real) / 4) * t <= Real.log (Real.log (p - 1 : Nat)) /\
      Real.log (Real.log (p - 1 : Nat)) <= ((5 : Real) / 4) * t := by
  have hEpos := Real.exp_pos (Real.exp t)
  have hE : (2 : Real) <= Real.exp (Real.exp t) := by
    linarith [Real.add_one_le_exp t, Real.add_one_le_exp (Real.exp t)]
  have hceil := Nat.le_ceil (Real.exp (Real.exp t))
  have hceilUpper := Nat.ceil_lt_add_one hEpos.le
  have hceilPos : 0 < Nat.ceil (Real.exp (Real.exp t)) := Nat.ceil_pos.mpr hEpos
  have hp1 : 1 <= p := by omega
  have hloR : (Nat.ceil (Real.exp (Real.exp t)) : Real) <= p := by exact_mod_cast hlo
  have hhiR : (p : Real) <= 4 * (Nat.ceil (Real.exp (Real.exp t)) : Real) := by
    exact_mod_cast hhi
  apply Real.log_log_in_double_exp_window ht
  next =>
    rw [Nat.cast_sub hp1, Nat.cast_one]
    linarith
  next =>
    rw [Nat.cast_sub hp1, Nat.cast_one]
    linarith

/-- A natural ceiling plus one supplies the exact lower prefix scale and has
every strictly larger eventual upper scale. The fixed threshold is arbitrary. -/
theorem eventually_ceil_double_exp_scale_bounds
    (a b : Real) (ha : 0 < a) (hab : a < b) (Q : Nat) :
    exists K : Nat, forall k : Nat, K <= k ->
      let U := Nat.ceil (Real.exp (Real.exp (a * k))) + 1
      Q <= U /\ a * k <= Real.log (Real.log (U - 1 : Nat)) /\
        (U : Real) <= Real.exp (Real.exp (b * k)) := by
  choose K0 hK0 using exists_nat_gt ((Q : Real) / a)
  choose K1 hK1 using eventually_mul_double_exp_add_one_le a b 2 ha.le hab
    (by norm_num)
  refine Exists.intro (max K0 K1) ?_
  intro k hk
  let E : Real := Real.exp (Real.exp (a * k))
  have hEp : 0 < E := Real.exp_pos _
  have hceil : E <= (Nat.ceil E : Real) := Nat.le_ceil E
  have hceilUpper : (Nat.ceil E : Real) < E + 1 := Nat.ceil_lt_add_one hEp.le
  have hkR : (K0 : Real) <= k := by exact_mod_cast (le_max_left K0 K1).trans hk
  have hquot : (Q : Real) / a <= k := hK0.le.trans hkR
  have hmul := mul_le_mul_of_nonneg_right hquot ha.le
  have hc : ((Q : Real) / a) * a = Q := by field_simp [ne_of_gt ha]
  rw [hc] at hmul
  have hElarge : (Q : Real) <= E := by
    have hinner := Real.add_one_le_exp (a * k)
    have houter := Real.add_one_le_exp (Real.exp (a * k))
    dsimp only [E]
    nlinarith only [hmul, hinner, houter]
  have hQceil : Q <= Nat.ceil E := by exact_mod_cast hElarge.trans hceil
  refine And.intro (Nat.le_trans hQceil (Nat.le_succ _)) (And.intro ?_ ?_)
  next =>
    simp only [Nat.add_sub_cancel]
    have hlog := Real.log_le_log hEp hceil
    change Real.log (Real.exp (Real.exp (a * k))) <=
      Real.log (Nat.ceil E : Real) at hlog
    rw [Real.log_exp] at hlog
    have hloglog := Real.log_le_log (Real.exp_pos _) hlog
    simpa only [Real.log_exp] using hloglog
  next =>
    have hu := hK1 k ((le_max_right K0 K1).trans hk)
    have hcR : ((Nat.ceil E + 1 : Nat) : Real) = (Nat.ceil E : Real) + 1 := by
      push_cast
      rfl
    change ((Nat.ceil E + 1 : Nat) : Real) <= _
    rw [hcR]
    change 2 * (E + 1) <= _ at hu
    linarith only [hceilUpper, hEp, hu]


end Real
