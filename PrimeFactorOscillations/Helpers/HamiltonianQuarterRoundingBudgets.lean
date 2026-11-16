/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianQuarterDegreeBounds
import PrimeFactorOscillations.Helpers.HamiltonianRoundedEdgeSet

/-! # Uniform envelopes for the exact quarter-power rounding degree -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.LPF

theorem hamiltonian_quarter_rounding_envelopes
    (m : Nat) (hm : 256 <= m) (alpha : Real) (ha : 0 <= alpha)
    (hMass : (m : Real) * alpha <= Real.log (2 * (m : Real))) :
    let d := (hamiltonianQuarterPrimeDegree m : Real)
    let L := Real.log (4 * (m : Real))
    let ell := Real.log (2 * (m : Real))
    d * alpha * L ^ 2 <= 4 * ell ^ 3 / (m : Real) ^ (1 / 2 : Real) /\
      d * alpha * L <= 2 * ell ^ 2 / (m : Real) ^ (1 / 2 : Real) /\
      L / d <= 4 * ell / (m : Real) ^ (1 / 4 : Real) := by
  intro d L ell
  have hM : (256 : Real) <= (m : Real) := by exact_mod_cast hm
  have hM0 : 0 < (m : Real) := by linarith only [hM]
  have hLog : 1 <= ell := hamiltonian_log_four_lower.trans
    (Real.log_le_log (by norm_num) (by linarith only [hM]))
  have hEll : 0 <= ell := by linarith only [hLog]
  have hLogTwo : Real.log 2 <= ell :=
    Real.log_le_log (by norm_num) (by linarith only [hM])
  have hLId : L = Real.log 2 + ell := by
    dsimp [L, ell]
    rw [show 4 * (m : Real) = 2 * (2 * (m : Real)) by ring,
      Real.log_mul (by norm_num) (by positivity)]
  have hL : 0 <= L := by
    have hTwo : 0 <= Real.log 2 := Real.log_nonneg (by norm_num)
    linarith only [hLId, hTwo, hEll]
  have hLCap : L <= 2 * ell := by linarith only [hLId, hLogTwo]
  have hD := hamiltonian_quarter_prime_degree_bounds m hm
  have hd : 0 < d := by
    have hOne : (1 : Real) <= d := by
      change (1 : Real) <= (hamiltonianQuarterPrimeDegree m : Real)
      exact_mod_cast hD.1
    linarith only [hOne]
  let x : Real := (m : Real) ^ (1 / 2 : Real)
  let y : Real := (m : Real) ^ (1 / 4 : Real)
  have hx : 0 < x := Real.rpow_pos_of_pos hM0 _
  have hy : 0 < y := Real.rpow_pos_of_pos hM0 _
  have hxSq : x ^ 2 = (m : Real) := by
    dsimp [x]
    rw [<- Real.rpow_natCast, <- Real.rpow_mul hM0.le]
    norm_num
  have hAlpha : alpha <= ell / (m : Real) := by
    calc
      alpha = ((m : Real) * alpha) / (m : Real) := by
        field_simp [ne_of_gt hM0]
      _ <= ell / (m : Real) := div_le_div_of_nonneg_right hMass hM0.le
  have hDA : d * alpha <= x * (ell / (m : Real)) :=
    mul_le_mul hD.2.1 hAlpha ha hx.le
  have hRight : 0 <= x * (ell / (m : Real)) :=
    mul_nonneg hx.le (div_nonneg hEll hM0.le)
  have hSmall : d * alpha * L ^ 2 <= 4 * ell ^ 3 / x := by
    calc
      _ <= x * (ell / (m : Real)) * (2 * ell) ^ 2 :=
        mul_le_mul hDA (wick_nonnegative_power_le L (2 * ell) hL hLCap 2)
          (sq_nonneg L) hRight
      _ = _ := by
        rw [<- hxSq]
        field_simp [ne_of_gt hx]
        <;> ring
  have hDrift : d * alpha * L <= 2 * ell ^ 2 / x := by
    calc
      _ <= x * (ell / (m : Real)) * (2 * ell) :=
        mul_le_mul hDA hLCap hL hRight
      _ = _ := by
        rw [<- hxSq]
        field_simp [ne_of_gt hx]
        <;> ring
  have hMoment : L / d <= 4 * ell / y := by
    have hCross : L * y <= 4 * ell * d := by
      have hFirst := mul_le_mul_of_nonneg_right hLCap hy.le
      have hSecond := mul_le_mul_of_nonneg_left hD.2.2 (by positivity : 0 <= 2 * ell)
      nlinarith only [hFirst, hSecond]
    calc
      L / d = (L * y) / (y * d) := by
        field_simp [ne_of_gt hy, ne_of_gt hd]
      _ <= (4 * ell * d) / (y * d) :=
        div_le_div_of_nonneg_right hCross (mul_nonneg hy.le hd.le)
      _ = 4 * ell / y := by field_simp [ne_of_gt hy, ne_of_gt hd]
  exact And.intro hSmall (And.intro hDrift hMoment)

end PrimeFactorOscillations.LPF
