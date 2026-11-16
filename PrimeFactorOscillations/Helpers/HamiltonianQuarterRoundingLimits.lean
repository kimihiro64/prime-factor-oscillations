/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianQuarterRoundingBudgets

/-! # All rounding errors vanish for one exact quarter-power degree sequence -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.LPF

theorem hamiltonian_quarter_rounding_budgets_terminal
    (c C eps : Real) (hc : 0 < c) (hC : 0 < C) (hEps : 0 < eps) :
    exists M0 : Nat, 256 <= M0 /\
      forall m : Nat, M0 <= m -> forall alpha : Real, 0 <= alpha ->
        (m : Real) * alpha <= Real.log (2 * (m : Real)) ->
        ((hamiltonianQuarterPrimeDegree m : Real) * alpha) *
            Real.log (4 * (m : Real)) ^ 2 <= c /\
          16 * Real.sqrt (Real.log (4 * (m : Real)) /
              (hamiltonianQuarterPrimeDegree m : Real)) +
            C * ((hamiltonianQuarterPrimeDegree m : Real) * alpha *
              Real.log (4 * (m : Real))) <= eps := by
  choose A hA hSmall using hamiltonian_log_power_dominated_uniform
    (4 / c) (div_pos (by norm_num) hc) 3 (1 / 2) (by norm_num)
  choose B hB hDrift using hamiltonian_log_power_dominated_uniform
    (4 * C / eps) (div_pos (by positivity) hEps) 2 (1 / 2) (by norm_num)
  choose E hE hMoment using hamiltonian_log_power_dominated_uniform
    (4096 / eps ^ 2) (div_pos (by norm_num) (sq_pos_of_pos hEps))
      1 (1 / 4) (by norm_num)
  let M0 := max A (max B E)
  refine Exists.intro M0 (And.intro (hA.trans (le_max_left _ _)) ?_)
  intro m hm alpha ha hMass
  have hmA : A <= m := (le_max_left _ _).trans hm
  have hmB : B <= m := by dsimp [M0] at hm; omega
  have hmE : E <= m := by dsimp [M0] at hm; omega
  have hm256 : 256 <= m := hA.trans hmA
  have hmPos : 0 < (m : Real) := by
    exact_mod_cast (show 0 < m by omega)
  let ell := Real.log (2 * (m : Real))
  let x := (m : Real) ^ (1 / 2 : Real)
  let y := (m : Real) ^ (1 / 4 : Real)
  let d := (hamiltonianQuarterPrimeDegree m : Real)
  let L := Real.log (4 * (m : Real))
  have hx : 0 < x := Real.rpow_pos_of_pos hmPos _
  have hy : 0 < y := Real.rpow_pos_of_pos hmPos _
  have hBounds := hamiltonian_quarter_rounding_envelopes m hm256 alpha ha hMass
  have hSmallCross : 4 * ell ^ 3 <= c * x := by
    calc
      _ = c * ((4 / c) * ell ^ 3) := by field_simp [ne_of_gt hc]
      _ <= c * x := mul_le_mul_of_nonneg_left (hSmall m hmA) hc.le
  have hSmallRatio : 4 * ell ^ 3 / x <= c := by
    calc
      _ <= (c * x) / x := div_le_div_of_nonneg_right hSmallCross hx.le
      _ = c := by field_simp [ne_of_gt hx]
  have hDriftCross : 2 * C * ell ^ 2 <= (eps / 2) * x := by
    calc
      _ = (eps / 2) * ((4 * C / eps) * ell ^ 2) := by
        field_simp [ne_of_gt hEps]
        <;> ring
      _ <= (eps / 2) * x :=
        mul_le_mul_of_nonneg_left (hDrift m hmB) (by positivity)
  have hDriftBound : C * (d * alpha * L) <= eps / 2 := by
    calc
      _ <= C * (2 * ell ^ 2 / x) :=
        mul_le_mul_of_nonneg_left hBounds.2.1 hC.le
      _ = (2 * C * ell ^ 2) / x := by ring
      _ <= ((eps / 2) * x) / x :=
        div_le_div_of_nonneg_right hDriftCross hx.le
      _ = eps / 2 := by field_simp [ne_of_gt hx]
  have hMomentCross : 4 * ell <= (eps ^ 2 / 1024) * y := by
    calc
      _ = (eps ^ 2 / 1024) * ((4096 / eps ^ 2) * ell ^ 1) := by
        field_simp [ne_of_gt hEps]
        <;> ring
      _ <= (eps ^ 2 / 1024) * y :=
        mul_le_mul_of_nonneg_left (hMoment m hmE) (by positivity)
  have hMomentBound : L / d <= eps ^ 2 / 1024 := by
    calc
      _ <= 4 * ell / y := hBounds.2.2
      _ <= ((eps ^ 2 / 1024) * y) / y :=
        div_le_div_of_nonneg_right hMomentCross hy.le
      _ = eps ^ 2 / 1024 := by field_simp [ne_of_gt hy]
  have hdPos : 0 < d := by
    have hOne : (1 : Real) <= d := by
      change (1 : Real) <= (hamiltonianQuarterPrimeDegree m : Real)
      exact_mod_cast (hamiltonian_quarter_prime_degree_bounds m hm256).1
    linarith only [hOne]
  have hL : 0 <= L := Real.log_nonneg (by
    have hMR : (256 : Real) <= (m : Real) := by exact_mod_cast hm256
    linarith only [hMR])
  have hRoot := Real.sq_sqrt (div_nonneg hL hdPos.le)
  have hRoot0 := Real.sqrt_nonneg (L / d)
  have hRootBound : 16 * Real.sqrt (L / d) <= eps / 2 := by
    nlinarith only [hMomentBound, hRoot, hRoot0, hEps]
  exact And.intro (hBounds.1.trans hSmallRatio)
    (by change 16 * Real.sqrt (L / d) + C * (d * alpha * L) <= eps
        linarith only [hRootBound, hDriftBound])

end PrimeFactorOscillations.LPF
