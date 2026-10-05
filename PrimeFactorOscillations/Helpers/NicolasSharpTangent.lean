/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasLogDegreeLocalization
import PrimeFactorOscillations.Helpers.NicolasLogSpectral

/-!
# The sharp RH logarithmic tangent correction

The signed log-log tangent error is nonnegative. The classical RH theta bound
makes its size at most a constant times log cubed over the endpoint. Keeping
that correction and the finite prime tail gives the same scale for the
difference between the Nicolas logarithm and its weighted theta integral.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Filter Robin1984

/-- The actual signed logarithmic tangent error has the classical RH scale. -/
theorem exists_eventually_nicolasHeightTangentError_log_bound
    (hRH : RiemannHypothesis) :
    Exists fun C : Real => And (0 < C)
      (Filter.Eventually (fun x : Real =>
        0 <= nicolasHeightTangentError x /\
        nicolasHeightTangentError x <= C * (Real.log x) ^ (3 : Nat) / x) atTop) := by
  choose K hK hTheta using exists_nicolasThetaError_le_sqrt_log_sq hRH
  refine Exists.intro (6 * K ^ (2 : Nat)) (And.intro (by positivity) ?_)
  filter_upwards [eventually_nicolasHeight_domain hRH] with x hx
  have hx4 : 4 <= x := (le_max_left _ _).trans hx.1
  have hx1 : 1 < x := by linarith
  have hxPos : 0 < x := by linarith
  have hxExp : 2 * Real.exp 1 <= x := (le_max_right _ _).trans hx.1
  have hLogHalf : 1 <= Real.log (x / 2) := by
    have h := Real.log_le_log (Real.exp_pos 1) (show Real.exp 1 <= x / 2 by linarith)
    simpa only [Real.log_exp] using h
  have hLog : 1 <= Real.log x :=
    hLogHalf.trans (Real.log_le_log (by linarith : 0 < x / 2) (by linarith : x / 2 <= x))
  have hLogPos : 0 < Real.log x := Real.log_pos hx1
  have hTheta1 : 1 < Chebyshev.theta x :=
    one_lt_chebyshevTheta_of_three_le (by linarith)
  have hNonneg : 0 <= nicolasHeightTangentError x := by
    by_cases hOrder : Chebyshev.theta x <= x
    . exact (Real.logLog_remainder_bounds_of_le hTheta1 hOrder hx.2.1 hx.2.2).1
    . have hE : 0 <= Chebyshev.theta x - x := by linarith
      have h := (Real.logLog_remainder_bounds x (Chebyshev.theta x - x) hx1 hE).1
      rw [show x + (Chebyshev.theta x - x) = Chebyshev.theta x by ring] at h
      exact h
  have hTaylor := Real.logLog_remainder_abs_le hx1 hTheta1 hLog hx.2.2 hx.2.1
  have hError := hTheta x hx4 hLogHalf
  have hSquare : (Chebyshev.theta x - x) ^ (2 : Nat) <=
      (K * Real.sqrt x * (Real.log x) ^ (2 : Nat)) ^ (2 : Nat) := by
    have h := mul_self_le_mul_self (abs_nonneg (Chebyshev.theta x - x)) hError
    simpa only [<- pow_two, sq_abs] using h
  have hScale := (div_le_div_iff_of_pos_right
    (show 0 < x ^ (2 : Nat) * Real.log x by positivity)).2
      (mul_le_mul_of_nonneg_left hSquare (by norm_num : (0 : Real) <= 6))
  have hNormalize :
      6 * (K * Real.sqrt x * (Real.log x) ^ (2 : Nat)) ^ (2 : Nat) /
          (x ^ (2 : Nat) * Real.log x) =
        6 * K ^ (2 : Nat) * (Real.log x) ^ (3 : Nat) / x := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hxPos.le]
    field_simp [hxPos.ne', hLogPos.ne']
  rw [hNormalize] at hScale
  exact And.intro hNonneg ((le_abs_self _).trans (hTaylor.trans hScale))

/-- The finite Nicolas logarithm differs from the theta integral only at
the logarithm-cubed over endpoint scale under RH. -/
theorem exists_eventually_nicolasLog_sub_K_le_log_cube
    (hRH : RiemannHypothesis) :
    Exists fun C : Real => And (0 < C)
      (Filter.Eventually (fun x : Real =>
        abs (nicolasLogMertensOscillation x - nicolasK x) <=
          C * (Real.log x) ^ (3 : Nat) / x) atTop) := by
  choose C hC hHeight using exists_eventually_nicolasHeightTangentError_log_bound hRH
  refine Exists.intro (C + 4) (And.intro (by linarith) ?_)
  filter_upwards [hHeight, eventually_nicolasHeight_domain hRH] with x hD hx
  have hx4 : 4 <= x := (le_max_left _ _).trans hx.1
  have hxPos : 0 < x := by linarith
  have hxExp : 2 * Real.exp 1 <= x := (le_max_right _ _).trans hx.1
  have hLog : 1 <= Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 <= x by linarith [Real.exp_pos 1])
    simpa only [Real.log_exp] using h
  let A := Finset.sum (Finset.Ioc 0 (Nat.floor x)) (fun n => Mertens.M_eq_summand n) -
    (Mertens.M - Real.eulerMascheroniConstant)
  have hA : abs A <= 4 / x := nicolasMertensSummandTail_le (by linarith)
  have hSplit : nicolasLogMertensOscillation x - nicolasK x =
      A - nicolasHeightTangentError x := by
    rw [nicolasLogMertensOscillation_eq_components (by linarith)]
    dsimp [A, nicolasHeightTangentError, nicolasThetaError]
    ring
  have hTriangle : abs (A - nicolasHeightTangentError x) <=
      abs A + nicolasHeightTangentError x := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hD.1] using
      norm_sub_le A (nicolasHeightTangentError x)
  have hCube : 1 <= (Real.log x) ^ (3 : Nat) := by
    have hSquare : 1 <= (Real.log x) ^ (2 : Nat) := by nlinarith
    have h := mul_le_mul hSquare hLog (by norm_num : (0 : Real) <= 1)
      (sq_nonneg (Real.log x))
    nlinarith only [h]
  have hFour : 4 / x <= 4 * (Real.log x) ^ (3 : Nat) / x :=
    div_le_div_of_nonneg_right (by nlinarith only [hCube]) hxPos.le
  rw [hSplit]
  have hDenom : (C + 4) * (Real.log x) ^ (3 : Nat) / x =
      C * (Real.log x) ^ (3 : Nat) / x + 4 * (Real.log x) ^ (3 : Nat) / x := by ring
  rw [hDenom]
  linarith only [hTriangle, hA, hFour, hD.2]

end PrimeFactorOscillations
