/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.Robin1984.Equivalence.WeightedKernelBounds
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.WeightedPrimePowerTail

/-!
# The signed RH upper envelope for the actual Nicolas logarithm

Retains the prime-square subtraction in F <= J_1 - P_1 + 4/x, and combines
Robin's n=1 and n=2 estimates with the exact root substitution. This is the
explicit envelope in the written argument, valid for x >= 4.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open MeasureTheory Set Robin1984

noncomputable section

theorem nicolasJ_eq_weighted_error_one {x : Real} (hx : 3 <= x) :
    nicolasJ x = robinPsiWeightedErrorIntegral 1 x := by
  unfold nicolasJ nicolasPsiError robinPsiWeightedErrorIntegral
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  change x < t at ht
  rw [robinRealWeight_one_eq_nicolasTailKernel (by linarith : 1 < t)]

theorem nicolasPrimePowerTail_eq_weighted_one {x : Real} (hx : 3 <= x) :
    nicolasPrimePowerTail x = robinPrimePowerWeightedTail 1 x := by
  unfold nicolasPrimePowerTail robinPrimePowerWeightedTail
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  change x < t at ht
  rw [robinRealWeight_one_eq_nicolasTailKernel (by linarith : 1 < t)]

theorem nicolasK_le_weighted_square_correction {x : Real} (hx : 3 <= x) :
    nicolasK x <=
      robinPsiWeightedErrorIntegral 1 x -
        (robinZeroKernel 1 (1 / 2 : Complex) x).re -
        (1 / 2 : Real) * robinPsiWeightedErrorIntegral 2 (x ^ (1 / 2 : Real)) := by
  have hxOne : 1 < x := by linarith
  have hKInt := nicolasThetaTail_integrableOn_Ioi_two.mono_set
    (Ioi_subset_Ioi (le_trans (by norm_num) hx))
  have hJInt := nicolasPsiTail_integrableOn_Ioi_three.mono_set
    (Ioi_subset_Ioi hx)
  have hIdentity := nicolasJ_eq_K_add_primePowerTail hKInt hJInt
  rw [nicolasJ_eq_weighted_error_one hx,
    nicolasPrimePowerTail_eq_weighted_one hx] at hIdentity
  have hLower := three_root_integrals_le_robinPrimePowerWeightedTail
    (n := 1) (by norm_num) hxOne
  have hNonneg (k : Nat) : 0 <=
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        Chebyshev.psi (t ^ (Inv.inv (k : Real))) * robinRealWeight 1 t) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Chebyshev.psi_nonneg _)
      (robinRealWeight_nonneg (lt_trans hxOne ht))
  have hRoot := integral_psi_root_mul_robinRealWeight_eq
    (n := 1) (k := 2) (by norm_num) (by norm_num) hxOne
  simp only [Nat.cast_ofNat, Nat.mul_one] at hRoot
  calc
    nicolasK x = robinPsiWeightedErrorIntegral 1 x -
        robinPrimePowerWeightedTail 1 x := by linarith
    _ <= robinPsiWeightedErrorIntegral 1 x -
        integral (volume.restrict (Ioi x)) (fun t : Real =>
          Chebyshev.psi (t ^ (Inv.inv (2 : Real))) * robinRealWeight 1 t) := by
      have hThree := hNonneg 3
      have hSeven := hNonneg 7
      norm_num only [Nat.cast_ofNat] at hThree hSeven
      linarith
    _ = _ := by
      rw [hRoot]
      norm_num <;> ring

theorem nicolasLog_le_weighted_square_correction {x : Real} (hx : 3 <= x) :
    nicolasLogMertensOscillation x <=
      robinPsiWeightedErrorIntegral 1 x -
        (robinZeroKernel 1 (1 / 2 : Complex) x).re -
        (1 / 2 : Real) * robinPsiWeightedErrorIntegral 2 (x ^ (1 / 2 : Real)) +
        4 / x := by
  have hLog := nicolasLogMertensOscillation_le_K_add_four_div hx
  have hK := nicolasK_le_weighted_square_correction hx
  linarith

theorem robinHalfKernel_lower_bound {x : Real} (hx : 1 < x) :
    2 * x ^ (-(1 / 2 : Real)) / Real.log x -
      2 * x ^ (-(1 / 2 : Real)) / (Real.log x) ^ 2 <=
        (robinZeroKernel 1 (1 / 2 : Complex) x).re := by
  have hIdentity := robinZeroKernel_ofReal_eq_main_add_signed_tail
    1 (r := (1 / 2 : Real)) (by norm_num) hx
  have hTail := robinCpowLogTail_ofReal_re_le
    (a := -(1 / 2 : Real)) (by norm_num) 2 hx
  norm_num at hIdentity hTail
  simp only [div_eq_mul_inv] at *
  nlinarith

def nicolasRHUpperEnvelope (x : Real) : Real :=
  let L := Real.log x
  let b := Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)
  x ^ (-(1 / 2 : Real)) *
      ((b - 2) / L + (b + 2) / L ^ 2 + 4 * b / L ^ 3) +
    b * x ^ (-(3 / 4 : Real)) *
      (2 / L + 2 / L ^ 2 + 16 / (3 * L ^ 3)) +
    Real.log (2 * Real.pi) / (x * L) + 4 / x

theorem nicolasRH_upper_envelope_of_weighted_square_bound
    (hRH : RiemannHypothesis) {x y : Real} (hx : 4 <= x)
    (hy : y <= robinPsiWeightedErrorIntegral 1 x -
      (robinZeroKernel 1 (1 / 2 : Complex) x).re -
      (1 / 2 : Real) * robinPsiWeightedErrorIntegral 2 (x ^ (1 / 2 : Real)) +
      4 / x) :
    y <= nicolasRHUpperEnvelope x := by
  have hxThree : 3 <= x := by linarith
  have hxTwo : 2 <= x := by linarith
  have hxOne : 1 < x := by linarith
  have hxPos : 0 < x := by linarith
  have hLog : Not (Real.log x = 0) := (Real.log_pos hxOne).ne'
  let L : Real := Real.log x
  let b : Real := Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)
  have hRootTwo : 2 <= x ^ (1 / 2 : Real) := by
    have hSqrt := Real.sqrt_le_sqrt hx
    have hFour : Real.sqrt (4 : Real) = 2 := by
      convert Real.sqrt_sq (by norm_num : 0 <= (2 : Real)) using 1 <;> norm_num
    rw [hFour] at hSqrt
    simpa only [Real.sqrt_eq_rpow] using hSqrt
  have hOne := robinPsiWeightedErrorIntegral_bounds_all hRH
    (n := 1) (by norm_num) hxTwo
  have hTwo := robinPsiWeightedErrorIntegral_bounds_all hRH
    (n := 2) (by norm_num) hRootTwo
  have hStart := hy
  have hKernel := robinHalfKernel_lower_bound hxOne
  have hPowThree :
      (x ^ (1 / 2 : Real)) ^ (-(3 / 2 : Real)) = x ^ (-(3 / 4 : Real)) := by
    rw [<- Real.rpow_mul hxPos.le]
    norm_num
  have hPowTwo :
      (x ^ (1 / 2 : Real)) ^ (-(2 : Real)) = x ^ (-(1 : Real)) := by
    rw [<- Real.rpow_mul hxPos.le]
    norm_num
  have hLogRoot : Real.log (x ^ (1 / 2 : Real)) = Real.log x / 2 := by
    rw [Real.log_rpow hxPos]
    ring
  have hScalarOne : robinPsiWeightedErrorScalar 1 x =
      b * x ^ (-(1 / 2 : Real)) *
        (1 / L + 1 / L ^ 2 + 4 / L ^ 3) := by
    dsimp [robinPsiWeightedErrorScalar, b, L]
    norm_num
    field_simp [hLog] <;> ring
  have hScalarTwo :
      (1 / 2 : Real) * robinPsiWeightedErrorScalar 2 (x ^ (1 / 2 : Real)) =
      b * x ^ (-(3 / 4 : Real)) *
        (2 / L + 2 / L ^ 2 + 16 / (3 * L ^ 3)) := by
    dsimp [robinPsiWeightedErrorScalar, b, L]
    norm_num
    rw [hPowThree, hLogRoot]
    field_simp [hLog] <;> ring
  have hCorrection :
      (1 / 2 : Real) *
        (Real.log (2 * Real.pi) * (x ^ (1 / 2 : Real)) ^ (-(2 : Real)) *
          Inv.inv (Real.log (x ^ (1 / 2 : Real)))) =
        Real.log (2 * Real.pi) / (x * L) := by
    rw [hPowTwo, Real.rpow_neg_one, hLogRoot]
    dsimp [L]
    field_simp [hxPos.ne', hLog] <;> ring
  have hRaw : y <=
      robinPsiWeightedErrorScalar 1 x -
        (2 * x ^ (-(1 / 2 : Real)) / Real.log x -
          2 * x ^ (-(1 / 2 : Real)) / (Real.log x) ^ 2) +
        (1 / 2 : Real) * robinPsiWeightedErrorScalar 2 (x ^ (1 / 2 : Real)) +
        (1 / 2 : Real) *
          (Real.log (2 * Real.pi) * (x ^ (1 / 2 : Real)) ^ (-(2 : Real)) *
            Inv.inv (Real.log (x ^ (1 / 2 : Real)))) + 4 / x := by
    norm_num only [Nat.cast_ofNat] at hTwo
    linarith [hOne.2, hTwo.1]
  rw [hScalarOne, hScalarTwo, hCorrection] at hRaw
  calc
    y <= _ := hRaw
    _ = nicolasRHUpperEnvelope x := by
      dsimp [nicolasRHUpperEnvelope, b, L]
      ring

theorem nicolasLog_le_RH_upper_envelope
    (hRH : RiemannHypothesis) {x : Real} (hx : 4 <= x) :
    nicolasLogMertensOscillation x <= nicolasRHUpperEnvelope x := by
  exact nicolasRH_upper_envelope_of_weighted_square_bound hRH hx
    (nicolasLog_le_weighted_square_correction (by linarith))

theorem nicolasK_add_four_div_le_RH_upper_envelope
    (hRH : RiemannHypothesis) {x : Real} (hx : 4 <= x) :
    nicolasK x + 4 / x <= nicolasRHUpperEnvelope x := by
  apply nicolasRH_upper_envelope_of_weighted_square_bound hRH hx
  have hK := nicolasK_le_weighted_square_correction (x := x) (by linarith)
  linarith

end

end PrimeFactorOscillations
