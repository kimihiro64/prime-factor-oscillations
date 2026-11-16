/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianAperiodicLogDet

/-! # Dimension-free lower normalization of the aperiodic signal

The full signed linear trace is compensated before the derivative
is bounded. Both stochastic row and column energy budgets control
the remaining sandwich on the complete interval from zero to one.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem hamiltonian_aperiodic_path_inverse
    (B : Matrix Iota Iota Real) (delta t : Real)
    (hDelta : 0 < delta) (hNorm : norm B <= 1 - delta)
    (ht0 : 0 <= t) (ht1 : t <= 1) :
    IsUnit ((1 : Matrix Iota Iota Real) - HSMul.hSMul t B) /\
      (((1 : Matrix Iota Iota Real) - HSMul.hSMul t B) *
        Ring.inverse ((1 : Matrix Iota Iota Real) - HSMul.hSMul t B) = 1) /\
      delta * norm (Ring.inverse
        ((1 : Matrix Iota Iota Real) - HSMul.hSMul t B)) <= 1 := by
  have hScaled : norm (HSMul.hSMul t B) <= 1 - delta := by
    have hSmul : HSMul.hSMul t B = SMul.smul t B := by ext i j; rfl
    rw [hSmul, hamiltonian_matrix_real_smul_norm, Real.norm_of_nonneg ht0]
    calc
      _ <= 1 * norm B := mul_le_mul_of_nonneg_right ht1 (norm_nonneg B)
      _ <= 1 - delta := by simpa only [one_mul] using hNorm
  have hRho : 1 - delta < 1 := by linarith only [hDelta]
  have hUnit : IsUnit ((1 : Matrix Iota Iota Real) - HSMul.hSMul t B) :=
    isUnit_one_sub_of_norm_lt_one (hScaled.trans_lt hRho)
  have hCert := l2_neumann_certificate (HSMul.hSMul t B) (1 - delta) hScaled hRho
  have hGap : 1 - (1 - delta) = delta := by ring
  rw [hGap] at hCert
  exact And.intro hUnit
    (And.intro (Ring.mul_inverse_cancel _ hUnit) hCert)

theorem stochastic_aperiodic_compensated_log_bound
    (T : Matrix Iota Iota Real) (q a delta : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (hDelta : 0 < delta)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j)
    (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= 1 - delta) :
    0 < Matrix.det ((1 : Matrix Iota Iota Real) - centeredKernel T q) /\
      abs (Real.log (Matrix.det ((1 : Matrix Iota Iota Real) - centeredKernel T q)) +
        Matrix.trace (centeredKernel T q)) <= (a - 1) / delta := by
  let B := centeredKernel T q
  let d : Real -> Real := fun t =>
    Matrix.det ((1 : Matrix Iota Iota Real) - HSMul.hSMul t B)
  let R : Real -> Matrix Iota Iota Real := fun t =>
    Ring.inverse ((1 : Matrix Iota Iota Real) - HSMul.hSMul t B)
  let g : Real -> Real := fun t => delta * (Real.log (d t) + t * Matrix.trace B)
  have hPath (t : Real) (ht : Membership.mem (Set.Icc (0 : Real) 1) t) :
      IsUnit ((1 : Matrix Iota Iota Real) - HSMul.hSMul t B) /\
        (((1 : Matrix Iota Iota Real) - HSMul.hSMul t B) * R t = 1) /\
        delta * norm (R t) <= 1 :=
    hamiltonian_aperiodic_path_inverse B delta t hDelta hNorm ht.1 ht.2
  have hTrace (t : Real) (ht : Membership.mem (Set.Icc (0 : Real) 1) t) :
      Matrix.trace (R t * B) =
        Matrix.trace B + t * Matrix.trace (B * R t * B) := by
    have hInv := (hPath t ht).2.1
    have hExpand : R t - HSMul.hSMul t (B * R t) = 1 := by
      simpa only [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul] using hInv
    have hMultiply := congrArg (fun X : Matrix Iota Iota Real => X * B) hExpand
    simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul] at hMultiply
    have hMatrix : R t * B = B + HSMul.hSMul t (B * R t * B) := by
      exact eq_add_of_sub_eq hMultiply
    rw [hMatrix, Matrix.trace_add, Matrix.trace_smul]
    rfl
  have hD (t : Real) (ht : Membership.mem (Set.Icc (0 : Real) 1) t) :
      HasDerivAt g (delta * (-t * Matrix.trace (B * R t * B))) t := by
    have hLog := hamiltonian_affine_log_determinant_hasDerivAt B t (hPath t ht).1
    have hdf := (hLog.add ((hasDerivAt_id t).mul_const (Matrix.trace B))).const_mul delta
    have hdf' : HasDerivAt g
        (delta * (-Matrix.trace (R t * B) + Matrix.trace B)) t := by
      simpa only [g, d, R, one_mul] using! hdf
    convert hdf' using 1
    rw [hTrace t ht]
    ring
  have hBound (t : Real) (ht : Membership.mem (Set.Icc (0 : Real) 1) t) :
      norm (delta * (-t * Matrix.trace (B * R t * B))) <= a - 1 := by
    have hTr := stochastic_centered_sandwich_trace_bound T (R t) q a delta
      hq hDelta hRow hCol hNonneg hUpper (hPath t ht).2.2
    change delta * abs (Matrix.trace (B * R t * B)) <= a - 1 at hTr
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hDelta, abs_mul, abs_neg, abs_of_nonneg ht.1]
    calc
      _ = t * (delta * abs (Matrix.trace (B * R t * B))) := by ring
      _ <= 1 * (delta * abs (Matrix.trace (B * R t * B))) :=
        mul_le_mul_of_nonneg_right ht.2 (mul_nonneg hDelta.le (abs_nonneg _))
      _ <= a - 1 := by simpa only [one_mul] using hTr
  have hZero : Membership.mem (Set.Icc (0 : Real) 1) 0 := by constructor <;> norm_num
  have hOne : Membership.mem (Set.Icc (0 : Real) 1) 1 := by constructor <;> norm_num
  have hMVT := (convex_Icc (0 : Real) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hD t ht).hasDerivWithinAt) hBound hZero hOne
  have hG0 : g 0 = 0 := by simp [g, d]
  have hG1 : g 1 = delta * (Real.log (Matrix.det (1 - B)) + Matrix.trace B) := by
    simp only [g, d, one_smul, one_mul]
  rw [hG0, hG1, sub_zero, Real.norm_eq_abs] at hMVT
  norm_num only [sub_zero, norm_one, mul_one] at hMVT
  rw [abs_mul, abs_of_pos hDelta] at hMVT
  have hAbs : abs (Real.log (Matrix.det (1 - B)) + Matrix.trace B) <= (a - 1) / delta := by
    have h := mul_le_mul_of_nonneg_left hMVT (le_of_lt (one_div_pos.mpr hDelta))
    have hCancel : (1 / delta) *
        (delta * abs (Real.log (Matrix.det (1 - B)) + Matrix.trace B)) =
        abs (Real.log (Matrix.det (1 - B)) + Matrix.trace B) := by field_simp
    rw [hCancel] at h
    calc
      _ <= (1 / delta) * (a - 1) := h
      _ = _ := by ring
  have hDetNe (t : Real) (ht : Membership.mem (Set.Icc (0 : Real) 1) t) :
      Not (d t = 0) :=
    hamiltonian_det_nonzero_of_right_inverse _ (R t) (hPath t ht).2.1
  have hContinuous : ContinuousOn d (Set.Icc (0 : Real) 1) := by
    let p := principalMinorGeneratingPolynomial B
    have hFunction : d = (fun t : Real => Polynomial.eval (-t) p) := by
      funext t
      dsimp only [d, p]
      rw [principalMinorGeneratingPolynomial_eval]
      simp only [neg_smul, sub_eq_add_neg]
    rw [hFunction]
    exact (p.continuous.comp continuous_neg).continuousOn
  have hD0 : d 0 = 1 := by simp [d]
  have hPositive : 0 < d 1 := by
    by_contra h
    have hLast : d 1 <= 0 := le_of_not_gt h
    have hBetween : Membership.mem (Set.Icc (d 1) (d 0)) 0 :=
      And.intro hLast (by rw [hD0]; norm_num)
    choose t ht hdt using intermediate_value_Icc' (by norm_num : (0 : Real) <= 1)
      hContinuous hBetween
    exact hDetNe t ht hdt
  refine And.intro ?_ hAbs
  simpa only [d, one_smul] using hPositive

theorem stochastic_aperiodic_determinant_lower_bound
    (T : Matrix Iota Iota Real) (q a delta : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (hDelta : 0 < delta)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j)
    (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= 1 - delta) :
    0 < Matrix.det ((1 : Matrix Iota Iota Real) - centeredKernel T q) /\
      Real.exp (-((a - 1) + (a - 1) / delta)) <=
        Matrix.det ((1 : Matrix Iota Iota Real) - centeredKernel T q) := by
  let B := centeredKernel T q
  have hData := stochastic_aperiodic_compensated_log_bound T q a delta hq hDelta
    hRow hCol hNonneg hUpper hNorm
  have hAverage : Matrix.trace (averagingKernel (Iota := Iota) q) = 1 := by
    change Finset.univ.sum (fun _ : Iota => q) = 1
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hq
  have hTraceT : Matrix.trace T <= a := by
    calc
      _ <= Finset.univ.sum (fun _ : Iota => a * q) :=
        Finset.sum_le_sum (fun i _ => hUpper i i)
      _ = a := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        calc
          _ = a * ((Fintype.card Iota : Real) * q) := by ring
          _ = _ := by rw [hq, mul_one]
  have hTrace : Matrix.trace B <= a - 1 := by
    dsimp only [B, centeredKernel]
    rw [Matrix.trace_sub, hAverage]
    linarith only [hTraceT]
  have hLog : -((a - 1) + (a - 1) / delta) <=
      Real.log (Matrix.det ((1 : Matrix Iota Iota Real) - B)) := by
    have hLower := (abs_le.mp hData.2).1
    change -((a - 1) / delta) <= Real.log (Matrix.det (1 - B)) + Matrix.trace B at hLower
    linarith only [hLower, hTrace]
  have hExp := Real.exp_le_exp.mpr hLog
  rw [Real.exp_log hData.1] at hExp
  exact And.intro hData.1 hExp

end PrimeFactorOscillations
