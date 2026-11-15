/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPermanentReindex

/-! # Uniform positive normalized permanent values

The first-order envelope is used only to justify positive logarithms.
The full signed second-order expansion remains the minor consumer.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianNormalizedPermanent {J : Type*} [Fintype J] [DecidableEq J]
    (T : Matrix J J Real) (q : Real) : Real :=
  (((Fintype.card J : Real) ^ Fintype.card J / ((Fintype.card J).factorial : Real)) *
    weightedPermutationSum T) / realGramDeterminantFactor (centeredKernel T q) 1

def hamiltonianPermanentPositiveData {J : Type*} [Fintype J] [DecidableEq J]
    (T : Matrix J J Real) (q : Real) : Prop :=
  1 / 2 <= hamiltonianNormalizedPermanent T q /\
  1 <= realGramDeterminantFactor (centeredKernel T q) 1 /\
  0 < weightedPermutationSum T

theorem hamiltonian_normalized_permanent_reindex
    {Iota Jota : Type*} [Fintype Iota] [DecidableEq Iota]
    [Fintype Jota] [DecidableEq Jota]
    (T : Matrix Iota Iota Real) (e : Equiv Jota Iota) (q : Real) :
    hamiltonianNormalizedPermanent (T.submatrix e e) q = hamiltonianNormalizedPermanent T q := by
  have hCentered : centeredKernel (T.submatrix e e) q = (centeredKernel T q).submatrix e e := rfl
  have hPer : weightedPermutationSum (T.submatrix e e) = weightedPermutationSum T :=
    finitePermutationSum_reindex e T
  have hCard : Fintype.card Jota = Fintype.card Iota := Fintype.card_congr e
  unfold hamiltonianNormalizedPermanent
  rw [hCard, hPer, hCentered, hamiltonian_real_gram_factor_reindex]

universe u

theorem stochastic_permanent_positive_polylog_uniform (delta K : Real)
    (hDelta : 0 < delta) (hDelta1 : delta <= 1) (hK : 0 <= K) :
    exists N0 : Nat, 256 <= N0 /\
      forall (J : Type u) [Fintype J] [DecidableEq J], N0 <= Fintype.card J ->
        forall (T : Matrix J J Real) (q a : Real),
          (Fintype.card J : Real) * q = 1 -> 1 <= a ->
          a <= (Real.log (Fintype.card J : Real)) ^ K ->
          (forall i, Finset.univ.sum (fun j => T i j) = 1) ->
          (forall j, Finset.univ.sum (fun i => T i j) = 1) ->
          (forall i j, 0 <= T i j) -> (forall i j, T i j <= a * q) ->
          norm (centeredKernel T q) <= 1 - delta ->
          hamiltonianPermanentPositiveData T q := by
  have hKPlus : 0 < K + 1 := by linarith only [hK]
  let range := stochastic_permanent_first_order_polylog_uniform delta (K + 1) hDelta hDelta1 hKPlus
  let N0 := max 256 (max range.choose (Nat.ceil (Real.exp 1)))
  refine Exists.intro N0 (And.intro (le_max_left _ _) ?_)
  intro J instF instD hn T q a hq ha hA hRow hCol hNonneg hUpper hNorm
  let n := Fintype.card J
  let e : Equiv (Fin n) J := (Fintype.equivFin J).symm
  let M := T.submatrix e e
  let D := realGramDeterminantFactor (centeredKernel T q) 1
  have hnRange : range.choose <= n :=
    le_trans (le_trans (le_max_left range.choose (Nat.ceil (Real.exp 1))) (le_max_right 256 _)) hn
  have hn256 : 256 <= n := le_trans (le_max_left 256 _) hn
  have hnReal : (256 : Real) <= (n : Real) := by exact_mod_cast hn256
  have hN0 : 0 < (n : Real) := by linarith only [hnReal]
  have hCeil : Nat.ceil (Real.exp 1) <= n :=
    le_trans (le_trans (le_max_right range.choose (Nat.ceil (Real.exp 1))) (le_max_right 256 _)) hn
  have hExp : Real.exp 1 <= (n : Real) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hCeil)
  have hLog1 : 1 <= Real.log (n : Real) := by
    have h := Real.log_le_log (Real.exp_pos 1) hExp
    simpa only [Real.log_exp] using h
  have hLog0 : 0 <= Real.log (n : Real) := le_trans (by norm_num) hLog1
  have hLogPos : 0 < Real.log (n : Real) := lt_of_lt_of_le (by norm_num) hLog1
  have hCap : a <= (Real.log (n : Real)) ^ (K + 1) := by
    have hGrow := mul_le_mul_of_nonneg_left hLog1 (Real.rpow_nonneg hLog0 K)
    calc
      _ <= (Real.log (n : Real)) ^ K := hA
      _ <= (Real.log (n : Real)) ^ K * Real.log (n : Real) := by
        simpa only [mul_one] using hGrow
      _ = _ := by rw [Real.rpow_add hLogPos, Real.rpow_one]
  have hCentered : centeredKernel M q = (centeredKernel T q).submatrix e e := rfl
  have hMNorm : norm (centeredKernel M q) <= 1 - delta := by
    rw [hCentered, hamiltonian_l2_reindex_norm]
    exact hNorm
  have hMRow (i : Fin n) : Finset.univ.sum (fun j => M i j) = 1 := by
    calc
      _ = Finset.univ.sum (fun j : J => T (e i) j) := Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = 1 := hRow (e i)
  have hMCol (j : Fin n) : Finset.univ.sum (fun i => M i j) = 1 := by
    calc
      _ = Finset.univ.sum (fun i : J => T i (e j)) := Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = 1 := hCol (e j)
  have hEstimate := range.choose_spec.2 n hnRange M q a hq ha hCap hMRow hMCol
    (fun i j => hNonneg (e i) (e j)) (fun i j => hUpper (e i) (e j)) hMNorm
  have hValue : (((n : Real) ^ n / (n.factorial : Real)) * weightedPermutationSum M) /
      realGramDeterminantFactor (centeredKernel M q) 1 = hamiltonianNormalizedPermanent T q := by
    simpa only [hamiltonianNormalizedPermanent, Fintype.card_fin] using
      hamiltonian_normalized_permanent_reindex T e q
  rw [hValue] at hEstimate
  have hConstant : (256 : Real) ^ (-1 / 8 : Real) = 1 / 2 := by
    have hLog : Real.log 256 = 8 * Real.log 2 := by
      rw [show (256 : Real) = 2 ^ 8 by norm_num, Real.log_pow]
      norm_num
    rw [Real.rpow_def_of_pos (by norm_num : (0 : Real) < 256), hLog]
    have hExponent : (8 * Real.log 2) * (-1 / 8 : Real) = -Real.log 2 := by ring
    rw [hExponent, Real.exp_neg, Real.exp_log (by norm_num : (0 : Real) < 2)]
    norm_num
  have hPower : (n : Real) ^ (-1 / 8 : Real) <= (256 : Real) ^ (-1 / 8 : Real) := by
    rw [Real.rpow_def_of_pos hN0, Real.rpow_def_of_pos (by norm_num : (0 : Real) < 256)]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_right (Real.log_le_log (by norm_num) hnReal) (by norm_num)
  rw [hConstant] at hPower
  have hHalf : 1 / 2 <= hamiltonianNormalizedPermanent T q := by
    have hLower := (abs_le.mp (le_trans hEstimate hPower)).1
    linarith only [hLower]
  have hD : 1 <= D := by
    have h := stochasticGramDeterminantFactor_one_le M q a delta hq hMRow
      (fun i j => hNonneg (e i) (e j)) (fun i j => hUpper (e i) (e j)) hDelta hDelta1 hMNorm
    rw [hCentered, hamiltonian_real_gram_factor_reindex] at h
    exact h
  have hD0 : 0 <= D := le_trans (by norm_num) hD
  have hCoefficient : 0 <= (n : Real) ^ n / (n.factorial : Real) :=
    div_nonneg (pow_nonneg (le_of_lt hN0) n) (Nat.cast_nonneg _)
  have hPositive : 0 < weightedPermutationSum T := by
    by_contra h
    have hNumerator := mul_nonpos_of_nonneg_of_nonpos hCoefficient (le_of_not_gt h)
    have hNonpos : hamiltonianNormalizedPermanent T q <= 0 :=
      div_nonpos_of_nonpos_of_nonneg hNumerator hD0
    linarith only [hHalf, hNonpos]
  exact And.intro hHalf (And.intro hD hPositive)

end PrimeFactorOscillations
