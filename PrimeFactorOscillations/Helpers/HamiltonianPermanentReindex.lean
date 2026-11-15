/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPermanentAsymptotics
import PrimeFactorOscillations.Helpers.HamiltonianRepairedCovarianceTransport

/-! # Index-independent normalized permanent asymptotics

The uniform threshold is independent of the finite coordinate type.
The actual determinant function and full signed correction are transported.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota Jota : Type*} [Fintype Iota] [DecidableEq Iota]
  [Fintype Jota] [DecidableEq Jota]

theorem hamiltonian_real_gram_factor_reindex
    (B : Matrix Iota Iota Real) (e : Equiv Jota Iota) (s : Real) :
    realGramDeterminantFactor (B.submatrix e e) s = realGramDeterminantFactor B s := by
  have hTranspose : (B.submatrix e e).transpose = B.transpose.submatrix e e := rfl
  have hMatrix : (1 : Matrix Jota Jota Real) -
      HSMul.hSMul (s ^ 2) ((B.submatrix e e).transpose * B.submatrix e e) =
      ((1 : Matrix Iota Iota Real) - HSMul.hSMul (s ^ 2) (B.transpose * B)).submatrix e e := by
    rw [hTranspose, Matrix.submatrix_mul_equiv]
    apply Matrix.ext
    intro i j
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, e.injective.eq_iff]
  unfold realGramDeterminantFactor
  rw [hMatrix, Matrix.det_submatrix_equiv_self]

theorem hamiltonian_covariance_correction_reindex (M : Matrix Iota Iota Real)
    (e : Equiv Jota Iota) :
    covarianceCorrection (M.submatrix e e) = covarianceCorrection M := by
  have h := hamiltonian_covariance_trace_correction_reindex M e 1
  simpa only [covarianceTraceCorrection, sub_self, mul_zero, div_zero, zero_add] using h

theorem hamiltonian_first_correction_reindex
    (T : Matrix Iota Iota Real) (e : Equiv Jota Iota) (q : Real) :
    stochasticPermanentFirstCorrection (T.submatrix e e) q = stochasticPermanentFirstCorrection T q := by
  have hCentered : centeredKernel (T.submatrix e e) q = (centeredKernel T q).submatrix e e := rfl
  have hFactor : realGramDeterminantFactor ((centeredKernel T q).submatrix e e) =
      realGramDeterminantFactor (centeredKernel T q) := by
    funext s
    exact hamiltonian_real_gram_factor_reindex _ e s
  have hCard : Fintype.card Jota = Fintype.card Iota := Fintype.card_congr e
  have hLift : bipartiteLift ((centeredKernel T q).submatrix e e) =
      (bipartiteLift (centeredKernel T q)).submatrix (Equiv.sumCongr e e) (Equiv.sumCongr e e) := by
    apply Matrix.ext
    intro i j
    cases i <;> cases j <;> rfl
  unfold stochasticPermanentFirstCorrection
  rw [hCentered, hFactor, hCard, hLift, hamiltonian_resolvent_covariance_reindex,
    hamiltonian_covariance_correction_reindex]

universe u

theorem stochastic_permanent_relative_correction_fintype_uniform (delta K : Real)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1) :
    exists N0 : Nat, 16 <= N0 /\
      forall (J : Type u) [Fintype J] [DecidableEq J], N0 <= Fintype.card J ->
        forall (T : Matrix J J Real) (q a : Real),
          (Fintype.card J : Real) * q = 1 -> 1 <= a ->
          a <= (Real.log (Fintype.card J : Real)) ^ K ->
          (forall i, Finset.univ.sum (fun j => T i j) = 1) ->
          (forall j, Finset.univ.sum (fun i => T i j) = 1) ->
          (forall i j, 0 <= T i j) -> (forall i j, T i j <= a * q) ->
          norm (centeredKernel T q) <= 1 - delta ->
          (abs ((((Fintype.card J : Real) ^ Fintype.card J /
              ((Fintype.card J).factorial : Real)) * weightedPermutationSum T) /
                realGramDeterminantFactor (centeredKernel T q) 1 -
                (1 + stochasticPermanentFirstCorrection T q)) <=
              (1 + a) ^ 24 * hamiltonianPermanentUniformBudget delta /
                (Fintype.card J : Real) ^ 2) /\
          abs (stochasticPermanentFirstCorrection T q) <=
            21 * a ^ 2 / (delta ^ 3 * (Fintype.card J : Real)) := by
  have hRange := stochastic_permanent_relative_correction_polylog_uniform delta K hDelta0 hDelta1
  refine Exists.intro hRange.choose (And.intro hRange.choose_spec.1 ?_)
  intro J instF instD hn T q a hq ha hA hRow hCol hNonneg hUpper hNorm
  let n := Fintype.card J
  let e : Equiv (Fin n) J := (Fintype.equivFin J).symm
  let M := T.submatrix e e
  have hCentered : centeredKernel M q = (centeredKernel T q).submatrix e e := rfl
  have hReindexNorm : norm (centeredKernel M q) = norm (centeredKernel T q) := by
    rw [hCentered]
    exact hamiltonian_l2_reindex_norm _ e
  have hMRow (i : Fin n) : Finset.univ.sum (fun j => M i j) = 1 := by
    calc
      _ = Finset.univ.sum (fun j : J => T (e i) j) := Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = 1 := hRow (e i)
  have hMCol (j : Fin n) : Finset.univ.sum (fun i => M i j) = 1 := by
    calc
      _ = Finset.univ.sum (fun i : J => T i (e j)) := Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = 1 := hCol (e j)
  have hEstimate := hRange.choose_spec.2 n hn M q a hq ha hA hMRow hMCol
    (fun i j => hNonneg (e i) (e j)) (fun i j => hUpper (e i) (e j))
    (by rw [hReindexNorm]; exact hNorm)
  have hPer : weightedPermutationSum M = weightedPermutationSum T := finitePermutationSum_reindex e T
  have hFactor : realGramDeterminantFactor (centeredKernel M q) 1 =
      realGramDeterminantFactor (centeredKernel T q) 1 := by
    rw [hCentered]
    exact hamiltonian_real_gram_factor_reindex _ e 1
  have hCorrection : stochasticPermanentFirstCorrection M q = stochasticPermanentFirstCorrection T q :=
    hamiltonian_first_correction_reindex T e q
  rw [hPer, hFactor, hCorrection] at hEstimate
  exact hEstimate

end PrimeFactorOscillations
