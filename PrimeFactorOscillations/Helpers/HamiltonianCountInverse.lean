/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCountPowerDecay

/-! # The actual counting-defect inverse

One fixed relative defect forces collective centered singular mass
with the sharp leading coefficient2/kappa. The count constant is
chosen before the defect size, and every normalization is retained.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_count_defect_log_amplification
    (n L C eta gamma : Real) (H : Nat)
    (hn : 0 < n) (hL : 1 <= L) (hC : 0 < C) (hEta : 0 < eta)
    (hFirst : 2 * C * L ^ H <= eta * n)
    (hCount : eta <= C * L ^ H / n + C * L ^ H * gamma / n ^ 2) :
    2 * Real.log n - (H : Real) * Real.log L + Real.log (eta / (2 * C)) <=
      Real.log gamma := by
  have hLPos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hLPow : 0 < L ^ H := pow_pos hLPos H
  have hNPow : 0 < n ^ (2 : Nat) := pow_pos hn 2
  have hWeight : 0 < C * L ^ H := mul_pos hC hLPow
  have hHalf : C * L ^ H / n <= eta / 2 := by
    apply le_of_mul_le_mul_right _ hn
    have hClear : (C * L ^ H / n) * n = C * L ^ H := by field_simp [ne_of_gt hn]
    rw [hClear]
    linarith only [hFirst]
  have hSecond : eta / 2 <= C * L ^ H * gamma / n ^ 2 := by linarith only [hCount, hHalf]
  have hScaled := mul_le_mul_of_nonneg_right hSecond (le_of_lt hNPow)
  have hClearScaled : (C * L ^ H * gamma / n ^ 2) * n ^ 2 = C * L ^ H * gamma := by
    field_simp [ne_of_gt hn]
  rw [hClearScaled] at hScaled
  have hRatio : 0 < eta / (2 * C) := div_pos hEta (mul_pos (by norm_num) hC)
  have hLower : 0 < (eta / (2 * C)) * n ^ 2 / L ^ H :=
    div_pos (mul_pos hRatio hNPow) hLPow
  have hClearLower :
      ((eta / (2 * C)) * n ^ 2 / L ^ H) * (C * L ^ H) = (eta / 2) * n ^ 2 := by
    field_simp [ne_of_gt hC, ne_of_gt hLPos]
    <;> ring
  have hAmplification : (eta / (2 * C)) * n ^ 2 / L ^ H <= gamma := by
    apply le_of_mul_le_mul_right _ hWeight
    rw [hClearLower]
    nlinarith only [hScaled]
  have hLog := Real.log_le_log hLower hAmplification
  have hExpand :
      Real.log ((eta / (2 * C)) * n ^ 2 / L ^ H) =
        2 * Real.log n - (H : Real) * Real.log L + Real.log (eta / (2 * C)) := by
    rw [Real.log_div (ne_of_gt (mul_pos hRatio hNPow)) (ne_of_gt hLPow),
      Real.log_mul (ne_of_gt hRatio) (ne_of_gt hNPow), Real.log_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    ring
  rw [hExpand] at hLog
  exact hLog

universe u

theorem stochastic_count_defect_inverse_uniform
    (rho c : Real) (hRho0 : 0 <= rho) (hRho1 : rho < 1) (hc : 0 <= c) :
    exists C : Real, 0 < C /\
      forall eta : Real, 0 < eta ->
        exists N0 : Nat, 256 <= N0 /\
          forall (J : Type u) [Fintype J] [DecidableEq J] [Nonempty J],
            N0 <= Fintype.card J ->
            forall (T : Matrix J J Real) (q a : Real),
              (Fintype.card J : Real) * q = 1 -> 1 <= a ->
              a <= c * Real.log (2 * (Fintype.card J : Real)) ->
              (forall i, Finset.univ.sum (fun j => T i j) = 1) ->
              (forall j, Finset.univ.sum (fun i => T i j) = 1) ->
              (forall i j, 0 <= T i j) -> (forall i j, T i j <= a * q) ->
              norm (centeredKernel T q) <= rho ->
              eta <= abs (hamiltonianBipartiteCountRatio T - 1) ->
              (2 * Real.log (Fintype.card J : Real) -
                (hamiltonianCountLogExponent : Real) *
                  Real.log (Real.log (2 * (Fintype.card J : Real))) +
                Real.log (eta / (2 * C)) <= Real.log (hamiltonianGramAmplification T q)) /\
              ((2 * Real.log (Fintype.card J : Real) -
                (hamiltonianCountLogExponent : Real) *
                  Real.log (Real.log (2 * (Fintype.card J : Real))) +
                Real.log (eta / (2 * C))) / hamiltonianSpectralKappa rho <=
                Finset.univ.sum (fun i => Finset.univ.sum
                  (fun j => centeredKernel T q i j ^ 2))) := by
  have hDelta : 0 < 1 - rho := sub_pos.mpr hRho1
  have hDelta1 : 1 - rho <= 1 := by linarith only [hRho0]
  have hRange := stochastic_weighted_cycle_log_envelope_uniform.{u}
    (1 - rho) c hDelta hDelta1 hc
  refine hRange.elim ?_
  intro C hC
  refine Exists.intro C (And.intro hC.1 ?_)
  intro eta hEta
  have hCoefficient : 0 < 2 * C / eta := div_pos (mul_pos (by norm_num) hC.1) hEta
  have hScalarRange := hamiltonian_log_power_dominated_uniform
    (2 * C / eta) hCoefficient hamiltonianCountLogExponent 1 (by norm_num)
  refine hC.2.elim ?_
  intro NC hNC
  refine hScalarRange.elim ?_
  intro NL hNL
  let N0 := max NC (max NL (Nat.ceil (Real.exp 1)))
  refine Exists.intro N0 (And.intro (le_trans hNC.1 (le_max_left _ _)) ?_)
  intro J instF instD instN hn T q a hq ha hA hRow hCol hNonneg hUpper hNorm hDefect
  have hnC : NC <= Fintype.card J := le_trans (le_max_left _ _) hn
  have hnL : NL <= Fintype.card J :=
    le_trans (le_trans (le_max_left NL _) (le_max_right NC _)) hn
  have hnCeil : Nat.ceil (Real.exp 1) <= Fintype.card J :=
    le_trans (le_trans (le_max_right NL _) (le_max_right NC _)) hn
  have hN256 : (256 : Real) <= Fintype.card J := by exact_mod_cast le_trans hNC.1 hnC
  have hN : 0 < (Fintype.card J : Real) := by linarith only [hN256]
  have hExp : Real.exp 1 <= (Fintype.card J : Real) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hnCeil)
  have hLogN : 1 <= Real.log (Fintype.card J : Real) := by
    have h := Real.log_le_log (Real.exp_pos 1) hExp
    simpa only [Real.log_exp] using h
  have hLog2 : 0 <= Real.log 2 := Real.log_nonneg (by norm_num)
  have hSplit : Real.log (2 * (Fintype.card J : Real)) =
      Real.log 2 + Real.log (Fintype.card J : Real) :=
    Real.log_mul (by norm_num) (ne_of_gt hN)
  have hL : 1 <= Real.log (2 * (Fintype.card J : Real)) := by
    linarith only [hLogN, hLog2, hSplit]
  have hScalar := hNL.2 (Fintype.card J) hnL
  rw [Real.rpow_one] at hScalar
  have hScaled := mul_le_mul_of_nonneg_right hScalar (le_of_lt hEta)
  have hClear :
      ((2 * C / eta) * (Real.log (2 * (Fintype.card J : Real))) ^ hamiltonianCountLogExponent) * eta =
        2 * C * (Real.log (2 * (Fintype.card J : Real))) ^ hamiltonianCountLogExponent := by
    field_simp [ne_of_gt hEta]
  rw [hClear] at hScaled
  have hFirst : 2 * C *
      (Real.log (2 * (Fintype.card J : Real))) ^ hamiltonianCountLogExponent <=
        eta * (Fintype.card J : Real) := by nlinarith only [hScaled]
  have hGap : 1 - (1 - rho) = rho := by ring
  have hNormDelta : norm (centeredKernel T q) <= 1 - (1 - rho) := by rw [hGap]; exact hNorm
  have hCount := hNC.2 J hnC T q a hq ha hA hRow hCol hNonneg hUpper hNormDelta
  have hLog := hamiltonian_count_defect_log_amplification
    (Fintype.card J : Real) (Real.log (2 * (Fintype.card J : Real)))
    C eta (hamiltonianGramAmplification T q) hamiltonianCountLogExponent
      hN hL hC.1 hEta hFirst (le_trans hDefect hCount)
  have hLogUpper := hamiltonian_matrix_log_amplification
    (centeredKernel T q) rho hRho0 hRho1 hNorm
  change Real.log (hamiltonianGramAmplification T q) <= hamiltonianSpectralKappa rho *
    Finset.univ.sum (fun i => Finset.univ.sum (fun j => centeredKernel T q i j ^ 2)) at hLogUpper
  have hKappa : 0 < hamiltonianSpectralKappa rho :=
    hamiltonian_spectral_kappa_positive rho hRho0 hRho1
  refine And.intro hLog ?_
  apply le_of_mul_le_mul_left _ hKappa
  have hClearInverse :
      hamiltonianSpectralKappa rho *
        ((2 * Real.log (Fintype.card J : Real) -
          (hamiltonianCountLogExponent : Real) *
            Real.log (Real.log (2 * (Fintype.card J : Real))) +
          Real.log (eta / (2 * C))) / hamiltonianSpectralKappa rho) =
        2 * Real.log (Fintype.card J : Real) -
          (hamiltonianCountLogExponent : Real) *
            Real.log (Real.log (2 * (Fintype.card J : Real))) +
          Real.log (eta / (2 * C)) := by field_simp [ne_of_gt hKappa]
  rw [hClearInverse]
  exact le_trans hLog hLogUpper


theorem stochastic_unoriented_count_defect_inverse_uniform
    (rho c : Real) (hRho0 : 0 <= rho) (hRho1 : rho < 1) (hc : 0 <= c) :
    exists C : Real, 0 < C /\
      forall eta : Real, 0 < eta ->
        exists N0 : Nat, 256 <= N0 /\
          forall (J : Type u) [Fintype J] [DecidableEq J] [Nonempty J],
            N0 <= Fintype.card J ->
            forall (T : Matrix J J Real) (q a : Real),
              (Fintype.card J : Real) * q = 1 -> 1 <= a ->
              a <= c * Real.log (2 * (Fintype.card J : Real)) ->
              (forall i, Finset.univ.sum (fun j => T i j) = 1) ->
              (forall j, Finset.univ.sum (fun i => T i j) = 1) ->
              (forall i j, 0 <= T i j) -> (forall i j, T i j <= a * q) ->
              norm (centeredKernel T q) <= rho ->
              eta <= abs ((2 * (Fintype.card J : Real) *
                (Fintype.card J : Real) ^ (2 * Fintype.card J) /
                ((Fintype.card J).factorial : Real) ^ 2) *
                (hamiltonianCycleSum (bipartiteLift T) / 2) - 1) ->
              (2 * Real.log (Fintype.card J : Real) -
                (hamiltonianCountLogExponent : Real) *
                  Real.log (Real.log (2 * (Fintype.card J : Real))) +
                Real.log (eta / (2 * C)) <=
                Real.log (Matrix.det ((1 : Matrix J J Real) +
                    centeredKernel T q * (centeredKernel T q).transpose) /
                  Matrix.det ((1 : Matrix J J Real) -
                    centeredKernel T q * (centeredKernel T q).transpose))) /\
              ((2 * Real.log (Fintype.card J : Real) -
                (hamiltonianCountLogExponent : Real) *
                  Real.log (Real.log (2 * (Fintype.card J : Real))) +
                Real.log (eta / (2 * C))) / hamiltonianSpectralKappa rho <=
                Finset.univ.sum (fun i => Finset.univ.sum
                  (fun j => centeredKernel T q i j ^ 2))) := by
  have hRange := stochastic_count_defect_inverse_uniform.{u} rho c hRho0 hRho1 hc
  refine hRange.elim ?_
  intro C hC
  refine Exists.intro C (And.intro hC.1 ?_)
  intro eta hEta
  have hEtaRange := hC.2 eta hEta
  refine hEtaRange.elim ?_
  intro N0 hN0
  refine Exists.intro N0 (And.intro hN0.1 ?_)
  intro J instF instD instN hn T q a hq ha hA hRow hCol hNonneg hUpper hNorm hDefect
  have hActualDefect : eta <= abs (hamiltonianBipartiteCountRatio T - 1) := by
    rw [hamiltonian_unoriented_cycle_ratio_identity]
    exact hDefect
  have hInverse := hN0.2 J hn T q a hq ha hA hRow hCol hNonneg hUpper hNorm hActualDefect
  unfold hamiltonianGramAmplification at hInverse
  rw [hamiltonian_gram_amplification_swap (centeredKernel T q)] at hInverse
  exact hInverse

end PrimeFactorOscillations
