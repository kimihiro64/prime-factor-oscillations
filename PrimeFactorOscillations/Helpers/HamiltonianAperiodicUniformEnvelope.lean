/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianAperiodicDeterminantBound
import PrimeFactorOscillations.Helpers.HamiltonianAperiodicResidual
import PrimeFactorOscillations.Helpers.HamiltonianComplementaryPermanentRatio

/-! # The full uniform aperiodic cycle/permanent comparison envelope

All local ratio and tail hypotheses are discharged from the original
stochastic kernel, cap and spectral gap. The retained signed signal
is normalized by its proved dimension-free determinant lower bound.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianAperiodicResidualEnvelope (n a : Real) : Real :=
  n ^ (-1 / 9 : Real) * (2 * Real.exp (16 * Real.exp 2 * a ^ 2)) +
    (2 * Real.exp (16 * a * Real.log (2 * n)) + 1) *
      Real.exp (-(Real.log (2 * n) ^ 3)) *
        (2 * Real.exp (16 * Real.exp 2 * a ^ 2 * (Real.exp 2) ^ 2))

theorem hamiltonian_relative_error_from_exponential_signal
    (x d E H : Real) (hD : 0 < d) (hLower : Real.exp (-H) <= d)
    (hError : abs (x - d) <= E) :
    abs (x / d - 1) <= Real.exp H * E := by
  have hE : 0 <= E := (abs_nonneg _).trans hError
  have hProduct : 1 <= Real.exp H * d := by
    have h := mul_le_mul_of_nonneg_left hLower (Real.exp_pos H).le
    rw [<- Real.exp_add, add_neg_cancel, Real.exp_zero] at h
    exact h
  have hClear : x / d - 1 = (x - d) / d := by field_simp
  rw [hClear, abs_div, abs_of_pos hD]
  apply le_of_mul_le_mul_right _ hD
  have hCancel : (abs (x - d) / d) * d = abs (x - d) := by field_simp
  rw [hCancel]
  calc
    _ <= E := hError
    _ <= (Real.exp H * E) * d := by
      have h := mul_le_mul_of_nonneg_right hProduct hE
      nlinarith only [h]

universe u

theorem stochastic_aperiodic_signed_envelope_uniform
    (delta : Real) (hDelta : 0 < delta) (hDelta1 : delta <= 1) :
    exists N0 : Nat, 256 <= N0 /\
      forall (J : Type u) [Fintype J] [DecidableEq J] [Nonempty J],
        N0 <= Fintype.card J ->
        forall (T : Matrix J J Real) (q a : Real),
          (Fintype.card J : Real) * q = 1 -> 1 <= a ->
          a <= Real.log (Fintype.card J : Real) ->
          (forall i, Finset.univ.sum (fun j => T i j) = 1) ->
          (forall j, Finset.univ.sum (fun i => T i j) = 1) ->
          (forall i j, 0 <= T i j) -> (forall i j, T i j <= a * q) ->
          norm (centeredKernel T q) <= 1 - delta ->
          0 < weightedPermutationSum T /\
            abs ((Fintype.card J : Real) * hamiltonianCycleSum T / weightedPermutationSum T -
              Matrix.det ((1 : Matrix J J Real) - centeredKernel T q)) <=
                hamiltonianAperiodicResidualEnvelope (Fintype.card J : Real) a := by
  choose P hP hMinor using stochastic_minor_relative_polylog_uniform.{u}
    delta 1 hDelta hDelta1 (by norm_num)
  choose Q hQ hRatio using stochastic_complementary_ratio_polylog_uniform.{u}
    delta 1 hDelta hDelta1 (by norm_num)
  refine Exists.intro (max P Q) (And.intro (hP.trans (le_max_left _ _)) ?_)
  intro J instF instD instN hn T q a hq ha hCap hRow hCol hNonneg hUpper hNorm
  have hnP : P <= Fintype.card J := (le_max_left _ _).trans hn
  have hnQ : Q <= Fintype.card J := (le_max_right _ _).trans hn
  let n : Real := Fintype.card J
  let L := Real.log (2 * n)
  have hnPos : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  have hn256 : (256 : Real) <= n := by
    change (256 : Real) <= (Fintype.card J : Real)
    exact_mod_cast hP.trans hnP
  have hqPos : 0 < q := by nlinarith only [hq, hnPos]
  have haPos : 0 < a := by linarith only [ha]
  have hc : 0 < a * q := mul_pos haPos hqPos
  have hL : 0 <= L := Real.log_nonneg (by linarith only [hn256])
  have hPolylog : a <= Real.log (Fintype.card J : Real) ^ (1 : Real) := by
    simpa only [Real.rpow_one] using hCap
  have hEps : 0 <= n ^ (-1 / 9 : Real) := Real.rpow_nonneg hnPos.le _
  have hLow (S : Finset J) (hS : (S.card : Real) <= L ^ 3) :
      abs (hamiltonianAperiodicMinorRatio T S - 1) <= n ^ (-1 / 9 : Real) :=
    (hMinor J hnP T S S rfl q a hq ha hPolylog hS hRow hCol hNonneg hUpper hNorm).2
  have hAll (S : Finset J) :
      0 <= hamiltonianAperiodicMinorRatio T S /\
        hamiltonianAperiodicMinorRatio T S <=
          (2 * Real.exp (16 * a * L)) * Real.exp (S.card : Real) := by
    have h := hRatio J hnQ T q a hq ha hPolylog hRow hCol hNonneg hUpper hNorm S S
    refine And.intro h.1 ?_
    calc
      _ <= 2 * Real.exp ((S.card : Real) + 16 * a * L) := h.2
      _ = _ := by rw [Real.exp_add]; ring
  have hEntry (i j : J) : abs (T i j) <= a * q := by
    rw [abs_of_nonneg (hNonneg i j)]
    exact hUpper i j
  have hScale : (Fintype.card J : Real) * (a * q) = a := by
    calc
      _ = a * ((Fintype.card J : Real) * q) := by ring
      _ = a := by rw [hq, mul_one]
  have hError := stochastic_aperiodic_complete_residual_envelope T q (a * q) (L ^ 3)
    (n ^ (-1 / 9 : Real)) (2 * Real.exp (16 * a * L)) hq hc hEps
    (mul_nonneg (by norm_num) (Real.exp_pos _).le) hRow hCol hEntry hLow hAll
  have hEmptySize : (((EmptyCollection.emptyCollection : Finset J) : Finset J).card : Real) <= L ^ 3 := by
    simpa using pow_nonneg hL 3
  have hPositive := (hMinor J hnP T (EmptyCollection.emptyCollection : Finset J) (EmptyCollection.emptyCollection : Finset J) rfl q a hq ha
    hPolylog hEmptySize hRow hCol hNonneg hUpper hNorm).1
  refine And.intro hPositive ?_
  simpa only [hamiltonianAperiodicResidualEnvelope, hScale] using hError

theorem stochastic_aperiodic_relative_envelope_uniform
    (delta : Real) (hDelta : 0 < delta) (hDelta1 : delta <= 1) :
    exists N0 : Nat, 256 <= N0 /\
      forall (J : Type u) [Fintype J] [DecidableEq J] [Nonempty J],
        N0 <= Fintype.card J ->
        forall (T : Matrix J J Real) (q a : Real),
          (Fintype.card J : Real) * q = 1 -> 1 <= a ->
          a <= Real.log (Fintype.card J : Real) ->
          (forall i, Finset.univ.sum (fun j => T i j) = 1) ->
          (forall j, Finset.univ.sum (fun i => T i j) = 1) ->
          (forall i j, 0 <= T i j) -> (forall i j, T i j <= a * q) ->
          norm (centeredKernel T q) <= 1 - delta ->
          0 < weightedPermutationSum T /\
            0 < Matrix.det ((1 : Matrix J J Real) - centeredKernel T q) /\
            abs (((Fintype.card J : Real) * hamiltonianCycleSum T / weightedPermutationSum T) /
              Matrix.det ((1 : Matrix J J Real) - centeredKernel T q) - 1) <=
                Real.exp ((a - 1) + (a - 1) / delta) *
                  hamiltonianAperiodicResidualEnvelope (Fintype.card J : Real) a := by
  choose N0 hN0 hRaw using stochastic_aperiodic_signed_envelope_uniform.{u} delta hDelta hDelta1
  refine Exists.intro N0 (And.intro hN0 ?_)
  intro J instF instD instN hn T q a hq ha hCap hRow hCol hNonneg hUpper hNorm
  have hError := hRaw J hn T q a hq ha hCap hRow hCol hNonneg hUpper hNorm
  have hSignal := stochastic_aperiodic_determinant_lower_bound T q a delta hq hDelta
    hRow hCol hNonneg hUpper hNorm
  exact And.intro hError.1 (And.intro hSignal.1
    (hamiltonian_relative_error_from_exponential_signal _ _ _ _ hSignal.1 hSignal.2 hError.2))

end PrimeFactorOscillations
