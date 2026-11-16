/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianAperiodicRate
import PrimeFactorOscillations.Helpers.HamiltonianPrimeCircleAsymptotic

/-! # The full factorial-normalized aperiodic Hamiltonian count

The actual cycle/permanent comparison and the proved permanent
asymptotic are multiplied with both errors retained. The reference
uses the actual centered determinant and Gram determinant factor.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianAperiodicCountRatio (T : Matrix Iota Iota Real) (q : Real) : Real :=
  (((Fintype.card Iota : Real) ^ Fintype.card Iota /
      ((Fintype.card Iota).factorial : Real)) *
    ((Fintype.card Iota : Real) * hamiltonianCycleSum T)) /
      (Matrix.det ((1 : Matrix Iota Iota Real) - centeredKernel T q) *
        realGramDeterminantFactor (centeredKernel T q) 1)

def hamiltonianAperiodicCycleReference (T : Matrix Iota Iota Real) (q : Real) : Real :=
  (((Fintype.card Iota - 1).factorial : Real) /
      (Fintype.card Iota : Real) ^ Fintype.card Iota) *
    Matrix.det ((1 : Matrix Iota Iota Real) - centeredKernel T q) *
      realGramDeterminantFactor (centeredKernel T q) 1

theorem hamiltonian_aperiodic_count_ratio_product
    (T : Matrix Iota Iota Real) (q : Real)
    (hPer : Not (weightedPermutationSum T = 0))
    (hDet : Not (Matrix.det ((1 : Matrix Iota Iota Real) - centeredKernel T q) = 0))
    (hGram : Not (realGramDeterminantFactor (centeredKernel T q) 1 = 0)) :
    hamiltonianAperiodicCountRatio T q =
      hamiltonianNormalizedPermanent T q *
        (((Fintype.card Iota : Real) * hamiltonianCycleSum T / weightedPermutationSum T) /
          Matrix.det ((1 : Matrix Iota Iota Real) - centeredKernel T q)) := by
  unfold hamiltonianAperiodicCountRatio hamiltonianNormalizedPermanent
  field_simp
  <;> ring

theorem hamiltonian_aperiodic_count_reference_identity
    (T : Matrix Iota Iota Real) (q : Real) (hn : 1 <= Fintype.card Iota)
    (hDet : Not (Matrix.det ((1 : Matrix Iota Iota Real) - centeredKernel T q) = 0))
    (hGram : Not (realGramDeterminantFactor (centeredKernel T q) 1 = 0)) :
    hamiltonianAperiodicCountRatio T q =
      hamiltonianCycleSum T / hamiltonianAperiodicCycleReference T q := by
  let n := Fintype.card Iota
  have hnPos : 0 < (n : Real) := by dsimp only [n]; exact_mod_cast (show 0 < Fintype.card Iota by omega)
  have hFact : (0 : Real) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hPred : (0 : Real) < (n - 1).factorial := by exact_mod_cast Nat.factorial_pos (n - 1)
  have hFactor : (n.factorial : Real) = (n : Real) * ((n - 1).factorial : Real) := by
    have hNat := Nat.factorial_succ (n - 1)
    have hIndex : n - 1 + 1 = n := Nat.sub_add_cancel hn
    rw [hIndex] at hNat
    exact_mod_cast hNat
  change (((n : Real) ^ n / (n.factorial : Real)) *
      ((n : Real) * hamiltonianCycleSum T)) /
      (Matrix.det ((1 : Matrix Iota Iota Real) - centeredKernel T q) *
        realGramDeterminantFactor (centeredKernel T q) 1) =
    hamiltonianCycleSum T /
      ((((n - 1).factorial : Real) / (n : Real) ^ n) *
        Matrix.det ((1 : Matrix Iota Iota Real) - centeredKernel T q) *
          realGramDeterminantFactor (centeredKernel T q) 1)
  rw [hFactor]
  field_simp
  <;> ring

theorem stochastic_aperiodic_count_polylog_uniform
    (delta : Real) (hDelta : 0 < delta) (hDelta1 : delta <= 1) :
    exists N0 : Nat, 256 <= N0 /\
      forall n : Nat, N0 <= n ->
        forall (T : Matrix (Fin n) (Fin n) Real) (q a : Real),
          (n : Real) * q = 1 -> 1 <= a -> a <= Real.log (n : Real) ->
          (forall i, Finset.univ.sum (fun j => T i j) = 1) ->
          (forall j, Finset.univ.sum (fun i => T i j) = 1) ->
          (forall i j, 0 <= T i j) -> (forall i j, T i j <= a * q) ->
          norm (centeredKernel T q) <= 1 - delta ->
          0 < weightedPermutationSum T /\
            0 < Matrix.det ((1 : Matrix (Fin n) (Fin n) Real) - centeredKernel T q) /\
            1 <= realGramDeterminantFactor (centeredKernel T q) 1 /\
            abs (hamiltonianAperiodicCountRatio T q - 1) <=
              17 * (n : Real) ^ (-1 / 9 : Real) *
                Real.exp (hamiltonianAperiodicErrorConstant delta * a ^ 2) := by
  choose A hA hCycle using stochastic_aperiodic_relative_envelope_uniform.{0} delta hDelta hDelta1
  choose B hB hPermanent using stochastic_permanent_first_order_polylog_uniform
    delta 1 hDelta hDelta1 (by norm_num)
  let D := Nat.ceil (Real.exp hamiltonianAperiodicTailLogThreshold)
  let N0 := max A (max B D)
  refine Exists.intro N0 (And.intro (hA.trans (le_max_left _ _)) ?_)
  intro n hn T q a hq ha hCap hRow hCol hNonneg hUpper hNorm
  have hnA : A <= n := (le_max_left _ _).trans hn
  have hnB : B <= n := by dsimp only [N0] at hn; omega
  have hnD : D <= n := by dsimp only [N0] at hn; omega
  have hn256 : 256 <= n := hA.trans hnA
  have hn1 : 1 <= n := by omega
  have hnPos : 0 < (n : Real) := by exact_mod_cast (show 0 < n by omega)
  have hnReal : (1 : Real) <= n := by exact_mod_cast hn1
  letI : NeZero n := NeZero.mk (by omega)
  have hqCard : (Fintype.card (Fin n) : Real) * q = 1 := by
    simpa only [Fintype.card_fin] using hq
  have hCapCard : a <= Real.log (Fintype.card (Fin n) : Real) := by
    simpa only [Fintype.card_fin] using hCap
  have hRaw := hCycle (Fin n) (by simpa only [Fintype.card_fin] using hnA)
    T q a hqCard ha hCapCard hRow hCol hNonneg hUpper hNorm
  have hExp : Real.exp hamiltonianAperiodicTailLogThreshold <= (n : Real) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hnD)
  have hLog : hamiltonianAperiodicTailLogThreshold <= Real.log (n : Real) := by
    have h := Real.log_le_log (Real.exp_pos _) hExp
    simpa only [Real.log_exp] using h
  have hRelative :
      abs ((((n : Real) * hamiltonianCycleSum T / weightedPermutationSum T) /
        Matrix.det ((1 : Matrix (Fin n) (Fin n) Real) - centeredKernel T q)) - 1) <=
        8 * (n : Real) ^ (-1 / 9 : Real) *
          Real.exp (hamiltonianAperiodicErrorConstant delta * a ^ 2) := by
    have h := hRaw.2.2
    rw [Fintype.card_fin] at h
    exact h.trans (hamiltonian_aperiodic_relative_log_envelope (n : Real) a delta
      hnReal ha hDelta hCap hLog)
  have hPolylog : a <= Real.log (n : Real) ^ (1 : Real) := by
    simpa only [Real.rpow_one] using hCap
  have hPerError : abs (hamiltonianNormalizedPermanent T q - 1) <=
      (n : Real) ^ (-1 / 8 : Real) := by
    have h := hPermanent n hnB T q a hq ha hPolylog hRow hCol hNonneg hUpper hNorm
    simpa only [hamiltonianNormalizedPermanent, Fintype.card_fin] using h
  have hGram := stochasticGramDeterminantFactor_one_le T q a delta hq hRow hNonneg hUpper
    hDelta hDelta1 hNorm
  have hPer0 : Not (weightedPermutationSum T = 0) := ne_of_gt hRaw.1
  have hDet0 : Not (Matrix.det ((1 : Matrix (Fin n) (Fin n) Real) - centeredKernel T q) = 0) :=
    ne_of_gt hRaw.2.1
  have hGram0 : Not (realGramDeterminantFactor (centeredKernel T q) 1 = 0) := by linarith only [hGram]
  have he : 0 <= (n : Real) ^ (-1 / 8 : Real) := Real.rpow_nonneg hnPos.le _
  have he1 : (n : Real) ^ (-1 / 8 : Real) <= 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hnReal (by norm_num)
  have hd : 0 <= 8 * (n : Real) ^ (-1 / 9 : Real) *
      Real.exp (hamiltonianAperiodicErrorConstant delta * a ^ 2) := by positivity
  have hProduct := LPF.hamiltonian_relative_product_error
    (hamiltonianNormalizedPermanent T q)
    (((n : Real) * hamiltonianCycleSum T / weightedPermutationSum T) /
      Matrix.det ((1 : Matrix (Fin n) (Fin n) Real) - centeredKernel T q))
    ((n : Real) ^ (-1 / 8 : Real))
    (8 * (n : Real) ^ (-1 / 9 : Real) *
      Real.exp (hamiltonianAperiodicErrorConstant delta * a ^ 2))
    he he1 hd hPerError hRelative
  have hPower : (n : Real) ^ (-1 / 8 : Real) <= (n : Real) ^ (-1 / 9 : Real) := by
    rw [Real.rpow_def_of_pos hnPos, Real.rpow_def_of_pos hnPos]
    apply Real.exp_le_exp.mpr
    have h := Real.log_nonneg hnReal
    nlinarith only [h]
  have hC := (hamiltonian_aperiodic_density_budget delta hDelta).1
  have hExp1 : 1 <= Real.exp (hamiltonianAperiodicErrorConstant delta * a ^ 2) :=
    Real.one_le_exp (mul_nonneg hC.le (sq_nonneg a))
  have hSmall : (n : Real) ^ (-1 / 8 : Real) <=
      (n : Real) ^ (-1 / 9 : Real) *
        Real.exp (hamiltonianAperiodicErrorConstant delta * a ^ 2) := by
    exact hPower.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hExp1 (Real.rpow_nonneg hnPos.le (-1 / 9 : Real)))
  refine And.intro hRaw.1 (And.intro hRaw.2.1 (And.intro hGram ?_))
  rw [hamiltonian_aperiodic_count_ratio_product T q hPer0 hDet0 hGram0]
  rw [Fintype.card_fin]
  nlinarith only [hProduct, hSmall]

end PrimeFactorOscillations
