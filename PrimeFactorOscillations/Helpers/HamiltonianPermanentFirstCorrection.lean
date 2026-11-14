/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCovarianceCorrection
import PrimeFactorOscillations.Helpers.HamiltonianMatrixSpectralAverage

/-! # The actual first permanent correction

The determinant's second derivative is identified from local equality with
its proved spectral product. The complete first correction, with the full
block covariance compensation, has an explicit uniform bound 21 A^2/N
after multiplication by the cube of the spectral gap.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [DecidableEq Iota] [Fintype Iota]

theorem realGramDeterminantFactor_eventually_eq_spectral
    (B : Matrix Iota Iota Real) (delta : Real)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm B <= 1 - delta) :
    Filter.Eventually
      (fun s => realGramDeterminantFactor B s =
        spectralFactors Finset.univ (realGramEigenvalues B) s) (nhds (1 : Real)) := by
  have hAt : forall i, 0 < 1 - (1 : Real) ^ 2 * realGramEigenvalues B i := by
    intro i
    have hStrip := spectralFactor_strip delta 0 (realGramEigenvalues B i) 1
      hDelta0 hDelta1 (by norm_num) (by linarith only [hDelta0])
      (realGramEigenvalues_nonnegative B i)
      (realGramEigenvalues_le_norm_bound B (1 - delta) (sub_nonneg.mpr hDelta1) hNorm i)
      (by norm_num)
    exact lt_of_lt_of_le hDelta0 hStrip.2.2.2
  have hEach : forall i, Filter.Eventually
      (fun s : Real => 0 < 1 - s ^ 2 * realGramEigenvalues B i) (nhds (1 : Real)) := by
    intro i
    have hContinuous : ContinuousAt
        (fun s : Real => 1 - s ^ 2 * realGramEigenvalues B i) 1 :=
      continuousAt_const.sub ((continuousAt_id.pow 2).mul continuousAt_const)
    exact hContinuous.eventually (isOpen_Ioi.mem_nhds (hAt i))
  have hAll := (Filter.eventually_all_finset (Finset.univ : Finset Iota)).mpr
    (fun i _ => hEach i)
  exact hAll.mono (fun s hs =>
    realGramDeterminantFactor_eq_spectral B s (fun i => hs i (Finset.mem_univ i)))

theorem realGramDeterminantFactor_second_derivative
    (B : Matrix Iota Iota Real) (delta : Real)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hNorm : norm B <= 1 - delta) :
    deriv (deriv (realGramDeterminantFactor B)) 1 =
      spectralFactorJet2 Finset.univ (realGramEigenvalues B) 1 := by
  have hEvent := realGramDeterminantFactor_eventually_eq_spectral
    B delta hDelta0 hDelta1 hNorm
  have hD2 := Filter.EventuallyEq.deriv_eq (Filter.EventuallyEq.deriv hEvent)
  have hDen : forall i, Membership.mem (Finset.univ : Finset Iota) i ->
      Not (1 - (1 : Real) ^ 2 * realGramEigenvalues B i = 0) := by
    intro i hi
    have hStrip := spectralFactor_strip delta 0 (realGramEigenvalues B i) 1
      hDelta0 hDelta1 (by norm_num) (by linarith only [hDelta0])
      (realGramEigenvalues_nonnegative B i)
      (realGramEigenvalues_le_norm_bound B (1 - delta) (sub_nonneg.mpr hDelta1) hNorm i)
      (by norm_num)
    exact ne_of_gt (lt_of_lt_of_le hDelta0 hStrip.2.2.2)
  have hIter := spectralFactors_iterated_two Finset.univ (realGramEigenvalues B) 1 hDen
  rw [iteratedDeriv_succ (n := 1), iteratedDeriv_one] at hIter
  exact hD2.trans hIter

def stochasticPermanentFirstCorrection (T : Matrix Iota Iota Real) (q : Real) : Real :=
  deriv (deriv (realGramDeterminantFactor (centeredKernel T q))) 1 /
    (2 * ((Fintype.card Iota : Real) - 1) *
      realGramDeterminantFactor (centeredKernel T q) 1) +
    covarianceCorrection (resolventCovariance (bipartiteLift (centeredKernel T q)))

variable [Nonempty Iota]

theorem stochasticPermanentFirstCorrection_bound
    (T : Matrix Iota Iota Real) (q a rho : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hN : 2 <= Fintype.card Iota)
    (hrow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hcol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hnonneg : forall i j, 0 <= T i j) (hupper : forall i j, T i j <= a * q)
    (hRho : rho < 1) (hNorm : norm (centeredKernel T q) <= rho) :
    (1 - rho) ^ 3 * abs (stochasticPermanentFirstCorrection T q) <= 21 * a ^ 2 * q := by
  let B := centeredKernel T q
  let lam := realGramEigenvalues B
  let g : Real := 1 - rho
  let mass : Real := Finset.sum Finset.univ lam
  let L1 : Real := Finset.sum Finset.univ (fun i => spectralCoordinate1 (lam i) 1)
  let L2 : Real := Finset.sum Finset.univ (fun i => spectralCoordinate2 (lam i) 1)
  let L : Real := L1 ^ 2 + L2
  let X : Real := L / (2 * ((Fintype.card Iota : Real) - 1))
  let P : Real := covarianceCorrection (resolventCovariance (bipartiteLift B))
  have hRho0 : 0 <= rho := le_trans (norm_nonneg B) hNorm
  have hGap0 : 0 < g := sub_pos.mpr hRho
  have hGap1 : g <= 1 := by dsimp only [g]; linarith only [hRho0]
  have hGapNorm : norm B <= 1 - g := by dsimp only [g]; linarith only [hNorm]
  have hData := stochasticGram_spectral_data T q a g hq hrow hnonneg hupper hGap1 hGapNorm
  have hBudget := spectralFactors_strip_budget Finset.univ lam g 0 1 hGap0 hGap1
    (by norm_num) (by linarith only [hGap0])
    (fun i _ => hData.1 i) (fun i _ => hData.2.1 i) (by norm_num)
  have hMass0 : 0 <= mass := hBudget.nonnegative_mass
  have hMass1 : mass <= a := by
    have h := hData.2.2
    change mass <= a - 1 at h
    linarith only [h]
  have ha0 : 0 <= a := le_trans (by norm_num) ha
  have hOne : 0 <= L1 := hBudget.nonnegative_one
  have hTwo : 0 <= L2 := hBudget.nonnegative_two
  have hL0 : 0 <= L := add_nonneg (sq_nonneg L1) hTwo
  have hFirst : g * L1 <= 2 * a := by
    have h := hBudget.bound_one
    change g * L1 <= 2 * mass at h
    linarith only [h, hMass1]
  have hFirstSquare : g ^ 2 * L1 ^ 2 <= 4 * a ^ 2 := by
    have h := mul_le_mul hFirst hFirst (mul_nonneg (le_of_lt hGap0) hOne)
      (mul_nonneg (by norm_num) ha0)
    nlinarith only [h]
  have hSecond : g ^ 2 * L2 <= 9 * a ^ 2 := by
    have h := hBudget.bound_two
    change g ^ 2 * L2 <= 9 * mass at h
    have hASquare : a <= a ^ 2 := by nlinarith only [ha]
    linarith only [h, hMass1, hASquare]
  have hLBound : g ^ 2 * L <= 13 * a ^ 2 := by
    dsimp only [L]
    nlinarith only [hFirstSquare, hSecond]
  have hNReal : (2 : Real) <= (Fintype.card Iota : Real) := by exact_mod_cast hN
  have hDen0 : 0 < 2 * ((Fintype.card Iota : Real) - 1) := by linarith only [hNReal]
  have hNm1 : Not ((Fintype.card Iota : Real) - 1 = 0) := by linarith only [hNReal]
  have hX0 : 0 <= X := div_nonneg hL0 (le_of_lt hDen0)
  have hq0 : 0 <= q := by nlinarith only [hq, hNReal]
  have hqHalf : q <= 1 / 2 := by
    have h := mul_le_mul_of_nonneg_right hNReal hq0
    linarith only [h, hq]
  have hDenq : 1 <= 2 * ((Fintype.card Iota : Real) - 1) * q := by
    nlinarith only [hq, hqHalf]
  have hXq : X <= L * q := by
    calc
      _ = X * 1 := (mul_one X).symm
      _ <= X * (2 * ((Fintype.card Iota : Real) - 1) * q) :=
        mul_le_mul_of_nonneg_left hDenq hX0
      _ = L * q := by dsimp only [X]; field_simp [hNm1]
  have hXBound2 : g ^ 2 * X <= 13 * a ^ 2 * q := by
    calc
      _ <= g ^ 2 * (L * q) := mul_le_mul_of_nonneg_left hXq (sq_nonneg g)
      _ = (g ^ 2 * L) * q := by ring
      _ <= _ := mul_le_mul_of_nonneg_right hLBound hq0
  have hXBound3 : g ^ 3 * abs X <= 13 * a ^ 2 * q := by
    rw [abs_of_nonneg hX0]
    calc
      _ = g * (g ^ 2 * X) := by ring
      _ <= 1 * (g ^ 2 * X) :=
        mul_le_mul_of_nonneg_right hGap1 (mul_nonneg (sq_nonneg g) hX0)
      _ = g ^ 2 * X := one_mul _
      _ <= _ := hXBound2
  have hSpectralAt1 : realGramDeterminantFactor B 1 = spectralFactors Finset.univ lam 1 :=
    realGramDeterminantFactor_eq_spectral_on_strip B g 0 1 hGap0 hGap1
      (by norm_num) (by linarith only [hGap0]) hGapNorm (by norm_num)
  have hDeltaPos : 0 < spectralFactors Finset.univ lam 1 := Real.exp_pos _
  have hSecondDerivative := realGramDeterminantFactor_second_derivative B g hGap0 hGap1 hGapNorm
  have hActualX :
      deriv (deriv (realGramDeterminantFactor B)) 1 /
        (2 * ((Fintype.card Iota : Real) - 1) * realGramDeterminantFactor B 1) = X := by
    rw [hSecondDerivative, hSpectralAt1]
    unfold spectralFactorJet2
    change spectralFactors Finset.univ lam 1 * L /
      (2 * ((Fintype.card Iota : Real) - 1) * spectralFactors Finset.univ lam 1) = X
    dsimp only [X]
    field_simp [ne_of_gt hDeltaPos, hNm1]
    <;> ring
  have hPBound : g ^ 3 * abs P <= 8 * a ^ 2 * q :=
    stochastic_block_covariance_correction_bound T q a rho hq ha hrow hcol hnonneg hupper hRho hNorm
  have hExact : stochasticPermanentFirstCorrection T q = X + P := by
    unfold stochasticPermanentFirstCorrection
    change deriv (deriv (realGramDeterminantFactor B)) 1 /
      (2 * ((Fintype.card Iota : Real) - 1) * realGramDeterminantFactor B 1) + P = X + P
    rw [hActualX]
  change g ^ 3 * abs (stochasticPermanentFirstCorrection T q) <= 21 * a ^ 2 * q
  rw [hExact]
  have hSum := mul_le_mul_of_nonneg_left (abs_add_le X P) (pow_nonneg (le_of_lt hGap0) 3)
  nlinarith only [hSum, hXBound3, hPBound]

end PrimeFactorOscillations
