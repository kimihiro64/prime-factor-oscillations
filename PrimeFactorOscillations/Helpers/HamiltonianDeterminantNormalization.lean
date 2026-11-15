/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianSignedComparisonAssembly

/-! # Positive determinant normalization of the complete signed comparison

Actual centered eigenvalues and energy control determinant division.
The complete retained tail is preserved under this division.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_log_one_sub_lower
    (x delta : Real) (hx : 0 <= x) (hDelta : 0 < delta)
    (hDen : delta <= 1 - x) :
    -x / delta <= Real.log (1 - x) := by
  have hPos : 0 < 1 - x := lt_of_lt_of_le hDelta hDen
  have hBase := Real.one_sub_inv_le_log_of_pos hPos
  have hMultiply := mul_le_mul_of_nonneg_left hDen hx
  have hClear : (1 - Inv.inv (1 - x)) * delta * (1 - x) = -x * delta := by
    field_simp [ne_of_gt hPos]
    <;> ring
  have hFraction : -x / delta <= 1 - Inv.inv (1 - x) := by
    apply le_of_mul_le_mul_right _ hDelta
    have hQuotient : (-x / delta) * delta = -x := by field_simp [ne_of_gt hDelta]
    rw [hQuotient]
    apply le_of_mul_le_mul_right _ hPos
    rw [hClear]
    nlinarith only [hMultiply]
  exact le_trans hFraction hBase

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem stochastic_centered_determinant_exponential_lower
    (T : Matrix Iota Iota Real) (q a delta : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (hDelta : 0 < delta) (hDelta1 : delta <= 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= 1 - delta) :
    Real.exp (-(a - 1) / delta) <=
      Matrix.det ((1 : Matrix Iota Iota Real) -
        (centeredKernel T q).transpose * centeredKernel T q) := by
  let B := centeredKernel T q
  let v := realGramEigenvalues B
  have hData := stochasticGram_spectral_data T q a delta hq hRow hNonneg hUpper hDelta1 hNorm
  have hNonnegEigen (i : Iota) : 0 <= v i := hData.1 i
  have hDen (i : Iota) : delta <= 1 - v i := by
    have h := hData.2.1 i
    nlinarith only [h, hDelta, hDelta1]
  have hPositive (i : Iota) : 0 < 1 - v i := lt_of_lt_of_le hDelta (hDen i)
  have hPoint (i : Iota) : Real.exp (-v i / delta) <= 1 - v i := by
    calc
      _ <= Real.exp (Real.log (1 - v i)) :=
        Real.exp_le_exp.mpr (hamiltonian_log_one_sub_lower (v i) delta
          (hNonnegEigen i) hDelta (hDen i))
      _ = _ := Real.exp_log (hPositive i)
  have hProd : Finset.univ.prod (fun i : Iota => Real.exp (-v i / delta)) <=
      Finset.univ.prod (fun i : Iota => 1 - v i) := by
    have hLeft (i : Iota) : 0 <= Real.exp (-v i / delta) := le_of_lt (Real.exp_pos _)
    gcongr with i hi
    all_goals first
      | exact fun i _ => hLeft i
      | exact fun i _ => hPoint i
      | exact hLeft _
      | exact hPoint _
  have hSum : Finset.univ.sum (fun i : Iota => -v i / delta) =
      -(Finset.univ.sum v) / delta := by
    rw [<- Finset.sum_div, Finset.sum_neg_distrib]
  rw [<- Real.exp_sum, hSum] at hProd
  have hEnergy : Finset.univ.sum v <= a - 1 := hData.2.2
  have hExponent := div_le_div_of_nonneg_right (neg_le_neg hEnergy) (le_of_lt hDelta)
  have hDet :
      Matrix.det ((1 : Matrix Iota Iota Real) - B.transpose * B) =
        Finset.univ.prod (fun i : Iota => 1 - v i) := by
    simpa only [one_smul, one_mul, v, realGramEigenvalues] using!
      hermitian_det_one_sub_smul (B.transpose * B) (realGramHermitian B) 1
  rw [hDet]
  exact le_trans (Real.exp_le_exp.mpr hExponent) hProd

theorem stochastic_centered_determinant_positive
    (T : Matrix Iota Iota Real) (q a delta : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (hDelta : 0 < delta) (hDelta1 : delta <= 1)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= 1 - delta) :
    0 < Matrix.det ((1 : Matrix Iota Iota Real) -
      (centeredKernel T q).transpose * centeredKernel T q) :=
  lt_of_lt_of_le (Real.exp_pos _)
    (stochastic_centered_determinant_exponential_lower T q a delta
      hq hDelta hDelta1 hRow hNonneg hUpper hNorm)

theorem hamiltonian_relative_signed_bound
    (K d f e z H : Real) (hd : 0 < d) (hz : 0 <= z)
    (hLower : Real.exp (-H) <= d)
    (hBound : abs (K - d) <= d * f + e + z) :
    abs (K / d - 1) <= f + e / d + z * Real.exp H := by
  have hDiff : K / d - 1 = (K - d) / d := by field_simp [ne_of_gt hd]
  rw [hDiff, abs_div, abs_of_pos hd]
  have hScaled := mul_le_mul_of_nonneg_left hLower
    (mul_nonneg hz (le_of_lt (Real.exp_pos H)))
  have hExp : Real.exp H * Real.exp (-H) = 1 := by
    rw [<- Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hTail : z <= z * Real.exp H * d := by
    have hLeft : z * Real.exp H * Real.exp (-H) = z := by rw [mul_assoc, hExp, mul_one]
    rw [hLeft] at hScaled
    exact hScaled
  have hClear : (e / d) * d = e := by field_simp [ne_of_gt hd]
  have hAbsClear : (abs (K - d) / d) * d = abs (K - d) := by field_simp [ne_of_gt hd]
  apply le_of_mul_le_mul_right _ hd
  rw [hAbsClear]
  nlinarith only [hBound, hTail, hClear]


def hamiltonianGramAmplification (T : Matrix Iota Iota Real) (q : Real) : Real :=
  Matrix.det ((1 : Matrix Iota Iota Real) +
    (centeredKernel T q).transpose * centeredKernel T q) /
  Matrix.det ((1 : Matrix Iota Iota Real) -
    (centeredKernel T q).transpose * centeredKernel T q)

theorem hamiltonian_gram_factor_squared_cancellation
    (B : Matrix Iota Iota Real)
    (hd : 0 < Matrix.det ((1 : Matrix Iota Iota Real) - B.transpose * B)) :
    realGramDeterminantFactor B 1 ^ 2 *
      Matrix.det ((1 : Matrix Iota Iota Real) - B.transpose * B) = 1 := by
  let d := Matrix.det ((1 : Matrix Iota Iota Real) - B.transpose * B)
  have hFactor : realGramDeterminantFactor B 1 =
      Real.exp (Real.log d * (-(1 / 2 : Real))) := by
    unfold realGramDeterminantFactor
    simp only [one_pow, one_smul]
    change d ^ (-(1 / 2 : Real)) = _
    dsimp only [d]
    rw [Real.rpow_def_of_pos hd]
  have hSquare : realGramDeterminantFactor B 1 ^ 2 = Real.exp (-Real.log d) := by
    rw [hFactor, pow_two, <- Real.exp_add]
    congr 1
    ring
  change realGramDeterminantFactor B 1 ^ 2 * d = 1
  rw [hSquare]
  calc
    _ = Real.exp (-Real.log d) * Real.exp (Real.log d) :=
      congrArg (fun z : Real => Real.exp (-Real.log d) * z) (Real.exp_log hd).symm
    _ = 1 := by rw [<- Real.exp_add, neg_add_cancel, Real.exp_zero]

universe u

theorem stochastic_relative_bipartite_comparison_logarithmic_uniform
    (delta c : Real) (hDelta : 0 < delta) (hDelta1 : delta <= 1) (hc : 0 <= c) :
    exists N0 : Nat, 256 <= N0 /\
      forall (J : Type u) [Fintype J] [DecidableEq J] [Nonempty J],
        N0 <= Fintype.card J ->
        forall (T : Matrix J J Real) (q a : Real),
          (Fintype.card J : Real) * q = 1 -> 1 <= a ->
          a <= c * Real.log (2 * (Fintype.card J : Real)) ->
          (forall i, Finset.univ.sum (fun j => T i j) = 1) ->
          (forall j, Finset.univ.sum (fun i => T i j) = 1) ->
          (forall i j, 0 <= T i j) -> (forall i j, T i j <= a * q) ->
          norm (centeredKernel T q) <= 1 - delta ->
          0 < weightedPermutationSum T /\
          0 < Matrix.det ((1 : Matrix J J Real) -
            (centeredKernel T q).transpose * centeredKernel T q) /\
          abs (hamiltonianNormalizedBipartitePacket T /
            Matrix.det ((1 : Matrix J J Real) -
              (centeredKernel T q).transpose * centeredKernel T q) - 1) <=
            900 * (a / delta) ^ 3 * q +
            2 * a * (hamiltonianMinorUniformConstant delta *
              (Real.log (2 * (Fintype.card J : Real))) ^ hamiltonianMinorUniformExponent 2 /
                (Fintype.card J : Real) ^ 2) * hamiltonianGramAmplification T q +
            Real.exp (-((Real.log (2 * (Fintype.card J : Real))) ^ 3 *
              Real.log (Real.log (2 * (Fintype.card J : Real)))) / 4 + (a - 1) / delta) := by
  have hRange := stochastic_signed_bipartite_comparison_logarithmic_uniform.{u}
    delta c hDelta hDelta1 hc
  refine hRange.elim ?_
  intro N0 hN0
  refine Exists.intro N0 (And.intro hN0.1 ?_)
  intro J instF instD instN hn T q a hq ha hA hRow hCol hNonneg hUpper hNorm
  have hData := hN0.2 J hn T q a hq ha hA hRow hCol hNonneg hUpper hNorm
  let d := Matrix.det ((1 : Matrix J J Real) -
    (centeredKernel T q).transpose * centeredKernel T q)
  let e := 2 * a * (hamiltonianMinorUniformConstant delta *
    (Real.log (2 * (Fintype.card J : Real))) ^ hamiltonianMinorUniformExponent 2 /
      (Fintype.card J : Real) ^ 2) *
    Matrix.det ((1 : Matrix J J Real) +
      (centeredKernel T q).transpose * centeredKernel T q)
  let z := Real.exp (-((Real.log (2 * (Fintype.card J : Real))) ^ 3 *
    Real.log (Real.log (2 * (Fintype.card J : Real)))) / 4)
  have hd : 0 < d := stochastic_centered_determinant_positive T q a delta
    hq hDelta hDelta1 hRow hNonneg hUpper hNorm
  have hLower : Real.exp (-((a - 1) / delta)) <= d := by
    simpa only [neg_div] using stochastic_centered_determinant_exponential_lower
      T q a delta hq hDelta hDelta1 hRow hNonneg hUpper hNorm
  have hBound : abs (hamiltonianNormalizedBipartitePacket T - d) <=
      d * (900 * (a / delta) ^ 3 * q) + e + z := by
    have h := hData.2
    rw [abs_of_pos hd] at h
    change abs (hamiltonianNormalizedBipartitePacket T - d) <=
      900 * d * (a / delta) ^ 3 * q + e + z at h
    nlinarith only [h]
  have hRelative := hamiltonian_relative_signed_bound
    (hamiltonianNormalizedBipartitePacket T) d (900 * (a / delta) ^ 3 * q)
      e z ((a - 1) / delta) hd (le_of_lt (Real.exp_pos _)) hLower hBound
  refine And.intro hData.1 (And.intro hd ?_)
  convert hRelative using 1
  dsimp only [e, z, d, hamiltonianGramAmplification]
  rw [Real.exp_add]
  ring

end PrimeFactorOscillations
