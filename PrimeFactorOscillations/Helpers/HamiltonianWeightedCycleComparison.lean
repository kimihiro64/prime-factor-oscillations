/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianDeterminantNormalization

/-! # The actual weighted Hamiltonian cycle comparison

Exact factorial and determinant cancellation turns the complete signed
comparison into an actual cycle-count estimate. The two independent
error allowances display every retained contribution.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_multiplicative_relative_error
    (r u p e : Real) (hp : 0 <= p)
    (hr : abs (r - 1) <= p) (hu : abs (u - 1) <= e) :
    abs (r ^ 2 * u - 1) <= (1 + p) ^ 2 * e + (2 + p) * p := by
  have he : 0 <= e := le_trans (abs_nonneg _) hu
  have hAbsR : abs r <= 1 + p := by
    have h := abs_add_le (r - 1) (1 : Real)
    have hId : (r - 1) + 1 = r := by ring
    rw [hId, abs_one] at h
    linarith only [h, hr]
  have hAbsPlus : abs (r + 1) <= 2 + p := by
    have h := abs_add_le r (1 : Real)
    rw [abs_one] at h
    linarith only [h, hAbsR]
  have hR2 : r ^ 2 <= (1 + p) ^ 2 := by
    have hSquare : abs r ^ 2 = r ^ 2 := sq_abs r
    nlinarith only [abs_nonneg r, hAbsR, hp, hSquare]
  have hFirst : abs (r ^ 2 - 1) <= p * (2 + p) := by
    have hFactor : r ^ 2 - 1 = (r - 1) * (r + 1) := by ring
    rw [hFactor, abs_mul]
    exact mul_le_mul hr hAbsPlus (abs_nonneg _) hp
  have hProduct := mul_le_mul_of_nonneg_left hu (sq_nonneg r)
  have hOuter := mul_le_mul_of_nonneg_right hR2 he
  have hIdentity : r ^ 2 * u - 1 = r ^ 2 * (u - 1) + (r ^ 2 - 1) := by ring
  rw [hIdentity]
  have hTriangle := abs_add_le (r ^ 2 * (u - 1)) (r ^ 2 - 1)
  rw [abs_mul, abs_of_nonneg (sq_nonneg r)] at hTriangle
  nlinarith only [hTriangle, hFirst, hProduct, hOuter]

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianBipartiteCountRatio (T : Matrix Iota Iota Real) : Real :=
  ((Fintype.card Iota : Real) ^ Fintype.card Iota /
    ((Fintype.card Iota).factorial : Real)) ^ 2 *
      ((Fintype.card Iota : Real) * hamiltonianCycleSum (bipartiteLift T))

def hamiltonianPermanentCountAllowance (n : Nat) (a delta : Real) : Real :=
  21 * a ^ 2 / (delta ^ 3 * (n : Real)) +
    abs (hamiltonianPermanentUniformBudget delta) * (1 + a) ^ 24 / (n : Real) ^ 2

def hamiltonianSignedCountAllowance (T : Matrix Iota Iota Real)
    (q a delta : Real) : Real :=
  900 * (a / delta) ^ 3 * q +
    2 * a * (hamiltonianMinorUniformConstant delta *
      (Real.log (2 * (Fintype.card Iota : Real))) ^ hamiltonianMinorUniformExponent 2 /
        (Fintype.card Iota : Real) ^ 2) * hamiltonianGramAmplification T q +
    Real.exp (-((Real.log (2 * (Fintype.card Iota : Real))) ^ 3 *
      Real.log (Real.log (2 * (Fintype.card Iota : Real)))) / 4 + (a - 1) / delta)

theorem hamiltonian_weighted_cycle_normalization [Nonempty Iota]
    (T : Matrix Iota Iota Real) (q : Real)
    (hP : Not (weightedPermutationSum T = 0))
    (hd : 0 < Matrix.det ((1 : Matrix Iota Iota Real) -
      (centeredKernel T q).transpose * centeredKernel T q)) :
    hamiltonianNormalizedPermanent T q ^ 2 *
      (hamiltonianNormalizedBipartitePacket T /
        Matrix.det ((1 : Matrix Iota Iota Real) -
          (centeredKernel T q).transpose * centeredKernel T q)) =
      hamiltonianBipartiteCountRatio T := by
  let C := (Fintype.card Iota : Real) ^ Fintype.card Iota /
    ((Fintype.card Iota).factorial : Real)
  let P := weightedPermutationSum T
  let D := realGramDeterminantFactor (centeredKernel T q) 1
  let d := Matrix.det ((1 : Matrix Iota Iota Real) -
    (centeredKernel T q).transpose * centeredKernel T q)
  let X := (Fintype.card Iota : Real) * hamiltonianCycleSum (bipartiteLift T)
  have hCancel : D ^ 2 * d = 1 :=
    hamiltonian_gram_factor_squared_cancellation (centeredKernel T q) hd
  have hD : Not (D = 0) := by
    intro h
    rw [h] at hCancel
    norm_num at hCancel
  have hP0 : Not (P = 0) := hP
  have hd0 : Not (d = 0) := ne_of_gt hd
  rw [hamiltonian_normalized_packet_cycle_readout]
  change (C * P / D) ^ 2 * ((X / P ^ 2) / d) = C ^ 2 * X
  calc
    _ = C ^ 2 * X / (D ^ 2 * d) := by
      field_simp [hP0, hD, hd0]
      <;> ring
    _ = _ := by rw [hCancel, div_one]

universe u

theorem stochastic_weighted_cycle_comparison_logarithmic_uniform
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
          abs (hamiltonianBipartiteCountRatio T - 1) <=
            (1 + hamiltonianPermanentCountAllowance (Fintype.card J) a delta) ^ 2 *
              hamiltonianSignedCountAllowance T q a delta +
            (2 + hamiltonianPermanentCountAllowance (Fintype.card J) a delta) *
              hamiltonianPermanentCountAllowance (Fintype.card J) a delta := by
  have hSignedRange := stochastic_relative_bipartite_comparison_logarithmic_uniform.{u}
    delta c hDelta hDelta1 hc
  have hPermanentRange := stochastic_permanent_relative_correction_fintype_uniform.{u}
    delta 2 hDelta hDelta1
  refine hSignedRange.elim ?_
  intro NS hNS
  refine hPermanentRange.elim ?_
  intro NP hNP
  let N0 := max NS (max NP (Nat.ceil (Real.exp (2 * c))))
  refine Exists.intro N0 (And.intro (le_trans hNS.1 (le_max_left _ _)) ?_)
  intro J instF instD instN hn T q a hq ha hA hRow hCol hNonneg hUpper hNorm
  have hnS : NS <= Fintype.card J := le_trans (le_max_left _ _) hn
  have hnP : NP <= Fintype.card J :=
    le_trans (le_trans (le_max_left NP _) (le_max_right NS _)) hn
  have hnCeil : Nat.ceil (Real.exp (2 * c)) <= Fintype.card J :=
    le_trans (le_trans (le_max_right NP _) (le_max_right NS _)) hn
  have hN256 : (256 : Real) <= Fintype.card J := by exact_mod_cast le_trans hNS.1 hnS
  have hN2 : (2 : Real) <= Fintype.card J := by linarith only [hN256]
  have hN : 0 < (Fintype.card J : Real) := by linarith only [hN256]
  have hExpN : Real.exp (2 * c) <= (Fintype.card J : Real) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hnCeil)
  have hLogNC : 2 * c <= Real.log (Fintype.card J : Real) := by
    have h := Real.log_le_log (Real.exp_pos _) hExpN
    simpa only [Real.log_exp] using h
  have hAPolyNat := hamiltonian_logarithmic_cap_square
    (Fintype.card J : Real) a c hN2 hc hLogNC hA
  have hRealTwo : (Real.log (Fintype.card J : Real)) ^ (2 : Real) =
      (Real.log (Fintype.card J : Real)) ^ (2 : Nat) := by
    simpa only [Nat.cast_ofNat] using Real.rpow_natCast (Real.log (Fintype.card J : Real)) 2
  have hAPoly : a <= (Real.log (Fintype.card J : Real)) ^ (2 : Real) := by
    rw [hRealTwo]
    exact hAPolyNat
  have hSigned := hNS.2 J hnS T q a hq ha hA hRow hCol hNonneg hUpper hNorm
  have hPermanent := hNP.2 J hnP T q a hq ha hAPoly hRow hCol hNonneg hUpper hNorm
  let r := hamiltonianNormalizedPermanent T q
  let u := hamiltonianNormalizedBipartitePacket T /
    Matrix.det ((1 : Matrix J J Real) -
      (centeredKernel T q).transpose * centeredKernel T q)
  let p := hamiltonianPermanentCountAllowance (Fintype.card J) a delta
  let e := hamiltonianSignedCountAllowance T q a delta
  let Q := stochasticPermanentFirstCorrection T q
  let C := hamiltonianPermanentUniformBudget delta
  have hp : 0 <= p := by dsimp only [p, hamiltonianPermanentCountAllowance]; positivity
  have hRem := hPermanent.1
  change abs (r - (1 + Q)) <= (1 + a) ^ 24 * C / (Fintype.card J : Real) ^ 2 at hRem
  have hBudget : (1 + a) ^ 24 * C / (Fintype.card J : Real) ^ 2 <=
      abs C * (1 + a) ^ 24 / (Fintype.card J : Real) ^ 2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    have h := mul_le_mul_of_nonneg_left (le_abs_self C) (by positivity : 0 <= (1 + a) ^ 24)
    nlinarith only [h]
  have hr : abs (r - 1) <= p := by
    have hIdentity : r - 1 = (r - (1 + Q)) + Q := by ring
    rw [hIdentity]
    have hTriangle := abs_add_le (r - (1 + Q)) Q
    have hQ := hPermanent.2
    change abs Q <= 21 * a ^ 2 / (delta ^ 3 * (Fintype.card J : Real)) at hQ
    change _ <= 21 * a ^ 2 / (delta ^ 3 * (Fintype.card J : Real)) +
      abs C * (1 + a) ^ 24 / (Fintype.card J : Real) ^ 2
    linarith only [hTriangle, hRem, hBudget, hQ]
  have hu : abs (u - 1) <= e := hSigned.2.2
  have hResult := hamiltonian_multiplicative_relative_error r u p e hp hr hu
  have hNormalize : r ^ 2 * u = hamiltonianBipartiteCountRatio T :=
    hamiltonian_weighted_cycle_normalization T q (ne_of_gt hSigned.1) hSigned.2.1
  rw [hNormalize] at hResult
  exact hResult

end PrimeFactorOscillations
