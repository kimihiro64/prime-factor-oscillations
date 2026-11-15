/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianMinorFirstOrderBudget
import PrimeFactorOscillations.Helpers.HamiltonianRootOccupancyBounds
import PrimeFactorOscillations.Helpers.HamiltonianSignedMinorFunctional

/-! # The actual full minor field in the signed consumer

The field is exactly the one retained in the uniform minor expansion.
Its coordinate bound consumes the existing repair-kernel certificate;
the complete first-order correction is matched on independent supports.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianMinorField (T : Matrix Iota Iota Real) (q : Real) : Sum Iota Iota -> Real :=
  let G := resolventCovariance (bipartiteLift (centeredKernel T q))
  let h := fun i => -G i i
  fun i => (1 / 2 : Real) * h i - (hamiltonianRepairKernel T q).mulVec h i

theorem hamiltonian_minor_first_order_as_support_correction
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (hCard : S.card = U.card) (q : Real) :
    hamiltonianMinorFirstOrder T S U q =
      hamiltonianSignedSupportCorrection
        (resolventCovariance (bipartiteLift (centeredKernel T q)))
        (hamiltonianMinorField T q) q (S.disjSum U) := by
  let D := S.disjSum U
  let u := hamiltonianDeletedSupportIndicator S U
  let G := resolventCovariance (bipartiteLift (centeredKernel T q))
  let v := hamiltonianMinorField T q
  have hIndicator : u = hamiltonianSupportIndicator D := by
    funext i
    cases i <;>
      simp [u, D, hamiltonianDeletedSupportIndicator, hamiltonianSupportIndicator]
  have hInner (i : Sum Iota Iota) : G.mulVec u i = D.sum (fun j => G i j) := by
    rw [hIndicator]
    change Finset.univ.sum (fun j => G i j * hamiltonianSupportIndicator D j) = _
    calc
      _ = Finset.univ.sum (fun j => hamiltonianSupportIndicator D j * G i j) :=
        Finset.sum_congr rfl (fun j _ => mul_comm _ _)
      _ = _ := hamiltonian_support_indicator_weighted_sum D _
  have hQuad : dotProduct u (G.mulVec u) = D.sum (fun i => D.sum (fun j => G i j)) := by
    change Finset.univ.sum (fun i => u i * G.mulVec u i) = _
    simp_rw [hInner]
    rw [hIndicator]
    exact hamiltonian_support_indicator_weighted_sum D _
  have hLinear : dotProduct v u = D.sum v := by
    rw [dotProduct_comm, hIndicator]
    exact hamiltonian_support_indicator_weighted_sum D v
  have hRank : (D.card : Real) / 2 = (U.card : Real) := by
    simp only [D, Finset.card_disjSum, hCard, Nat.cast_add]
    ring
  change (U.card : Real) * ((U.card : Real) - 1) * q +
      dotProduct u (G.mulVec u) + 2 * dotProduct v u =
    ((D.card : Real) / 2) * ((D.card : Real) / 2 - 1) * q +
      D.sum (fun i => D.sum (fun j => G i j)) + 2 * D.sum v
  rw [hQuad, hLinear, hRank]

variable [Nonempty Iota]

theorem stochastic_minor_field_coordinate_bound
    (T : Matrix Iota Iota Real) (q a rho : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1)
    (i : Sum Iota Iota) :
    (1 - rho) ^ 2 * abs (hamiltonianMinorField T q i) <= 19 * a ^ 2 * q := by
  let g := 1 - rho
  let G := resolventCovariance (bipartiteLift (centeredKernel T q))
  let h := fun j => -G j j
  let K := hamiltonianRepairKernel T q
  have hg : 0 < g := sub_pos.mpr hRho
  have hRho0 : 0 <= rho := le_trans (norm_nonneg _) hNorm
  have hg1 : g <= 1 := by dsimp only [g]; linarith only [hRho0]
  have ha0 : 0 <= a := le_trans (by norm_num) ha
  have hCard : 0 < (Fintype.card Iota : Real) := Nat.cast_pos.mpr Fintype.card_pos
  have hq0 : 0 <= q := by nlinarith only [hq, hCard]
  have haq : 0 <= a * q := mul_nonneg ha0 hq0
  have hBounds := stochastic_root_occupancy_coefficient_bounds T q a rho hq ha
    hRow hCol hNonneg hUpper hNorm hRho
  have hDiag (j : Sum Iota Iota) : g * abs (h j) <= 2 * a * q := by
    simpa only [h, abs_neg] using hBounds.1 j j
  have hFull : (Fintype.card (Sum Iota Iota) : Real) * q = 2 := by
    simp only [Fintype.card_sum, Nat.cast_add]
    nlinarith only [hq]
  have hMass : g * Finset.univ.sum (fun j => abs (h j)) <= 4 * a := by
    rw [Finset.mul_sum]
    calc
      _ <= Finset.univ.sum (fun _ : Sum Iota Iota => 2 * a * q) :=
        Finset.sum_le_sum (fun j _ => hDiag j)
      _ = 2 * a * ((Fintype.card (Sum Iota Iota) : Real) * q) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
      _ = _ := by rw [hFull]; ring
  have hKh := stochastic_repair_kernel_mulVec T q a rho hq ha
    hRow hCol hNonneg hUpper hNorm hRho h i
  change g * abs (K.mulVec h i) <= g * abs (h i) +
    4 * a * q * Finset.univ.sum (fun j => abs (h j)) at hKh
  have hScaled := mul_le_mul_of_nonneg_left hKh (le_of_lt hg)
  have hMassScaled := mul_le_mul_of_nonneg_left hMass (by nlinarith only [haq] : 0 <= 4 * a * q)
  have hDiagScaled := mul_le_mul_of_nonneg_left (hDiag i) (le_of_lt hg)
  have hGaq : g * (a * q) <= a ^ 2 * q := by
    have h := mul_le_mul_of_nonneg_right (le_trans hg1 ha) haq
    nlinarith only [h]
  have hKhFinal : g ^ 2 * abs (K.mulVec h i) <= 18 * a ^ 2 * q := by
    nlinarith only [hScaled, hMassScaled, hDiagScaled, hGaq]
  have hAbs := hamiltonian_abs_sub_bound ((1 / 2 : Real) * h i) (K.mulVec h i)
  rw [abs_mul, abs_of_pos (by norm_num : (0 : Real) < 1 / 2)] at hAbs
  have hAbsScaled := mul_le_mul_of_nonneg_left hAbs (sq_nonneg g)
  change g ^ 2 * abs ((1 / 2 : Real) * h i - K.mulVec h i) <= 19 * a ^ 2 * q
  nlinarith only [hAbsScaled, hKhFinal, hDiagScaled, hGaq]

end PrimeFactorOscillations
