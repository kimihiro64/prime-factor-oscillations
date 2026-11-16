/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianDiffuseScaling

/-! # Exact weighted-mode control in degree normalization

The normalized Perron mode is kept. Its conjugate differs from the
constant averaging kernel by at most seven times the degree defect.
The complete original centered norm then costs at most eight defects.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem hamiltonian_near_one_product_ratio
    (r c t eps : Real) (he0 : 0 <= eps) (he1 : eps <= 1 / 2)
    (hr : abs (r - 1) <= eps) (hc : abs (c - 1) <= eps)
    (ht : abs (t - 1) <= eps) :
    abs (r * c / t - 1) <= 7 * eps := by
  have hrBounds := abs_le.mp hr
  have hcBounds := abs_le.mp hc
  have htBounds := abs_le.mp ht
  have hr0 : 0 <= r := by linarith only [hrBounds.1, he1]
  have hc0 : 0 <= c := by linarith only [hcBounds.1, he1]
  have ht0 : 0 < t := by linarith only [htBounds.1, he1]
  have hSmall : eps ^ 2 <= eps / 2 := by nlinarith only [he0, he1]
  have hLow := mul_le_mul
    (by linarith only [hrBounds.1] : 1 - eps <= r)
    (by linarith only [hcBounds.1] : 1 - eps <= c)
    (by linarith only [he1] : 0 <= 1 - eps) hr0
  have hHigh := mul_le_mul
    (by linarith only [hrBounds.2] : r <= 1 + eps)
    (by linarith only [hcBounds.2] : c <= 1 + eps)
    hc0 (by positivity : 0 <= 1 + eps)
  have hNumerator : abs (r * c - t) <= 3 * eps + eps ^ 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith only [hLow, hHigh, htBounds.1, htBounds.2, he0]
  have hProduct := mul_le_mul_of_nonneg_left
    (by linarith only [htBounds.1] : 1 - eps <= t) he0
  have hBudget : 3 * eps + eps ^ 2 <= (7 * eps) * t := by
    nlinarith only [hProduct, hSmall]
  have h := div_le_div_of_nonneg_right (hNumerator.trans hBudget) ht0.le
  have hCancel : ((7 * eps) * t) / t = 7 * eps := by field_simp [ne_of_gt ht0]
  have hId : r * c / t - 1 = (r * c - t) / t := by field_simp [ne_of_gt ht0]
  rw [hCancel] at h
  rw [hId, abs_div, abs_of_pos ht0]
  exact h

def hamiltonianDegreeReference (r c : Iota -> Real) (q t : Real) :
    Matrix Iota Iota Real := fun i j => q * r i * c j / t

theorem hamiltonian_degree_reference_error
    (r c : Iota -> Real) (q t eps : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (he0 : 0 <= eps) (he1 : eps <= 1 / 2)
    (hr : forall i, abs (r i - 1) <= eps)
    (hc : forall j, abs (c j - 1) <= eps)
    (ht : abs (t - 1) <= eps) :
    norm (hamiltonianDegreeReference r c q t - (averagingKernel q : Matrix Iota Iota Real)) <= 7 * eps := by
  have hn : 0 < (Fintype.card Iota : Real) := Nat.cast_pos.mpr Fintype.card_pos
  have hq0 : 0 <= q := by nlinarith only [hq, hn]
  have hEach (i j : Iota) :
      norm ((hamiltonianDegreeReference r c q t - (averagingKernel q : Matrix Iota Iota Real)) i j) <=
        7 * eps * q := by
    have hId : (hamiltonianDegreeReference r c q t - (averagingKernel q : Matrix Iota Iota Real)) i j =
        q * (r i * c j / t - 1) := by
      simp only [hamiltonianDegreeReference, averagingKernel, Matrix.sub_apply]
      ring
    rw [hId, Real.norm_eq_abs, abs_mul, abs_of_nonneg hq0]
    have h := mul_le_mul_of_nonneg_left
      (hamiltonian_near_one_product_ratio (r i) (c j) t eps he0 he1 (hr i) (hc j) ht) hq0
    nlinarith only [h]
  have hSum : Finset.univ.sum (fun _ : Iota => 7 * eps * q) = 7 * eps := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc
      _ = (7 * eps) * ((Fintype.card Iota : Real) * q) := by ring
      _ = _ := by rw [hq]; ring
  apply hamiltonian_l2_row_column_budget _ (7 * eps) (by positivity)
  . intro i
    exact (Finset.sum_le_sum (fun j _ => hEach i j)).trans_eq hSum
  . intro j
    exact (Finset.sum_le_sum (fun i _ => hEach i j)).trans_eq hSum

def hamiltonianDegreeNormalizedCross (T : Matrix Iota Iota Real)
    (r c : Iota -> Real) : Matrix Iota Iota Real :=
  fun i j => T i j / (Real.sqrt (r i) * Real.sqrt (c j))

def hamiltonianDegreeNormalizedMode (r c : Iota -> Real) (q t : Real) :
    Matrix Iota Iota Real :=
  fun i j => q * Real.sqrt (r i) * Real.sqrt (c j) / t

theorem hamiltonian_degree_conjugation_identity
    (T : Matrix Iota Iota Real) (r c : Iota -> Real) (q t : Real)
    (hr : forall i, 0 < r i) (hc : forall j, 0 < c j) :
    T = (Matrix.diagonal (fun i => Real.sqrt (r i)) *
      (hamiltonianDegreeNormalizedCross T r c - hamiltonianDegreeNormalizedMode r c q t)) *
      Matrix.diagonal (fun j => Real.sqrt (c j)) + hamiltonianDegreeReference r c q t := by
  ext i j
  simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.sub_apply, hamiltonianDegreeNormalizedCross, hamiltonianDegreeNormalizedMode,
    hamiltonianDegreeReference]
  rw [mul_sub, sub_mul]
  have hCancel : Real.sqrt (r i) *
      (T i j / (Real.sqrt (r i) * Real.sqrt (c j))) * Real.sqrt (c j) = T i j := by
    field_simp [ne_of_gt (Real.sqrt_pos.mpr (hr i)), ne_of_gt (Real.sqrt_pos.mpr (hc j))]
    <;> ring
  have hMode : Real.sqrt (r i) *
      (q * Real.sqrt (r i) * Real.sqrt (c j) / t) * Real.sqrt (c j) =
        q * r i * c j / t := by
    calc
      _ = q * (Real.sqrt (r i) * Real.sqrt (r i)) *
        (Real.sqrt (c j) * Real.sqrt (c j)) / t := by ring
      _ = _ := by rw [<- pow_two, Real.sq_sqrt (hr i).le,
        <- pow_two, Real.sq_sqrt (hc j).le]
  rw [hCancel, hMode]
  ring

theorem hamiltonian_degree_conjugation_norm
    (N : Matrix Iota Iota Real) (r c : Iota -> Real) (eps rho : Real)
    (he : 0 <= eps) (hp : 0 <= rho) (hN : norm N <= rho)
    (hr : forall i, r i <= 1 + eps) (hc : forall j, c j <= 1 + eps) :
    norm ((Matrix.diagonal (fun i => Real.sqrt (r i)) * N) *
      Matrix.diagonal (fun j => Real.sqrt (c j))) <= (1 + eps) * rho := by
  let s := Real.sqrt (1 + eps)
  have hs : 0 <= s := Real.sqrt_nonneg _
  have hL : norm (Matrix.diagonal (fun i => Real.sqrt (r i))) <= s := by
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg hs).mpr
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (hr i)
  have hR : norm (Matrix.diagonal (fun j => Real.sqrt (c j))) <= s := by
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg hs).mpr
    intro j
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (hc j)
  have hFirst := Matrix.l2_opNorm_mul (Matrix.diagonal (fun i => Real.sqrt (r i))) N
  have hFirstBound : norm (Matrix.diagonal (fun i => Real.sqrt (r i)) * N) <= s * rho :=
    hFirst.trans (mul_le_mul hL hN (norm_nonneg _) hs)
  calc
    _ <= norm (Matrix.diagonal (fun i => Real.sqrt (r i)) * N) *
      norm (Matrix.diagonal (fun j => Real.sqrt (c j))) := Matrix.l2_opNorm_mul _ _
    _ <= (s * rho) * s := mul_le_mul hFirstBound hR (norm_nonneg _) (mul_nonneg hs hp)
    _ = (s * s) * rho := by ring
    _ = _ := by
      rw [<- pow_two]
      dsimp [s]
      rw [Real.sq_sqrt (by positivity : 0 <= 1 + eps)]

theorem hamiltonian_normalized_degree_centered_gap
    (T : Matrix Iota Iota Real) (r c : Iota -> Real) (q t eps rho : Real)
    (hq : (Fintype.card Iota : Real) * q = 1)
    (he0 : 0 <= eps) (he1 : eps <= 1 / 2)
    (hp0 : 0 <= rho) (hp1 : rho <= 1)
    (hr : forall i, abs (r i - 1) <= eps)
    (hc : forall j, abs (c j - 1) <= eps)
    (ht : abs (t - 1) <= eps)
    (hNorm : norm (hamiltonianDegreeNormalizedCross T r c -
      hamiltonianDegreeNormalizedMode r c q t) <= rho) :
    norm (centeredKernel T q) <= rho + 8 * eps := by
  have hrPos (i : Iota) : 0 < r i := by
    have h := (abs_le.mp (hr i)).1
    linarith only [h, he1]
  have hcPos (j : Iota) : 0 < c j := by
    have h := (abs_le.mp (hc j)).1
    linarith only [h, he1]
  let N := hamiltonianDegreeNormalizedCross T r c - hamiltonianDegreeNormalizedMode r c q t
  let D := (Matrix.diagonal (fun i => Real.sqrt (r i)) * N) *
    Matrix.diagonal (fun j => Real.sqrt (c j))
  have hD : norm D <= (1 + eps) * rho :=
    hamiltonian_degree_conjugation_norm N r c eps rho he0 hp0 hNorm
      (fun i => by linarith only [(abs_le.mp (hr i)).2])
      (fun j => by linarith only [(abs_le.mp (hc j)).2])
  have hR := hamiltonian_degree_reference_error r c q t eps hq he0 he1 hr hc ht
  have hId : centeredKernel T q =
      D + (hamiltonianDegreeReference r c q t - (averagingKernel q : Matrix Iota Iota Real)) := by
    change T - (averagingKernel q : Matrix Iota Iota Real) = _
    have h := hamiltonian_degree_conjugation_identity T r c q t hrPos hcPos
    change T = D + hamiltonianDegreeReference r c q t at h
    rw [h]
    abel
  rw [hId]
  have hTriangle := norm_add_le D (hamiltonianDegreeReference r c q t - (averagingKernel q : Matrix Iota Iota Real))
  have hCost := mul_le_mul_of_nonneg_right hp1 he0
  nlinarith only [hTriangle, hD, hR, hCost]

end PrimeFactorOscillations
