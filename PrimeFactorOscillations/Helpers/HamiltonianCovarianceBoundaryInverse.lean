/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianBlockCovariance
import PrimeFactorOscillations.Helpers.HamiltonianBoundaryBudgets

/-! # Actual retained covariance inverse with uniform row budgets

The retained inverse is the complete signed Schur complement of the
full inverse. Only its explicit boundary correction is estimated.
The final theorem derives the inverse equation, entry error and row
bound from the original stochastic matrix.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_resolvent_one_sub (Q : Matrix Iota Iota Real)
    (hUnit : IsUnit ((1 : Matrix Iota Iota Real) + Q)) :
    Ring.inverse (1 + Q) = 1 - Q * Ring.inverse (1 + Q) := by
  apply eq_sub_iff_add_eq.mpr
  have h := Ring.mul_inverse_cancel ((1 : Matrix Iota Iota Real) + Q) hUnit
  simpa only [add_mul, one_mul] using h

theorem hamiltonianBoundaryKernel_actual_inverse
    (H K : Matrix Iota Iota Real) (D : Finset Iota) (hInverse : H * K = 1)
    (hUnit : IsUnit (K.submatrix (fun d : D => d.val) (fun d : D => d.val))) :
    H.submatrix (fun r : (Compl.compl D : Finset Iota) => r.val)
      (fun r : (Compl.compl D : Finset Iota) => r.val) *
        hamiltonianBoundaryKernel K D = 1 := by
  let rr := fun r : (Compl.compl D : Finset Iota) => (r.val : Iota)
  let rd := fun d : D => (d.val : Iota)
  have hRR : (1 : Matrix Iota Iota Real).submatrix rr rr = 1 := by
    apply Matrix.ext
    intro i j
    simp only [rr, Matrix.submatrix_apply, Matrix.one_apply, Subtype.ext_iff]
  have hRD : (1 : Matrix Iota Iota Real).submatrix rr rd = 0 := by
    apply Matrix.ext
    intro i d
    have hne : Not (i.val = d.val) := by
      intro h
      have hm : Membership.mem D i.val := by rw [h]; exact d.property
      exact (Finset.mem_compl.mp i.property) hm
    simp only [rr, rd, Matrix.submatrix_apply, Matrix.one_apply, Matrix.zero_apply,
      ite_eq_right hne]
  have h := hamiltonianBoundaryKernel_inverse_equation H K D hUnit
  rw [hInverse, hRR, hRD, Matrix.zero_mul, Matrix.zero_mul, sub_zero] at h
  exact h

theorem hamiltonian_close_identity_boundary_budgets
    (K : Matrix Iota Iota Real) (D : Finset Iota) (c : Real) (hc : 0 <= c)
    (hEntry : forall i j, abs ((K - 1) i j) <= c)
    (hSmall : (D.card : Real) * c <= 1 / 2) :
    IsUnit (K.submatrix (fun d : D => d.val) (fun d : D => d.val)) /\
    (forall i j : (Compl.compl D : Finset Iota),
      abs (hamiltonianBoundaryKernel K D i j - K i.val j.val) <=
        2 * (D.card : Real) * c ^ 2) /\
    forall i : (Compl.compl D : Finset Iota),
      Finset.sum Finset.univ (fun j => abs (hamiltonianBoundaryKernel K D i j)) <=
        1 + (Fintype.card Iota : Real) * c +
          ((Compl.compl D : Finset Iota).card : Real) * (2 * (D.card : Real) * c ^ 2) := by
  let KD := K.submatrix (fun d : D => d.val) (fun d : D => d.val)
  have hInv : IsUnit KD /\
      forall i : D, Finset.sum Finset.univ (fun j : D => abs (Ring.inverse KD i j)) <= 2 := by
    apply matrix_row_half_inverse KD
    intro i
    have hEach (j : D) : abs ((KD - 1) i j) <= c := by
      simpa only [KD, Matrix.sub_apply, Matrix.submatrix_apply,
        Matrix.one_apply, Subtype.ext_iff] using hEntry i.val j.val
    calc
      _ <= Finset.sum Finset.univ (fun _ : D => c) :=
        Finset.sum_le_sum (fun j _ => hEach j)
      _ = (D.card : Real) * c := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      _ <= _ := hSmall
  have hOff (i j : Iota) (hne : Not (i = j)) : abs (K i j) <= c := by
    have h := hEntry i j
    simpa only [Matrix.sub_apply, Matrix.one_apply, ite_eq_right hne, sub_zero] using h
  have hLeft (i : (Compl.compl D : Finset Iota)) (d : D) : abs (K i.val d.val) <= c := by
    apply hOff
    intro h
    have hm : Membership.mem D i.val := by rw [h]; exact d.property
    exact (Finset.mem_compl.mp i.property) hm
  have hRight (d : D) (i : (Compl.compl D : Finset Iota)) : abs (K d.val i.val) <= c := by
    apply hOff
    intro h
    have hm : Membership.mem D i.val := by rw [<- h]; exact d.property
    exact (Finset.mem_compl.mp i.property) hm
  have hError (i j : (Compl.compl D : Finset Iota)) :
      abs (hamiltonianBoundaryKernel K D i j - K i.val j.val) <=
        2 * (D.card : Real) * c ^ 2 :=
    hamiltonianBoundaryKernel_entry_error K D c hc hLeft hRight hInv.2 i j
  have hRow (i : Iota) :
      Finset.sum Finset.univ (fun j => abs (K i j)) <=
        1 + (Fintype.card Iota : Real) * c := by
    have hEach (j : Iota) : abs (K i j) <= abs ((1 : Matrix Iota Iota Real) i j) + c := by
      have hTriangle := abs_add_le ((K - 1) i j) ((1 : Matrix Iota Iota Real) i j)
      have hEq : (K - 1) i j + (1 : Matrix Iota Iota Real) i j = K i j := by
        simp only [Matrix.sub_apply]; ring
      rw [hEq] at hTriangle
      linarith only [hTriangle, hEntry i j]
    calc
      _ <= Finset.sum Finset.univ (fun j => abs ((1 : Matrix Iota Iota Real) i j) + c) :=
        Finset.sum_le_sum (fun j _ => hEach j)
      _ = _ := by simp [Finset.sum_add_distrib, Matrix.one_apply, abs_ite]
  refine And.intro hInv.1 (And.intro hError ?_)
  intro i
  exact hamiltonianBoundaryKernel_row_bound K D _ _ hRow hError i

variable [Nonempty Iota]

theorem stochastic_retained_covariance_inverse_budgets
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (hCard : S.card = U.card)
    (q a rho : Real) (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1)
    (hSmall : (U.card : Real) * a ^ 2 * q / (1 - rho) ^ 2 <= 1 / 1000) :
    let D := S.disjSum U
    let R : Finset (Sum Iota Iota) := Compl.compl D
    let Omega := bipartiteLift (centeredKernel T q)
    let H := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) + Omega
    let K := Ring.inverse H
    let J := hamiltonianBoundaryKernel K D
    H.submatrix (fun i : R => i.val) (fun i : R => i.val) * J = 1 /\
    (forall i j : R, abs (J i j - K i.val j.val) <=
      16 * (U.card : Real) * (a / (1 - rho)) ^ 2 * q ^ 2) /\
    forall i : R, Finset.sum Finset.univ (fun j => abs (J i j)) <= 6 * (a / (1 - rho)) := by
  let delta := 1 - rho
  let r : Real := U.card
  let p := a / delta
  let t := r * p * q
  let c := 2 * p * q
  let D := S.disjSum U
  let R : Finset (Sum Iota Iota) := Compl.compl D
  let Omega := bipartiteLift (centeredKernel T q)
  let H := (1 : Matrix (Sum Iota Iota) (Sum Iota Iota) Real) + Omega
  let K := Ring.inverse H
  let Gamma := Omega * K
  let J := hamiltonianBoundaryKernel K D
  have hDelta : 0 < delta := sub_pos.mpr hRho
  have hDen : Not (delta = 0) := ne_of_gt hDelta
  have hRho0 : 0 <= rho := le_trans (norm_nonneg _) hNorm
  have hDelta1 : delta <= 1 := by dsimp only [delta]; linarith only [hRho0]
  have ha0 : 0 <= a := le_trans (by norm_num) ha
  have hN : 0 < (Fintype.card Iota : Real) := Nat.cast_pos.mpr Fintype.card_pos
  have hq0 : 0 <= q := by nlinarith only [hq, hN]
  have hr : 0 <= r := Nat.cast_nonneg _
  have hp0 : 0 <= p := div_nonneg ha0 (le_of_lt hDelta)
  have hpClear : delta * p = a := by dsimp only [p]; field_simp
  have hp : 1 <= p := by nlinarith only [hpClear, hDelta1, hp0, ha]
  have ht : 0 <= t := by dsimp only [t]; positivity
  have hc : 0 <= c := by dsimp only [c]; positivity
  have hPt : p * t <= 1 / 1000 := by
    have hEq : p * t = r * a ^ 2 * q / delta ^ 2 := by dsimp only [p, t]; field_simp
    rw [hEq]
    exact hSmall
  have htSmall : t <= 1 / 1000 := by
    have hMul := mul_le_mul_of_nonneg_right hp ht
    nlinarith only [hMul, hPt]
  have hDCard : (D.card : Real) = 2 * r := by
    simp only [D, Finset.card_disjSum, hCard, Nat.cast_add, r]
    ring
  have hUnit : IsUnit H := by
    have hOmegaNorm : norm Omega <= rho :=
      le_trans (bipartiteLift_l2_norm_le _) hNorm
    have hNeg : norm (-Omega) < 1 := by rw [norm_neg]; exact lt_of_le_of_lt hOmegaNorm hRho
    simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one hNeg
  have hInverse : H * K = 1 := Ring.mul_inverse_cancel _ hUnit
  have hKernel : K = 1 - Gamma := hamiltonian_resolvent_one_sub Omega hUnit
  have hGamma (i j : Sum Iota Iota) : abs (Gamma i j) <= c := by
    have h := stochastic_block_covariance_entry_bound T q a rho hq ha
      hRow hCol hNonneg hUpper hRho hNorm i j
    change delta * norm (Gamma i j) <= (2 - rho) * (a * q) at h
    rw [Real.norm_eq_abs] at h
    have hSigned := mul_nonneg hRho0 (mul_nonneg ha0 hq0)
    have hClear : delta * c = 2 * a * q := by dsimp only [c]; rw [<- hpClear]; ring
    nlinarith only [h, hSigned, hClear, hDelta]
  have hEntry (i j : Sum Iota Iota) : abs ((K - 1) i j) <= c := by
    have hDiff : K - 1 = -Gamma := by rw [hKernel]; abel
    rw [hDiff, Matrix.neg_apply, abs_neg]
    exact hGamma i j
  have hSmallD : (D.card : Real) * c <= 1 / 2 := by
    have hEq : (D.card : Real) * c = 4 * t := by
      rw [hDCard]
      dsimp only [c, t]
      ring
    rw [hEq]
    linarith only [htSmall]
  have hBudgets := hamiltonian_close_identity_boundary_budgets K D c hc hEntry hSmallD
  have hErrorEq : 2 * (D.card : Real) * c ^ 2 = 16 * r * p ^ 2 * q ^ 2 := by
    rw [hDCard]
    dsimp only [c]
    ring
  have hFullQ : (Fintype.card (Sum Iota Iota) : Real) * q = 2 := by
    simp only [Fintype.card_sum, Nat.cast_add]
    nlinarith only [hq]
  have hFullC : (Fintype.card (Sum Iota Iota) : Real) * c = 4 * p := by
    dsimp only [c]
    nlinarith only [congrArg (fun x : Real => x * (2 * p)) hFullQ]
  have hRCard : (R.card : Real) <= (Fintype.card (Sum Iota Iota) : Real) := by
    have h : (R.card : Real) <= ((Finset.univ : Finset (Sum Iota Iota)).card : Real) :=
      Nat.cast_le.mpr (Finset.card_le_card (Finset.subset_univ R))
    simpa only [Finset.card_univ] using h
  have hRQ : (R.card : Real) * q <= 2 := by
    nlinarith only [mul_le_mul_of_nonneg_right hRCard hq0, hFullQ]
  have hExtra : (R.card : Real) * (16 * r * p ^ 2 * q ^ 2) <= p := by
    calc
      _ = (16 * r * p ^ 2 * q) * ((R.card : Real) * q) := by ring
      _ <= (16 * r * p ^ 2 * q) * 2 :=
        mul_le_mul_of_nonneg_left hRQ (by positivity)
      _ = 32 * p * t := by dsimp only [t]; ring
      _ <= p := by
        have h := mul_le_mul_of_nonneg_left htSmall hp0
        nlinarith only [h, hp0]
  refine And.intro (hamiltonianBoundaryKernel_actual_inverse H K D hInverse hBudgets.1)
    (And.intro ?_ ?_)
  case refine_1 =>
    intro i j
    have h := hBudgets.2.1 i j
    rw [hErrorEq] at h
    exact h
  case refine_2 =>
    intro i
    have h := hBudgets.2.2 i
    rw [hFullC, hErrorEq] at h
    change Finset.sum Finset.univ (fun j => abs (J i j)) <= 6 * p
    nlinarith only [h, hExtra, hp]

end PrimeFactorOscillations
