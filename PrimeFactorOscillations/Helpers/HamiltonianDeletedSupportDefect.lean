/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianRepairKernel

/-! # The actual deleted-support defect and its linear compensation

The defect is exactly the bipartite kernel applied to the two independent
support indicators. Its full mass is the sum of their cardinalities.
The actual repair kernel therefore gives a dimension-uniform linear
scaling bound while leaving the quadratic compensation intact.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

def hamiltonianDeletedSupportIndicator (S U : Finset Iota) : Sum Iota Iota -> Real := by
  classical
  exact fun x => match x with
    | Sum.inl i => if Membership.mem S i then 1 else 0
    | Sum.inr j => if Membership.mem U j then 1 else 0

def hamiltonianDeletedSupportDefect (T : Matrix Iota Iota Real)
    (S U : Finset Iota) : Sum Iota Iota -> Real :=
  fun x => match x with
    | Sum.inl i => Finset.sum U (fun j => T i j)
    | Sum.inr j => Finset.sum S (fun i => T i j)

theorem hamiltonianDeletedSupportDefect_eq_mulVec
    (T : Matrix Iota Iota Real) (S U : Finset Iota) :
    hamiltonianDeletedSupportDefect T S U =
      (bipartiteLift T).mulVec (hamiltonianDeletedSupportIndicator S U) := by
  classical
  have hSelect (f : Iota -> Real) (W : Finset Iota) :
      Finset.sum Finset.univ (fun j => f j * (if Membership.mem W j then 1 else 0)) =
        Finset.sum W f := by
    simp only [mul_ite, mul_one, mul_zero, <- Finset.sum_filter]
    apply Finset.sum_congr
    next => apply Finset.ext; intro j; simp
    next => intro j hj; rfl
  apply funext
  intro x
  cases x with
  | inl i =>
    symm
    simpa [bipartiteLift, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Matrix.fromBlocks, hamiltonianDeletedSupportIndicator, hamiltonianDeletedSupportDefect]
        using hSelect (fun j => T i j) U
  | inr j =>
    symm
    simpa [bipartiteLift, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Matrix.fromBlocks, Matrix.transpose_apply, hamiltonianDeletedSupportIndicator,
      hamiltonianDeletedSupportDefect] using hSelect (fun i => T i j) S

theorem hamiltonianDeletedSupportDefect_nonnegative
    (T : Matrix Iota Iota Real) (S U : Finset Iota)
    (hNonneg : forall i j, 0 <= T i j) (x : Sum Iota Iota) :
    0 <= hamiltonianDeletedSupportDefect T S U x := by
  cases x with
  | inl i => exact Finset.sum_nonneg (fun j _ => hNonneg i j)
  | inr j => exact Finset.sum_nonneg (fun i _ => hNonneg i j)

theorem hamiltonianDeletedSupportDefect_half_masses
    (T : Matrix Iota Iota Real) (S U : Finset Iota)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1) :
    And
      (Finset.sum Finset.univ
        (fun i => hamiltonianDeletedSupportDefect T S U (Sum.inl i)) = (U.card : Real))
      (Finset.sum Finset.univ
        (fun j => hamiltonianDeletedSupportDefect T S U (Sum.inr j)) = (S.card : Real)) := by
  apply And.intro
  next =>
    change Finset.sum Finset.univ (fun i => Finset.sum U (fun j => T i j)) = _
    calc
      _ = Finset.sum U (fun j => Finset.sum Finset.univ (fun i => T i j)) :=
        Finset.sum_comm
      _ = _ := by simp [hCol]
  next =>
    change Finset.sum Finset.univ (fun j => Finset.sum S (fun i => T i j)) = _
    rw [Finset.sum_comm]
    simp [hRow]

theorem hamiltonianDeletedSupportDefect_abs_mass
    (T : Matrix Iota Iota Real) (S U : Finset Iota)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) :
    Finset.sum Finset.univ (fun x => abs (hamiltonianDeletedSupportDefect T S U x)) =
      (U.card : Real) + (S.card : Real) := by
  have hMasses := hamiltonianDeletedSupportDefect_half_masses T S U hRow hCol
  calc
    _ = Finset.sum Finset.univ (hamiltonianDeletedSupportDefect T S U) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact abs_of_nonneg (hamiltonianDeletedSupportDefect_nonnegative T S U hNonneg x)
    _ = _ := by
      rw [Fintype.sum_sum_type, hMasses.1, hMasses.2]

theorem hamiltonianDeletedSupportDefect_entry
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (hCard : S.card = U.card)
    (q a : Real) (hUpper : forall i j, T i j <= a * q) (x : Sum Iota Iota) :
    hamiltonianDeletedSupportDefect T S U x <= (U.card : Real) * a * q := by
  cases x with
  | inl i =>
    change Finset.sum U (fun j => T i j) <= _
    calc
      _ <= Finset.sum U (fun _ => a * q) := Finset.sum_le_sum (fun j _ => hUpper i j)
      _ = _ := by simp [mul_assoc]
  | inr j =>
    change Finset.sum S (fun i => T i j) <= _
    calc
      _ <= Finset.sum S (fun _ => a * q) := Finset.sum_le_sum (fun i _ => hUpper i j)
      _ = _ := by simp [hCard, mul_assoc]

variable [Nonempty Iota]

theorem stochastic_deleted_support_linear_repair
    (T : Matrix Iota Iota Real) (S U : Finset Iota) (hCard : S.card = U.card)
    (q a rho : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.sum Finset.univ (fun j => T i j) = 1)
    (hCol : forall j, Finset.sum Finset.univ (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1)
    (i : Sum Iota Iota) :
    (1 - rho) * abs ((hamiltonianRepairKernel T q).mulVec
      (hamiltonianDeletedSupportDefect T S U) i) <= 9 * (U.card : Real) * a * q := by
  let ell := hamiltonianDeletedSupportDefect T S U
  have hNonnegative : 0 <= ell i :=
    hamiltonianDeletedSupportDefect_nonnegative T S U hNonneg i
  have hMass := hamiltonianDeletedSupportDefect_abs_mass T S U hRow hCol hNonneg
  have hCap := hamiltonianDeletedSupportDefect_entry T S U hCard q a hUpper i
  have h := stochastic_repair_kernel_mulVec T q a rho hq ha
    hRow hCol hNonneg hUpper hNorm hRho ell i
  change (1 - rho) * abs ((hamiltonianRepairKernel T q).mulVec ell i) <=
    (1 - rho) * abs (ell i) +
      4 * a * q * Finset.sum Finset.univ (fun j => abs (hamiltonianDeletedSupportDefect T S U j))
        at h
  rw [abs_of_nonneg hNonnegative, hMass, hCard] at h
  have hRho0 : 0 <= rho := le_trans (norm_nonneg _) hNorm
  have hProduct : 0 <= rho * ell i := mul_nonneg hRho0 hNonnegative
  have hScaled : (1 - rho) * ell i <= ell i := by nlinarith only [hProduct]
  change (1 - rho) * abs ((hamiltonianRepairKernel T q).mulVec ell i) <= _
  nlinarith only [h, hCap, hScaled]

end PrimeFactorOscillations
