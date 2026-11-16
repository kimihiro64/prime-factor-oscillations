/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPrescribedPathMinor
import PrimeFactorOscillations.Helpers.HamiltonianRepairedPermanentTransport

/-! # Retaining the actual row-mass deficit in Hamiltonian avoidance

Row normalization preserves its complete product of row sums.
Halving marked edges keeps every avoiding cycle unchanged while
creating an explicit deficit. The resulting exponential suppression
is retained beside the existing row-cap cost.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

omit [DecidableEq Iota] in
theorem hamiltonian_positive_product_deficit
    (s : Iota -> Real) (hPos : forall i, 0 < s i) :
    Finset.univ.prod s <=
      Real.exp (-Finset.univ.sum (fun i => 1 - s i)) := by
  calc
    _ = Real.exp (Finset.univ.sum (fun i => Real.log (s i))) := by
      rw [Real.exp_sum]
      apply Finset.prod_congr rfl
      intro i hi
      exact (Real.exp_log (hPos i)).symm
    _ <= Real.exp (Finset.univ.sum (fun i => s i - 1)) := by
      apply Real.exp_le_exp.mpr
      exact Finset.sum_le_sum (fun i hi => Real.log_le_sub_one_of_pos (hPos i))
    _ = _ := by
      congr 1
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one]
      ring

theorem hamiltonian_permanent_row_mass_upper
    (M : Matrix Iota Iota Real) (a X r : Real)
    (ha : 1 <= a) (hX1 : 1 <= X) (hX : (Fintype.card Iota : Real) <= X)
    (hr : 0 < r) (hr1 : r <= 1)
    (hNonneg : forall i j, 0 <= M i j)
    (hRowLower : forall i, r <= Finset.univ.sum (fun j => M i j))
    (hCap : forall i j, M i j <= a / X) :
    finitePermutationSum M <=
      Real.exp (-(Fintype.card Iota : Real) -
        Finset.univ.sum (fun i => 1 - Finset.univ.sum (fun j => M i j)) +
          16 * (a / r) * Real.log (2 * X)) := by
  let s := fun i => Finset.univ.sum (fun j => M i j)
  let A : Matrix Iota Iota Real := fun i j => M i j / s i
  have hS (i : Iota) : 0 < s i := hr.trans_le (hRowLower i)
  have ha0 : 0 <= a := le_trans (by norm_num) ha
  have hX0 : 0 <= X := le_trans (by norm_num) hX1
  have hAR : 1 <= a / r := by
    have hRatio0 : 0 <= a / r := div_nonneg ha0 hr.le
    have hProduct := mul_le_mul_of_nonneg_right hr1 hRatio0
    have hClear : r * (a / r) = a := by field_simp [ne_of_gt hr]
    nlinarith only [hProduct, hClear, ha]
  have hA0 (i j : Iota) : 0 <= A i j := div_nonneg (hNonneg i j) (hS i).le
  have hARow (i : Iota) : Finset.univ.sum (fun j => A i j) = 1 := by
    change Finset.univ.sum (fun j => M i j / s i) = 1
    rw [<- Finset.sum_div]
    exact div_self (ne_of_gt (hS i))
  have hACap (i j : Iota) : A i j <= (a / r) / X := by
    calc
      _ <= (a / X) / s i := div_le_div_of_nonneg_right (hCap i j) (hS i).le
      _ <= (a / X) / r := div_le_div_of_nonneg_left (div_nonneg ha0 hX0) hr (hRowLower i)
      _ = _ := by ring
  have hUpper := hamiltonian_finite_permanent_row_cap_upper A.transpose (a / r) X
    hAR hX1 hX (fun i j => hA0 j i) (fun j => le_of_eq (hARow j))
    (fun i j => hACap j i)
  rw [finitePermutationSum_transpose] at hUpper
  have hMatrix : (fun i j => s i * A i j * (1 : Real)) = M := by
    ext i j
    dsimp only [A]
    field_simp [ne_of_gt (hS i)]
  have hScale := finitePermutationSum_diagonal_scale A s (fun _ => (1 : Real))
  rw [hMatrix] at hScale
  simp only [Finset.prod_const_one, mul_one] at hScale
  have hProd0 : 0 <= Finset.univ.prod s :=
    Finset.prod_nonneg (fun i hi => (hS i).le)
  have hDeficit := hamiltonian_positive_product_deficit s hS
  rw [hScale]
  calc
    _ <= (Finset.univ.prod s) *
        Real.exp (-(Fintype.card Iota : Real) + 16 * (a / r) * Real.log (2 * X)) :=
      mul_le_mul_of_nonneg_left hUpper hProd0
    _ <= Real.exp (-Finset.univ.sum (fun i => 1 - s i)) *
        Real.exp (-(Fintype.card Iota : Real) + 16 * (a / r) * Real.log (2 * X)) :=
      mul_le_mul_of_nonneg_right hDeficit (Real.exp_pos _).le
    _ = _ := by
      rw [<- Real.exp_add]
      congr 1
      ring

def hamiltonianMarkedEdgeMass (M : Matrix Iota Iota Real)
    (E : Iota -> Iota -> Prop) [DecidableRel E] : Real :=
  Finset.univ.sum (fun i => Finset.univ.sum (fun j => if E i j then M i j else 0))

def hamiltonianHalfMarkedKernel (M : Matrix Iota Iota Real)
    (E : Iota -> Iota -> Prop) [DecidableRel E] : Matrix Iota Iota Real :=
  fun i j => if E i j then M i j / 2 else M i j

def hamiltonianAvoidingKernel (M : Matrix Iota Iota Real)
    (E : Iota -> Iota -> Prop) [DecidableRel E] : Matrix Iota Iota Real :=
  fun i j => if E i j then 0 else M i j

omit [DecidableEq Iota] in
theorem hamiltonian_half_marked_row_identity
    (M : Matrix Iota Iota Real) (E : Iota -> Iota -> Prop) [DecidableRel E] (i : Iota) :
    Finset.univ.sum (fun j => hamiltonianHalfMarkedKernel M E i j) =
      Finset.univ.sum (fun j => M i j) -
        Finset.univ.sum (fun j => if E i j then M i j else 0) / 2 := by
  have hPoint (j : Iota) : hamiltonianHalfMarkedKernel M E i j =
      M i j - (if E i j then M i j else 0) / 2 := by
    unfold hamiltonianHalfMarkedKernel
    split_ifs <;> ring
  simp_rw [hPoint]
  rw [Finset.sum_sub_distrib, Finset.sum_div]

theorem hamiltonian_half_marked_permanent_upper
    (M : Matrix Iota Iota Real) (E : Iota -> Iota -> Prop) [DecidableRel E]
    (a X : Real) (ha : 1 <= a) (hX1 : 1 <= X)
    (hX : (Fintype.card Iota : Real) <= X)
    (hNonneg : forall i j, 0 <= M i j)
    (hRowLower : forall i, 1 / 2 <= Finset.univ.sum (fun j => M i j))
    (hRowUpper : forall i, Finset.univ.sum (fun j => M i j) <= 1)
    (hCap : forall i j, M i j <= a / X) :
    finitePermutationSum (hamiltonianHalfMarkedKernel M E) <=
      Real.exp (-(Fintype.card Iota : Real) -
        hamiltonianMarkedEdgeMass M E / 2 + 64 * a * Real.log (2 * X)) := by
  let K := hamiltonianHalfMarkedKernel M E
  let mass := fun i => Finset.univ.sum (fun j => if E i j then M i j else 0)
  have hMassLe (i : Iota) : mass i <= Finset.univ.sum (fun j => M i j) := by
    apply Finset.sum_le_sum
    intro j hj
    split_ifs
    next => exact le_refl _
    next => exact hNonneg i j
  have hK0 (i j : Iota) : 0 <= K i j := by
    dsimp only [K, hamiltonianHalfMarkedKernel]
    split_ifs
    next => exact div_nonneg (hNonneg i j) (by norm_num)
    next => exact hNonneg i j
  have hKLe (i j : Iota) : K i j <= M i j := by
    dsimp only [K, hamiltonianHalfMarkedKernel]
    split_ifs
    next => linarith only [hNonneg i j]
    next => exact le_refl _
  have hKRowLower (i : Iota) : 1 / 4 <= Finset.univ.sum (fun j => K i j) := by
    rw [hamiltonian_half_marked_row_identity]
    have h := hMassLe i
    have hRow := hRowLower i
    change mass i <= _ at h
    change 1 / 4 <= Finset.univ.sum (fun j => M i j) - mass i / 2
    linarith only [h, hRow]
  have hDeficit :
      hamiltonianMarkedEdgeMass M E / 2 <=
        Finset.univ.sum (fun i => 1 - Finset.univ.sum (fun j => K i j)) := by
    have hPoint (i : Iota) : mass i / 2 <= 1 - Finset.univ.sum (fun j => K i j) := by
      rw [hamiltonian_half_marked_row_identity]
      change mass i / 2 <= 1 - (Finset.univ.sum (fun j => M i j) - mass i / 2)
      linarith only [hRowUpper i]
    have hSum : Finset.univ.sum (fun i => mass i / 2) <=
        Finset.univ.sum (fun i => 1 - Finset.univ.sum (fun j => K i j)) :=
      Finset.sum_le_sum (fun i hi => hPoint i)
    rw [<- Finset.sum_div] at hSum
    exact hSum
  have h := hamiltonian_permanent_row_mass_upper K a X (1 / 4) ha hX1 hX
    (by norm_num) (by norm_num) hK0 hKRowLower
    (fun i j => (hKLe i j).trans (hCap i j))
  have hConstant : 16 * (a / (1 / 4)) * Real.log (2 * X) =
      64 * a * Real.log (2 * X) := by ring
  rw [hConstant] at h
  exact h.trans (Real.exp_le_exp.mpr (by linarith only [hDeficit]))

theorem hamiltonian_cycle_sum_mono
    (M K : Matrix Iota Iota Real)
    (hNonneg : forall i j, 0 <= M i j) (hLe : forall i j, M i j <= K i j) :
    hamiltonianCycleSum M <= hamiltonianCycleSum K := by
  unfold hamiltonianCycleSum
  apply Finset.sum_le_sum
  intro f hf
  split_ifs
  next =>
    have hProduct (S : Finset Iota) :
        S.prod (fun i => M (f i) i) <= S.prod (fun i => K (f i) i) := by
      induction S using Finset.induction_on with
      | empty => simp only [Finset.prod_empty, le_refl]
      | @insert i S hi ih =>
        rw [Finset.prod_insert hi, Finset.prod_insert hi]
        exact mul_le_mul (hLe (f i) i) ih
          (Finset.prod_nonneg (fun j hj => hNonneg (f j) j))
          ((hNonneg (f i) i).trans (hLe (f i) i))
    exact hProduct Finset.univ
  next => exact le_refl 0

theorem hamiltonian_avoiding_cycle_row_mass_upper
    (M : Matrix Iota Iota Real) (E : Iota -> Iota -> Prop) [DecidableRel E]
    (a X : Real) (ha : 1 <= a) (hX1 : 1 <= X)
    (hX : (Fintype.card Iota : Real) <= X)
    (hNonneg : forall i j, 0 <= M i j)
    (hRowLower : forall i, 1 / 2 <= Finset.univ.sum (fun j => M i j))
    (hRowUpper : forall i, Finset.univ.sum (fun j => M i j) <= 1)
    (hCap : forall i j, M i j <= a / X) :
    hamiltonianCycleSum (hamiltonianAvoidingKernel M E) <=
      Real.exp (-(Fintype.card Iota : Real) -
        hamiltonianMarkedEdgeMass M E / 2 + 64 * a * Real.log (2 * X)) := by
  have hAvoid0 (i j : Iota) : 0 <= hamiltonianAvoidingKernel M E i j := by
    unfold hamiltonianAvoidingKernel
    split_ifs
    next => exact le_refl 0
    next => exact hNonneg i j
  have hHalf0 (i j : Iota) : 0 <= hamiltonianHalfMarkedKernel M E i j := by
    unfold hamiltonianHalfMarkedKernel
    split_ifs
    next => exact div_nonneg (hNonneg i j) (by norm_num)
    next => exact hNonneg i j
  have hLe (i j : Iota) :
      hamiltonianAvoidingKernel M E i j <= hamiltonianHalfMarkedKernel M E i j := by
    unfold hamiltonianAvoidingKernel hamiltonianHalfMarkedKernel
    split_ifs
    next => exact div_nonneg (hNonneg i j) (by norm_num)
    next => exact le_refl _
  exact (hamiltonian_cycle_sum_mono _ _ hAvoid0 hLe).trans
    ((hamiltonian_cycle_sum_le_permanent _ hHalf0).trans
      (hamiltonian_half_marked_permanent_upper M E a X ha hX1 hX
        hNonneg hRowLower hRowUpper hCap))


def hamiltonianMarkedCycleSum (M : Matrix Iota Iota Real)
    (E : Iota -> Iota -> Prop) [DecidableRel E] : Real := by
  classical
  exact Finset.univ.sum (fun f : Equiv.Perm Iota =>
    if (hamiltonianPermutationOrbits f).card = 1 /\ exists i, E (f i) i then
      Finset.univ.prod (fun i => M (f i) i) else 0)

theorem hamiltonian_marked_cycle_exact_complement
    (M : Matrix Iota Iota Real) (E : Iota -> Iota -> Prop) [DecidableRel E] :
    hamiltonianMarkedCycleSum M E =
      hamiltonianCycleSum M - hamiltonianCycleSum (hamiltonianAvoidingKernel M E) := by
  classical
  unfold hamiltonianMarkedCycleSum hamiltonianCycleSum
  rw [<- Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro f hf
  by_cases hOrbit : (hamiltonianPermutationOrbits f).card = 1
  case pos =>
    by_cases hMarked : exists i, E (f i) i
    case pos =>
      let i := hMarked.choose
      have hi : E (f i) i := hMarked.choose_spec
      have hZero : Finset.univ.prod (fun j => hamiltonianAvoidingKernel M E (f j) j) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp only [hamiltonianAvoidingKernel, ite_eq_left hi]
      simp only [hOrbit, hMarked, and_self, ite_true, hZero, sub_zero]
    case neg =>
      have hProduct : Finset.univ.prod (fun j => hamiltonianAvoidingKernel M E (f j) j) =
          Finset.univ.prod (fun j => M (f j) j) := by
        apply Finset.prod_congr rfl
        intro j hj
        have hNot : Not (E (f j) j) := fun h => hMarked (Exists.intro j h)
        simp only [hamiltonianAvoidingKernel, ite_eq_right hNot]
      simp only [hOrbit, hMarked, and_false, ite_true, ite_false, hProduct, sub_self]
  case neg =>
    simp only [hOrbit, false_and, ite_false, sub_zero]

theorem hamiltonian_marked_cycle_mass_lower
    (M : Matrix Iota Iota Real) (E : Iota -> Iota -> Prop) [DecidableRel E]
    (a X : Real) (ha : 1 <= a) (hX1 : 1 <= X)
    (hX : (Fintype.card Iota : Real) <= X)
    (hNonneg : forall i j, 0 <= M i j)
    (hRowLower : forall i, 1 / 2 <= Finset.univ.sum (fun j => M i j))
    (hRowUpper : forall i, Finset.univ.sum (fun j => M i j) <= 1)
    (hCap : forall i j, M i j <= a / X) :
    hamiltonianCycleSum M -
        Real.exp (-(Fintype.card Iota : Real) -
          hamiltonianMarkedEdgeMass M E / 2 + 64 * a * Real.log (2 * X)) <=
      hamiltonianMarkedCycleSum M E := by
  rw [hamiltonian_marked_cycle_exact_complement]
  have h := hamiltonian_avoiding_cycle_row_mass_upper M E a X ha hX1 hX
    hNonneg hRowLower hRowUpper hCap
  linarith only [h]

theorem hamiltonian_marked_cycle_exists_of_pos
    (M : Matrix Iota Iota Real) (E : Iota -> Iota -> Prop) [DecidableRel E]
    (hPositive : 0 < hamiltonianMarkedCycleSum M E) :
    exists f : Equiv.Perm Iota,
      (hamiltonianPermutationOrbits f).card = 1 /\
        0 < Finset.univ.prod (fun i => M (f i) i) /\ exists i, E (f i) i := by
  classical
  by_contra hNone
  have hPoint (f : Equiv.Perm Iota) :
      (if (hamiltonianPermutationOrbits f).card = 1 /\ exists i, E (f i) i then
        Finset.univ.prod (fun i => M (f i) i) else 0) <= 0 := by
    split_ifs with h
    next =>
      by_contra hNot
      have hWeight : 0 < Finset.univ.prod (fun i => M (f i) i) := lt_of_not_ge hNot
      exact hNone (Exists.intro f (And.intro h.1 (And.intro hWeight h.2)))
    next => exact le_refl 0
  have hSum : hamiltonianMarkedCycleSum M E <= 0 :=
    Finset.sum_nonpos (fun f hf => hPoint f)
  exact not_lt_of_ge hSum hPositive

end PrimeFactorOscillations
