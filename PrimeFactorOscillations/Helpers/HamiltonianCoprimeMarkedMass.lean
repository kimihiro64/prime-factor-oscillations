/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCoprimeConductorPhase
import PrimeFactorOscillations.Helpers.HamiltonianPermanentRowMass

/-! # Exact closing-edge supply after both coprime endpoints are removed

Both endpoint losses and their intersection are retained before
the native cubic lower bound is applied. No marked cycles are
counted with the multiplicity of their usable edges.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_sum_erase_two {Iota : Type*} [Fintype Iota] [DecidableEq Iota]
    (a b : Iota) (hab : Not (a = b)) (f : Iota -> Real) :
    ((Finset.univ.erase a).erase b).sum f =
      Finset.univ.sum f - f a - f b := by
  have ha := Finset.sum_erase_add (Finset.univ : Finset Iota) f (Finset.mem_univ a)
  have hb := Finset.sum_erase_add (Finset.univ.erase a) f
    (Finset.mem_erase.mpr (And.intro (Ne.symm hab) (Finset.mem_univ b)))
  linarith only [ha, hb]

variable {n : Nat} [NeZero n]

def hamiltonianCoprimeInterior (a b : ZMod n) : Finset (ZMod n) :=
  (Finset.univ.erase a).erase b

def hamiltonianCoprimeClosingMark (a b i j : ZMod n) : Prop :=
  hamiltonianCoprimeRelation a j /\ hamiltonianCoprimeRelation i b

def hamiltonianCoprimeClosingSummand (a b i j : ZMod n) : Real :=
  if hamiltonianCoprimeClosingMark a b i j then hamiltonianCoprimeKernel i j else 0

def hamiltonianCoprimeClosingMass (a b : ZMod n) : Real :=
  (hamiltonianCoprimeInterior a b).sum (fun i =>
    (hamiltonianCoprimeInterior a b).sum (fun j =>
      hamiltonianCoprimeClosingSummand a b i j))

theorem hamiltonian_coprime_kernel_point_symmetry (x y : ZMod n) :
    hamiltonianCoprimeKernel x y = hamiltonianCoprimeKernel y x := by
  exact (congrArg (fun M : Matrix (ZMod n) (ZMod n) Real => M x y)
    (hamiltonian_coprime_kernel_symmetric (n := n))).symm

theorem hamiltonian_coprime_kernel_indicator (x y : ZMod n) :
    hamiltonianCoprimeKernel x y =
      if hamiltonianCoprimeRelation x y then 1 / (n.totient : Real) else 0 := by
  unfold hamiltonianCoprimeKernel hamiltonianCoprimeAdjacency hamiltonianCoprimeRelation
  split_ifs <;> simp

theorem hamiltonian_coprime_closing_summand_product (a b i j : ZMod n) :
    hamiltonianCoprimeClosingSummand a b i j =
      (n.totient : Real) ^ 2 *
        (hamiltonianCoprimeKernel a j * hamiltonianCoprimeKernel j i *
          hamiltonianCoprimeKernel i b) := by
  have hd : Not ((n.totient : Real) = 0) := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos n)).ne'
  rw [hamiltonian_coprime_kernel_indicator a j,
    hamiltonian_coprime_kernel_indicator i b,
    hamiltonian_coprime_kernel_point_symmetry j i]
  unfold hamiltonianCoprimeClosingSummand hamiltonianCoprimeClosingMark
  by_cases hAj : hamiltonianCoprimeRelation a j
  . by_cases hiB : hamiltonianCoprimeRelation i b
    . simp only [hAj, hiB, and_self, ite_true]
      field_simp [hd]
    . simp [hiB]
  . simp [hAj]

theorem hamiltonian_coprime_full_closing_mass (a b : ZMod n) :
    Finset.univ.sum (fun i : ZMod n => Finset.univ.sum (fun j : ZMod n =>
      hamiltonianCoprimeClosingSummand a b i j)) =
        (n.totient : Real) ^ 2 * hamiltonianCoprimeThreeStepKernel a b := by
  simp_rw [hamiltonian_coprime_closing_summand_product]
  simp only [hamiltonianCoprimeThreeStepKernel, Matrix.mul_apply,
    Finset.sum_mul, Finset.mul_sum]

theorem hamiltonian_coprime_closing_row_left (a b : ZMod n) :
    Finset.univ.sum (fun j : ZMod n =>
      hamiltonianCoprimeClosingSummand a b a j) =
      if hamiltonianCoprimeRelation a b then 1 else 0 := by
  have hPoint (j : ZMod n) : hamiltonianCoprimeClosingSummand a b a j =
      if hamiltonianCoprimeRelation a b then hamiltonianCoprimeKernel a j else 0 := by
    unfold hamiltonianCoprimeClosingSummand hamiltonianCoprimeClosingMark
    by_cases hab : hamiltonianCoprimeRelation a b
    . by_cases haj : hamiltonianCoprimeRelation a j
      . simp [hab, haj]
      . simp [hab, haj, hamiltonian_coprime_kernel_indicator]
    . simp [hab]
  simp_rw [hPoint]
  split_ifs <;> simp [hamiltonian_coprime_kernel_row_sum]

theorem hamiltonian_coprime_closing_col_right (a b : ZMod n) :
    Finset.univ.sum (fun i : ZMod n =>
      hamiltonianCoprimeClosingSummand a b i b) =
      if hamiltonianCoprimeRelation a b then 1 else 0 := by
  have hPoint (i : ZMod n) : hamiltonianCoprimeClosingSummand a b i b =
      if hamiltonianCoprimeRelation a b then hamiltonianCoprimeKernel i b else 0 := by
    unfold hamiltonianCoprimeClosingSummand hamiltonianCoprimeClosingMark
    by_cases hab : hamiltonianCoprimeRelation a b
    . by_cases hib : hamiltonianCoprimeRelation i b
      . simp [hab, hib]
      . simp [hab, hib, hamiltonian_coprime_kernel_indicator]
    . simp [hab]
  simp_rw [hPoint]
  split_ifs <;> simp [hamiltonian_coprime_kernel_col_sum]

theorem hamiltonian_coprime_closing_overlap (a b : ZMod n) :
    hamiltonianCoprimeClosingSummand a b a b = hamiltonianCoprimeKernel a b := by
  unfold hamiltonianCoprimeClosingSummand hamiltonianCoprimeClosingMark
  by_cases hab : hamiltonianCoprimeRelation a b
  . simp [hab]
  . simp [hab, hamiltonian_coprime_kernel_indicator]

theorem hamiltonian_coprime_closing_mass_exact [Nontrivial (ZMod n)]
    (a b : ZMod n) (hab : Not (a = b)) :
    hamiltonianCoprimeClosingMass a b =
      (n.totient : Real) ^ 2 * hamiltonianCoprimeThreeStepKernel a b -
        2 * (if hamiltonianCoprimeRelation a b then 1 else 0) +
          hamiltonianCoprimeKernel a b := by
  let F := hamiltonianCoprimeClosingSummand a b
  let s := hamiltonianCoprimeInterior a b
  have hRowB (j : ZMod n) : F b j = 0 := by
    simp [F, hamiltonianCoprimeClosingSummand, hamiltonianCoprimeClosingMark,
      hamiltonian_coprime_relation_irreflexive b]
  have hColA (i : ZMod n) : F i a = 0 := by
    simp [F, hamiltonianCoprimeClosingSummand, hamiltonianCoprimeClosingMark,
      hamiltonian_coprime_relation_irreflexive a]
  have hInner (i : ZMod n) :
      s.sum (fun j => F i j) = Finset.univ.sum (fun j => F i j) - F i b := by
    change ((Finset.univ.erase a).erase b).sum (fun j => F i j) = _
    rw [hamiltonian_sum_erase_two a b hab, hColA]
    ring
  have hOuter :
      s.sum (fun i => s.sum (fun j => F i j)) =
        Finset.univ.sum (fun i : ZMod n => Finset.univ.sum (fun j => F i j)) -
          Finset.univ.sum (fun i : ZMod n => F i b) -
          Finset.univ.sum (fun j : ZMod n => F a j) + F a b := by
    change ((Finset.univ.erase a).erase b).sum (fun i => s.sum (fun j => F i j)) = _
    rw [hamiltonian_sum_erase_two a b hab]
    simp_rw [hInner]
    simp only [Finset.sum_sub_distrib, hRowB, Finset.sum_const_zero]
    ring
  change s.sum (fun i => s.sum (fun j => F i j)) = _
  rw [hOuter]
  dsimp only [F]
  rw [hamiltonian_coprime_full_closing_mass, hamiltonian_coprime_closing_col_right,
    hamiltonian_coprime_closing_row_left, hamiltonian_coprime_closing_overlap]
  ring

theorem hamiltonian_coprime_closing_mass_lower [Nontrivial (ZMod n)]
    (a b : ZMod n) (hab : Not (a = b))
    (hParity : Odd n \/ Odd (-(a - b)).val) :
    (n.totient : Real) ^ 2 / (2 * (n : Real)) - 2 <=
      hamiltonianCoprimeClosingMass a b := by
  have hWalk := hamiltonian_coprime_three_step_lower n a b hParity
  have hScale := mul_le_mul_of_nonneg_left hWalk (sq_nonneg (n.totient : Real))
  have hIndicator : (if hamiltonianCoprimeRelation a b then (1 : Real) else 0) <= 1 := by
    split_ifs <;> norm_num
  have hNonneg := hamiltonian_coprime_kernel_nonnegative a b
  rw [hamiltonian_coprime_closing_mass_exact a b hab]
  have hDiv : (n.totient : Real) ^ 2 * (1 / (2 * (n : Real))) =
      (n.totient : Real) ^ 2 / (2 * (n : Real)) := by ring
  rw [hDiv] at hScale
  linarith only [hScale, hIndicator, hNonneg]

theorem hamiltonian_coprime_interior_row_exact
    (a b i : ZMod n) (hab : Not (a = b)) :
    (hamiltonianCoprimeInterior a b).sum (fun j => hamiltonianCoprimeKernel i j) =
      1 - hamiltonianCoprimeKernel i a - hamiltonianCoprimeKernel i b := by
  unfold hamiltonianCoprimeInterior
  rw [hamiltonian_sum_erase_two a b hab, hamiltonian_coprime_kernel_row_sum]

theorem hamiltonian_coprime_interior_row_bounds
    (a b i : ZMod n) (hab : Not (a = b)) :
    1 - 2 / (n.totient : Real) <=
        (hamiltonianCoprimeInterior a b).sum (fun j => hamiltonianCoprimeKernel i j) /\
      (hamiltonianCoprimeInterior a b).sum (fun j => hamiltonianCoprimeKernel i j) <= 1 := by
  rw [hamiltonian_coprime_interior_row_exact a b i hab]
  have ha := hamiltonian_coprime_kernel_entry_cap i a
  have hb := hamiltonian_coprime_kernel_entry_cap i b
  have hA0 := hamiltonian_coprime_kernel_nonnegative i a
  have hB0 := hamiltonian_coprime_kernel_nonnegative i b
  have hTwo : (2 : Real) / (n.totient : Real) = 2 * (1 / (n.totient : Real)) := by ring
  rw [hTwo]
  constructor <;> linarith


theorem hamiltonian_sum_on_finset {Iota : Type*} [DecidableEq Iota]
    (s : Finset Iota) (f : Iota -> Real) :
    Finset.univ.sum (fun i : s => f i.val) = s.sum f := by
  apply Finset.sum_bij (fun i _ => i.val)
  . intro i hi
    exact i.property
  . intro i hi j hj h
    exact Subtype.ext h
  . intro i hi
    exact Exists.intro (Subtype.mk i hi) (Exists.intro (Finset.mem_univ _) rfl)
  . intro i hi
    rfl

def hamiltonianCoprimeInteriorKernel (a b : ZMod n) :
    Matrix (hamiltonianCoprimeInterior a b) (hamiltonianCoprimeInterior a b) Real :=
  fun i j => hamiltonianCoprimeKernel i.val j.val

theorem hamiltonian_coprime_interior_marked_mass (a b : ZMod n) :
    hamiltonianMarkedEdgeMass (hamiltonianCoprimeInteriorKernel a b)
      (fun i j => hamiltonianCoprimeClosingMark a b i.val j.val) =
        hamiltonianCoprimeClosingMass a b := by
  change Finset.univ.sum (fun i : hamiltonianCoprimeInterior a b =>
    Finset.univ.sum (fun j : hamiltonianCoprimeInterior a b =>
      hamiltonianCoprimeClosingSummand a b i.val j.val)) = _
  simp only [hamiltonian_sum_on_finset, hamiltonianCoprimeClosingMass]
  exact hamiltonian_sum_on_finset (hamiltonianCoprimeInterior a b)
    (fun i => (hamiltonianCoprimeInterior a b).sum
      (fun j => hamiltonianCoprimeClosingSummand a b i j))

theorem hamiltonian_coprime_interior_card
    (a b : ZMod n) (hab : Not (a = b)) :
    Fintype.card (hamiltonianCoprimeInterior a b) = n - 2 := by
  have hb : Membership.mem (Finset.univ.erase a) b :=
    Finset.mem_erase.mpr (And.intro (Ne.symm hab) (Finset.mem_univ b))
  have hCard : Fintype.card (hamiltonianCoprimeInterior a b) =
      (hamiltonianCoprimeInterior a b).card := by
    have h := hamiltonian_sum_on_finset (hamiltonianCoprimeInterior a b)
      (fun _ => (1 : Real))
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
    exact_mod_cast h
  rw [hCard]
  unfold hamiltonianCoprimeInterior
  rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem (Finset.mem_univ a),
    Finset.card_univ, ZMod.card]
  omega

theorem hamiltonian_coprime_interior_avoidance_upper [Nontrivial (ZMod n)]
    (a b : ZMod n) (hab : Not (a = b))
    (hParity : Odd n \/ Odd (-(a - b)).val)
    (hd4 : 4 <= (n.totient : Real)) :
    hamiltonianCycleSum
        (hamiltonianAvoidingKernel (hamiltonianCoprimeInteriorKernel a b)
          (fun i j => hamiltonianCoprimeClosingMark a b i.val j.val)) <=
      Real.exp (-((n - 2 : Nat) : Real) -
        ((n.totient : Real) ^ 2 / (2 * (n : Real)) - 2) / 2 +
          64 * ((n : Real) / (n.totient : Real)) * Real.log (2 * (n : Real))) := by
  let M := hamiltonianCoprimeInteriorKernel a b
  let E := fun i j : hamiltonianCoprimeInterior a b =>
    hamiltonianCoprimeClosingMark a b i.val j.val
  have hn : 0 < (n : Real) := by exact_mod_cast NeZero.pos n
  have hn1 : (1 : Real) <= n := by exact_mod_cast NeZero.pos n
  have hd : 0 < (n.totient : Real) := by linarith only [hd4]
  have hTot : (n.totient : Real) <= n := by exact_mod_cast Nat.totient_le n
  have ha : 1 <= (n : Real) / (n.totient : Real) := by
    have h := div_le_div_of_nonneg_right hTot hd.le
    rw [div_self (ne_of_gt hd)] at h
    exact h
  have hCard : (Fintype.card (hamiltonianCoprimeInterior a b) : Real) <= n := by
    rw [hamiltonian_coprime_interior_card a b hab]
    exact_mod_cast Nat.sub_le n 2
  have hHalf : (2 : Real) / (n.totient : Real) <= 1 / 2 := by
    have h := div_le_div_of_nonneg_right hd4 hd.le
    rw [div_self (ne_of_gt hd)] at h
    have hId : (4 : Real) / (n.totient : Real) =
        2 * (2 / (n.totient : Real)) := by ring
    rw [hId] at h
    linarith only [h]
  have hRows (i : hamiltonianCoprimeInterior a b) :
      1 / 2 <= Finset.univ.sum (fun j => M i j) /\
        Finset.univ.sum (fun j => M i j) <= 1 := by
    have hRow := hamiltonian_coprime_interior_row_bounds a b i.val hab
    have hRead : Finset.univ.sum (fun j => M i j) =
        (hamiltonianCoprimeInterior a b).sum (fun j => hamiltonianCoprimeKernel i.val j) := by
      simpa only [M, hamiltonianCoprimeInteriorKernel] using
        hamiltonian_sum_on_finset (hamiltonianCoprimeInterior a b)
          (fun j => hamiltonianCoprimeKernel i.val j)
    rw [hRead]
    exact And.intro (by linarith only [hRow.1, hHalf]) hRow.2
  have hCap (i j : hamiltonianCoprimeInterior a b) :
      M i j <= ((n : Real) / (n.totient : Real)) / (n : Real) := by
    have h := hamiltonian_coprime_kernel_entry_cap i.val j.val
    have hId : ((n : Real) / (n.totient : Real)) / (n : Real) =
        1 / (n.totient : Real) := by field_simp [ne_of_gt hn]
    rw [hId]
    exact h
  have hAvoid := hamiltonian_avoiding_cycle_row_mass_upper M E
    ((n : Real) / (n.totient : Real)) (n : Real) ha hn1 hCard
    (fun i j => hamiltonian_coprime_kernel_nonnegative i.val j.val)
    (fun i => (hRows i).1) (fun i => (hRows i).2) hCap
  change hamiltonianCycleSum (hamiltonianAvoidingKernel M E) <= _
  apply hAvoid.trans
  apply Real.exp_le_exp.mpr
  have hMass := hamiltonian_coprime_closing_mass_lower a b hab hParity
  have hMassRead : hamiltonianMarkedEdgeMass M E =
      hamiltonianCoprimeClosingMass a b :=
    hamiltonian_coprime_interior_marked_mass a b
  rw [hMassRead, hamiltonian_coprime_interior_card a b hab]
  linarith only [hMass]

end PrimeFactorOscillations
