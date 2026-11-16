/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianFactorCutGeometry

/-! # Exact local deletion and regular-factor resilience

Both complementary crossing counts are retained. The factor is extracted
from the remaining edges, while its operator loss is measured from the
original graph, so the deleted edges are charged exactly once.
-/

set_option autoImplicit false
set_option Elab.async false

open Finset
open scoped Matrix.Norms.L2Operator

universe u v

variable {A : Type u} {B : Type v} [Fintype A] [Fintype B]
variable [DecidableEq A] [DecidableEq B]

theorem hamiltonian_factor_filtered_deletion
    (E Q : Finset (Prod A B)) (hQE : Q <= E)
    (P : Prod A B -> Prop) [DecidablePred P] :
    (((E \ Q).filter P).card + (Q.filter P).card : Nat) = (E.filter P).card := by
  classical
  have heq : E.filter P = Union.union ((E \ Q).filter P) (Q.filter P) := by
    ext e
    by_cases hQ : Membership.mem Q e
    . simp [hQ, hQE hQ]
    . simp [hQ]
  have hd : Disjoint ((E \ Q).filter P) (Q.filter P) := by
    apply Finset.disjoint_left.mpr
    intro e hE hQ
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hE).1).2 (Finset.mem_filter.mp hQ).1
  rw [heq, Finset.card_union_of_disjoint hd]

theorem hamiltonian_factor_cross_raw_card
    (E : Finset (Prod A B)) (S : Finset A) (T : Finset B) :
    (hamiltonianFactorCross E S T).card =
      (E.filter (fun e => Membership.mem S e.1 /\ Not (Membership.mem T e.2))).card := by
  classical
  have himg : (univ : Finset (hamiltonianFactorEdge E)).image Subtype.val = E := by
    ext e
    simp
  have hc := hamiltonian_factor_projection_card E univ
    (fun e => Membership.mem S e.1 /\ Not (Membership.mem T e.2))
  rw [himg] at hc
  exact hc.symm

theorem hamiltonian_factor_cross_deletion
    (E Q : Finset (Prod A B)) (hQE : Q <= E) (S : Finset A) (T : Finset B) :
    ((hamiltonianFactorCross (E \ Q) S T).card : Real) +
        ((hamiltonianFactorCross Q S T).card : Real) =
      ((hamiltonianFactorCross E S T).card : Real) := by
  classical
  simp only [hamiltonian_factor_cross_raw_card]
  exact_mod_cast hamiltonian_factor_filtered_deletion E Q hQE
    (fun e => Membership.mem S e.1 /\ Not (Membership.mem T e.2))

theorem hamiltonian_factor_boundary_upper_one_side
    (E : Finset (Prod A B)) (S : Finset A) (T : Finset B) (d : Real)
    (hleft : forall a, hamiltonianFactorMass
      (fun e : hamiltonianFactorEdge E => e.val.1) {a} <= d)
    (hright : forall b, hamiltonianFactorMass
      (fun e : hamiltonianFactorEdge E => e.val.2) {b} <= d) :
    ((hamiltonianFactorCross E S T).card : Real) +
      ((hamiltonianFactorCross E (Compl.compl S) (Compl.compl T)).card : Real) <=
      d * ((S.card : Real) + (T.card : Real)) := by
  classical
  have hA : ((hamiltonianFactorCross E S T).card : Real) <=
      hamiltonianFactorMass (fun e : hamiltonianFactorEdge E => e.val.1) S := by
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro e he
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      (Finset.mem_filter.mp he).2.1
  have hB : ((hamiltonianFactorCross E (Compl.compl S) (Compl.compl T)).card : Real) <=
      hamiltonianFactorMass (fun e : hamiltonianFactorEdge E => e.val.2) T := by
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro e he
    have ht := (Finset.mem_filter.mp he).2.2
    have hmem : Membership.mem T e.val.2 := by simpa only [Finset.mem_compl, not_not] using ht
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hmem
  have hMassL := (hamiltonian_factor_mass_bounds
    (fun e : hamiltonianFactorEdge E => e.val.1) S 0 d
      (fun a => And.intro (by unfold hamiltonianFactorMass; positivity) (hleft a))).2
  have hMassR := (hamiltonian_factor_mass_bounds
    (fun e : hamiltonianFactorEdge E => e.val.2) T 0 d
      (fun b => And.intro (by unfold hamiltonianFactorMass; positivity) (hright b))).2
  nlinarith only [hA, hB, hMassL, hMassR]

theorem hamiltonian_factor_boundary_upper
    (E : Finset (Prod A B)) (S : Finset A) (T : Finset B) (d : Real)
    (hleft : forall a, hamiltonianFactorMass
      (fun e : hamiltonianFactorEdge E => e.val.1) {a} <= d)
    (hright : forall b, hamiltonianFactorMass
      (fun e : hamiltonianFactorEdge E => e.val.2) {b} <= d) :
    ((hamiltonianFactorCross E S T).card : Real) +
      ((hamiltonianFactorCross E (Compl.compl S) (Compl.compl T)).card : Real) <=
      d * min ((S.card : Real) + (T.card : Real))
        (((Compl.compl S).card : Real) + ((Compl.compl T).card : Real)) := by
  have h1 := hamiltonian_factor_boundary_upper_one_side E S T d hleft hright
  have h2 := hamiltonian_factor_boundary_upper_one_side E (Compl.compl S) (Compl.compl T)
    d hleft hright
  simp only [compl_compl] at h2
  rcases le_total ((S.card : Real) + (T.card : Real))
    (((Compl.compl S).card : Real) + ((Compl.compl T).card : Real)) with h | h
  . simpa only [min_eq_left h] using h1
  . rw [min_eq_right h]
    linarith only [h2]

theorem hamiltonian_regular_factor_after_local_deletion
    (E Q : Finset (Prod A B)) (hQE : Q <= E) (r : Nat)
    (hAB : Fintype.card A = Fintype.card B)
    (D g eps zeta : Real) (hD : 0 < D) (heps : 0 <= eps) (hzeta : 0 <= zeta)
    (hg : 0 < g - zeta) (hSmall : eps + zeta < (g - zeta) / 2)
    (hr : (r : Real) <= (1 - 2 * (eps + zeta) / (g - zeta)) * D)
    (hleft : forall a, (1 - eps) * D <= ((E.filter (fun e => e.1 = a)).card : Real) /\
      ((E.filter (fun e => e.1 = a)).card : Real) <= (1 + eps) * D)
    (hright : forall b, (1 - eps) * D <= ((E.filter (fun e => e.2 = b)).card : Real) /\
      ((E.filter (fun e => e.2 = b)).card : Real) <= (1 + eps) * D)
    (hQleft : forall a, ((Q.filter (fun e => e.1 = a)).card : Real) <= zeta * D)
    (hQright : forall b, ((Q.filter (fun e => e.2 = b)).card : Real) <= zeta * D)
    (hcut : forall (S : Finset A) (T : Finset B),
      g * D * min ((S.card : Real) + (T.card : Real))
        (((Compl.compl S).card : Real) + ((Compl.compl T).card : Real)) <=
      ((hamiltonianFactorCross E S T).card : Real) +
        ((hamiltonianFactorCross E (Compl.compl S) (Compl.compl T)).card : Real)) :
    Exists (fun F : Finset (Prod A B) =>
      F <= E \ Q /\
      (forall a, (F.filter (fun e => e.1 = a)).card = r) /\
      (forall b, (F.filter (fun e => e.2 = b)).card = r) /\
      norm (hamiltonianFactorAdjacency E - hamiltonianFactorAdjacency F) <=
        (1 + eps) * D - (r : Real)) := by
  classical
  have hRemainingL : forall a,
      (1 - (eps + zeta)) * D <=
        hamiltonianFactorMass (fun e : hamiltonianFactorEdge (E \ Q) => e.val.1) {a} /\
      hamiltonianFactorMass (fun e : hamiltonianFactorEdge (E \ Q) => e.val.1) {a} <=
        (1 + (eps + zeta)) * D := by
    intro a
    rw [hamiltonian_factor_mass_left_original]
    have hp : (((E \ Q).filter (fun e => e.1 = a)).card : Real) +
        ((Q.filter (fun e => e.1 = a)).card : Real) =
        ((E.filter (fun e => e.1 = a)).card : Real) := by
      exact_mod_cast hamiltonian_factor_filtered_deletion E Q hQE (fun e => e.1 = a)
    have hn : (0 : Real) <= ((Q.filter (fun e => e.1 = a)).card : Real) := Nat.cast_nonneg _
    constructor <;> nlinarith only [hp, (hleft a).1, (hleft a).2, hQleft a, hn,
      mul_nonneg hzeta hD.le]
  have hRemainingR : forall b,
      (1 - (eps + zeta)) * D <=
        hamiltonianFactorMass (fun e : hamiltonianFactorEdge (E \ Q) => e.val.2) {b} /\
      hamiltonianFactorMass (fun e : hamiltonianFactorEdge (E \ Q) => e.val.2) {b} <=
        (1 + (eps + zeta)) * D := by
    intro b
    rw [hamiltonian_factor_mass_right_original]
    have hp : (((E \ Q).filter (fun e => e.2 = b)).card : Real) +
        ((Q.filter (fun e => e.2 = b)).card : Real) =
        ((E.filter (fun e => e.2 = b)).card : Real) := by
      exact_mod_cast hamiltonian_factor_filtered_deletion E Q hQE (fun e => e.2 = b)
    have hn : (0 : Real) <= ((Q.filter (fun e => e.2 = b)).card : Real) := Nat.cast_nonneg _
    constructor <;> nlinarith only [hp, (hright b).1, (hright b).2, hQright b, hn,
      mul_nonneg hzeta hD.le]
  have hQmassL : forall a, hamiltonianFactorMass
      (fun e : hamiltonianFactorEdge Q => e.val.1) {a} <= zeta * D := by
    intro a
    rw [hamiltonian_factor_mass_left_original]
    exact hQleft a
  have hQmassR : forall b, hamiltonianFactorMass
      (fun e : hamiltonianFactorEdge Q => e.val.2) {b} <= zeta * D := by
    intro b
    rw [hamiltonian_factor_mass_right_original]
    exact hQright b
  have hRemainingCut : forall (S : Finset A) (T : Finset B),
      (g - zeta) * D * min ((S.card : Real) + (T.card : Real))
        (((Compl.compl S).card : Real) + ((Compl.compl T).card : Real)) <=
      ((hamiltonianFactorCross (E \ Q) S T).card : Real) +
        ((hamiltonianFactorCross (E \ Q) (Compl.compl S) (Compl.compl T)).card : Real) := by
    intro S T
    have hu := hamiltonian_factor_boundary_upper Q S T (zeta * D) hQmassL hQmassR
    have h1 := hamiltonian_factor_cross_deletion E Q hQE S T
    have h2 := hamiltonian_factor_cross_deletion E Q hQE (Compl.compl S) (Compl.compl T)
    nlinarith only [hcut S T, hu, h1, h2]
  choose F hF hFL hFR using hamiltonian_regular_factor_from_cuts (E \ Q) r hAB
    D (g - zeta) (eps + zeta) hD hg (add_nonneg heps hzeta) hSmall hr
    hRemainingL hRemainingR hRemainingCut
  have hFE : F <= E := fun e he => (Finset.mem_sdiff.mp (hF he)).1
  have hRankD : (r : Real) <= D := by
    have hz : 0 <= 2 * (eps + zeta) / (g - zeta) :=
      div_nonneg (mul_nonneg (by norm_num) (add_nonneg heps hzeta)) hg.le
    nlinarith only [hr, mul_nonneg hz hD.le]
  have hdelta : 0 <= (1 + eps) * D - (r : Real) := by
    nlinarith only [hRankD, mul_nonneg heps hD.le]
  exact Exists.intro F (And.intro hF (And.intro hFL (And.intro hFR
    (hamiltonian_factor_adjacency_loss E F r ((1 + eps) * D) hFE hdelta
      (fun a => (hleft a).2) (fun b => (hright b).2) hFL hFR))))
