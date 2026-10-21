/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyPrimeClass

/-!
# Actual prime-class rank comparison under a local cap

Only the competing class is truncated. The greedy class remains the same
fixed class at every cutoff. Local real feasibility is transported to the
global generic selection theorem without strengthening its hypothesis.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open PrimeFactorUnimodality
open PrimeFactorOscillations.PrimeClassSampling

def boundedPrimeClass (P : Set Nat) (X : Nat) : Set Nat :=
  fun p => And (Membership.mem P p) (p <= X)

theorem primeClassPrefix_bounded_eq (P : Set Nat) (X Y : Nat) :
    primeClassPrefix (boundedPrimeClass P X) Y = primeClassPrefix P (min X Y) := by
  classical
  apply Finset.ext
  intro p
  simp only [primeClassPrefix, Finset.mem_filter, Finset.mem_Icc, le_min_iff]
  constructor
  case mp =>
    intro h
    exact And.intro (And.intro h.1.1 (And.intro h.2.2.2 h.1.2))
      (And.intro h.2.1 h.2.2.1)
  case mpr =>
    intro h
    exact And.intro (And.intro h.1.1 h.1.2.2)
      (And.intro h.2.1 (And.intro h.2.2 h.1.2.1))

theorem primeClassTheta_bounded_eq (P : Set Nat) (X Y : Nat) :
    primeClassTheta (boundedPrimeClass P X) Y = primeClassTheta P (min X Y) := by
  unfold primeClassTheta
  rw [primeClassPrefix_bounded_eq]

theorem primeClassPrefix_bounded_eq_of_le (P : Set Nat) (X Y : Nat) (hYX : Y <= X) :
    primeClassPrefix (boundedPrimeClass P X) Y = primeClassPrefix P Y := by
  rw [primeClassPrefix_bounded_eq, min_eq_right hYX]

theorem primeClassTheta_eq_zero_of_lt_two (P : Set Nat) (Y : Nat) (hY : Y < 2) :
    primeClassTheta P Y = 0 := by
  classical
  have he : Finset.Icc 2 Y = Finset.empty := Finset.Icc_eq_empty_of_lt hY
  simp only [primeClassTheta, primeClassPrefix, he]
  rfl

theorem boundedPrimeClass_nat_cap_of_local (P : Set Nat) (X : Nat)
    (hP : forall Y : Nat, 2 <= Y -> Y <= X -> primeClassTheta P Y <= (Y : Real)) :
    forall Y : Nat, primeClassTheta (boundedPrimeClass P X) Y <= (Y : Real) := by
  intro Y
  rw [primeClassTheta_bounded_eq]
  by_cases hm : 2 <= min X Y
  case pos =>
    exact (hP (min X Y) hm (min_le_left X Y)).trans (Nat.cast_le.mpr (min_le_right X Y))
  case neg =>
    rw [primeClassTheta_eq_zero_of_lt_two P (min X Y) (by omega)]
    exact Nat.cast_nonneg Y

theorem boundedPrimeClass_nat_cap_of_local_real (P : Set Nat) (x : Real) (hx : 2 <= x)
    (hP : forall t : Real, 2 <= t -> t <= x -> primeClassThetaReal P t <= t) :
    forall Y : Nat,
      primeClassTheta (boundedPrimeClass P (Nat.floor x)) Y <= (Y : Real) := by
  apply boundedPrimeClass_nat_cap_of_local
  intro Y hY hYX
  have hy : (2 : Real) <= (Y : Real) := by exact_mod_cast hY
  have hyx : (Y : Real) <= x :=
    (Nat.cast_le.mpr hYX).trans (Nat.floor_le (by linarith only [hx]))
  simpa only [primeClassThetaReal, Nat.floor_natCast] using hP (Y : Real) hy hyx

theorem greedyPrimeClass_local_count_optimal (P : Set Nat) (x : Real) (hx : 2 <= x)
    (hP : forall t : Real, 2 <= t -> t <= x -> primeClassThetaReal P t <= t) :
    (primeClassPrefix P (Nat.floor x)).card <=
      (primeClassPrefix greedyPrimeClass (Nat.floor x)).card := by
  have h := greedyPrimeClass_count_optimal (boundedPrimeClass P (Nat.floor x))
    (boundedPrimeClass_nat_cap_of_local_real P x hx hP) (Nat.floor x)
  simpa only [primeClassPrefix_bounded_eq, min_self] using h

theorem greedyDeletedPrimeClass_local_count_optimal
    (P : Set Nat) (x : Real) (hx : 2 <= x)
    (hP : forall t : Real, 2 <= t -> t <= x -> primeClassThetaReal P t <= t) :
    (primeClassPrefix greedyDeletedPrimeClass (Nat.floor x)).card <=
      (primeClassPrefix (fun p => Not (Membership.mem P p)) (Nat.floor x)).card := by
  rw [greedyDeletedPrimeClass_count_eq_sub, primeClassPrefix_complement_card]
  exact Nat.sub_le_sub_left (greedyPrimeClass_local_count_optimal P x hx hP)
    (primeCutoffLength (Nat.floor x))

theorem primeCutoffLength_before_primeAt (i : Nat) :
    primeCutoffLength (primeAt i - 1) = i := by
  unfold primeCutoffLength
  rw [Nat.sub_add_cancel (by have h := one_lt_primeAt i; omega : 1 <= primeAt i)]
  exact primeCount_primeAt i

theorem primeClassPrefix_before_primeAt_card (P : Set Nat) (i : Nat) :
    (primeClassPrefix P (primeAt i - 1)).card = selectionCount (classPrimeIndices P) i := by
  rw [primeClassPrefix_card_eq_selectionCount, primeCutoffLength_before_primeAt]

theorem greedyPrimeClass_local_rank_witness
    (P : Set Nat) (x : Real) (hx : 2 <= x)
    (hP : forall t : Real, 2 <= t -> t <= x -> primeClassThetaReal P t <= t)
    (p : Nat) (hp : Nat.Prime p) (hpP : Membership.mem P p) (hpx : (p : Real) <= x) :
    exists s : Nat, And (Nat.Prime s) (And (Membership.mem greedyPrimeClass s)
      (And (s <= p)
        ((primeClassPrefix greedyPrimeClass (s - 1)).card =
          (primeClassPrefix P (p - 1)).card))) := by
  let X := Nat.floor x
  let Q := boundedPrimeClass P X
  let i := Nat.count Nat.Prime p
  have hpi : primeAt i = p := primeAt_count_prime p hp
  have hpX : p <= X := Nat.le_floor hpx
  have hi : classPrimeIndices Q i := by
    change And (Membership.mem P (primeAt i)) (primeAt i <= X)
    rw [hpi]
    exact And.intro hpP hpX
  have hQ : forall Y : Nat, primeClassTheta Q Y <= (Y : Real) :=
    boundedPrimeClass_nat_cap_of_local_real P x hx hP
  choose j hj using greedySelection_rank_le (classPrimeIndices Q) primeLogWeight
    (fun k => (primeAt k : Real)) primeLogWeight_monotone
    (primeClass_cap_implies_index_feasible Q hQ) i hi
  have hsG : Membership.mem greedyPrimeClass (primeAt j) := by
    change And (Nat.Prime (primeAt j))
      (greedyPrimeIndices (Nat.count Nat.Prime (primeAt j)))
    rw [primeCount_primeAt]
    exact And.intro (prime_primeAt j) hj.2.1
  have hsp : primeAt j <= p := by
    rw [<- hpi]
    exact primeAt_strictMono.monotone hj.1
  have hprefix : primeClassPrefix Q (p - 1) = primeClassPrefix P (p - 1) :=
    primeClassPrefix_bounded_eq_of_le P X (p - 1) (by omega)
  have hcard : (primeClassPrefix greedyPrimeClass (primeAt j - 1)).card =
      (primeClassPrefix P (p - 1)).card := by
    rw [primeClassPrefix_before_primeAt_card greedyPrimeClass j,
      classPrimeIndices_greedyPrimeClass, <- hprefix, <- hpi,
      primeClassPrefix_before_primeAt_card Q i]
    exact hj.2.2
  exact Exists.intro (primeAt j) (And.intro (prime_primeAt j)
    (And.intro hsG (And.intro hsp hcard)))

theorem primeClassPrefix_rank_lt (P : Set Nat) (p q : Nat)
    (hp : Nat.Prime p) (hpP : Membership.mem P p) (hpq : p < q) :
    (primeClassPrefix P (p - 1)).card < (primeClassPrefix P (q - 1)).card := by
  classical
  have hsub : forall z : Nat, Membership.mem (primeClassPrefix P (p - 1)) z ->
      Membership.mem (primeClassPrefix P (q - 1)) z := by
    intro z hz
    simp only [primeClassPrefix, Finset.mem_filter, Finset.mem_Icc] at hz
    simp only [primeClassPrefix, Finset.mem_filter, Finset.mem_Icc]
    exact And.intro (And.intro hz.1.1 (by omega)) hz.2
  have hmem : Membership.mem (primeClassPrefix P (q - 1)) p := by
    simp only [primeClassPrefix, Finset.mem_filter, Finset.mem_Icc]
    exact And.intro (And.intro hp.two_le (by omega)) (And.intro hp hpP)
  have hnot : Not (Membership.mem (primeClassPrefix P (p - 1)) p) := by
    intro h
    have hi := Finset.mem_Icc.mp (Finset.mem_filter.mp h).1
    have hp2 := hp.two_le
    omega
  have hne : Not (primeClassPrefix P (p - 1) = primeClassPrefix P (q - 1)) := by
    intro heq
    rw [<- heq] at hmem
    exact hnot hmem
  apply Finset.card_lt_card
  exact Finset.ssubset_iff_subset_ne.mpr (And.intro hsub hne)

theorem greedyPrimeClass_local_rank_at
    (P : Set Nat) (x : Real) (hx : 2 <= x)
    (hP : forall t : Real, 2 <= t -> t <= x -> primeClassThetaReal P t <= t)
    (r p s : Nat) (hp : Nat.Prime p) (hpP : Membership.mem P p) (hpx : (p : Real) <= x)
    (hprank : (primeClassPrefix P (p - 1)).card = r)
    (hsrank : (primeClassPrefix greedyPrimeClass (s - 1)).card = r) :
    s <= p := by
  choose u hu using greedyPrimeClass_local_rank_witness P x hx hP p hp hpP hpx
  by_contra h
  have hps : p < s := by omega
  have hus : u < s := hu.2.2.1.trans_lt hps
  have hlt := primeClassPrefix_rank_lt greedyPrimeClass u s hu.1 hu.2.1 hus
  rw [hu.2.2.2, hprank, hsrank] at hlt
  omega

end PrimeFactorOscillations.PrimeClassDeletion
