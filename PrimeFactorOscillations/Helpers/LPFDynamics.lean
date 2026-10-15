/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.NormNum
import PrimeFactorOscillations.Mathlib.Data.Finset.SumPartners
import PrimeFactorOscillations.Mathlib.NumberTheory.SmoothNumbers.LargestPrimeFactor

/-!
# Fresh largest-prime-factor dynamics and robust generation

The current fullStep/fullOrbit dynamics allows equal inputs at every step,
starts from fullSeed p = {2,p}, and retains the old state. The distinct-input
step/orbit is retained as a subordinate operator for the existing lower bounds.
Its closed-set examples are not claims about fullStep. A representation surplus
gives an actual member of the next state. No distribution assumption is imposed.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

def affineValue (p q : Nat) : Nat := 2 * (p + q) - 1

def step (S : Finset Nat) : Finset Nat :=
  Union.union S (((S.product S).filter (fun a => Not (a.1 = a.2))).image
    (fun a => Nat.largestPrimeFactor (affineValue a.1 a.2)))

def orbit (S : Finset Nat) : Nat -> Finset Nat
  | 0 => S
  | n + 1 => step (orbit S n)

theorem subset_step (S : Finset Nat) : S <= step S := by
  intro p hp
  exact Finset.mem_union_left _ hp

theorem mem_step_of_pair (S : Finset Nat) {p q : Nat}
    (hp : Membership.mem S p) (hq : Membership.mem S q) (hne : Not (p = q)) :
    Membership.mem (step S) (Nat.largestPrimeFactor (affineValue p q)) := by
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  exact Exists.intro (p, q) (And.intro
    (Finset.mem_filter.mpr (And.intro (Finset.mem_product.mpr (And.intro hp hq)) hne)) rfl)

theorem prime_mem_step_of_representation_surplus
    (P S : Finset Nat) (n m r : Nat) (hm : 0 < m) (hr : Nat.Prime r)
    (hmr : Nat.largestPrimeFactor m <= r) (hlift : 2 * n = m * r + 1)
    (hCount : 2 * (SDiff.sdiff P S).card + 1 < (Finset.sumPartners P n).card) :
    Membership.mem (step S) r := by
  have h := Finset.exists_distinct_sum_of_card_sumPartners_gt P S n hCount
  let p : Nat := Classical.choose h
  have hp := Classical.choose_spec h
  let q : Nat := Classical.choose hp
  have hq := Classical.choose_spec hp
  have hStep := mem_step_of_pair S hq.1 hq.2.1 hq.2.2.1
  have hv : affineValue p q = m * r := by
    unfold affineValue
    rw [hq.2.2.2]
    omega
  rw [hv, Nat.largestPrimeFactor_mul_prime (Nat.ne_of_gt hm) hr hmr] at hStep
  exact hStep

theorem prime_mem_step_three_mod_four
    (P S : Finset Nat) (r : Nat) (hr : Nat.Prime r) (hmod : r % 4 = 3)
    (hCount : 2 * (SDiff.sdiff P S).card + 1 <
      (Finset.sumPartners P ((r + 1) / 2)).card) : Membership.mem (step S) r := by
  apply prime_mem_step_of_representation_surplus P S ((r + 1) / 2) 1 r
    (by omega) hr _ _ hCount
  next => simpa [Nat.largestPrimeFactor] using hr.one_lt.le
  next => omega

theorem prime_mem_step_one_mod_four
    (P S : Finset Nat) (r : Nat) (hr : Nat.Prime r) (hr3 : 3 <= r)
    (hmod : r % 4 = 1)
    (hCount : 2 * (SDiff.sdiff P S).card + 1 <
      (Finset.sumPartners P ((3 * r + 1) / 2)).card) : Membership.mem (step S) r := by
  apply prime_mem_step_of_representation_surplus P S ((3 * r + 1) / 2) 3 r
    (by omega) hr _ _ hCount
  next => simpa [Nat.largestPrimeFactor_of_prime (by decide : Nat.Prime 3)] using hr3
  next => omega

theorem step_preserves_primes (S : Finset Nat)
    (hS : forall p, Membership.mem S p -> Nat.Prime p) :
    forall r, Membership.mem (step S) r -> Nat.Prime r := by
  intro r hr
  rcases Finset.mem_union.mp hr with hold | hnew
  next => exact hS r hold
  next =>
    let a : Prod Nat Nat := Classical.choose (Finset.mem_image.mp hnew)
    have ha := Classical.choose_spec (Finset.mem_image.mp hnew)
    have hp := hS a.1 (Finset.mem_product.mp (Finset.mem_filter.mp ha.1).1).1
    have hq := hS a.2 (Finset.mem_product.mp (Finset.mem_filter.mp ha.1).1).2
    rw [<- ha.2]
    apply Nat.largestPrimeFactor_prime
    change 1 < 2 * (a.1 + a.2) - 1
    have hp2 := hp.two_le
    have hq2 := hq.two_le
    omega

theorem step_eq_self_iff (S : Finset Nat) :
    step S = S <-> forall p q, Membership.mem S p -> Membership.mem S q ->
      Not (p = q) -> Membership.mem S (Nat.largestPrimeFactor (affineValue p q)) := by
  constructor
  next =>
    intro h p q hp hq hne
    rw [<- h]
    exact mem_step_of_pair S hp hq hne
  next =>
    intro h
    apply le_antisymm ?_ (subset_step S)
    intro r hr
    rcases Finset.mem_union.mp hr with hold | hnew
    next => exact hold
    next =>
      let a : Prod Nat Nat := Classical.choose (Finset.mem_image.mp hnew)
      have ha := Classical.choose_spec (Finset.mem_image.mp hnew)
      have hmem := Finset.mem_filter.mp ha.1
      have hpq := Finset.mem_product.mp hmem.1
      rw [<- ha.2]
      exact h a.1 a.2 hpq.1 hpq.2 hmem.2

/-- A prime and its prime double-minus-one form a closed distinct-input state. -/
theorem step_pair_eq_self (p q : Nat) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (heq : q = 2 * p - 1) : step {p, q} = {p, q} := by
  have hp2 := hp.two_le
  have hq3 : 3 <= q := by omega
  have hv : affineValue p q = 3 * q := by unfold affineValue; omega
  have hLargest : Nat.largestPrimeFactor (affineValue p q) = q := by
    rw [hv]
    apply Nat.largestPrimeFactor_mul_prime (by omega) hq
    simpa [Nat.largestPrimeFactor_of_prime (by decide : Nat.Prime 3)] using hq3
  have hSwap : Nat.largestPrimeFactor (affineValue q p) = q := by
    simpa only [affineValue, Nat.add_comm] using hLargest
  apply (step_eq_self_iff {p, q}).mpr
  intro a b ha hb hne
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  have hCases : Or (And (a = p) (b = q)) (And (a = q) (b = p)) := by omega
  rcases hCases with h | h
  next => simp only [h.1, h.2, hLargest, Finset.mem_insert, Finset.mem_singleton, or_true]
  next => simp only [h.1, h.2, hSwap, Finset.mem_insert, Finset.mem_singleton, or_true]

theorem orbit_eq_of_step_eq_self (S : Finset Nat) (h : step S = S) (j : Nat) :
    orbit S j = S := by
  induction j with
  | zero => rfl
  | succ j ih => simpa only [orbit, ih] using h

theorem orbit_three_five (j : Nat) : orbit {3, 5} j = {3, 5} :=
  orbit_eq_of_step_eq_self {3, 5}
    (step_pair_eq_self 3 5 (by decide) (by decide) (by decide)) j

/-- Current dynamics: all pairs, including every diagonal, at every generation. -/
def fullStep (S : Finset Nat) : Finset Nat :=
  Union.union S ((S.product S).image
    (fun a => Nat.largestPrimeFactor (affineValue a.1 a.2)))

def fullOrbit (S : Finset Nat) : Nat -> Finset Nat
  | 0 => S
  | n + 1 => fullStep (fullOrbit S n)

/-- Two is included for every input prime; its diagonal is not used in advance. -/
def fullSeed (p : Nat) : Finset Nat := {2, p}

theorem subset_fullStep (S : Finset Nat) : S <= fullStep S := by
  intro p hp
  exact Finset.mem_union_left _ hp

theorem mem_fullStep_of_pair (S : Finset Nat) {p q : Nat}
    (hp : Membership.mem S p) (hq : Membership.mem S q) :
    Membership.mem (fullStep S) (Nat.largestPrimeFactor (affineValue p q)) := by
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  exact Exists.intro (p, q)
    (And.intro (Finset.mem_product.mpr (And.intro hp hq)) rfl)

theorem mem_fullStep_diagonal (S : Finset Nat) {p : Nat}
    (hp : Membership.mem S p) :
    Membership.mem (fullStep S) (Nat.largestPrimeFactor (4 * p - 1)) := by
  have hv : affineValue p p = 4 * p - 1 := by unfold affineValue; omega
  simpa only [hv] using mem_fullStep_of_pair S hp hp

theorem fullStep_mono {S T : Finset Nat} (h : S <= T) : fullStep S <= fullStep T := by
  intro r hr
  rcases Finset.mem_union.mp hr with hold | hnew
  next => exact subset_fullStep T (h hold)
  next =>
    let a : Prod Nat Nat := Classical.choose (Finset.mem_image.mp hnew)
    have ha := Classical.choose_spec (Finset.mem_image.mp hnew)
    have hpq := Finset.mem_product.mp ha.1
    rw [<- ha.2]
    exact mem_fullStep_of_pair T (h hpq.1) (h hpq.2)

theorem step_subset_fullStep (S : Finset Nat) : step S <= fullStep S := by
  intro r hr
  rcases Finset.mem_union.mp hr with hold | hnew
  next => exact subset_fullStep S hold
  next =>
    let a : Prod Nat Nat := Classical.choose (Finset.mem_image.mp hnew)
    have ha := Classical.choose_spec (Finset.mem_image.mp hnew)
    have hpq := Finset.mem_product.mp (Finset.mem_filter.mp ha.1).1
    rw [<- ha.2]
    exact mem_fullStep_of_pair S hpq.1 hpq.2

theorem fullStep_preserves_primes (S : Finset Nat)
    (hS : forall p, Membership.mem S p -> Nat.Prime p) :
    forall r, Membership.mem (fullStep S) r -> Nat.Prime r := by
  intro r hr
  rcases Finset.mem_union.mp hr with hold | hnew
  next => exact hS r hold
  next =>
    let a : Prod Nat Nat := Classical.choose (Finset.mem_image.mp hnew)
    have ha := Classical.choose_spec (Finset.mem_image.mp hnew)
    have hp := hS a.1 (Finset.mem_product.mp ha.1).1
    have hq := hS a.2 (Finset.mem_product.mp ha.1).2
    rw [<- ha.2]
    apply Nat.largestPrimeFactor_prime
    change 1 < 2 * (a.1 + a.2) - 1
    have hp2 := hp.two_le
    have hq2 := hq.two_le
    omega

theorem fullOrbit_mono {S T : Finset Nat} (h : S <= T) (j : Nat) :
    fullOrbit S j <= fullOrbit T j := by
  induction j with
  | zero => exact h
  | succ j ih => exact fullStep_mono ih

theorem orbit_subset_fullOrbit (S : Finset Nat) (j : Nat) : orbit S j <= fullOrbit S j := by
  induction j with
  | zero => exact le_refl S
  | succ j ih => exact (step_subset_fullStep (orbit S j)).trans (fullStep_mono ih)

theorem fullOrbit_subset_add (S : Finset Nat) (j n : Nat) :
    fullOrbit S j <= fullOrbit S (j + n) := by
  induction n with
  | zero => simpa only [Nat.add_zero] using le_refl (fullOrbit S j)
  | succ n ih => exact ih.trans (subset_fullStep (fullOrbit S (j + n)))

theorem fullOrbit_add (S : Finset Nat) (j n : Nat) :
    fullOrbit S (j + n) = fullOrbit (fullOrbit S j) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change fullStep (fullOrbit S (j + n)) = fullStep (fullOrbit (fullOrbit S j) n)
    exact congrArg fullStep ih

theorem fullOrbit_two_subset {S : Finset Nat} (hTwo : Membership.mem S 2) (j : Nat) :
    fullOrbit {2} j <= fullOrbit S j := by
  apply fullOrbit_mono
  intro r hr
  have hr2 : r = 2 := Finset.mem_singleton.mp hr
  simpa only [hr2] using hTwo

theorem fullOrbit_two_subset_seed (p j : Nat) :
    fullOrbit {2} j <= fullOrbit (fullSeed p) j :=
  fullOrbit_two_subset (by simp [fullSeed]) j

/-- Reaching q now suffices to simulate its entire seeded future. -/
theorem fullOrbit_reached_seed {S : Finset Nat} {q j : Nat}
    (hTwo : Membership.mem S 2) (hq : Membership.mem (fullOrbit S j) q) (n : Nat) :
    fullOrbit (fullSeed q) n <= fullOrbit S (j + n) := by
  rw [fullOrbit_add]
  apply fullOrbit_mono
  have hTwoj : Membership.mem (fullOrbit S j) 2 := by
    have h := fullOrbit_subset_add S 0 j hTwo
    simpa only [Nat.zero_add] using h
  intro r hr
  simp only [fullSeed, Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with h | h
  next => simpa only [h] using hTwoj
  next => simpa only [h] using hq

/-- Universal reachability for all augmented seeds is exactly the {2} problem. -/
theorem all_seed_reachability_iff_two :
    (forall p, Nat.Prime p -> forall r, Nat.Prime r ->
      exists j, Membership.mem (fullOrbit (fullSeed p) j) r) <->
    (forall r, Nat.Prime r -> exists j, Membership.mem (fullOrbit {2} j) r) := by
  constructor
  next =>
    intro h r hr
    simpa [fullSeed] using h 2 (by decide) r hr
  next =>
    intro h p _ r hr
    let j := Classical.choose (h r hr)
    have hj := Classical.choose_spec (h r hr)
    exact Exists.intro j (fullOrbit_two_subset_seed p j hj)

end PrimeFactorOscillations.LPF
