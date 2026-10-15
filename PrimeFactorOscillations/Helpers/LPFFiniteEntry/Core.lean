/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.NormNum.Prime
import PrimeFactorOscillations.Helpers.LPFDynamics

/-! Bounded component of the inclusive finite orbit certificate. -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF



structure TreeOrbitWitness where
  generation : Nat
  parentLeft : Nat
  parentRight : Nat
  output : Nat
  factors : List Nat
  factorsPrime : forall p, Membership.mem factors p -> Nat.Prime p

inductive OrbitWitnessTree where
  | empty
  | node (left : OrbitWitnessTree) (row : TreeOrbitWitness) (right : OrbitWitnessTree)

def orbitTreeLookup : OrbitWitnessTree -> Nat -> Option TreeOrbitWitness
  | .empty, _ => none
  | .node left row right, p =>
    if p < row.output then orbitTreeLookup left p
    else if row.output < p then orbitTreeLookup right p
    else some row

def orbitTreeAll (test : TreeOrbitWitness -> Bool) : OrbitWitnessTree -> Bool
  | .empty => true
  | .node left row right =>
    test row && (orbitTreeAll test left && orbitTreeAll test right)

theorem orbitTreeLookup_output (tree : OrbitWitnessTree) (p : Nat) (w : TreeOrbitWitness)
    (h : orbitTreeLookup tree p = some w) : w.output = p := by
  induction tree with
  | empty => simp [orbitTreeLookup] at h
  | node left row right ihLeft ihRight =>
    simp only [orbitTreeLookup] at h
    split_ifs at h with hLeft hRight
    next => exact ihLeft h
    next => exact ihRight h
    next =>
      have hw : row = w := Option.some.inj h
      subst w
      omega

theorem orbitTreeAll_lookup (tree : OrbitWitnessTree) (test : TreeOrbitWitness -> Bool)
    (hAll : orbitTreeAll test tree = true) (p : Nat) (w : TreeOrbitWitness)
    (h : orbitTreeLookup tree p = some w) : test w = true := by
  induction tree with
  | empty => simp [orbitTreeLookup] at h
  | node left row right ihLeft ihRight =>
    simp only [orbitTreeAll, Bool.and_eq_true] at hAll
    simp only [orbitTreeLookup] at h
    split_ifs at h
    next => exact ihLeft hAll.2.1 h
    next => exact ihRight hAll.2.2 h
    next =>
      have hw : row = w := Option.some.inj h
      subst w
      exact hAll.1

def orbitTreeParent (tree : OrbitWitnessTree) (p j : Nat) : Bool :=
  if p = 2 then true
  else match orbitTreeLookup tree p with
    | none => false
    | some row => decide (row.generation < j)

def ValidTreeOrbitWitness (tree : OrbitWitnessTree) (w : TreeOrbitWitness) : Prop :=
  0 < w.generation /\
  orbitTreeParent tree w.parentLeft w.generation = true /\
  orbitTreeParent tree w.parentRight w.generation = true /\
  affineValue w.parentLeft w.parentRight = w.factors.prod /\
  w.factors.foldr max 1 = w.output

instance (tree : OrbitWitnessTree) (w : TreeOrbitWitness) :
    Decidable (ValidTreeOrbitWitness tree w) := by
  unfold ValidTreeOrbitWitness
  infer_instance

def orbitTreeCheck (tree : OrbitWitnessTree) : Bool :=
  orbitTreeAll (fun w => decide (ValidTreeOrbitWitness tree w)) tree

private theorem tree_factor_list_product (fs : List Nat)
    (h : forall p, Membership.mem fs p -> Nat.Prime p) :
    0 < fs.prod /\ Nat.largestPrimeFactor fs.prod = fs.foldr max 1 := by
  induction fs with
  | nil => simp [Nat.largestPrimeFactor]
  | cons p fs ih =>
    have hp : Nat.Prime p := h p (by simp)
    have ht := ih (fun q hq => h q (by simp [hq]))
    refine And.intro (Nat.mul_pos hp.pos ht.1) ?_
    rw [List.prod_cons, Nat.largestPrimeFactor_mul hp.ne_zero (Nat.ne_of_gt ht.1),
      Nat.largestPrimeFactor_of_prime hp, ht.2]
    rfl

private theorem tree_two_reachable (j : Nat) :
    Membership.mem (fullOrbit {2} j) 2 := by
  have h := fullOrbit_subset_add {2} 0 j
  have hTwo : Membership.mem (fullOrbit {2} 0) 2 := by simp [fullOrbit]
  simpa only [Nat.zero_add] using h hTwo

theorem orbitTreeCheck_reachable (tree : OrbitWitnessTree) (hCheck : orbitTreeCheck tree = true)
    (j : Nat) :
    forall p w, orbitTreeLookup tree p = some w -> w.generation <= j ->
      Membership.mem (fullOrbit {2} j) p := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro p w hLookup hGen
    have hValid : ValidTreeOrbitWitness tree w :=
      of_decide_eq_true (orbitTreeAll_lookup tree
        (fun w => decide (ValidTreeOrbitWitness tree w)) hCheck p w hLookup)
    have hOutput := orbitTreeLookup_output tree p w hLookup
    have hPos : 0 < w.generation := hValid.1
    have hParent : forall q, orbitTreeParent tree q w.generation = true ->
        Membership.mem (fullOrbit {2} (w.generation - 1)) q := by
      intro q hq
      by_cases hTwo : q = 2
      next => rw [hTwo]; exact tree_two_reachable _
      next =>
        cases hRow : orbitTreeLookup tree q with
        | none => simp [orbitTreeParent, hTwo, hRow] at hq
        | some v =>
          have hv : v.generation < w.generation := by
            simpa [orbitTreeParent, hTwo, hRow] using hq
          exact ih (w.generation - 1) (by omega) q v hRow (by omega)
    have hPair := mem_fullStep_of_pair (fullOrbit {2} (w.generation - 1))
      (hParent w.parentLeft hValid.2.1) (hParent w.parentRight hValid.2.2.1)
    have hFactors := tree_factor_list_product w.factors w.factorsPrime
    rw [hValid.2.2.2.1, hFactors.2, hValid.2.2.2.2, hOutput] at hPair
    have hStep : Membership.mem (fullOrbit {2} w.generation) p := by
      have hSucc : w.generation - 1 + 1 = w.generation := by omega
      change Membership.mem (fullOrbit {2} (w.generation - 1 + 1)) p at hPair
      rw [hSucc] at hPair
      exact hPair
    have hMono := fullOrbit_subset_add {2} w.generation (j - w.generation)
    have hIndex : w.generation + (j - w.generation) = j := by omega
    rw [hIndex] at hMono
    exact hMono hStep

def orbitTreeCoveredAt (tree : OrbitWitnessTree) (j p : Nat) : Bool :=
  if p = 2 then true
  else match orbitTreeLookup tree p with
    | none => false
    | some w => decide (w.generation <= j)

theorem orbitTreeCoveredAt_reachable (tree : OrbitWitnessTree)
    (hCheck : orbitTreeCheck tree = true) (j p : Nat)
    (h : orbitTreeCoveredAt tree j p = true) :
    Membership.mem (fullOrbit {2} j) p := by
  by_cases hTwo : p = 2
  next => rw [hTwo]; exact tree_two_reachable _
  next =>
    cases hRow : orbitTreeLookup tree p with
    | none => simp [orbitTreeCoveredAt, hTwo, hRow] at h
    | some w =>
      have hGen : w.generation <= j := by
        simpa [orbitTreeCoveredAt, hTwo, hRow] using h
      exact orbitTreeCheck_reachable tree hCheck j p w hRow hGen


def orbitTreeIntervalCheck (tree : OrbitWitnessTree) (j start count : Nat) : Bool :=
  (List.range count).all (fun i =>
    decide (Nat.Prime (start + i) -> orbitTreeCoveredAt tree j (start + i) = true))

theorem orbitTreeIntervalCheck_reachable (tree : OrbitWitnessTree)
    (hTree : orbitTreeCheck tree = true) (j start count : Nat)
    (hInterval : orbitTreeIntervalCheck tree j start count = true)
    (p : Nat) (hp : Nat.Prime p) (hStart : start <= p) (hEnd : p < start + count) :
    Membership.mem (fullOrbit {2} j) p := by
  apply orbitTreeCoveredAt_reachable tree hTree j p
  have h := (List.all_eq_true.mp hInterval) (p - start)
    (List.mem_range.mpr (by omega))
  have hIndex : start + (p - start) = p := by omega
  have hValue := (of_decide_eq_true h)
  rw [hIndex] at hValue
  exact hValue hp

end PrimeFactorOscillations.LPF
