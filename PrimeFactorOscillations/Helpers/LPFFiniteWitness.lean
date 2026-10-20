/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.NormNum.Prime
import PrimeFactorOscillations.Helpers.LPFDynamics

/-! Finite list witnesses for affine largest-prime-factor orbits. -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

structure FiniteOrbitWitness where
  generation : Nat
  parentLeft : Nat
  parentRight : Nat
  output : Nat
  factors : List Nat
  deriving DecidableEq

def witnessPool (ws : List FiniteOrbitWitness) (j : Nat) : List Nat :=
  2 :: (ws.filter (fun w => decide (w.generation <= j))).map
    FiniteOrbitWitness.output

def ValidOrbitWitness (ws : List FiniteOrbitWitness) (w : FiniteOrbitWitness) : Prop :=
  0 < w.generation /\
  Membership.mem (witnessPool ws (w.generation - 1)) w.parentLeft /\
  Membership.mem (witnessPool ws (w.generation - 1)) w.parentRight /\
  affineValue w.parentLeft w.parentRight = w.factors.prod /\
  (forall p, Membership.mem w.factors p -> Nat.Prime p) /\
  w.factors.foldr max 1 = w.output

instance (ws : List FiniteOrbitWitness) (w : FiniteOrbitWitness) :
    Decidable (ValidOrbitWitness ws w) := by
  unfold ValidOrbitWitness
  infer_instance

theorem prime_factor_list_product (fs : List Nat)
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

theorem mem_witnessPool_iff (ws : List FiniteOrbitWitness) (j p : Nat) :
    Membership.mem (witnessPool ws j) p <->
      p = 2 \/ exists w, Membership.mem ws w /\ w.generation <= j /\ w.output = p := by
  simp only [witnessPool, List.mem_cons, List.mem_map, List.mem_filter,
    decide_eq_true_eq]
  constructor
  next =>
    intro h
    rcases h with h | h
    next => exact Or.inl h
    next =>
      let w := Classical.choose h
      have hw := Classical.choose_spec h
      exact Or.inr (Exists.intro w (And.intro hw.1.1 (And.intro hw.1.2 hw.2)))
  next =>
    intro h
    rcases h with h | h
    next => exact Or.inl h
    next =>
      let w := Classical.choose h
      have hw := Classical.choose_spec h
      exact Or.inr (Exists.intro w (And.intro (And.intro hw.1 hw.2.1) hw.2.2))

theorem witnessPool_reachable (ws : List FiniteOrbitWitness)
    (hValid : forall w, Membership.mem ws w -> ValidOrbitWitness ws w) (j : Nat) :
    forall p, Membership.mem (witnessPool ws j) p -> Membership.mem (fullOrbit {2} j) p := by
  induction j with
  | zero =>
    intro p hp
    rcases (mem_witnessPool_iff ws 0 p).mp hp with h | h
    next => simp [h, fullOrbit]
    next =>
      let w := Classical.choose h
      have hw := Classical.choose_spec h
      have hwPos : 0 < w.generation := (hValid w hw.1).1
      have hwBound : w.generation <= 0 := hw.2.1
      omega
  | succ j ih =>
    intro p hp
    rcases (mem_witnessPool_iff ws (j + 1) p).mp hp with h | h
    next =>
      have h2 : Membership.mem (fullOrbit {2} j) 2 := ih 2 (by simp [witnessPool])
      rw [h]
      exact subset_fullStep _ h2
    next =>
      let w := Classical.choose h
      have hw := Classical.choose_spec h
      by_cases hOld : w.generation <= j
      next =>
        have hpOld := (mem_witnessPool_iff ws j p).mpr
          (Or.inr (Exists.intro w (And.intro hw.1 (And.intro hOld hw.2.2))))
        exact subset_fullStep _ (ih p hpOld)
      next =>
        have hwBound : w.generation <= j + 1 := hw.2.1
        have hGen : w.generation = j + 1 := by omega
        have hv := hValid w hw.1
        have hLeft : Membership.mem (witnessPool ws j) w.parentLeft := by
          simpa only [hGen, Nat.add_sub_cancel] using hv.2.1
        have hRight : Membership.mem (witnessPool ws j) w.parentRight := by
          simpa only [hGen, Nat.add_sub_cancel] using hv.2.2.1
        have hPair := mem_fullStep_of_pair (fullOrbit {2} j)
          (ih w.parentLeft hLeft) (ih w.parentRight hRight)
        have hf := prime_factor_list_product w.factors hv.2.2.2.2.1
        rw [hv.2.2.2.1, hf.2, hv.2.2.2.2.2, hw.2.2] at hPair
        exact hPair

def testWitnesses : List FiniteOrbitWitness :=
  [FiniteOrbitWitness.mk 1 2 2 7 [7],
    FiniteOrbitWitness.mk 2 7 2 17 [17],
    FiniteOrbitWitness.mk 2 7 7 3 [3, 3, 3]]

theorem testWitnesses_valid :
    forall w, Membership.mem testWitnesses w -> ValidOrbitWitness testWitnesses w := by decide

example : Membership.mem (fullOrbit {2} 2) 3 :=
  witnessPool_reachable testWitnesses testWitnesses_valid 2 3 (by decide)

end PrimeFactorOscillations.LPF
