/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Lattice.Lemmas
import Mathlib.Tactic.Ring.Basic

/-!
# Rank-sensitive counts of bounded subset products

Insertion identities retain both the product cutoff and the rank in a
selected prefix. Separating two marked elements gives an exact signed
contrast. The weights are arbitrary integers; a nonnegative counting
interpretation requires a nonnegative weight.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Finset

/-- Weighted subsets with bounded product and prescribed prefix rank. -/
def rankProductMass (s t : Finset Nat) (w : Int) (X r : Nat) : Int :=
  s.powerset.sum (fun a => if a.prod id <= X /\ (Inter.inter a t).card = r
    then w ^ a.card else 0)

/-- The same finite sum with one mandatory marked element. -/
def markedRankProductMass (s t : Finset Nat) (w : Int) (X r q : Nat) : Int :=
  s.powerset.sum (fun a => if Membership.mem a q /\
      a.prod id <= X /\ (Inter.inter a t).card = r then w ^ a.card else 0)

private theorem mul_cost_le_iff (q a T : Nat) (hq : 0 < q) :
    q * a <= q * T <-> a <= T := by
  constructor
  case mp =>
    intro hh
    by_contra hn
    have hl : T < a := Nat.lt_of_not_ge hn
    have hl' := Nat.mul_lt_mul_of_pos_left hl hq
    exact (not_lt_of_ge hh) hl'
  case mpr => exact Nat.mul_le_mul_left q

/-- Inserting an element outside the prefix preserves its rank. -/
theorem rankProductMass_insert_outside (s t : Finset Nat) (w : Int)
    (q T r : Nat) (hqs : Not (Membership.mem s q))
    (hqt : Not (Membership.mem t q)) (hq : 0 < q) :
    rankProductMass (insert q s) t w (q * T) r =
      rankProductMass s t w (q * T) r + w * rankProductMass s t w T r := by
  classical
  unfold rankProductMass
  rw [sum_powerset_insert hqs]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro a ha
  have hqa : Not (Membership.mem a q) :=
    fun h => hqs ((mem_powerset.mp ha) h)
  rw [prod_insert hqa, card_insert_of_notMem hqa, insert_inter_of_notMem hqt]
  simp only [id_eq, mul_cost_le_iff q _ T hq]
  by_cases hh : a.prod id <= T /\ (Inter.inter a t).card = r
  all_goals simp [hh, pow_succ, mul_comm]

/-- Inserting the marked element into the prefix increases its rank by one. -/
theorem rankProductMass_insert_inside (s t : Finset Nat) (w : Int)
    (q T r : Nat) (hqs : Not (Membership.mem s q))
    (hq : 0 < q) :
    rankProductMass (insert q s) (insert q t) w (q * T) (r + 1) =
      rankProductMass s t w (q * T) (r + 1) + w * rankProductMass s t w T r := by
  classical
  unfold rankProductMass
  rw [sum_powerset_insert hqs]
  congr 1
  next =>
    apply sum_congr rfl
    intro a ha
    have hqa : Not (Membership.mem a q) :=
      fun h => hqs ((mem_powerset.mp ha) h)
    rw [inter_insert_of_notMem hqa]
  next =>
    rw [mul_sum]
    apply sum_congr rfl
    intro a ha
    have hqa : Not (Membership.mem a q) :=
      fun h => hqs ((mem_powerset.mp ha) h)
    have hqint : Not (Membership.mem (Inter.inter a t) q) :=
      fun h => hqa (mem_inter.mp h).1
    rw [prod_insert hqa, card_insert_of_notMem hqa,
      insert_inter_of_mem (mem_insert_self q t), inter_insert_of_notMem hqa,
      card_insert_of_notMem hqint]
    simp only [id_eq, mul_cost_le_iff q _ T hq, Nat.add_right_cancel_iff]
    by_cases hh : a.prod id <= T /\ (Inter.inter a t).card = r
    all_goals simp [hh, pow_succ, mul_comm]

/-- Remove a mandatory element and divide its exact product cutoff. -/
theorem markedRankProductMass_insert_outside (s t : Finset Nat) (w : Int)
    (q T r : Nat) (hqs : Not (Membership.mem s q))
    (hqt : Not (Membership.mem t q)) (hq : 0 < q) :
    markedRankProductMass (insert q s) t w (q * T) r q =
      w * rankProductMass s t w T r := by
  classical
  unfold markedRankProductMass rankProductMass
  rw [sum_powerset_insert hqs]
  have hz : s.powerset.sum (fun a => if Membership.mem a q /\
      a.prod id <= q * T /\ (Inter.inter a t).card = r then w ^ a.card else 0) = 0 := by
    apply sum_eq_zero
    intro a ha
    have hqa : Not (Membership.mem a q) :=
      fun h => hqs ((mem_powerset.mp ha) h)
    simp only [hqa, false_and, ite_false]
  rw [hz, zero_add, mul_sum]
  apply sum_congr rfl
  intro a ha
  have hqa : Not (Membership.mem a q) :=
    fun h => hqs ((mem_powerset.mp ha) h)
  rw [prod_insert hqa, card_insert_of_notMem hqa, insert_inter_of_notMem hqt]
  simp only [mem_insert_self, true_and, id_eq, mul_cost_le_iff q _ T hq]
  by_cases hh : a.prod id <= T /\ (Inter.inter a t).card = r
  all_goals simp [hh, pow_succ, mul_comm]

/-- Exact two-marker contrast, retaining the rank-shift and interval terms. -/
theorem markedRankProductMass_two_point_contrast (s t : Finset Nat) (w : Int)
    (p q T r : Nat) (hps : Not (Membership.mem s p))
    (hqs : Not (Membership.mem s q)) (hpt : Not (Membership.mem t p))
    (hqt : Not (Membership.mem t q)) (hpq : Not (p = q))
    (hp : 0 < p) (hq : 0 < q) :
    markedRankProductMass (insert p (insert q s)) (insert p t) w
        (p * q * T) (r + 1) q -
      markedRankProductMass (insert p (insert q s)) t w (p * q * T) (r + 1) p =
    w ^ 2 * (rankProductMass s t w T r - rankProductMass s t w T (r + 1)) -
      w * (rankProductMass s t w (q * T) (r + 1) -
        rankProductMass s t w (p * T) (r + 1)) := by
  classical
  have hqp : Not (q = p) := fun h => hpq h.symm
  have hpqs : Not (Membership.mem (insert q s) p) := by
    simp only [mem_insert, hpq, hps, or_self, not_false_eq_true]
  have hqps : Not (Membership.mem (insert p s) q) := by
    simp only [mem_insert, hqp, hqs, or_self, not_false_eq_true]
  have hqpt : Not (Membership.mem (insert p t) q) := by
    simp only [mem_insert, hqp, hqt, or_self, not_false_eq_true]
  have hleft := markedRankProductMass_insert_outside (insert p s) (insert p t)
    w q (p * T) (r + 1) hqps hqpt hq
  have hright := markedRankProductMass_insert_outside (insert q s) t
    w p (q * T) (r + 1) hpqs hpt hp
  rw [rankProductMass_insert_inside s t w p T r hps hp] at hleft
  rw [rankProductMass_insert_outside s t w q T (r + 1) hqs hqt hq] at hright
  have heq : q * (p * T) = p * q * T := by ring1
  rw [heq, insert_comm q p s] at hleft
  rw [<- mul_assoc p q T] at hright
  rw [hleft, hright]
  ring1

end Finset
