/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Field.ZMod
import PrimeFactorOscillations.Definitions.ConsecutiveRootFamily
import PrimeFactorOscillations.Mathlib.Algebra.Field.FiniteAffineRoots
import PrimeFactorOscillations.Mathlib.Algebra.Group.FiniteFunctionFibers

/-!
# Exact local counts for a consecutive-root polynomial plus a prime

The root count is min(d,p), including every small-prime collision. Adding
a nonzero residue gives exactly p - min(d,p) successful ordered pairs.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace PrimeFactorOscillations

theorem consecutiveRootValue_card_roots (d p : Nat) (hp : Nat.Prime p) (hd : d < p) :
    letI : NeZero p := NeZero.mk hp.ne_zero
    ((Finset.univ : Finset (ZMod p)).filter
      (fun a => consecutiveRootValue d a = 0)).card = d := by
  classical
  letI : NeZero p := NeZero.mk hp.ne_zero
  letI : Fact (Nat.Prime p) := Fact.mk hp
  have hi (i : Fin d) : i.val + 1 < p := by omega
  have hinj : Function.Injective (fun i : Fin d => ((i.val + 1 : Nat) : ZMod p)) := by
    intro i j h
    have hv := congrArg (fun x : ZMod p => x.val) h
    simp only [ZMod.val_natCast_of_lt (hi i), ZMod.val_natCast_of_lt (hi j)] at hv
    exact Fin.ext (by omega)
  have h := Finset.card_affine_product_roots
    (fun _ : Fin d => (1 : ZMod p))
    (fun i : Fin d => -((i.val + 1 : Nat) : ZMod p))
    (fun _ => one_ne_zero) (by
      intro i j hij heq
      apply hij
      apply hinj
      simpa only [one_mul, neg_inj] using heq.symm)
  simpa only [consecutiveRootValue, one_mul, sub_eq_add_neg, Fintype.card_fin] using h

theorem consecutiveRootValue_eq_zero_of_prime_le (d p : Nat)
    (hp : Nat.Prime p) (hd : p <= d) (a : ZMod p) :
    consecutiveRootValue d a = 0 := by
  classical
  letI : NeZero p := NeZero.mk hp.ne_zero
  unfold consecutiveRootValue
  by_cases ha : a.val = 0
  . let i : Fin d := Fin.mk (p - 1) (by have := hp.pos; omega)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    change a - ((i.val + 1 : Nat) : ZMod p) = 0
    have hz : a = 0 := by
      calc
        a = (a.val : ZMod p) := (ZMod.natCast_zmod_val a).symm
        _ = 0 := by rw [ha]; simp
    have he : i.val + 1 = p := by dsimp [i]; have := hp.pos; omega
    rw [hz, he]
    simp
  . let i : Fin d := Fin.mk (a.val - 1) (by have := ZMod.val_lt a; omega)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    change a - ((i.val + 1 : Nat) : ZMod p) = 0
    have he : i.val + 1 = a.val := by dsimp [i]; omega
    rw [he, ZMod.natCast_zmod_val]
    exact sub_self _

theorem consecutiveRootValue_card_roots_eq_min (d p : Nat) (hp : Nat.Prime p) :
    letI : NeZero p := NeZero.mk hp.ne_zero
    ((Finset.univ : Finset (ZMod p)).filter
      (fun a => consecutiveRootValue d a = 0)).card = min d p := by
  classical
  let : NeZero p := NeZero.mk hp.ne_zero
  by_cases hd : d < p
  . rw [Nat.min_eq_left hd.le]
    exact consecutiveRootValue_card_roots d p hp hd
  . have hpd : p <= d := Nat.le_of_not_gt hd
    have hset : ((Finset.univ : Finset (ZMod p)).filter
        (fun a => consecutiveRootValue d a = 0)) = Finset.univ := by
      apply Finset.filter_eq_self.mpr
      intro a _
      exact consecutiveRootValue_eq_zero_of_prime_le d p hp hpd a
    rw [hset, Finset.card_univ, ZMod.card, Nat.min_eq_right hpd]

theorem consecutiveRootPrimeAddition_count (d p : Nat) (hp : Nat.Prime p) :
    letI : NeZero p := NeZero.mk hp.ne_zero
    (((Finset.univ : Finset (ZMod p)).product (Finset.univ.erase (0 : ZMod p))).filter
      (fun ab : Prod (ZMod p) (ZMod p) => consecutiveRootValue d ab.1 + ab.2 = 0)).card =
        p - min d p := by
  classical
  let : NeZero p := NeZero.mk hp.ne_zero
  rw [Finset.card_function_add_nonzero, Finset.card_univ, ZMod.card,
    consecutiveRootValue_card_roots_eq_min d p hp]

end PrimeFactorOscillations
