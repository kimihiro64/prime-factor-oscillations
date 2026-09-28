/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliMass

/-! # Exact odds factorization and first difference of finite Bernoulli masses -/

set_option autoImplicit false
set_option Elab.async false

namespace List

variable {R : Type*} [Field R]

private theorem esymm_step (a : R) (s : Multiset R) (r : Nat) :
    (Multiset.cons a s).esymm (r + 1) = s.esymm (r + 1) + a * s.esymm r := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.sum_map_mul_left]

/-- The exact odds representation over any field. Coordinates equal to zero
are allowed; forced coordinates must first be removed by the exact rank shift. -/
theorem bernoulliMass_eq_survival_mul_esymm
    (s : List R) (hne : forall a, List.Mem a s -> Not (a = 1)) (r : Nat) :
    bernoulliMass s r = (s.map (fun a => 1 - a)).prod *
      ((s.map (fun a => a / (1 - a)) : List R) : Multiset R).esymm r := by
  induction s generalizing r with
  | nil =>
      cases r with
      | zero => simp [bernoulliMass]
      | succ r =>
          rw [bernoulliMass]
          simp only [List.map_nil, List.prod_nil, one_mul]
          have hn : (([] : List R) : Multiset R) = 0 := rfl
          rw [hn, Multiset.esymm_of_card_lt (by simp)]
  | cons a s ih =>
      have ha : Not (1 - a = 0) := sub_ne_zero.mpr (Ne.symm (hne a (List.Mem.head _)))
      have ht : forall b, List.Mem b s -> Not (b = 1) :=
        fun b hb => hne b (List.Mem.tail _ hb)
      have hc : (1 - a) * (a / (1 - a)) = a := by field_simp
      cases r with
      | zero =>
          rw [bernoulliMass, ih ht 0]
          simp
      | succ r =>
          rw [bernoulliMass, ih ht (r + 1), ih ht r]
          simp only [List.map_cons, List.prod_cons]
          have hcons : ((a / (1 - a) :: s.map (fun b => b / (1 - b)) : List R) :
              Multiset R) = Multiset.cons (a / (1 - a))
                (s.map (fun b => b / (1 - b)) : Multiset R) := rfl
          rw [hcons, esymm_step]
          calc
            _ = ((1 - a) * (s.map (fun b => 1 - b)).prod) *
                  ((s.map (fun b => b / (1 - b)) : List R) : Multiset R).esymm (r + 1) +
                ((1 - a) * (a / (1 - a))) * (s.map (fun b => 1 - b)).prod *
                  ((s.map (fun b => b / (1 - b)) : List R) : Multiset R).esymm r := by
                    rw [hc]
                    ring
            _ = _ := by ring

/-- Exact signed first-difference factorization. No ordered or probabilistic
hypothesis is needed for this algebraic identity. -/
theorem bernoulliMass_step_difference (s : List R) (a b : R) (r : Nat)
    (ha : Not (a = 0)) (hb : Not (b = 0))
    (hF : Not (bernoulliMass s (r + 1) = 0)) :
    b * bernoulliMass (a :: s) (r + 1) - a * bernoulliMass s (r + 1) =
      (a * b * bernoulliMass s (r + 1)) *
        (bernoulliMass s r / bernoulliMass s (r + 1) - (1 / b - 1 / a + 1)) := by
  simp only [bernoulliMass]
  field_simp
  ring

end List
