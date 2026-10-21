/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Mathlib.RingTheory.MvPolynomial.Symmetric.OrderedBounds
import PrimeFactorOscillations.Proof.PrimeClassDeletion.BernoulliDominance

/-! # Coefficient order for finite nonnegative odds products -/

set_option autoImplicit false
set_option Elab.async false

namespace List

noncomputable def bernoulliOddsProduct (s : List Real) : Polynomial Real :=
  (s.map (fun a => 1 + Polynomial.C a * Polynomial.X)).prod

theorem bernoulliOddsProduct_coeff (s : List Real) (r : Nat) :
    (bernoulliOddsProduct s).coeff r = (s : Multiset Real).esymm r := by
  induction s generalizing r with
  | nil =>
      cases r with
      | zero => simp [bernoulliOddsProduct]
      | succ r =>
          have hm : (0 : Multiset Real).esymm (r + 1) = 0 :=
            Multiset.esymm_of_card_lt (by simp)
          change (Polynomial.C (1 : Real)).coeff (r + 1) =
            (0 : Multiset Real).esymm (r + 1)
          rw [hm, Polynomial.coeff_C_succ]
  | cons a s ih =>
      have hc : ((a :: s : List Real) : Multiset Real) =
          Multiset.cons a (s : Multiset Real) := rfl
      cases r with
      | zero =>
          rw [Multiset.esymm_zero]
          have h0 : (bernoulliOddsProduct s).coeff 0 = 1 := by
            simpa only [Multiset.esymm_zero] using ih 0
          change ((1 + Polynomial.C a * Polynomial.X) *
            bernoulliOddsProduct s).coeff 0 = 1
          simp only [add_mul, one_mul, mul_assoc, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_mul_zero,
            mul_zero, add_zero, h0]
      | succ r =>
          rw [hc, Multiset.esymm_cons_succ_ordered]
          change ((1 + Polynomial.C a * Polynomial.X) *
            bernoulliOddsProduct s).coeff (r + 1) = _
          simp only [add_mul, one_mul, mul_assoc, Polynomial.coeff_add,
            Polynomial.coeff_C_mul, Polynomial.coeff_X_mul, ih]

theorem bernoulli_esymm_mono (s t : List Real)
    (hst : BernoulliCoordinateLE s t)
    (hs0 : forall a, List.Mem a s -> 0 <= a)
    (ht0 : forall a, List.Mem a t -> 0 <= a) (r : Nat) :
    (s : Multiset Real).esymm r <= (t : Multiset Real).esymm r := by
  revert hs0 ht0
  induction hst generalizing r with
  | nil =>
      intro hs0 ht0
      exact le_rfl
  | @cons a b s t hab hst ih =>
      intro hs0 ht0
      have hs : forall c, List.Mem c s -> 0 <= c :=
        fun c hc => hs0 c (List.Mem.tail _ hc)
      have ht : forall c, List.Mem c t -> 0 <= c :=
        fun c hc => ht0 c (List.Mem.tail _ hc)
      have hb : 0 <= b := ht0 b (List.Mem.head _)
      cases r with
      | zero => simp
      | succ r =>
          change (Multiset.cons a (s : Multiset Real)).esymm (r + 1) <=
            (Multiset.cons b (t : Multiset Real)).esymm (r + 1)
          rw [Multiset.esymm_cons_succ_ordered, Multiset.esymm_cons_succ_ordered]
          exact add_le_add (ih (r + 1) hs ht)
            (mul_le_mul hab (ih r hs ht)
              (Multiset.esymm_nonneg_ordered _ (fun c hc => hs c hc) r) hb)

theorem bernoulli_esymm_replicate_zero (n r : Nat) :
    ((List.replicate n (0 : Real) : List Real) : Multiset Real).esymm r =
      (0 : Multiset Real).esymm r := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
      cases r with
      | zero => simp
      | succ r =>
          change (Multiset.cons 0
            ((List.replicate n (0 : Real) : List Real) : Multiset Real)).esymm (r + 1) = _
          rw [Multiset.esymm_cons_succ_ordered, zero_mul, add_zero, ih]

theorem bernoulli_esymm_append_zeros (s : List Real) (n r : Nat) :
    ((s ++ List.replicate n (0 : Real) : List Real) : Multiset Real).esymm r =
      (s : Multiset Real).esymm r := by
  induction s generalizing r with
  | nil => simpa using bernoulli_esymm_replicate_zero n r
  | cons a s ih =>
      cases r with
      | zero => simp
      | succ r =>
          change (Multiset.cons a
            ((s ++ List.replicate n (0 : Real) : List Real) : Multiset Real)).esymm
              (r + 1) = (Multiset.cons a (s : Multiset Real)).esymm (r + 1)
          rw [Multiset.esymm_cons_succ_ordered, Multiset.esymm_cons_succ_ordered,
            ih (r + 1), ih r]

theorem bernoulliOddsProduct_coeff_mono_padded
    (s t : List Real) (n r : Nat)
    (hst : BernoulliCoordinateLE (s ++ List.replicate n (0 : Real)) t)
    (hs0 : forall a, List.Mem a s -> 0 <= a)
    (ht0 : forall a, List.Mem a t -> 0 <= a) :
    (bernoulliOddsProduct s).coeff r <= (bernoulliOddsProduct t).coeff r := by
  have hp : forall a, List.Mem a (s ++ List.replicate n (0 : Real)) -> 0 <= a := by
    intro a ha
    cases List.mem_append.mp ha with
    | inl hs => exact hs0 a hs
    | inr hz =>
        have hzero : a = 0 := (List.mem_replicate.mp hz).2
        subst a
        exact le_refl _
  have h := bernoulli_esymm_mono _ _ hst hp ht0 r
  simpa only [bernoulliOddsProduct_coeff, bernoulli_esymm_append_zeros] using h

end List
