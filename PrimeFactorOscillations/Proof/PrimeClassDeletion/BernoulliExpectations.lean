/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Proof.PrimeClassDeletion.BernoulliDominance

/-! # Increasing tests of finite Bernoulli laws

The finite Abel identity retains its upper boundary term until the support
bound is proved. Tests may have either sign at zero. All comparisons use
the established Bernoulli masses and their exact tails.
-/

set_option autoImplicit false
set_option Elab.async false

namespace List

noncomputable def bernoulliExpectation (s : List Real) (phi : Nat -> Real) : Real :=
  (Finset.range (s.length + 1)).sum (fun r => phi r * bernoulliMass s r)

theorem bernoulliTail_eq_zero_of_length_lt (s : List Real) (r : Nat)
    (hr : s.length < r) : bernoulliTail s r = 0 := by
  induction s generalizing r with
  | nil =>
      cases r with
      | zero => simp at hr
      | succ r => rfl
  | cons a s ih =>
      cases r with
      | zero => simp at hr
      | succ r =>
          have hs : s.length < r := by simpa only [List.length_cons,
            Nat.succ_lt_succ_iff] using hr
          simp only [bernoulliTail, ih r hs,
            ih (r + 1) (Nat.lt_trans hs (Nat.lt_succ_self r)), mul_zero, add_zero]

theorem bernoulliMass_eq_zero_of_length_lt (s : List Real) (r : Nat)
    (hr : s.length < r) : bernoulliMass s r = 0 := by
  rw [<- bernoulliTail_sub_succ,
    bernoulliTail_eq_zero_of_length_lt s r hr,
    bernoulliTail_eq_zero_of_length_lt s (r + 1)
      (Nat.lt_trans hr (Nat.lt_succ_self r)), sub_self]

theorem bernoulli_sum_by_tails (s : List Real) (phi : Nat -> Real) (m : Nat) :
    (Finset.range (m + 1)).sum (fun r => phi r * bernoulliMass s r) =
      phi 0 + (Finset.range m).sum
        (fun k => (phi (k + 1) - phi k) * bernoulliTail s (k + 1)) -
        phi m * bernoulliTail s (m + 1) := by
  induction m with
  | zero =>
      simp only [Nat.zero_add, Finset.range_one, Finset.sum_singleton,
        Finset.range_zero, Finset.sum_empty, add_zero]
      rw [<- bernoulliTail_sub_succ]
      simp only [bernoulliTail]
      ring
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      rw [<- bernoulliTail_sub_succ s (m + 1)]
      ring

theorem bernoulliExpectation_eq_tail_sum (s : List Real) (phi : Nat -> Real) :
    bernoulliExpectation s phi = phi 0 + (Finset.range s.length).sum
      (fun k => (phi (k + 1) - phi k) * bernoulliTail s (k + 1)) := by
  rw [bernoulliExpectation, bernoulli_sum_by_tails,
    bernoulliTail_eq_zero_of_length_lt s (s.length + 1) (Nat.lt_succ_self _),
    mul_zero, sub_zero]

theorem bernoulliExpectation_eq_tail_sum_of_length_le
    (s : List Real) (phi : Nat -> Real) (m : Nat) (hm : s.length <= m) :
    bernoulliExpectation s phi = phi 0 + (Finset.range m).sum
      (fun k => (phi (k + 1) - phi k) * bernoulliTail s (k + 1)) := by
  rw [bernoulliExpectation_eq_tail_sum]
  congr 1
  apply Finset.sum_subset (Finset.range_mono hm)
  intro k hk hnot
  have hlarge : s.length <= k := by
    simpa only [Finset.mem_range, not_lt] using hnot
  rw [bernoulliTail_eq_zero_of_length_lt s (k + 1)
    (Nat.lt_of_le_of_lt hlarge (Nat.lt_succ_self k)), mul_zero]

theorem bernoulliExpectation_le_of_tails
    (s t : List Real) (hlen : s.length <= t.length)
    (htails : forall r, bernoulliTail s r <= bernoulliTail t r)
    (phi : Nat -> Real)
    (hphi : forall k, k < t.length -> phi k <= phi (k + 1)) :
    bernoulliExpectation s phi <= bernoulliExpectation t phi := by
  rw [bernoulliExpectation_eq_tail_sum_of_length_le s phi t.length hlen,
    bernoulliExpectation_eq_tail_sum]
  apply add_le_add (le_refl _)
  apply Finset.sum_le_sum
  intro k hk
  exact mul_le_mul_of_nonneg_left (htails (k + 1))
    (sub_nonneg.mpr (hphi k (Finset.mem_range.mp hk)))

theorem bernoulliExpectation_const (s : List Real) (c : Real) :
    bernoulliExpectation s (fun _ => c) = c := by
  simp [bernoulliExpectation_eq_tail_sum]

theorem sum_bernoulliMass (s : List Real) :
    (Finset.range (s.length + 1)).sum (fun r => bernoulliMass s r) = 1 := by
  simpa only [bernoulliExpectation, one_mul] using bernoulliExpectation_const s 1

theorem bernoulliExpectation_neg (s : List Real) (phi : Nat -> Real) :
    bernoulliExpectation s (fun r => -phi r) = -bernoulliExpectation s phi := by
  simp [bernoulliExpectation, neg_mul, Finset.sum_neg_distrib]

theorem bernoulliExpectation_le_of_antitone_tails
    (s t : List Real) (hlen : s.length <= t.length)
    (htails : forall r, bernoulliTail s r <= bernoulliTail t r)
    (phi : Nat -> Real)
    (hphi : forall k, k < t.length -> phi (k + 1) <= phi k) :
    bernoulliExpectation t phi <= bernoulliExpectation s phi := by
  have h := bernoulliExpectation_le_of_tails s t hlen htails
    (fun r => -phi r) (fun k hk => neg_le_neg (hphi k hk))
  simpa only [bernoulliExpectation_neg, neg_le_neg_iff] using h

theorem bernoulliExpectation_pow_le_of_one_le
    (s t : List Real) (hlen : s.length <= t.length)
    (htails : forall r, bernoulliTail s r <= bernoulliTail t r)
    (z : Real) (hz : 1 <= z) :
    bernoulliExpectation s (fun r => z ^ r) <=
      bernoulliExpectation t (fun r => z ^ r) := by
  apply bernoulliExpectation_le_of_tails s t hlen htails
  intro k hk
  have hp : 0 <= z ^ k := pow_nonneg (le_trans zero_le_one hz) k
  have h := mul_le_mul_of_nonneg_left hz hp
  simpa only [mul_one, <- pow_succ] using h

theorem bernoulliExpectation_pow_le_of_mem_unit
    (s t : List Real) (hlen : s.length <= t.length)
    (htails : forall r, bernoulliTail s r <= bernoulliTail t r)
    (z : Real) (hz0 : 0 <= z) (hz1 : z <= 1) :
    bernoulliExpectation t (fun r => z ^ r) <=
      bernoulliExpectation s (fun r => z ^ r) := by
  apply bernoulliExpectation_le_of_antitone_tails s t hlen htails
  intro k hk
  have h := mul_le_mul_of_nonneg_left hz1 (pow_nonneg hz0 k)
  simpa only [mul_one, <- pow_succ] using h

end List
