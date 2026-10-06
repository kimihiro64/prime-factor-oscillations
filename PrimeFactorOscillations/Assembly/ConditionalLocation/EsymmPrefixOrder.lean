/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.RingTheory.MvPolynomial.Symmetric.RationalBounds

/-!
# Esymm Prefix Order

Maintained implementation of the conditional last-ascent location argument.
The arithmetic coverage assumptions remain explicit; no conjecture is an axiom.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Multiset

/-- Strong coefficient log concavity, including all zero tail coefficients. -/
theorem esymm_cross_le_rat (s : Multiset Rat)
    (hs : forall a, Membership.mem s a -> 0 <= a)
    (i j : Nat) (hij : i <= j) :
    s.esymm i * s.esymm (j + 1) <= s.esymm (i + 1) * s.esymm j := by
  induction s using Multiset.induction_on generalizing i j with
  | empty =>
      rw [esymm_of_card_lt (show (0 : Multiset Rat).card < j + 1 by simp),
        esymm_of_card_lt (show (0 : Multiset Rat).card < i + 1 by simp)]
      simp
  | @cons a s ih =>
      have ha : 0 <= a := hs a (by simp)
      have ht : forall b, Membership.mem s b -> 0 <= b :=
        fun b hb => hs b (by simp [hb])
      cases i with
      | zero =>
          cases j with
          | zero => simp only [esymm_zero, one_mul, mul_one, le_refl]
          | succ j =>
              have hbase := ih ht 0 (j + 1) (Nat.zero_le _)
              simp only [esymm_zero, one_mul] at hbase
              have hpos := mul_nonneg
                (mul_nonneg ha (esymm_nonneg_rat s ht 1))
                (esymm_nonneg_rat s ht j)
              have hsq := mul_nonneg (sq_nonneg a) (esymm_nonneg_rat s ht j)
              simp only [esymm_zero, one_mul, esymm_cons_succ_rat]
              nlinarith only [hbase, hpos, hsq]
      | succ i =>
          cases j with
          | zero => omega
          | succ j =>
              have hij' : i <= j := by omega
              have hhi := ih ht (i + 1) (j + 1) (by omega)
              have hlo := ih ht i j hij'
              have hmid : s.esymm i * s.esymm (j + 2) <=
                  s.esymm (i + 2) * s.esymm j := by
                by_cases heq : i = j
                next => subst j; exact le_of_eq (mul_comm _ _)
                next =>
                  exact (ih ht i (j + 1) (by omega)).trans
                    (ih ht (i + 1) j (by omega))
              have hm := mul_nonneg ha (sub_nonneg.mpr hmid)
              have hl := mul_nonneg (sq_nonneg a) (sub_nonneg.mpr hlo)
              simp only [esymm_cons_succ_rat]
              nlinarith only [hhi, hm, hl]

/-- Adding a nonnegative weight lowers every supported adjacent ratio. -/
theorem esymm_ratio_cons_le_rat (s : Multiset Rat)
    (hs : forall a, Membership.mem s a -> 0 <= a)
    (a : Rat) (ha : 0 <= a) (r : Nat) (hr : 1 <= r)
    (hden : 0 < s.esymm r) :
    (cons a s).esymm (r - 1) / (cons a s).esymm r <=
      s.esymm (r - 1) / s.esymm r := by
  cases r with
  | zero => omega
  | succ r =>
      have hnew : 0 < (cons a s).esymm (r + 1) := by
        rw [esymm_cons_succ_rat]
        exact add_pos_of_pos_of_nonneg hden
          (mul_nonneg ha (esymm_nonneg_rat s hs r))
      simp only [Nat.add_sub_cancel]
      have hcross : (cons a s).esymm r * s.esymm (r + 1) <=
          (cons a s).esymm (r + 1) * s.esymm r := by
        cases r with
        | zero =>
            simp only [esymm_zero, one_mul, esymm_cons_succ_rat, mul_one]
            linarith
        | succ r =>
            have hlog := esymm_cross_le_rat s hs r (r + 1) (by omega)
            have hm := mul_nonneg ha (sub_nonneg.mpr hlog)
            simp only [esymm_cons_succ_rat]
            nlinarith only [hm]
      have hdiv := div_le_div_of_nonneg_right hcross
        (le_of_lt (mul_pos hnew hden))
      simpa only [mul_div_mul_right _ _ (ne_of_gt hden),
        mul_div_mul_left _ _ (ne_of_gt hnew)] using hdiv

end Multiset
