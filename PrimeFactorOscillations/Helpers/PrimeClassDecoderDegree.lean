/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.Linarith
import PrimeFactorOscillations.Mathlib.Analysis.Polynomial.SignIntervals

/-!
# Exact degree obstruction for the prime-label sign decoder

The actual consecutive negative half-integers define the sign-change indices
and reported labels. Their cardinalities are bounded by the degree of every
nonzero real polynomial, with no accuracy or root-existence assumption.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDecoder

noncomputable def signChangeIndices (R : Nat) (p : Polynomial Real) : Finset Nat := by
  classical
  exact (Finset.Icc 1 R).filter (fun n =>
    p.eval (-(n : Real) + 1 / 2) * p.eval (-(n : Real) - 1 / 2) < 0)

noncomputable def decodedPrimeLabels (R : Nat) (p : Polynomial Real) : Finset Nat :=
  (signChangeIndices R p).image Nat.succ

theorem card_signChangeIndices_le_natDegree
    (R : Nat) (p : Polynomial Real) (hp : Not (p = 0)) :
    (signChangeIndices R p).card <= p.natDegree := by
  classical
  apply p.card_le_natDegree_of_disjoint_sign_intervals hp
    (signChangeIndices R p)
    (fun n => -(n : Real) - 1 / 2) (fun n => -(n : Real) + 1 / 2)
  case hab =>
    intro i hi
    linarith
  case hdis =>
    intro i hi j hj hne
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    change And (-(i : Real) - 1 / 2 < x) (x < -(i : Real) + 1 / 2) at hxi
    change And (-(j : Real) - 1 / 2 < x) (x < -(j : Real) + 1 / 2) at hxj
    rcases lt_or_gt_of_ne hne with hij | hji
    case inl =>
      have hreal : ((i + 1 : Nat) : Real) <= (j : Real) :=
        Nat.cast_le.mpr (Nat.succ_le_of_lt hij)
      simp only [Nat.cast_add, Nat.cast_one] at hreal
      linarith [hxi.1, hxj.2]
    case inr =>
      have hreal : ((j + 1 : Nat) : Real) <= (i : Real) :=
        Nat.cast_le.mpr (Nat.succ_le_of_lt hji)
      simp only [Nat.cast_add, Nat.cast_one] at hreal
      linarith [hxj.1, hxi.2]
  case hsign =>
    intro i hi
    have hs := (Finset.mem_filter.mp hi).2
    change p.eval (-(i : Real) + 1 / 2) *
      p.eval (-(i : Real) - 1 / 2) < 0 at hs
    simpa only [mul_comm] using hs

theorem card_decodedPrimeLabels_le_natDegree
    (R : Nat) (p : Polynomial Real) (hp : Not (p = 0)) :
    (decodedPrimeLabels R p).card <= p.natDegree := by
  exact (Finset.card_image_le).trans
    (card_signChangeIndices_le_natDegree R p hp)

end PrimeFactorOscillations.PrimeClassDecoder
