/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimePowerComponentOverlap

/-!
# Exact total variation between full component reference laws

No inclusion between the prime classes is required. The entire common
mass is the intersection normalizer divided by the larger normalizer.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

private theorem abs_sub_eq_add_sub_twice_min (u v : Real) :
    abs (u - v) = u + v - 2 * min u v := by
  by_cases h : u <= v
  case pos =>
    rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  case neg =>
    have h' : v <= u := le_of_lt (lt_of_not_ge h)
    rw [min_eq_right h', abs_of_nonneg (sub_nonneg.mpr h')]
    ring

theorem classPrimePowerReference_min_hasSum
    (P Q : Set Nat)
    (hP : Summable (classPowerWeight P 1))
    (hQ : Summable (classPowerWeight Q 1)) :
    HasSum (fun a => min (classPrimePowerReference P a) (classPrimePowerReference Q a))
      (classPrimePowerOverlap P Q) := by
  have h := (classPrimePowerWeight_inter_summable P Q hP).hasSum.div_const
    (max (classPrimePowerNormalizer P) (classPrimePowerNormalizer Q))
  have heq : (fun a => min (classPrimePowerReference P a) (classPrimePowerReference Q a)) =
      (fun a => classPrimePowerWeight (Set.inter P Q) 1 a /
        max (classPrimePowerNormalizer P) (classPrimePowerNormalizer Q)) := by
    funext a
    exact classPrimePowerReference_min P Q hP hQ a
  rw [heq]
  exact h

theorem classPrimePowerReference_l1_hasSum
    (P Q : Set Nat)
    (hP : Summable (classPowerWeight P 1))
    (hQ : Summable (classPowerWeight Q 1)) :
    HasSum (fun a => abs (classPrimePowerReference P a - classPrimePowerReference Q a))
      (2 * (1 - classPrimePowerOverlap P Q)) := by
  have h := ((classPrimePowerReference_hasSum_one P hP).add
    (classPrimePowerReference_hasSum_one Q hQ)).sub
      ((classPrimePowerReference_min_hasSum P Q hP hQ).mul_left 2)
  have heq : (fun a => abs (classPrimePowerReference P a - classPrimePowerReference Q a)) =
      (fun a => classPrimePowerReference P a + classPrimePowerReference Q a -
        2 * min (classPrimePowerReference P a) (classPrimePowerReference Q a)) := by
    funext a
    exact abs_sub_eq_add_sub_twice_min _ _
  rw [heq]
  have hc : (1 : Real) + 1 - 2 * classPrimePowerOverlap P Q =
      2 * (1 - classPrimePowerOverlap P Q) := by ring
  rw [hc] at h
  exact h

theorem classPrimePowerReference_totalVariation_eq
    (P Q : Set Nat)
    (hP : Summable (classPowerWeight P 1))
    (hQ : Summable (classPowerWeight Q 1)) :
    tsum (fun a => abs (classPrimePowerReference P a - classPrimePowerReference Q a)) / 2 =
      1 - classPrimePowerOverlap P Q := by
  rw [(classPrimePowerReference_l1_hasSum P Q hP hQ).tsum_eq]
  ring

theorem classPrimePowerNormalizer_mono
    (P Q : Set Nat)
    (hPQ : forall p : Nat, Membership.mem P p -> Membership.mem Q p)
    (hP : Summable (classPowerWeight P 1))
    (hQ : Summable (classPowerWeight Q 1)) :
    classPrimePowerNormalizer P <= classPrimePowerNormalizer Q := by
  exact Summable.tsum_le_tsum (fun a => classPrimePowerWeight_mono P Q hPQ 1 a)
    (classPrimePowerWeight_summable P 1 zero_lt_one hP)
    (classPrimePowerWeight_summable Q 1 zero_lt_one hQ)

theorem classPrimePowerReference_subset_totalVariation_eq
    (P Q : Set Nat)
    (hPQ : forall p : Nat, Membership.mem P p -> Membership.mem Q p)
    (hP : Summable (classPowerWeight P 1))
    (hQ : Summable (classPowerWeight Q 1)) :
    tsum (fun a => abs (classPrimePowerReference P a - classPrimePowerReference Q a)) / 2 =
      1 - classPrimePowerNormalizer P / classPrimePowerNormalizer Q := by
  have hI : Set.inter P Q = P := by
    apply Set.ext
    intro p
    constructor
    case mp => exact fun hp => hp.1
    case mpr => exact fun hp => And.intro hp (hPQ p hp)
  rw [classPrimePowerReference_totalVariation_eq P Q hP hQ]
  unfold classPrimePowerOverlap
  rw [hI, max_eq_right (classPrimePowerNormalizer_mono P Q hPQ hP hQ)]

theorem classPrimePowerOverlap_pos
    (P Q : Set Nat)
    (hP : Summable (classPowerWeight P 1))
    (_hQ : Summable (classPowerWeight Q 1)) :
    0 < classPrimePowerOverlap P Q := by
  have hsum := classPrimePowerWeight_inter_summable P Q hP
  have hone : (1 : Real) <= classPrimePowerNormalizer (Set.inter P Q) := by
    calc
      1 = ({1} : Finset Nat).sum (classPrimePowerWeight (Set.inter P Q) 1) := by
        simp only [Finset.sum_singleton, classPrimePowerWeight_one]
      _ <= _ := Summable.sum_le_tsum {1}
        (fun a ha => classPrimePowerWeight_nonneg (Set.inter P Q) 1 a) hsum
  have hd : 0 < max (classPrimePowerNormalizer P) (classPrimePowerNormalizer Q) :=
    lt_of_lt_of_le (classPrimePowerWeight_tsum_pos P 1 zero_lt_one hP)
      (le_max_left _ _)
  exact div_pos (lt_of_lt_of_le zero_lt_one hone) hd

theorem classPrimePowerReference_totalVariation_lt_one
    (P Q : Set Nat)
    (hP : Summable (classPowerWeight P 1))
    (hQ : Summable (classPowerWeight Q 1)) :
    tsum (fun a => abs (classPrimePowerReference P a - classPrimePowerReference Q a)) / 2 <
      1 := by
  rw [classPrimePowerReference_totalVariation_eq P Q hP hQ]
  have h := classPrimePowerOverlap_pos P Q hP hQ
  linarith

end PrimeFactorOscillations.PrimeClassSampling
