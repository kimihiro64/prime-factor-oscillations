/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.PSeries
import PrimeFactorOscillations.Helpers.PrimeClassSpecialValueCapacity

/-!
# Invariance of prime-class decoding capacity under sparse deletion

Every prime class has a nonempty set of convergent positive exponents.
Deleting a class of convergence exponent zero preserves that entire set.
The capacity conclusion retains the summability hypothesis below one
from the exact decoder classification.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

theorem classPowerWeight_le_rpow (P : Set Nat) (s : Real) (p : Nat) :
    classPowerWeight P s p <= (p : Real) ^ (-s) := by
  classical
  unfold classPowerWeight
  split_ifs
  case pos => exact le_refl _
  case neg => exact Real.rpow_nonneg (Nat.cast_nonneg p) _

theorem classPowerWeight_summable_two (P : Set Nat) :
    Summable (classPowerWeight P 2) := by
  have hs : Summable (fun n : Nat => (n : Real) ^ (-(2 : Real))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  exact Summable.of_nonneg_of_le (classPowerWeight_nonneg P 2)
    (classPowerWeight_le_rpow P 2) hs

theorem primeClassConvergentExponents_nonempty (P : Set Nat) :
    (primeClassConvergentExponents P).Nonempty :=
  Exists.intro 2 (And.intro (by norm_num) (classPowerWeight_summable_two P))

theorem classPowerWeight_summable_of_zero_exponent
    (Q : Set Nat) (hQ : primeClassConvergenceExponent Q = 0)
    (s : Real) (hs : 0 < s) : Summable (classPowerWeight Q s) := by
  apply classPowerWeight_summable_above_convergenceExponent Q 2 s
    (by norm_num) (classPowerWeight_summable_two Q)
  simpa only [hQ] using hs

theorem classPowerWeight_mono_class
    (P Q : Set Nat) (hPQ : forall p, Membership.mem P p -> Membership.mem Q p)
    (s : Real) (p : Nat) : classPowerWeight P s p <= classPowerWeight Q s p := by
  classical
  by_cases hp : And (Nat.Prime p) (Membership.mem P p)
  case pos =>
    have hq : And (Nat.Prime p) (Membership.mem Q p) := And.intro hp.1 (hPQ p hp.2)
    simp only [classPowerWeight, ite_eq_left hp, ite_eq_left hq]
    exact le_refl _
  case neg =>
    simpa only [classPowerWeight, ite_eq_right hp] using classPowerWeight_nonneg Q s p

theorem classPowerWeight_summable_of_subset
    (P Q : Set Nat) (hPQ : forall p, Membership.mem P p -> Membership.mem Q p)
    (s : Real) (hQ : Summable (classPowerWeight Q s)) :
    Summable (classPowerWeight P s) :=
  Summable.of_nonneg_of_le (classPowerWeight_nonneg P s)
    (classPowerWeight_mono_class P Q hPQ s) hQ

theorem classPowerWeight_diff_inter_identity (P Q : Set Nat) (s : Real) (p : Nat) :
    classPowerWeight P s p =
      classPowerWeight (Set.diff P Q) s p + classPowerWeight (Set.inter P Q) s p := by
  classical
  by_cases hp : Nat.Prime p <;> by_cases hP : Membership.mem P p <;>
    by_cases hQ : Membership.mem Q p
  all_goals simp [classPowerWeight, Set.diff, Set.inter, hp, hP, hQ]

theorem classPowerWeight_sum_diff_inter_identity
    (P Q : Set Nat) (s : Real) (u : Finset Nat) :
    u.sum (classPowerWeight P s) =
      u.sum (classPowerWeight (Set.diff P Q) s) +
        u.sum (classPowerWeight (Set.inter P Q) s) := by
  rw [<- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  exact classPowerWeight_diff_inter_identity P Q s p

theorem classPowerWeight_summable_diff_iff
    (P Q : Set Nat) (s : Real) (hQ : Summable (classPowerWeight Q s)) :
    Summable (classPowerWeight (Set.diff P Q) s) <-> Summable (classPowerWeight P s) := by
  constructor
  case mp =>
    intro hdiff
    have hinter := classPowerWeight_summable_of_subset (Set.inter P Q) Q
      (fun _ hp => hp.2) s hQ
    apply (hdiff.add hinter).congr
    intro p
    exact (classPowerWeight_diff_inter_identity P Q s p).symm
  case mpr =>
    intro hP
    exact classPowerWeight_summable_of_subset (Set.diff P Q) P
      (fun _ hp => hp.1) s hP

theorem primeClassConvergentExponents_diff_eq
    (P Q : Set Nat) (hQ : primeClassConvergenceExponent Q = 0) :
    primeClassConvergentExponents (Set.diff P Q) = primeClassConvergentExponents P := by
  apply Set.ext
  intro s
  change And (0 < s) (Summable (classPowerWeight (Set.diff P Q) s)) <->
    And (0 < s) (Summable (classPowerWeight P s))
  constructor
  case mp =>
    intro hs
    exact And.intro hs.1 ((classPowerWeight_summable_diff_iff P Q s
      (classPowerWeight_summable_of_zero_exponent Q hQ s hs.1)).mp hs.2)
  case mpr =>
    intro hs
    exact And.intro hs.1 ((classPowerWeight_summable_diff_iff P Q s
      (classPowerWeight_summable_of_zero_exponent Q hQ s hs.1)).mpr hs.2)

theorem primeClassConvergenceExponent_diff_eq
    (P Q : Set Nat) (hQ : primeClassConvergenceExponent Q = 0) :
    primeClassConvergenceExponent (Set.diff P Q) = primeClassConvergenceExponent P := by
  unfold primeClassConvergenceExponent
  rw [primeClassConvergentExponents_diff_eq P Q hQ]

theorem integerDecoderCapacity_diff_eq
    (P Q : Set Nat) (s0 : Real) (hs0 : 0 < s0) (hs01 : s0 < 1)
    (hsum : Summable (classPowerWeight P s0))
    (hQ : primeClassConvergenceExponent Q = 0) :
    integerDecoderCapacity (Set.diff P Q) = integerDecoderCapacity P := by
  have hdiff := classPowerWeight_summable_of_subset (Set.diff P Q) P
    (fun _ hp => hp.1) s0 hsum
  rw [integerDecoderCapacity_eq_inverse_convergenceExponent (Set.diff P Q) s0 hs0 hs01 hdiff,
    integerDecoderCapacity_eq_inverse_convergenceExponent P s0 hs0 hs01 hsum,
    primeClassConvergenceExponent_diff_eq P Q hQ]

theorem classPowerWeight_union_le_add (P Q : Set Nat) (s : Real) (p : Nat) :
    classPowerWeight (Set.union P Q) s p <=
      classPowerWeight P s p + classPowerWeight Q s p := by
  classical
  have hn := Real.rpow_nonneg (Nat.cast_nonneg p) (-s)
  by_cases hp : Nat.Prime p <;> by_cases hP : Membership.mem P p <;>
    by_cases hQ : Membership.mem Q p
  all_goals simp [classPowerWeight, Set.union, hp, hP, hQ, hn]

theorem classPowerWeight_summable_union
    (P Q : Set Nat) (s : Real) (hP : Summable (classPowerWeight P s))
    (hQ : Summable (classPowerWeight Q s)) :
    Summable (classPowerWeight (Set.union P Q) s) :=
  Summable.of_nonneg_of_le (classPowerWeight_nonneg (Set.union P Q) s)
    (classPowerWeight_union_le_add P Q s) (hP.add hQ)

def specialPrimeValueUnion : Set Nat :=
  Set.union fermatPrimeValues (Set.union mersennePrimeValues fibonacciPrimeValues)

theorem specialPrimeValueUnion_all_positive_power_summable
    (s : Real) (hs : 0 < s) :
    Summable (classPowerWeight specialPrimeValueUnion s) := by
  apply classPowerWeight_summable_union fermatPrimeValues
    (Set.union mersennePrimeValues fibonacciPrimeValues) s
    (fermatPrimeValues_all_positive_power_summable s hs)
  exact classPowerWeight_summable_union mersennePrimeValues fibonacciPrimeValues s
    (mersennePrimeValues_all_positive_power_summable s hs)
    (fibonacciPrimeValues_all_positive_power_summable s hs)

theorem specialPrimeValueUnion_convergenceExponent_zero :
    primeClassConvergenceExponent specialPrimeValueUnion = 0 :=
  primeClassConvergenceExponent_zero_of_all_positive_summable specialPrimeValueUnion
    specialPrimeValueUnion_all_positive_power_summable

theorem primeClassConvergenceExponent_diff_specialPrimeValueUnion (P : Set Nat) :
    primeClassConvergenceExponent (Set.diff P specialPrimeValueUnion) =
      primeClassConvergenceExponent P :=
  primeClassConvergenceExponent_diff_eq P specialPrimeValueUnion
    specialPrimeValueUnion_convergenceExponent_zero

theorem integerDecoderCapacity_diff_specialPrimeValueUnion
    (P : Set Nat) (s0 : Real) (hs0 : 0 < s0) (hs01 : s0 < 1)
    (hsum : Summable (classPowerWeight P s0)) :
    integerDecoderCapacity (Set.diff P specialPrimeValueUnion) = integerDecoderCapacity P :=
  integerDecoderCapacity_diff_eq P specialPrimeValueUnion s0 hs0 hs01 hsum
    specialPrimeValueUnion_convergenceExponent_zero

theorem primeClassConvergenceExponent_zero_of_subset_specialPrimeValueUnion
    (Q : Set Nat)
    (hQ : forall p, Membership.mem Q p -> Membership.mem specialPrimeValueUnion p) :
    primeClassConvergenceExponent Q = 0 := by
  apply primeClassConvergenceExponent_zero_of_all_positive_summable Q
  intro s hs
  exact classPowerWeight_summable_of_subset Q specialPrimeValueUnion hQ s
    (specialPrimeValueUnion_all_positive_power_summable s hs)

theorem primeClassConvergenceExponent_diff_subset_specialPrimeValueUnion
    (P Q : Set Nat)
    (hQ : forall p, Membership.mem Q p -> Membership.mem specialPrimeValueUnion p) :
    primeClassConvergenceExponent (Set.diff P Q) = primeClassConvergenceExponent P :=
  primeClassConvergenceExponent_diff_eq P Q
    (primeClassConvergenceExponent_zero_of_subset_specialPrimeValueUnion Q hQ)

theorem integerDecoderCapacity_diff_subset_specialPrimeValueUnion
    (P Q : Set Nat) (s0 : Real) (hs0 : 0 < s0) (hs01 : s0 < 1)
    (hsum : Summable (classPowerWeight P s0))
    (hQ : forall p, Membership.mem Q p -> Membership.mem specialPrimeValueUnion p) :
    integerDecoderCapacity (Set.diff P Q) = integerDecoderCapacity P :=
  integerDecoderCapacity_diff_eq P Q s0 hs0 hs01 hsum
    (primeClassConvergenceExponent_zero_of_subset_specialPrimeValueUnion Q hQ)

end PrimeFactorOscillations.PrimeClassSampling
