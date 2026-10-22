/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimePowerComponentIndependence

/-!
# Exact common mass of two full component laws

The common atoms are precisely the integers supported on the intersection.
On those atoms both laws are constant multiples of the same reciprocal
weight. The smaller density is selected by the larger normalizer.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

noncomputable def classPrimePowerNormalizer (P : Set Nat) : Real :=
  tsum (classPrimePowerWeight P 1)

noncomputable def classPrimePowerOverlap (P Q : Set Nat) : Real :=
  classPrimePowerNormalizer (Set.inter P Q) /
    max (classPrimePowerNormalizer P) (classPrimePowerNormalizer Q)

theorem classPrimePowerSupported_mono
    (P Q : Set Nat)
    (hPQ : forall p : Nat, Membership.mem P p -> Membership.mem Q p)
    (a : Nat) (ha : classPrimePowerSupported P a) :
    classPrimePowerSupported Q a := by
  exact And.intro ha.1 (fun p hp => hPQ p (ha.2 p hp))

theorem classPrimePowerSupported_inter (P Q : Set Nat) (a : Nat) :
    classPrimePowerSupported (Set.inter P Q) a <->
      And (classPrimePowerSupported P a) (classPrimePowerSupported Q a) := by
  constructor
  case mp =>
    intro ha
    exact And.intro
      (And.intro ha.1 (fun p hp => (ha.2 p hp).1))
      (And.intro ha.1 (fun p hp => (ha.2 p hp).2))
  case mpr =>
    intro ha
    exact And.intro ha.1.1
      (fun p hp => And.intro (ha.1.2 p hp) (ha.2.2 p hp))

theorem classPrimePowerWeight_mono
    (P Q : Set Nat)
    (hPQ : forall p : Nat, Membership.mem P p -> Membership.mem Q p)
    (sigma : Real) (a : Nat) :
    classPrimePowerWeight P sigma a <= classPrimePowerWeight Q sigma a := by
  classical
  by_cases ha : classPrimePowerSupported P a
  case pos =>
    have hb := classPrimePowerSupported_mono P Q hPQ a ha
    simp only [classPrimePowerWeight, ite_eq_left ha, ite_eq_left hb]
    exact le_rfl
  case neg =>
    have hz : classPrimePowerWeight P sigma a = 0 := by
      simp only [classPrimePowerWeight, ite_eq_right ha]
    rw [hz]
    exact classPrimePowerWeight_nonneg Q sigma a

theorem classPrimePowerWeight_inter_summable
    (P Q : Set Nat) (hsum : Summable (classPowerWeight P 1)) :
    Summable (classPrimePowerWeight (Set.inter P Q) 1) := by
  exact Summable.of_nonneg_of_le
    (classPrimePowerWeight_nonneg (Set.inter P Q) 1)
    (fun a => classPrimePowerWeight_mono (Set.inter P Q) P
      (fun p hp => hp.1) 1 a)
    (classPrimePowerWeight_summable P 1 zero_lt_one hsum)

theorem classPrimePowerReference_min
    (P Q : Set Nat)
    (hP : Summable (classPowerWeight P 1))
    (hQ : Summable (classPowerWeight Q 1)) (a : Nat) :
    min (classPrimePowerReference P a) (classPrimePowerReference Q a) =
      classPrimePowerWeight (Set.inter P Q) 1 a /
        max (classPrimePowerNormalizer P) (classPrimePowerNormalizer Q) := by
  classical
  have hZP : 0 < classPrimePowerNormalizer P :=
    classPrimePowerWeight_tsum_pos P 1 zero_lt_one hP
  have hZQ : 0 < classPrimePowerNormalizer Q :=
    classPrimePowerWeight_tsum_pos Q 1 zero_lt_one hQ
  by_cases haP : classPrimePowerSupported P a
  case pos =>
    by_cases haQ : classPrimePowerSupported Q a
    case pos =>
      have haI := (classPrimePowerSupported_inter P Q a).mpr (And.intro haP haQ)
      have hwP : classPrimePowerWeight P 1 a = (a : Real) ^ (-(1 : Real)) := by
        simp only [classPrimePowerWeight, ite_eq_left haP]
      have hwQ : classPrimePowerWeight Q 1 a = (a : Real) ^ (-(1 : Real)) := by
        simp only [classPrimePowerWeight, ite_eq_left haQ]
      have hwI : classPrimePowerWeight (Set.inter P Q) 1 a =
          (a : Real) ^ (-(1 : Real)) := by
        simp only [classPrimePowerWeight, ite_eq_left haI]
      change min
        (classPrimePowerWeight P 1 a / classPrimePowerNormalizer P)
        (classPrimePowerWeight Q 1 a / classPrimePowerNormalizer Q) = _
      rw [hwP, hwQ, hwI]
      have hw : 0 <= (a : Real) ^ (-(1 : Real)) :=
        Real.rpow_nonneg (Nat.cast_nonneg a) _
      by_cases hZ : classPrimePowerNormalizer P <= classPrimePowerNormalizer Q
      case pos =>
        have hd := div_le_div_of_nonneg_left hw hZP hZ
        rw [min_eq_right hd, max_eq_right hZ]
      case neg =>
        have hZ' : classPrimePowerNormalizer Q <= classPrimePowerNormalizer P :=
          le_of_lt (lt_of_not_ge hZ)
        have hd := div_le_div_of_nonneg_left hw hZQ hZ'
        rw [min_eq_left hd, max_eq_left hZ']
    case neg =>
      have haI : Not (classPrimePowerSupported (Set.inter P Q) a) := by
        intro ha
        exact haQ ((classPrimePowerSupported_inter P Q a).mp ha).2
      have hzQ : classPrimePowerReference Q a = 0 := by
        simp only [classPrimePowerReference, classPrimePowerWeight,
          ite_eq_right haQ, zero_div]
      have hzI : classPrimePowerWeight (Set.inter P Q) 1 a = 0 := by
        simp only [classPrimePowerWeight, ite_eq_right haI]
      rw [hzQ, hzI, zero_div, min_eq_right (classPrimePowerReference_nonneg P hP a)]
  case neg =>
    have haI : Not (classPrimePowerSupported (Set.inter P Q) a) := by
      intro ha
      exact haP ((classPrimePowerSupported_inter P Q a).mp ha).1
    have hzP : classPrimePowerReference P a = 0 := by
      simp only [classPrimePowerReference, classPrimePowerWeight,
        ite_eq_right haP, zero_div]
    have hzI : classPrimePowerWeight (Set.inter P Q) 1 a = 0 := by
      simp only [classPrimePowerWeight, ite_eq_right haI]
    rw [hzP, hzI, zero_div, min_eq_left (classPrimePowerReference_nonneg Q hQ a)]

end PrimeFactorOscillations.PrimeClassSampling
