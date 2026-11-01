/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeWordLaw
import PrimeFactorOscillations.Helpers.NativePrimeSmallCycles

/-! # Seven-wise independence of actual signed native rows

Any at most seven distinct lower/upper rows have every Boolean sign word
with reciprocal-prime limiting probability equal to its fair product value.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter FiniteFieldIntegerWindowTransfer
open scoped Classical
attribute [local instance] Classical.propDecidable

theorem native_signed_small_mask_empty (P : Finset Nat)
    (A B O T : Finset (Prod Nat Nat))
    (hA : A <= nativePrimeVertexEdges P)
    (hO : O <= A) (hT : T <= B) (hsize : A.card + B.card <= 7)
    (hmask : nativeSignedCycleMask P O T) : And (O = {}) (T = {}) := by
  have heq : O = T := hmask.1
  have hleft := Finset.card_le_card hO
  have hright := Finset.card_le_card hT
  have hcard : O.card <= 3 := by rw [<- heq] at hright; omega
  have hzero := native_small_even_cycle_empty P O (hO.trans hA)
    hmask.2.1 hcard hmask.2.2
  exact And.intro hzero (heq.symm.trans hzero)

theorem native_signed_word_rate_seven (P : Finset Nat)
    (A B : Finset (Prod Nat Nat))
    (hA : A <= nativePrimeVertexEdges P)
    (hsize : A.card + B.card <= 7) (a b : Prod Nat Nat -> Bool) :
    nativeSignedWordRate P A B a b = 1 / (2 : Real) ^ (A.card + B.card) := by
  have hinner (O : Finset (Prod Nat Nat)) (hO : Membership.mem A.powerset O) :
      B.powerset.sum (fun T => nativeSignedWordMaskCoefficient O T a b *
        (if nativeSignedCycleMask P O T then 1 else 0)) =
          if O = {} then 1 else 0 := by
    by_cases hz : O = {}
    . subst O
      rw [ite_eq_left rfl]
      rw [Finset.sum_eq_single {}]
      . simp [nativeSignedWordMaskCoefficient, nativeSignedCycleMask,
          nativePrimeVertexCycleDegree]
      . intro T hT hne
        have hn : Not (nativeSignedCycleMask P {} T) := by
          intro hm
          exact hne hm.1.symm
        rw [ite_eq_right hn, mul_zero]
      . intro hn
        exact False.elim (hn (by simp))
    . rw [ite_eq_right hz]
      apply Finset.sum_eq_zero
      intro T hT
      by_cases hm : nativeSignedCycleMask P O T
      . have hempty := native_signed_small_mask_empty P A B O T hA
          (Finset.mem_powerset.mp hO) (Finset.mem_powerset.mp hT) hsize hm
        exact False.elim (hz hempty.1)
      . rw [ite_eq_right hm, mul_zero]
  have hsum : A.powerset.sum (fun O =>
      B.powerset.sum (fun T => nativeSignedWordMaskCoefficient O T a b *
        (if nativeSignedCycleMask P O T then 1 else 0))) = 1 := by
    calc
      _ = A.powerset.sum (fun O => if O = {} then (1 : Real) else 0) := by
        apply Finset.sum_congr rfl
        exact hinner
      _ = 1 := by simp
  rw [nativeSignedWordRate, hsum, mul_one]

theorem native_signed_word_ratio_tendsto_seven (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (hind : nativePrimeVertexGapIndependent P)
    (A B : Finset (Prod Nat Nat))
    (hA : A <= nativePrimeVertexEdges P) (hB : B <= nativePrimeVertexEdges P)
    (hsize : A.card + B.card <= 7) (a b : Prod Nat Nat -> Bool) :
    Tendsto (fun U : Nat =>
      nativeSignedWordMass A B a b (preciseCore U + 1) (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (1 / (2 : Real) ^ (A.card + B.card))) := by
  rw [<- native_signed_word_rate_seven P A B hA hsize a b]
  exact native_signed_word_ratio_tendsto P hP hind A B hA hB a b

theorem native_reservoir_signed_word_ratio_tendsto_seven
    (R : Nat -> Prop) [DecidablePred R] (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p ->
      Membership.mem (nativePrimeVertexGapReservoirClass R) p)
    (A B : Finset (Prod Nat Nat))
    (hA : A <= nativePrimeVertexEdges P) (hB : B <= nativePrimeVertexEdges P)
    (hsize : A.card + B.card <= 7) (a b : Prod Nat Nat -> Bool) :
    Tendsto (fun U : Nat =>
      nativeSignedWordMass A B a b (preciseCore U + 1) (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (1 / (2 : Real) ^ (A.card + B.card))) := by
  rw [<- native_signed_word_rate_seven P A B hA hsize a b]
  exact native_reservoir_signed_word_ratio_tendsto R P hP A B hA hB a b

end PrimeFactorOscillations.FiniteFieldIntegerSignature
