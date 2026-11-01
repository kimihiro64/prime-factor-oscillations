/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeSevenRows
import PrimeFactorOscillations.Helpers.NativePrimeFourCycle

/-! # The exact four-cycle law and failure of eight-wise independence -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter FiniteFieldIntegerWindowTransfer
open scoped Classical
attribute [local instance] Classical.propDecidable

theorem native_four_cycle_mask_iff (P : Finset Nat) (p q r s : Nat)
    (hp : Membership.mem P p) (hq : Membership.mem P q)
    (hr : Membership.mem P r) (hs : Membership.mem P s)
    (hpq : p < q) (hqr : q < r) (hrs : r < s)
    (O T : Finset (Prod Nat Nat))
    (hO : O <= nativePrimeFourCycle p q r s) :
    nativeSignedCycleMask P O T <->
      Or (And (O = {}) (T = {}))
        (And (O = nativePrimeFourCycle p q r s) (T = nativePrimeFourCycle p q r s)) := by
  have hC := native_four_cycle_support P p q r s hp hq hr hs hpq hqr hrs
  have hc := native_four_cycle_card p q r s hpq hqr hrs
  constructor
  . intro hm
    by_cases hz : O = {}
    . exact Or.inl (And.intro hz (hm.1.symm.trans hz))
    . have hnot : Not (O.card <= 3) := by
        intro hsmall
        exact hz (native_small_even_cycle_empty P O (hO.trans hC) hm.2.1 hsmall hm.2.2)
      have hle := Finset.card_le_card hO
      have hback : (nativePrimeFourCycle p q r s).card <= O.card := by omega
      have hwhole : O = nativePrimeFourCycle p q r s :=
        Finset.eq_of_subset_of_card_le hO hback
      exact Or.inr (And.intro hwhole (hm.1.symm.trans hwhole))
  . intro h
    rcases h with h | h
    . rw [h.1, h.2]
      simp [nativeSignedCycleMask, nativePrimeVertexCycleDegree]
    . rw [h.1, h.2]
      exact And.intro rfl (And.intro
        (fun x _ => native_four_cycle_degrees_even p q r s hpq hqr hrs x)
        (by rw [hc]))

theorem native_four_cycle_word_rate (P : Finset Nat) (p q r s : Nat)
    (hp : Membership.mem P p) (hq : Membership.mem P q)
    (hr : Membership.mem P r) (hs : Membership.mem P s)
    (hpq : p < q) (hqr : q < r) (hrs : r < s)
    (a b : Prod Nat Nat -> Bool) :
    nativeSignedWordRate P (nativePrimeFourCycle p q r s) (nativePrimeFourCycle p q r s) a b =
      (1 / (2 : Real) ^ 8) *
        (1 + nativeSignedWordMaskCoefficient
          (nativePrimeFourCycle p q r s) (nativePrimeFourCycle p q r s) a b) := by
  let C := nativePrimeFourCycle p q r s
  have hc : C.card = 4 := native_four_cycle_card p q r s hpq hqr hrs
  have hne : Not (C = {}) := by
    intro hz
    rw [hz, Finset.card_empty] at hc
    omega
  have hterm (O T : Finset (Prod Nat Nat))
      (hO : Membership.mem C.powerset O) :
      nativeSignedWordMaskCoefficient O T a b * (if nativeSignedCycleMask P O T then 1 else 0) =
        (if And (O = {}) (T = {}) then 1 else 0) +
        (if And (O = C) (T = C) then nativeSignedWordMaskCoefficient C C a b else 0) := by
    have hm := native_four_cycle_mask_iff P p q r s hp hq hr hs hpq hqr hrs O T
      (Finset.mem_powerset.mp hO)
    by_cases h0 : And (O = {}) (T = {})
    . have h1 : Not (And (O = C) (T = C)) := by
        intro h
        exact hne (h.1.symm.trans h0.1)
      have hmask := hm.mpr (Or.inl h0)
      rw [ite_eq_left hmask, ite_eq_left h0, ite_eq_right h1, mul_one, add_zero]
      simp [h0.1, h0.2, nativeSignedWordMaskCoefficient]
    . by_cases h1 : And (O = C) (T = C)
      . have hmask := hm.mpr (Or.inr h1)
        rw [ite_eq_left hmask, ite_eq_right h0, ite_eq_left h1, mul_one, zero_add,
          h1.1, h1.2]
      . have hmask : Not (nativeSignedCycleMask P O T) := by
          intro h
          rcases hm.mp h with hz | hz
          . exact h0 hz
          . exact h1 hz
        rw [ite_eq_right hmask, ite_eq_right h0, ite_eq_right h1, mul_zero, zero_add]
  have hsum : C.powerset.sum (fun O => C.powerset.sum (fun T =>
      nativeSignedWordMaskCoefficient O T a b * (if nativeSignedCycleMask P O T then 1 else 0))) =
        1 + nativeSignedWordMaskCoefficient C C a b := by
    calc
      _ = C.powerset.sum (fun O => C.powerset.sum (fun T =>
          (if And (O = {}) (T = {}) then (1 : Real) else 0) +
          (if And (O = C) (T = C) then nativeSignedWordMaskCoefficient C C a b else 0))) := by
        apply Finset.sum_congr rfl
        intro O hO
        apply Finset.sum_congr rfl
        intro T hT
        exact hterm O T hO
      _ = 1 + nativeSignedWordMaskCoefficient C C a b := by
        simp [ite_and, Finset.sum_add_distrib]
  change nativeSignedWordRate P C C a b =
    (1 / (2 : Real) ^ 8) * (1 + nativeSignedWordMaskCoefficient C C a b)
  rw [nativeSignedWordRate, hsum, hc]

theorem native_four_cycle_all_positive_rate (P : Finset Nat) (p q r s : Nat)
    (hp : Membership.mem P p) (hq : Membership.mem P q)
    (hr : Membership.mem P r) (hs : Membership.mem P s)
    (hpq : p < q) (hqr : q < r) (hrs : r < s) :
    nativeSignedWordRate P (nativePrimeFourCycle p q r s) (nativePrimeFourCycle p q r s)
      (fun _ => true) (fun _ => true) = 1 / 128 := by
  rw [native_four_cycle_word_rate P p q r s hp hq hr hs hpq hqr hrs]
  norm_num [nativeSignedWordMaskCoefficient, nativeWordSign]

theorem native_four_cycle_word_ratio_tendsto (P : Finset Nat)
    (hP : forall x : Nat, Membership.mem P x -> Nat.Prime x)
    (hind : nativePrimeVertexGapIndependent P) (p q r s : Nat)
    (hp : Membership.mem P p) (hq : Membership.mem P q)
    (hr : Membership.mem P r) (hs : Membership.mem P s)
    (hpq : p < q) (hqr : q < r) (hrs : r < s)
    (a b : Prod Nat Nat -> Bool) :
    Tendsto (fun U : Nat =>
      nativeSignedWordMass (nativePrimeFourCycle p q r s) (nativePrimeFourCycle p q r s) a b
        (preciseCore U + 1) (preciseCore U * preciseCore U + 1) /
          reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds ((1 / (2 : Real) ^ 8) *
        (1 + nativeSignedWordMaskCoefficient
          (nativePrimeFourCycle p q r s) (nativePrimeFourCycle p q r s) a b))) := by
  rw [<- native_four_cycle_word_rate P p q r s hp hq hr hs hpq hqr hrs a b]
  have hC := native_four_cycle_support P p q r s hp hq hr hs hpq hqr hrs
  exact native_signed_word_ratio_tendsto P hP hind _ _ hC hC a b

theorem native_four_cycle_all_positive_ratio_tendsto (P : Finset Nat)
    (hP : forall x : Nat, Membership.mem P x -> Nat.Prime x)
    (hind : nativePrimeVertexGapIndependent P) (p q r s : Nat)
    (hp : Membership.mem P p) (hq : Membership.mem P q)
    (hr : Membership.mem P r) (hs : Membership.mem P s)
    (hpq : p < q) (hqr : q < r) (hrs : r < s) :
    Tendsto (fun U : Nat =>
      nativeSignedWordMass (nativePrimeFourCycle p q r s) (nativePrimeFourCycle p q r s)
        (fun _ => true) (fun _ => true)
        (preciseCore U + 1) (preciseCore U * preciseCore U + 1) /
          reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (1 / 128 : Real)) := by
  rw [<- native_four_cycle_all_positive_rate P p q r s hp hq hr hs hpq hqr hrs]
  have hC := native_four_cycle_support P p q r s hp hq hr hs hpq hqr hrs
  exact native_signed_word_ratio_tendsto P hP hind _ _ hC hC _ _

end PrimeFactorOscillations.FiniteFieldIntegerSignature
