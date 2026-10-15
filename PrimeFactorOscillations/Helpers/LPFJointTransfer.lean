/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFDynamics
import PrimeFactorOscillations.Mathlib.Data.Finset.SumPartnersDeletion

/-!
# Joint deletion bounds for the actual LPF step

An injective family of cofactor lifts turns failed prime targets into failed
sum representations. Analytic exceptions remain explicit, and old missing
primes are carried through the next-state defect bound.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem mem_step_of_lifted_pair (S : Finset Nat) (p q r m n : Nat)
    (hp : Membership.mem S p) (hq : Membership.mem S q) (hne : Not (p = q))
    (hr : Nat.Prime r) (hm : 0 < m) (hOwner : Nat.largestPrimeFactor m <= r)
    (hSum : p + q = n) (hLift : 2 * n = m * r + 1) :
    Membership.mem (step S) r := by
  have h := mem_step_of_pair S hp hq hne
  have hValue : affineValue p q = m * r := by
    unfold affineValue
    rw [hSum]
    omega
  rw [hValue, Nat.largestPrimeFactor_mul_prime (Nat.ne_of_gt hm) hr hOwner] at h
  exact h

theorem card_missing_prime_targets_le
    (P S R : Finset Nat) (t m : Nat -> Nat) (L K : Real)
    (hL : 0 < L) (hK : 0 <= K)
    (hInjective : forall r, Membership.mem R r -> forall s, Membership.mem R s ->
      t r = t s -> r = s)
    (hPrime : forall r, Membership.mem R r -> Nat.Prime r)
    (hCofactor : forall r, Membership.mem R r ->
      And (0 < m r) (Nat.largestPrimeFactor (m r) <= r))
    (hLift : forall r, Membership.mem R r -> 2 * t r = m r * r + 1)
    (hRepresentations : forall r, Membership.mem R r ->
      L + 1 <= ((Finset.sumPartners P (t r)).card : Real))
    (hCross : forall r, Membership.mem R r -> forall s, Membership.mem R s ->
      Not (s = r) ->
      ((Inter.inter (Finset.sumPartners P (t r)) (Finset.sumPartners P (t s))).card : Real) <= K)
    (hSmall : 8 * ((SDiff.sdiff P S).card : Real) * K <= L ^ 2) :
    ((SDiff.sdiff R (step S)).card : Real) <=
      8 * ((SDiff.sdiff P S).card : Real) * (P.card : Real) / L ^ 2 := by
  classical
  let A := SDiff.sdiff R (step S)
  let B := A.image t
  have hCard : B.card = A.card := by
    apply Finset.card_image_of_injOn
    intro r hr s hs he
    exact hInjective r (Finset.mem_sdiff.mp hr).1 s (Finset.mem_sdiff.mp hs).1 he
  have hRepB : forall n, Membership.mem B n ->
      L + 1 <= ((Finset.sumPartners P n).card : Real) := by
    intro n hn
    let r := Classical.choose (Finset.mem_image.mp hn)
    have hr := Classical.choose_spec (Finset.mem_image.mp hn)
    rw [<- hr.2]
    exact hRepresentations r (Finset.mem_sdiff.mp hr.1).1
  have hMissing : forall n, Membership.mem B n ->
      Not (exists p, exists q, And (Membership.mem S p)
        (And (Membership.mem S q) (And (Not (p = q)) (p + q = n)))) := by
    intro n hn hRep
    let r := Classical.choose (Finset.mem_image.mp hn)
    have hr := Classical.choose_spec (Finset.mem_image.mp hn)
    have hrR := (Finset.mem_sdiff.mp hr.1).1
    let p := Classical.choose hRep
    have hp := Classical.choose_spec hRep
    let q := Classical.choose hp
    have hq := Classical.choose_spec hp
    have hSum : p + q = t r := hq.2.2.2.trans hr.2.symm
    have hStep := mem_step_of_lifted_pair S p q r (m r) (t r)
      hq.1 hq.2.1 hq.2.2.1 (hPrime r hrR) (hCofactor r hrR).1
      (hCofactor r hrR).2 hSum (hLift r hrR)
    exact (Finset.mem_sdiff.mp hr.1).2 hStep
  have hCrossB : forall n, Membership.mem B n -> forall k, Membership.mem B k ->
      Not (k = n) ->
      ((Inter.inter (Finset.sumPartners P n) (Finset.sumPartners P k)).card : Real) <= K := by
    intro n hn k hk hne
    let r := Classical.choose (Finset.mem_image.mp hn)
    have hr := Classical.choose_spec (Finset.mem_image.mp hn)
    let s := Classical.choose (Finset.mem_image.mp hk)
    have hs := Classical.choose_spec (Finset.mem_image.mp hk)
    have hsr : Not (s = r) := by
      intro he
      apply hne
      calc
        k = t s := hs.2.symm
        _ = t r := congrArg t he
        _ = n := hr.2
    rw [<- hr.2, <- hs.2]
    exact hCross r (Finset.mem_sdiff.mp hr.1).1 s (Finset.mem_sdiff.mp hs.1).1 hsr
  have h := Finset.failed_sum_target_card_le P S B L K hL hK hRepB hMissing hCrossB hSmall
  rw [hCard] at h
  exact h

def primeTargetCofactor (r : Nat) : Nat := if r % 4 = 1 then 3 else 1

def primeTargetSum (r : Nat) : Nat :=
  if r % 4 = 1 then (3 * r + 1) / 2 else (r + 1) / 2

theorem primeTarget_lift (r : Nat) (hr : Nat.Prime r) (hr3 : 3 <= r) :
    2 * primeTargetSum r = primeTargetCofactor r * r + 1 := by
  have hOdd : r % 2 = 1 := hr.eq_two_or_odd.resolve_left (by omega)
  unfold primeTargetSum primeTargetCofactor
  split_ifs <;> omega

theorem primeTarget_owner (r : Nat) (hr : Nat.Prime r) (hr3 : 3 <= r) :
    And (0 < primeTargetCofactor r)
      (Nat.largestPrimeFactor (primeTargetCofactor r) <= r) := by
  unfold primeTargetCofactor
  split_ifs
  next =>
    constructor
    next => omega
    next => simpa only [Nat.largestPrimeFactor_of_prime (by decide : Nat.Prime 3)] using hr3
  next =>
    constructor
    next => omega
    next => simpa [Nat.largestPrimeFactor] using hr.one_lt.le

theorem primeTarget_injective_window (M r s : Nat) (hM : 3 <= M)
    (hr : Nat.Prime r) (hs : Nat.Prime s)
    (hrange : And (M < r) (r <= 5 * M / 4))
    (srange : And (M < s) (s <= 5 * M / 4))
    (hEq : primeTargetSum r = primeTargetSum s) : r = s := by
  have hlr := primeTarget_lift r hr (by omega)
  have hls := primeTarget_lift s hs (by omega)
  rw [hEq] at hlr
  unfold primeTargetCofactor at hlr hls
  split_ifs at hlr hls <;> omega

theorem card_missing_window_targets_le
    (P S R : Finset Nat) (M : Nat) (L K : Real)
    (hM : 3 <= M) (hL : 0 < L) (hK : 0 <= K)
    (hR : forall r, Membership.mem R r -> And (Nat.Prime r)
      (And (M < r) (r <= 5 * M / 4)))
    (hRepresentations : forall r, Membership.mem R r ->
      L + 1 <= ((Finset.sumPartners P (primeTargetSum r)).card : Real))
    (hCross : forall r, Membership.mem R r -> forall s, Membership.mem R s ->
      Not (s = r) ->
      ((Inter.inter (Finset.sumPartners P (primeTargetSum r))
        (Finset.sumPartners P (primeTargetSum s))).card : Real) <= K)
    (hSmall : 8 * ((SDiff.sdiff P S).card : Real) * K <= L ^ 2) :
    ((SDiff.sdiff R (step S)).card : Real) <=
      8 * ((SDiff.sdiff P S).card : Real) * (P.card : Real) / L ^ 2 := by
  apply card_missing_prime_targets_le P S R primeTargetSum primeTargetCofactor L K hL hK
  next =>
    intro r hr s hs he
    exact primeTarget_injective_window M r s hM (hR r hr).1 (hR s hs).1
      (hR r hr).2 (hR s hs).2 he
  next => intro r hr; exact (hR r hr).1
  next => intro r hr; exact primeTarget_owner r (hR r hr).1 (by have := (hR r hr).2.1; omega)
  next => intro r hr; exact primeTarget_lift r (hR r hr).1 (by have := (hR r hr).2.1; omega)
  next => exact hRepresentations
  next => exact hCross
  next => exact hSmall

theorem card_missing_targets_le_exceptions (S R E : Finset Nat) :
    (SDiff.sdiff R (step S)).card <=
      E.card + (SDiff.sdiff (SDiff.sdiff R E) (step S)).card := by
  have hCover : SDiff.sdiff R (step S) <=
      Union.union E (SDiff.sdiff (SDiff.sdiff R E) (step S)) := by
    intro r hr
    have h := Finset.mem_sdiff.mp hr
    by_cases he : Membership.mem E r
    next => exact Finset.mem_union_left _ he
    next =>
      exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
        (And.intro (Finset.mem_sdiff.mpr (And.intro h.1 he)) h.2))
  exact (Finset.card_le_card hCover).trans (Finset.card_union_le _ _)

theorem card_next_defect_le (P Q R S : Finset Nat)
    (hCover : Q <= Union.union P R) :
    (SDiff.sdiff Q (step S)).card <=
      (SDiff.sdiff P S).card + (SDiff.sdiff R (step S)).card := by
  have hSubset : SDiff.sdiff Q (step S) <=
      Union.union (SDiff.sdiff P S) (SDiff.sdiff R (step S)) := by
    intro p hp
    have h := Finset.mem_sdiff.mp hp
    have hu := Finset.mem_union.mp (hCover h.1)
    cases hu with
    | inl hP =>
      apply Finset.mem_union_left
      apply Finset.mem_sdiff.mpr
      exact And.intro hP (fun hS => h.2 (subset_step S hS))
    | inr hR => exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr (And.intro hR h.2))
  exact (Finset.card_le_card hSubset).trans (Finset.card_union_le _ _)

theorem joint_next_defect_bound
    (P Q R S Z : Finset Nat) (M : Nat) (L K : Real)
    (hM : 3 <= M) (hL : 0 < L) (hK : 0 <= K)
    (hCover : Q <= Union.union P R)
    (hR : forall r, Membership.mem R r -> And (Nat.Prime r)
      (And (M < r) (r <= 5 * M / 4)))
    (hRepresentations : forall r, Membership.mem (SDiff.sdiff R Z) r ->
      L + 1 <= ((Finset.sumPartners P (primeTargetSum r)).card : Real))
    (hCross : forall r, Membership.mem (SDiff.sdiff R Z) r ->
      forall s, Membership.mem (SDiff.sdiff R Z) s -> Not (s = r) ->
      ((Inter.inter (Finset.sumPartners P (primeTargetSum r))
        (Finset.sumPartners P (primeTargetSum s))).card : Real) <= K)
    (hSmall : 8 * ((SDiff.sdiff P S).card : Real) * K <= L ^ 2) :
    ((SDiff.sdiff Q (step S)).card : Real) <=
      ((SDiff.sdiff P S).card : Real) + (Z.card : Real) +
        8 * ((SDiff.sdiff P S).card : Real) * (P.card : Real) / L ^ 2 := by
  have hGood := card_missing_window_targets_le P S (SDiff.sdiff R Z) M L K hM hL hK
    (fun r hr => hR r (Finset.mem_sdiff.mp hr).1) hRepresentations hCross hSmall
  have hExceptions : ((SDiff.sdiff R (step S)).card : Real) <=
      (Z.card : Real) + ((SDiff.sdiff (SDiff.sdiff R Z) (step S)).card : Real) := by
    exact_mod_cast card_missing_targets_le_exceptions S R Z
  have hNext : ((SDiff.sdiff Q (step S)).card : Real) <=
      ((SDiff.sdiff P S).card : Real) + ((SDiff.sdiff R (step S)).card : Real) := by
    exact_mod_cast card_next_defect_le P Q R S hCover
  linarith

theorem not_closed_of_joint_window_surplus
    (P R S Z : Finset Nat) (M : Nat) (L K : Real)
    (hM : 3 <= M) (hL : 0 < L) (hK : 0 <= K)
    (hBound : forall p, Membership.mem S p -> p <= M)
    (hR : forall r, Membership.mem R r -> And (Nat.Prime r)
      (And (M < r) (r <= 5 * M / 4)))
    (hRepresentations : forall r, Membership.mem (SDiff.sdiff R Z) r ->
      L + 1 <= ((Finset.sumPartners P (primeTargetSum r)).card : Real))
    (hCross : forall r, Membership.mem (SDiff.sdiff R Z) r ->
      forall s, Membership.mem (SDiff.sdiff R Z) s -> Not (s = r) ->
      ((Inter.inter (Finset.sumPartners P (primeTargetSum r))
        (Finset.sumPartners P (primeTargetSum s))).card : Real) <= K)
    (hSmall : 8 * ((SDiff.sdiff P S).card : Real) * K <= L ^ 2)
    (hSurplus : (Z.card : Real) +
      8 * ((SDiff.sdiff P S).card : Real) * (P.card : Real) / L ^ 2 < (R.card : Real)) :
    Not (step S = S) := by
  intro hClosed
  have hGood := card_missing_window_targets_le P S (SDiff.sdiff R Z) M L K hM hL hK
    (fun r hr => hR r (Finset.mem_sdiff.mp hr).1) hRepresentations hCross hSmall
  have hExceptions : ((SDiff.sdiff R (step S)).card : Real) <=
      (Z.card : Real) + ((SDiff.sdiff (SDiff.sdiff R Z) (step S)).card : Real) := by
    exact_mod_cast card_missing_targets_le_exceptions S R Z
  have hAllMissing : SDiff.sdiff R (step S) = R := by
    ext r
    constructor
    next => intro hr; exact (Finset.mem_sdiff.mp hr).1
    next =>
      intro hr
      apply Finset.mem_sdiff.mpr
      refine And.intro hr ?_
      intro hStep
      rw [hClosed] at hStep
      have hUpper := hBound r hStep
      have hLower := (hR r hr).2.1
      omega
  rw [hAllMissing] at hExceptions
  linarith

def inputPrimePrefix (M : Nat) : Finset Nat := (Finset.Icc 1 M).filter Nat.Prime

def nextPrimeWindow (M : Nat) : Finset Nat :=
  (Finset.Icc (M + 1) (5 * M / 4)).filter Nat.Prime

theorem nextPrimeWindow_spec (M r : Nat) (hr : Membership.mem (nextPrimeWindow M) r) :
    And (Nat.Prime r) (And (M < r) (r <= 5 * M / 4)) := by
  have h := Finset.mem_filter.mp hr
  have hi := Finset.mem_Icc.mp h.1
  exact And.intro h.2 (And.intro (by omega) hi.2)

theorem inputPrimePrefix_next_cover (M : Nat) :
    inputPrimePrefix (5 * M / 4) <= Union.union (inputPrimePrefix M) (nextPrimeWindow M) := by
  intro p hp
  have h := Finset.mem_filter.mp hp
  have hi := Finset.mem_Icc.mp h.1
  by_cases hOld : p <= M
  next =>
    apply Finset.mem_union_left
    exact Finset.mem_filter.mpr (And.intro (Finset.mem_Icc.mpr (And.intro hi.1 hOld)) h.2)
  next =>
    apply Finset.mem_union_right
    exact Finset.mem_filter.mpr
      (And.intro (Finset.mem_Icc.mpr (And.intro (by omega) hi.2)) h.2)

theorem primePrefix_next_defect_bound
    (S Z : Finset Nat) (M : Nat) (L K : Real)
    (hM : 3 <= M) (hL : 0 < L) (hK : 0 <= K)
    (hRepresentations : forall r, Membership.mem (SDiff.sdiff (nextPrimeWindow M) Z) r ->
      L + 1 <= ((Finset.sumPartners (inputPrimePrefix M) (primeTargetSum r)).card : Real))
    (hCross : forall r, Membership.mem (SDiff.sdiff (nextPrimeWindow M) Z) r ->
      forall s, Membership.mem (SDiff.sdiff (nextPrimeWindow M) Z) s -> Not (s = r) ->
      ((Inter.inter (Finset.sumPartners (inputPrimePrefix M) (primeTargetSum r))
        (Finset.sumPartners (inputPrimePrefix M) (primeTargetSum s))).card : Real) <= K)
    (hSmall : 8 * ((SDiff.sdiff (inputPrimePrefix M) S).card : Real) * K <= L ^ 2) :
    ((SDiff.sdiff (inputPrimePrefix (5 * M / 4)) (step S)).card : Real) <=
      ((SDiff.sdiff (inputPrimePrefix M) S).card : Real) + (Z.card : Real) +
        8 * ((SDiff.sdiff (inputPrimePrefix M) S).card : Real) *
          ((inputPrimePrefix M).card : Real) / L ^ 2 :=
  joint_next_defect_bound (inputPrimePrefix M) (inputPrimePrefix (5 * M / 4))
    (nextPrimeWindow M) S Z M L K hM hL hK (inputPrimePrefix_next_cover M)
    (nextPrimeWindow_spec M) hRepresentations hCross hSmall

end PrimeFactorOscillations.LPF
