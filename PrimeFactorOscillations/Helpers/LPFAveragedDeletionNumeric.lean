/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFAveragedOverlapNumeric
import PrimeFactorOscillations.Helpers.LPFAveragedTransfer

/-!
# Numerical averaged deletion for the actual LPF step

The full overlap bound supplies constant 6144 at an explicit cutoff. The
representation lower bound, diagonal and cross energies, size condition and
absorption inequality remain explicit. Input diagonals are enabled throughout.
-/


set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

private theorem card_sumPartners_le_twice_deleted (P S : Finset Nat) (n : Nat)
    (hMissing : Not (exists p, exists q, And (Membership.mem S p)
      (And (Membership.mem S q) (p + q = n)))) :
    (Finset.sumPartners P n).card <=
      2 * (SDiff.sdiff (Finset.sumPartners P n) S).card := by
  classical
  let D := SDiff.sdiff (Finset.sumPartners P n) S
  have hCover : Finset.sumPartners P n <= Union.union D (D.image (fun p => n - p)) := by
    intro p hp
    have hpd := Finset.mem_filter.mp hp
    by_cases hpS : Membership.mem S p
    next =>
      have hqS : Not (Membership.mem S (n - p)) := by
        intro hqS
        exact hMissing (Exists.intro p (Exists.intro (n - p)
          (And.intro hpS (And.intro hqS (by omega)))))
      have hqP : Membership.mem (Finset.sumPartners P n) (n - p) := by
        apply Finset.mem_filter.mpr
        refine And.intro hpd.2.1 (And.intro ?_ ?_)
        next => simpa only [Nat.sub_sub_self hpd.2.2] using hpd.1
        next => omega
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      exact Exists.intro (n - p)
        (And.intro (Finset.mem_sdiff.mpr (And.intro hqP hqS)) (by omega))
    next => exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr (And.intro hp hpS))
  have h1 := Finset.card_le_card hCover
  have h2 := Finset.card_union_le D (D.image (fun p => n - p))
  have h3 : (D.image (fun p => n - p)).card <= D.card := Finset.card_image_le
  change (Finset.sumPartners P n).card <= 2 * D.card
  omega

private theorem missed_target_has_no_pair (S : Finset Nat) (M r : Nat)
    (hM : 3 <= M) (hr : Membership.mem (nextPrimeWindow M) r)
    (hMissing : Not (Membership.mem (fullStep S) r)) :
    Not (exists p, exists q, And (Membership.mem S p)
      (And (Membership.mem S q) (p + q = primeTargetSum r))) := by
  intro hPair
  choose p q hp hq hSum using hPair
  have hSpec := nextPrimeWindow_spec M r hr
  have hr3 : 3 <= r := by omega
  have hLift := primeTarget_lift r hSpec.1 hr3
  have hOwner := primeTarget_owner r hSpec.1 hr3
  have hValue : affineValue p q = primeTargetCofactor r * r := by
    unfold affineValue
    rw [hSum]
    omega
  have h := mem_fullStep_of_pair S hp hq
  rw [hValue, Nat.largestPrimeFactor_mul_prime (Nat.ne_of_gt hOwner.1) hSpec.1 hOwner.2] at h
  exact hMissing h

private theorem deleted_primeTargetWeight_eq (P S : Finset Nat) (v : Nat -> Real) (r : Nat) :
    Finset.sum (SDiff.sdiff P S) (fun p => primeTargetWeight P v p r) =
      ((SDiff.sdiff (Finset.sumPartners P (primeTargetSum r)) S).card : Real) * v r := by
  classical
  have hSubset : Finset.sumPartners P (primeTargetSum r) <= P :=
    fun p hp => (Finset.mem_filter.mp hp).1
  have hFilter : (SDiff.sdiff P S).filter
      (fun p => Membership.mem (Finset.sumPartners P (primeTargetSum r)) p) =
        SDiff.sdiff (Finset.sumPartners P (primeTargetSum r)) S := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    constructor
    next => intro h; exact And.intro h.2 h.1.2
    next => intro h; exact And.intro (And.intro (hSubset h.1) h.2) h.1
  have h := Finset.sum_filter (s := SDiff.sdiff P S)
    (p := fun p => Membership.mem (Finset.sumPartners P (primeTargetSum r)) p)
    (f := fun _ => v r)
  simpa only [hFilter, Finset.sum_const, nsmul_eq_mul, primeTargetWeight] using h.symm

private theorem primeTarget_energy_le (P B : Finset Nat) (w : Nat -> Nat -> Real) (U V : Real)
    (hDiag : forall r, Membership.mem B r -> Finset.sum P (fun p => w p r ^ 2) <= U)
    (hCross : forall r, Membership.mem B r -> forall s, Membership.mem B s ->
      Not (s = r) -> Finset.sum P (fun p => w p r * w p s) <=
        V * singularDivisorProduct (primeTargetSeparation r s)) :
    Finset.sum P (fun p => (Finset.sum B (w p)) ^ 2) <=
      (B.card : Real) * U + V * Finset.sum B (fun r => Finset.sum (B.erase r)
        (fun s => singularDivisorProduct (primeTargetSeparation r s))) := by
  classical
  have hExpand : Finset.sum P (fun p => (Finset.sum B (w p)) ^ 2) =
      Finset.sum B (fun r => Finset.sum B (fun s =>
        Finset.sum P (fun p => w p r * w p s))) := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s hs
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [hExpand]
  calc
    _ <= Finset.sum B (fun r => U + V * Finset.sum (B.erase r)
        (fun s => singularDivisorProduct (primeTargetSeparation r s))) := by
      apply Finset.sum_le_sum
      intro r hr
      rw [<- Finset.sum_erase_add B (fun s => Finset.sum P (fun p => w p r * w p s)) hr]
      have hOff : Finset.sum (B.erase r) (fun s => Finset.sum P (fun p => w p r * w p s)) <=
          V * Finset.sum (B.erase r) (fun s => singularDivisorProduct (primeTargetSeparation r s)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro s hs
        have h := Finset.mem_erase.mp hs
        exact hCross r hr s h.2 h.1
      have hSelf : Finset.sum P (fun p => w p r * w p r) <= U := by
        simpa only [pow_two] using hDiag r hr
      linarith only [hOff, hSelf]
    _ = _ := by rw [Finset.sum_add_distrib, <- Finset.mul_sum]; simp

theorem lpf_averaged_fullStep_deletion_numeric (M : Nat) (hM : 4 <= M)
    (hLog : 32768 <= Real.log (M : Real)) :
    forall (P S B : Finset Nat) (v : Nat -> Real) (L U V : Real),
    B <= nextPrimeWindow M ->
    (M : Real) / Real.log (M : Real) ^ 4 <= (B.card : Real) ->
    0 < L -> 0 <= U -> 0 <= V ->
    (forall r, Membership.mem B r -> 0 <= v r) ->
    (forall r, Membership.mem B r -> Not (Membership.mem (fullStep S) r)) ->
    (forall r, Membership.mem B r ->
      L <= v r * ((Finset.sumPartners P (primeTargetSum r)).card : Real)) ->
    (forall r, Membership.mem B r ->
      Finset.sum P (fun p => primeTargetWeight P v p r ^ 2) <= U) ->
    (forall r, Membership.mem B r -> forall s, Membership.mem B s ->
      Not (s = r) -> Finset.sum P (fun p =>
        primeTargetWeight P v p r * primeTargetWeight P v p s) <=
          V * singularDivisorProduct (primeTargetSeparation r s)) ->
    8 * ((SDiff.sdiff P S).card : Real) *
      (V * 6144 * Real.log (3 + Real.log (max 1 (((M : Real) / Real.log (M : Real)) / (B.card : Real)))))
      <= L ^ 2 ->
    (B.card : Real) <= 8 * ((SDiff.sdiff P S).card : Real) * U / L ^ 2 := by
  classical
  intro P S B v L U V hB hSize hL hU hV hv hMissing hRepresentations hDiag hCross hSmall
  have hM3 : 3 <= M := by omega
  let w : Nat -> Nat -> Real := primeTargetWeight P v
  let K : Real := V * 6144 *
    Real.log (3 + Real.log (max 1 (((M : Real) / Real.log (M : Real)) / (B.card : Real))))
  have hCover : forall r, Membership.mem B r ->
      L <= 2 * Finset.sum (SDiff.sdiff P S) (fun p => w p r) := by
    intro r hr
    have hNoPair := missed_target_has_no_pair S M r hM3 (hB hr) (hMissing r hr)
    have hCount : ((Finset.sumPartners P (primeTargetSum r)).card : Real) <=
        2 * ((SDiff.sdiff (Finset.sumPartners P (primeTargetSum r)) S).card : Real) := by
      exact_mod_cast card_sumPartners_le_twice_deleted P S (primeTargetSum r) hNoPair
    have hWeighted := mul_le_mul_of_nonneg_left hCount (hv r hr)
    have hSupply := hRepresentations r hr
    change L <= 2 * Finset.sum (SDiff.sdiff P S) (fun p => primeTargetWeight P v p r)
    rw [deleted_primeTargetWeight_eq]
    nlinarith only [hSupply, hWeighted]
  have hEnergy : Finset.sum P (fun p => (Finset.sum B (w p)) ^ 2) <=
      (B.card : Real) * U + (B.card : Real) ^ 2 * K := by
    calc
      _ <= (B.card : Real) * U + V * Finset.sum B (fun r => Finset.sum (B.erase r)
          (fun s => singularDivisorProduct (primeTargetSeparation r s))) :=
        primeTarget_energy_le P B w U V hDiag hCross
      _ <= (B.card : Real) * U + V * (6144 * (B.card : Real) ^ 2 *
          Real.log (3 + Real.log (max 1 (((M : Real) / Real.log (M : Real)) / (B.card : Real))))) :=
        _root_.add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (lpf_primeTarget_overlap_numeric M B hM hLog hB hSize) hV)
      _ = _ := by dsimp [K]; ring
  exact Finset.covered_target_card_le_of_energy P (SDiff.sdiff P S) B
    (fun p hp => (Finset.mem_sdiff.mp hp).1) w L U K hL hU hCover hEnergy hSmall


end PrimeFactorOscillations.LPF
