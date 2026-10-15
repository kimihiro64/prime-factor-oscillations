/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFPrimeTargetOverlap

/-! # Averaged deletion for the actual all-pairs LPF step -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

noncomputable def primeTargetWeight (P : Finset Nat) (v : Nat -> Real)
    (p r : Nat) : Real :=
  if Membership.mem (Finset.sumPartners P (primeTargetSum r)) p then v r else 0

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

/-- The analytic representation and codegree inputs remain explicit premises.
The actual missed targets refer to fullStep, with all input diagonals enabled. -/
theorem exists_averaged_fullStep_deletion_bound :
    exists C : Real, And (0 < C)
      (Filter.Eventually (fun M : Nat =>
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
          (V * C * Real.log (3 + Real.log (((M : Real) / Real.log (M : Real)) / (B.card : Real))))
          <= L ^ 2 ->
        (B.card : Real) <= 8 * ((SDiff.sdiff P S).card : Real) * U / L ^ 2)
        Filter.atTop) := by
  classical
  choose C hC hOverlapEvent using exists_uniform_primeTarget_overlap
  refine Exists.intro C (And.intro hC ?_)
  filter_upwards [hOverlapEvent, Filter.eventually_ge_atTop (3 : Nat)] with M hOverlap hM
  intro P S B v L U V hB hSize hL hU hV hv hMissing hRepresentations hDiag hCross hSmall
  let w : Nat -> Nat -> Real := primeTargetWeight P v
  let K : Real := V * C *
    Real.log (3 + Real.log (((M : Real) / Real.log (M : Real)) / (B.card : Real)))
  have hCover : forall r, Membership.mem B r ->
      L <= 2 * Finset.sum (SDiff.sdiff P S) (fun p => w p r) := by
    intro r hr
    have hNoPair := missed_target_has_no_pair S M r hM (hB hr) (hMissing r hr)
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
      _ <= (B.card : Real) * U + V * (C * (B.card : Real) ^ 2 *
          Real.log (3 + Real.log (((M : Real) / Real.log (M : Real)) / (B.card : Real)))) :=
        _root_.add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (hOverlap B hB hSize) hV)
      _ = _ := by dsimp [K]; ring
  exact Finset.covered_target_card_le_of_energy P (SDiff.sdiff P S) B
    (fun p hp => (Finset.mem_sdiff.mp hp).1) w L U K hL hU hCover hEnergy hSmall

private theorem fullStep_prefix_defect_cover (S Z : Finset Nat) (M : Nat) :
    (SDiff.sdiff (inputPrimePrefix (5 * M / 4)) (fullStep S)).card <=
      (SDiff.sdiff (inputPrimePrefix M) S).card + Z.card +
        (SDiff.sdiff (SDiff.sdiff (nextPrimeWindow M) Z) (fullStep S)).card := by
  classical
  let D := SDiff.sdiff (inputPrimePrefix M) S
  let B := SDiff.sdiff (SDiff.sdiff (nextPrimeWindow M) Z) (fullStep S)
  have hCover : SDiff.sdiff (inputPrimePrefix (5 * M / 4)) (fullStep S) <=
      Union.union (Union.union D Z) B := by
    intro r hr
    have h := Finset.mem_sdiff.mp hr
    rcases Finset.mem_union.mp (inputPrimePrefix_next_cover M h.1) with hOld | hNew
    next =>
      have hNotS : Not (Membership.mem S r) := fun hrS => h.2 (subset_fullStep S hrS)
      exact Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_sdiff.mpr (And.intro hOld hNotS)))
    next =>
      by_cases hz : Membership.mem Z r
      next => exact Finset.mem_union_left _ (Finset.mem_union_right _ hz)
      next => exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
        (And.intro (Finset.mem_sdiff.mpr (And.intro hNew hz)) h.2))
  have h1 := Finset.card_le_card hCover
  have h2 := Finset.card_union_le (Union.union D Z) B
  have h3 := Finset.card_union_le D Z
  change (SDiff.sdiff (inputPrimePrefix (5 * M / 4)) (fullStep S)).card <=
    D.card + Z.card + B.card
  omega

/-- A next-generation prime-prefix bound with explicit analytic exceptions.
The absorption condition is needed only when the failed set exceeds M/log^4 M. -/
theorem exists_averaged_fullStep_prefix_bound :
    exists C : Real, And (0 < C)
      (Filter.Eventually (fun M : Nat =>
        forall (S Z : Finset Nat) (v : Nat -> Real) (L U V : Real),
        let P := inputPrimePrefix M
        let G := SDiff.sdiff (nextPrimeWindow M) Z
        let B := SDiff.sdiff G (fullStep S)
        let E := ((SDiff.sdiff P S).card : Real)
        let F := (M : Real) / Real.log (M : Real) ^ 4
        0 < L -> 0 <= U -> 0 <= V ->
        (forall r, Membership.mem G r -> 0 <= v r) ->
        (forall r, Membership.mem G r ->
          L <= v r * ((Finset.sumPartners P (primeTargetSum r)).card : Real)) ->
        (forall r, Membership.mem G r ->
          Finset.sum P (fun p => primeTargetWeight P v p r ^ 2) <= U) ->
        (forall r, Membership.mem G r -> forall s, Membership.mem G s ->
          Not (s = r) -> Finset.sum P (fun p =>
            primeTargetWeight P v p r * primeTargetWeight P v p s) <=
              V * singularDivisorProduct (primeTargetSeparation r s)) ->
        (F <= (B.card : Real) -> 8 * E *
          (V * C * Real.log (3 + Real.log (((M : Real) / Real.log (M : Real)) / (B.card : Real))))
          <= L ^ 2) ->
        ((SDiff.sdiff (inputPrimePrefix (5 * M / 4)) (fullStep S)).card : Real) <=
          E + (Z.card : Real) + F + 8 * E * U / L ^ 2)
        Filter.atTop) := by
  classical
  choose C hC hEvent using exists_averaged_fullStep_deletion_bound
  refine Exists.intro C (And.intro hC ?_)
  filter_upwards [hEvent] with M hDel
  intro S Z v L U V
  let P := inputPrimePrefix M
  let G := SDiff.sdiff (nextPrimeWindow M) Z
  let B := SDiff.sdiff G (fullStep S)
  let E : Real := ((SDiff.sdiff P S).card : Real)
  let F : Real := (M : Real) / Real.log (M : Real) ^ 4
  change 0 < L -> 0 <= U -> 0 <= V -> _
  intro hL hU hV hv hRep hDiag hCross hSmall
  have hBG : B <= G := fun r hr => (Finset.mem_sdiff.mp hr).1
  have hBR : B <= nextPrimeWindow M := fun r hr => (Finset.mem_sdiff.mp (hBG hr)).1
  have hMissing : forall r, Membership.mem B r -> Not (Membership.mem (fullStep S) r) :=
    fun r hr => (Finset.mem_sdiff.mp hr).2
  have hF : 0 <= F := by dsimp [F]; positivity
  have hE : 0 <= E := Nat.cast_nonneg _
  have hError : 0 <= 8 * E * U / L ^ 2 := by positivity
  have hBad : (B.card : Real) <= F + 8 * E * U / L ^ 2 := by
    by_cases hSize : F <= (B.card : Real)
    next =>
      have h := hDel P S B v L U V hBR hSize hL hU hV
        (fun r hr => hv r (hBG hr)) hMissing
        (fun r hr => hRep r (hBG hr))
        (fun r hr => hDiag r (hBG hr))
        (fun r hr s hs hne => hCross r (hBG hr) s (hBG hs) hne) (hSmall hSize)
      change (B.card : Real) <= 8 * E * U / L ^ 2 at h
      linarith only [h, hF]
    next => have h := lt_of_not_ge hSize; linarith only [h, hError]
  have hPrefix : ((SDiff.sdiff (inputPrimePrefix (5 * M / 4)) (fullStep S)).card : Real) <=
      E + (Z.card : Real) + (B.card : Real) := by
    dsimp [E, P, B, G]
    exact_mod_cast fullStep_prefix_defect_cover S Z M
  change ((SDiff.sdiff (inputPrimePrefix (5 * M / 4)) (fullStep S)).card : Real) <=
    E + (Z.card : Real) + F + 8 * E * U / L ^ 2
  linarith only [hPrefix, hBad]

end PrimeFactorOscillations.LPF
