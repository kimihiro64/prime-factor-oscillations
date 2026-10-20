/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PrimeProfileSaturationThreshold
import PrimeFactorOscillations.Mathlib.Combinatorics.FinitePrefixTailSpectrum

/-!
# Every escape-multiplicity threshold of a fixed probability-profile probe

The complete signed cost has an exact threshold for keeping all but k-1
observed coordinates in one finite ambient prefix. Every critical budget
has finite block-permutation witnesses. The case k=1 is the fixed-probe
locality saturation already proved independently.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimeProfileRigidity

/-- The compensated prime weights approach zero from below along the full enumeration. -/
theorem primeLogWeight_cofinal_zero (t : Real) (ht : 0 < t) :
    forall a : Real, a < 0 -> exists M : Nat, a < primeLogWeight t M := by
  intro a ha
  let eps : Real := -a
  have heps : 0 < eps := neg_pos.mpr ha
  have hM : exists M : Nat, max (2 : Real) (t ^ 2 / eps) < (M : Real) :=
    exists_nat_gt _
  let M := Classical.choose hM
  have hMgt := Classical.choose_spec hM
  let q : Real := PrimeFactorUnimodality.primeAt M
  have hMq : (M : Real) <= q := by
    dsimp only [q]
    exact_mod_cast PrimeFactorUnimodality.primeAt_strictMono.id_le M
  have hq2 : (2 : Real) <= q := by
    dsimp only [q]
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt M).two_le
  have hq : 0 < q := by linarith only [hq2]
  have hquot : t ^ 2 / eps < q :=
    ((le_max_right _ _).trans_lt hMgt).trans_le hMq
  have hmul := mul_lt_mul_of_pos_right hquot heps
  have hid : t ^ 2 / eps * eps = t ^ 2 := by field_simp [heps.ne']
  rw [hid] at hmul
  have hqt : 1 <= q + t := by linarith only [hq2, ht]
  have hden : q <= q * (q + t) := by nlinarith only [hqt, hq]
  have hdeneps := mul_le_mul_of_nonneg_left hden heps.le
  have hdenpos : 0 < q * (q + t) := by positivity
  have hb := (Real.neg_bernoulliLogProfile_bounds t q ht hq).2
  have hbmul := mul_le_mul_of_nonneg_right hb hdenpos.le
  have hid2 : t ^ 2 / (q * (q + t)) * (q * (q + t)) = t ^ 2 := by
    field_simp [hq.ne', (add_pos hq ht).ne']
  rw [hid2] at hbmul
  have hsmall : -Real.bernoulliLogProfile t q < eps := by
    by_contra hn
    have hbad := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hdenpos.le
    nlinarith only [hbad, hbmul, hmul, hdeneps]
  refine Exists.intro M ?_
  change a < Real.bernoulliLogProfile t q
  dsimp only [eps] at hsmall
  linarith only [hsmall]

/-- A single weight sequence whose finite-prefix defect is the full normalized cost. -/
def normalizedPrimePrefixWeight (t : Real) (n i : Nat) : Real :=
  (PrimeFactorUnimodality.primeAt n : Real) ^ 2 *
    ((PrimeFactorUnimodality.primeAt n : Real) + t) / t ^ 2 * primeLogWeight t i

/-- Every hypothesis of the general finite-ceiling spectrum holds for the actual prime weights. -/
theorem normalizedPrimePrefixWeight_properties (t : Real) (n : Nat) (ht : 0 < t) :
    Monotone (normalizedPrimePrefixWeight t n) /\
      (forall i : Nat, normalizedPrimePrefixWeight t n i <= 0) /\
      (forall a : Real, a < 0 -> exists M : Nat, a < normalizedPrimePrefixWeight t n M) := by
  let c := (PrimeFactorUnimodality.primeAt n : Real) ^ 2 *
    ((PrimeFactorUnimodality.primeAt n : Real) + t) / t ^ 2
  have hr : (0 : Real) < PrimeFactorUnimodality.primeAt n := by
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt n).pos
  have hc : 0 < c := by dsimp only [c]; positivity
  constructor
  . intro i j hij
    exact mul_le_mul_of_nonneg_left ((primeLogWeight_strictMono t ht).monotone hij) hc.le
  . constructor
    . intro i
      have hi : (0 : Real) < PrimeFactorUnimodality.primeAt i := by
        exact_mod_cast (PrimeFactorUnimodality.prime_primeAt i).pos
      have hb := (Real.neg_bernoulliLogProfile_bounds t _ ht hi).1
      have hneg : primeLogWeight t i < 0 := by
        unfold primeLogWeight
        linarith only [hb]
      exact (mul_neg_of_pos_of_neg hc hneg).le
    . intro a ha
      have hac : a / c < 0 := div_neg_of_neg_of_pos ha hc
      have hM := primeLogWeight_cofinal_zero t ht (a / c) hac
      let M := Classical.choose hM
      have hMgt := Classical.choose_spec hM
      have hmul := mul_lt_mul_of_pos_left hMgt hc
      have hid : c * (a / c) = a := by field_simp [hc.ne']
      rw [hid] at hmul
      exact Exists.intro M hmul

/-- No information or compensation term changes when the normalizer is put inside the weights. -/
theorem normalizedPrimePrefixDefect_eq_scaled_prefix (e : Equiv.Perm Nat)
    (t : Real) (n : Nat) :
    normalizedPrimePrefixDefect e (fun _ => t) n =
      Finset.prefixDefect (normalizedPrimePrefixWeight t n) e (n + 1) := by
  unfold normalizedPrimePrefixDefect Finset.prefixDefect normalizedPrimePrefixWeight
  simp only [mul_sub, Finset.mul_sum]

/-- The exact cost of sending the k least expensive prefix coordinates to infinity. -/
def primePrefixEscapeThreshold (t : Real) (n k : Nat) : Real :=
  (PrimeFactorUnimodality.primeAt n : Real) ^ 2 *
    ((PrimeFactorUnimodality.primeAt n : Real) + t) / t ^ 2 *
      ((Finset.range (n + 1 - k)).sum (primeLogWeight t) -
        (Finset.range (n + 1)).sum (primeLogWeight t))

/-- The profile threshold is exactly the general finite-ceiling saturation. -/
theorem primePrefixEscapeThreshold_eq_saturation (t : Real) (n k : Nat) :
    primePrefixEscapeThreshold t n k =
      Finset.prefixTailSaturation (normalizedPrimePrefixWeight t n) 0 (n + 1) k := by
  unfold primePrefixEscapeThreshold Finset.prefixTailSaturation normalizedPrimePrefixWeight
  rw [<- Finset.mul_sum, <- Finset.mul_sum]
  ring

/-- Exactly k tail coordinates become possible at their complete signed saturation budget. -/
theorem prime_prefix_escape_spectrum_iff (t : Real) (n k : Nat) (ht : 0 < t)
    (hkpos : 0 < k) (hk : k <= n + 1) (C : Real) :
    (exists M : Nat, forall e : Equiv.Perm Nat,
      normalizedPrimePrefixDefect e (fun _ => t) n <= C ->
      (((Finset.range (n + 1)).image e) \ Finset.range M).card < k) <->
    C < primePrefixEscapeThreshold t n k := by
  have hdata := normalizedPrimePrefixWeight_properties t n ht
  have h := Finset.prefixTail_locality_iff (normalizedPrimePrefixWeight t n) 0
    hdata.1 hdata.2.1 hdata.2.2 (n + 1) k hkpos hk C
  simpa only [<- normalizedPrimePrefixDefect_eq_scaled_prefix,
    <- primePrefixEscapeThreshold_eq_saturation] using h

/-- Failure at a critical budget is witnessed by permutations fixed outside a finite interval. -/
theorem prime_prefix_escape_at_threshold (t : Real) (n k M : Nat) (ht : 0 < t)
    (hk : k <= n + 1) :
    exists e : Equiv.Perm Nat, exists L : Nat,
      (forall i : Nat, L <= i -> e i = i) /\
      k <= (((Finset.range (n + 1)).image e) \ Finset.range M).card /\
      normalizedPrimePrefixDefect e (fun _ => t) n <= primePrefixEscapeThreshold t n k := by
  have hdata := normalizedPrimePrefixWeight_properties t n ht
  have h := Finset.exists_prefixTail_escape_at_saturation (normalizedPrimePrefixWeight t n) 0
    hdata.2.1 (n + 1) k M hk
  simpa only [<- normalizedPrimePrefixDefect_eq_scaled_prefix,
    <- primePrefixEscapeThreshold_eq_saturation] using h

/-- The first member of the complete spectrum agrees with the independent fixed-probe theorem. -/
theorem primePrefixEscapeThreshold_one (t : Real) (n : Nat) :
    primePrefixEscapeThreshold t n 1 =
      Real.normalizedLogBoundarySaturation t (PrimeFactorUnimodality.primeAt n : Real) := by
  unfold primePrefixEscapeThreshold Real.normalizedLogBoundarySaturation
  simp only [Nat.add_sub_cancel, Finset.sum_range_succ]
  unfold primeLogWeight
  ring

/-- The empty escape class has zero saturation cost. -/
theorem primePrefixEscapeThreshold_zero (t : Real) (n : Nat) :
    primePrefixEscapeThreshold t n 0 = 0 := by
  unfold primePrefixEscapeThreshold
  simp only [Nat.sub_zero, sub_self, mul_zero]

/-- Every threshold increment is exactly one retained positive log deficit. -/
theorem primePrefixEscapeThreshold_succ_sub (t : Real) (n k : Nat) (hk : k <= n) :
    primePrefixEscapeThreshold t n (k + 1) - primePrefixEscapeThreshold t n k =
      (PrimeFactorUnimodality.primeAt n : Real) ^ 2 *
        ((PrimeFactorUnimodality.primeAt n : Real) + t) / t ^ 2 *
          (-primeLogWeight t (n - k)) := by
  have hleft : n + 1 - (k + 1) = n - k := by omega
  have hright : n + 1 - k = (n - k) + 1 := by omega
  unfold primePrefixEscapeThreshold
  rw [hleft, hright, Finset.sum_range_succ (primeLogWeight t) (n - k)]
  ring

/-- The admissible finite spectrum is strictly ordered for every positive probe. -/
theorem primePrefixEscapeThreshold_strict_step (t : Real) (n k : Nat)
    (ht : 0 < t) (hk : k <= n) :
    primePrefixEscapeThreshold t n k < primePrefixEscapeThreshold t n (k + 1) := by
  have hr : (0 : Real) < PrimeFactorUnimodality.primeAt n := by
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt n).pos
  have hp : (0 : Real) < PrimeFactorUnimodality.primeAt (n - k) := by
    exact_mod_cast (PrimeFactorUnimodality.prime_primeAt (n - k)).pos
  have hb := (Real.neg_bernoulliLogProfile_bounds t _ ht hp).1
  have hc : 0 < (PrimeFactorUnimodality.primeAt n : Real) ^ 2 *
      ((PrimeFactorUnimodality.primeAt n : Real) + t) / t ^ 2 := by positivity
  have hpos := mul_pos hc hb
  have hid := primePrefixEscapeThreshold_succ_sub t n k hk
  unfold primeLogWeight at hid
  linarith only [hpos, hid]

end PrimeFactorOscillations.PrimeProfileRigidity
