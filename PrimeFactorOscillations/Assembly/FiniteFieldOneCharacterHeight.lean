/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.DetectorPackets.IntegerQuadraticParity
import PrimeFactorOscillations.Assembly.FiniteFieldIntegerAmplitude

/-!
# One-character bounds at general integer height

The negative numerator character is always nonprincipal. Its signed
prime tail is retained, while the second character contributes at most
one reciprocal-prime main term. Opening zeros and shift-dividing rows
remain in the complete packet. This estimates integer inputs without
assuming primality or restricting them to the quadratic height window.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldOneCharacterHeight

open FiniteField
open FiniteField.QuadraticPairTwistEuler
open FiniteField.QuadraticPairTwistLikelihood
open FiniteFieldIntegerTail
open FiniteFieldIntegerMass
open FiniteFieldIntegerExtrema
open FiniteFieldFrozenGrowth
open IntegerQuadraticCharacter

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem characterA_lower (c h : F) : -1 <= characterA c h := by
  by_cases hx : (-h) * c = 0
  . simp [characterA, hx]
  . have hs := QuadraticPairEuler.quadraticChar_real_signs ((-h) * c) hx
    cases hs with
    | inl he => simp only [characterA, he]; norm_num
    | inr he => simp only [characterA, he]; norm_num

theorem local_log_one_character_upper (c h : F) (hh : Not (h = 0))
    (hq : 7 <= (Fintype.card F : Real)) :
    Real.log (1 + localCorrection c h) <=
      (characterA c h + 1) / (Fintype.card F : Real) +
        8 / (Fintype.card F : Real) ^ 2 := by
  have hq0 : 0 <= (Fintype.card F : Real) := Nat.cast_nonneg _
  have hA := characterA_lower c h
  have hzero (hz : localCorrection c h = 0) :
      Real.log (1 + localCorrection c h) <=
        (characterA c h + 1) / (Fintype.card F : Real) +
          8 / (Fintype.card F : Real) ^ 2 := by
    rw [hz]
    simp only [add_zero, Real.log_one]
    exact add_nonneg (div_nonneg (by linarith only [hA]) hq0)
      (div_nonneg (by norm_num) (sq_nonneg _))
  by_cases hc : c = 0
  . apply hzero
    simp [localCorrection, admissibilityMask, hc, traceFreePairWeight_zero]
  . by_cases hch : c + h = 0
    . have hn : c = -h := eq_neg_of_add_eq_zero_left hch
      apply hzero
      simp [localCorrection, admissibilityMask, hn, traceFreePairWeight_neg_shift]
    . have hb := (FiniteFieldIntegerHeight.local_log_character_bounds c h hc hch hh hq).2
      have hB := character_le_one (h * (c + h))
      change characterB c h <= 1 at hB
      have hs : (characterA c h + characterB c h) / (Fintype.card F : Real) <=
          (characterA c h + 1) / (Fintype.card F : Real) :=
        div_le_div_of_nonneg_right (by linarith only [hB]) hq0
      linarith only [hb, hs]

def negativePrimePhase (h n p : Nat) : Real :=
  (numeratorKernel (-((h : Int) * (n : Int))) p).re

def negativeTail (K h Q n : Nat) : Real :=
  (allTailPrimes K Q).sum (fun p => negativePrimePhase h n p / (p : Real))

theorem all_tail_primes_eq_interval (K Q : Nat) :
    allTailPrimes K Q = (Finset.Ico (K + 1) (Q + 1)).filter Nat.Prime := by
  apply Finset.ext
  intro p
  simp only [allTailPrimes, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
  constructor
  . intro hp
    exact And.intro (And.intro (by omega) (by omega)) hp.2.1
  . intro hp
    exact And.intro (And.intro (by omega) (by omega)) (And.intro hp.2 (by omega))

theorem prime_tail_sum_attach (K Q : Nat) (f : Nat -> Real) :
    (Finset.Icc 1 Q).attach.sum (fun q =>
      if Nat.Prime q.val /\ K < q.val then f q.val else 0) =
        (allTailPrimes K Q).sum f := by
  let g : Nat -> Real := fun p => if Nat.Prime p /\ K < p then f p else 0
  have ht := Finset.sum_attach (Finset.Icc 1 Q) g
  change (Finset.Icc 1 Q).attach.sum (fun q => g q.val) = (allTailPrimes K Q).sum f
  rw [ht]
  unfold allTailPrimes
  rw [Finset.sum_filter]

theorem row_log_one_character_upper (K h Q n : Nat) (hK : 6 <= K)
    (q : BoundedModulus Q) :
    Real.log (1 + tailCorrection K (h : Int) q (n : ZMod q.val)) <=
      (if Nat.Prime q.val /\ K < q.val
        then (negativePrimePhase h n q.val + 1) / (q.val : Real) else 0) +
      (if K < q.val then 8 / (q.val : Real) ^ 2 else 0) := by
  by_cases hp : Nat.Prime q.val
  . have : Fact (Nat.Prime q.val) := Fact.mk hp
    by_cases hk : K < q.val
    . have hphase : negativePrimePhase h n q.val =
          characterA (n : ZMod q.val) (h : ZMod q.val) := by
        unfold negativePrimePhase
        rw [<- FiniteFieldIntegerCharacter.integer_characterA h n q.val (by omega)]
        simp
      by_cases hz : ((h : Int) : ZMod q.val) = 0
      . have hfail : Not (K < q.val /\ Not (((h : Int) : ZMod q.val) = 0)) :=
          fun ht => ht.2 hz
        have hNat : (h : ZMod q.val) = 0 := by simpa only [Int.cast_natCast] using hz
        have htailzero : tailCorrection K (h : Int) q (n : ZMod q.val) = 0 := by
          rw [tailCorrection, dite_eq_left hp, ite_eq_right hfail]
        have hphasezero : negativePrimePhase h n q.val = 0 := by
          rw [hphase, hNat]
          simp [characterA]
        simp only [htailzero, add_zero, Real.log_one, ite_eq_left (And.intro hp hk),
          hphasezero, zero_add, ite_eq_left hk]
        positivity
      . have hNat : Not ((h : ZMod q.val) = 0) := by
          simpa only [Int.cast_natCast] using hz
        have hq7 : 7 <= (Fintype.card (ZMod q.val) : Real) := by
          rw [ZMod.card]
          exact_mod_cast (show 7 <= q.val by omega)
        have hb := local_log_one_character_upper (n : ZMod q.val) (h : ZMod q.val) hNat hq7
        have hid : tailCorrection K (h : Int) q (n : ZMod q.val) =
            localCorrection (n : ZMod q.val) (h : ZMod q.val) := by
          rw [tailCorrection, dite_eq_left hp, ite_eq_left (And.intro hk hz)]
          simp only [Int.cast_natCast]
        simp only [ite_eq_left (And.intro hp hk), ite_eq_left hk]
        rw [hid, hphase]
        simpa only [ZMod.card] using hb
    . simp [tailCorrection, hp, hk]
  . have hfail : Not (Nat.Prime q.val /\ K < q.val) := fun ht => hp ht.1
    simp only [tailCorrection, dite_eq_right hp, add_zero, Real.log_one,
      ite_eq_right hfail, zero_add]
    split_ifs <;> positivity

theorem tail_log_one_character_upper (K h Q n : Nat)
    (hK : 6 <= K) (hKQ : K <= Q) :
    tailLogSum K (h : Int) Q n <=
      negativeTail K h Q n +
        (allTailPrimes K Q).sum (fun p => (1 : Real) / (p : Real)) + 8 / (K : Real) := by
  have hs := Finset.sum_le_sum (s := (Finset.Icc 1 Q).attach)
    (fun q _ => row_log_one_character_upper K h Q n hK q)
  rw [Finset.sum_add_distrib] at hs
  rw [prime_tail_sum_attach K Q (fun p => (negativePrimePhase h n p + 1) / (p : Real))] at hs
  have hid :
      (allTailPrimes K Q).sum (fun p => (negativePrimePhase h n p + 1) / (p : Real)) =
        negativeTail K h Q n +
          (allTailPrimes K Q).sum (fun p => (1 : Real) / (p : Real)) := by
    simp only [negativeTail, add_div, Finset.sum_add_distrib]
  rw [hid] at hs
  have h8 := tail_envelope_sum_le K hK hKQ 8 (by norm_num)
  change tailLogSum K (h : Int) Q n <= _ at hs
  linarith only [hs, h8]

theorem negative_tail_eq_re (K h Q n : Nat) :
    negativeTail K h Q n =
      (Finset.sum ((Finset.Ico (K + 1) (Q + 1)).filter Nat.Prime)
        (fun p => HSMul.hSMul (1 / (p : Real))
          (numeratorKernel (-((h : Int) * (n : Int))) p))).re := by
  rw [negativeTail, all_tail_primes_eq_interval]
  simp [negativePrimePhase, div_eq_mul_inv, mul_comm]
  apply Finset.sum_congr rfl
  intro p hp
  have hp0 : Not ((p : Real) = 0) := by
    exact_mod_cast (Finset.mem_filter.mp hp).2.ne_zero
  field_simp [hp0]

theorem all_tail_reciprocal_mertens_upper (K Q : Nat)
    (hK : 6 <= K) (hKQ : K <= Q) :
    (allTailPrimes K Q).sum (fun p => (1 : Real) / (p : Real)) <=
      Real.log (Real.log (Q : Real)) - Real.log (Real.log (K : Real)) + 2 * mertensBudget := by
  have hid := all_tail_reciprocal_sum K Q hKQ
  have hQ := reciprocal_prime_log_bound Q (by omega)
  have hKlower := reciprocal_prime_lower K (by omega)
  linarith only [hid, hQ, hKlower]

theorem exists_negative_tail_bounded :
    exists C : Real, And (0 < C)
      (forall K h Q n : Nat, 0 < h -> 0 < n ->
        (3 + Real.log ((4 * h * n : Nat) : Real)) ^ 64 <= ((K + 1 : Nat) : Real) ->
        abs (negativeTail K h Q n) <= C) := by
  let C : Real := Classical.choose QRH.exists_primeCharacter_reciprocal_tail_bounded
  have hSpec := Classical.choose_spec QRH.exists_primeCharacter_reciprocal_tail_bounded
  refine Exists.intro C (And.intro hSpec.1 ?_)
  intro K h Q n hh hn hcut
  let a : Nat := h * n
  have ha : 0 < a := Nat.mul_pos hh hn
  have hD : Not (-(a : Int) = 0) := neg_ne_zero.mpr (by exact_mod_cast (ne_of_gt ha))
  have hlevel : 4 * (-(a : Int)).natAbs = 4 * h * n := by
    simp only [Int.natAbs_neg, Int.natAbs_natCast, a]
    ring
  have : NeZero (4 * (-(a : Int)).natAbs) := NeZero.mk (by rw [hlevel]; positivity)
  have hchi := numerator_character_negative_nonprincipal a ha hD
  have ht := hSpec.2 (numeratorCharacter (-(a : Int)) hD) hchi (K + 1) (Q + 1)
    (by omega) (by simpa only [hlevel] using hcut)
  have hsum :
      norm (Finset.sum ((Finset.Ico (K + 1) (Q + 1)).filter Nat.Prime)
        (fun p => HSMul.hSMul (1 / (p : Real))
          (numeratorKernel (-((h : Int) * (n : Int))) p))) <= C := by
    simpa only [numerator_character_natCast, a, Nat.cast_mul] using ht
  rw [negative_tail_eq_re]
  exact (Complex.abs_re_le_norm _).trans hsum

theorem exists_one_character_packet_comparison :
    exists C : Real, And (0 < C)
      (forall K h Q n : Nat, 6 <= K -> 0 < h -> 0 < n -> K <= Q ->
        (3 + Real.log ((4 * h * n : Nat) : Real)) ^ 64 <= ((K + 1 : Nat) : Real) ->
        actualPacket (h : Int) Q n <=
          Real.exp (C + 2 * mertensBudget + 8 / (K : Real)) *
            (Real.log (Q : Real) / Real.log (K : Real)) * hybridPacket K (h : Int) Q n) := by
  let C : Real := Classical.choose exists_negative_tail_bounded
  have hSpec := Classical.choose_spec exists_negative_tail_bounded
  refine Exists.intro C (And.intro hSpec.1 ?_)
  intro K h Q n hK hh hn hKQ hcut
  have hlog := tail_log_one_character_upper K h Q n hK hKQ
  have htail := (abs_le.mp (hSpec.2 K h Q n hh hn hcut)).2
  have hM := all_tail_reciprocal_mertens_upper K Q hK hKQ
  have hupper : tailLogSum K (h : Int) Q n <=
      (C + 2 * mertensBudget + 8 / (K : Real)) +
        (Real.log (Real.log (Q : Real)) - Real.log (Real.log (K : Real))) := by
    linarith only [hlog, htail, hM]
  have hLQ : 0 < Real.log (Q : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < Q from by omega))
  have hLK : 0 < Real.log (K : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < K from by omega))
  have hV := hybrid_packet_nonneg K (h : Int) Q n
  calc
    _ = hybridPacket K (h : Int) Q n * Real.exp (tailLogSum K (h : Int) Q n) :=
      full_packet_factorization K (h : Int) hK Q n
    _ <= hybridPacket K (h : Int) Q n *
        Real.exp ((C + 2 * mertensBudget + 8 / (K : Real)) +
          (Real.log (Real.log (Q : Real)) - Real.log (Real.log (K : Real)))) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hupper) hV
    _ = _ := by
      rw [Real.exp_add, Real.exp_sub, Real.exp_log hLQ, Real.exp_log hLK]
      ring

theorem exists_one_character_split_amplitude :
    exists A : Real, And (0 < A)
      (forall K h Q n : Nat, 6 <= K -> 0 < h -> 0 < n -> K <= Q ->
        (3 + Real.log ((4 * h * n : Nat) : Real)) ^ 64 <= ((K + 1 : Nat) : Real) ->
        actualPacket (h : Int) Q n <=
          A * (Real.log (Q : Real)) ^ 3 * Real.log (K : Real)) := by
  let C : Real := Classical.choose exists_one_character_packet_comparison
  have hSpec := Classical.choose_spec exists_one_character_packet_comparison
  let A : Real := Real.exp (C + 2 * mertensBudget + 2) * replacementConstant
  have hA : 0 < A := by dsimp [A, replacementConstant]; positivity
  refine Exists.intro A (And.intro hA ?_)
  intro K h Q n hK hh hn hKQ hcut
  have hc := hSpec.2 K h Q n hK hh hn hKQ hcut
  have hV := FiniteFieldIntegerAmplitude.hybrid_packet_split_envelope K (h : Int) Q n hK hKQ
  have hLK : 0 < Real.log (K : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < K from by omega))
  have hLQ : 0 <= Real.log (Q : Real) :=
    (Real.log_pos (by exact_mod_cast (show 1 < Q from by omega))).le
  have hKR : (6 : Real) <= (K : Real) := by exact_mod_cast hK
  have h8 : 8 / (K : Real) <= 2 := by
    calc
      _ <= (8 : Real) / 6 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKR
      _ <= _ := by norm_num
  have hR : 0 <= Real.log (Q : Real) / Real.log (K : Real) := div_nonneg hLQ hLK.le
  calc
    _ <= Real.exp (C + 2 * mertensBudget + 8 / (K : Real)) *
        (Real.log (Q : Real) / Real.log (K : Real)) * hybridPacket K (h : Int) Q n := hc
    _ <= Real.exp (C + 2 * mertensBudget + 8 / (K : Real)) *
        (Real.log (Q : Real) / Real.log (K : Real)) *
        (replacementConstant * (Real.log (Q : Real)) ^ 2 * (Real.log (K : Real)) ^ 2) :=
      mul_le_mul_of_nonneg_left hV (mul_nonneg (Real.exp_pos _).le hR)
    _ <= Real.exp (C + 2 * mertensBudget + 2) *
        (Real.log (Q : Real) / Real.log (K : Real)) *
        (replacementConstant * (Real.log (Q : Real)) ^ 2 * (Real.log (K : Real)) ^ 2) := by
      apply mul_le_mul_of_nonneg_right
      . exact mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (by linarith only [h8])) hR
      . unfold replacementConstant
        positivity
    _ = _ := by
      dsimp [A]
      field_simp [ne_of_gt hLK]

end PrimeFactorOscillations.FiniteFieldOneCharacterHeight
