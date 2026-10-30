/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldIntegerCharacter

/-!
# Pointwise packet comparison at natural integer height

The exact local likelihood correction retains both quadratic characters.
Its signed logarithmic error is between -18/q^2 and 8/q^2 for q >= 7.
Summing the actual supported rows and applying the uniform integer
character estimate gives a constant-factor actual/hybrid comparison
after a polylogarithmic core. All opening zeros, small rows and
prime-dividing-shift rows remain in the exact product factorization.
No positive prime-pair mass or new zero-free exponent is asserted.
-/


set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerHeight

open FiniteField
open FiniteField.QuadraticPairTwistEuler
open FiniteField.QuadraticPairTwistLikelihood
open FiniteFieldIntegerTail
open FiniteFieldIntegerMass

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem local_correction_character_identity (c h : F)
    (hc : Not (c = 0)) (hch : Not (c + h = 0))
    (hq : 7 <= (Fintype.card F : Real)) :
    localCorrection c h =
      (characterA c h + characterB c h) / (Fintype.card F : Real) +
      (2 + characterA c h + characterB c h) /
        ((Fintype.card F : Real) * ((Fintype.card F : Real) - 3)) := by
  have hn : Not (c = -h) := by
    intro hz
    apply hch
    rw [hz]
    ring
  have hq0 : Not ((Fintype.card F : Real) = 0) := ne_of_gt (by linarith only [hq])
  have hq3 : Not ((Fintype.card F : Real) - 3 = 0) := ne_of_gt (by linarith only [hq])
  unfold localCorrection
  simp only [admissibilityMask, ite_eq_right hc, ite_eq_right hn]
  rw [traceFreePairWeight_scalar c h hc hn]
  field_simp [hq0, hq3]
  ring

theorem local_correction_character_bounds (c h : F)
    (hc : Not (c = 0)) (hch : Not (c + h = 0)) (hh : Not (h = 0))
    (hq : 7 <= (Fintype.card F : Real)) :
    0 <= localCorrection c h -
        (characterA c h + characterB c h) / (Fintype.card F : Real) /\
      localCorrection c h -
        (characterA c h + characterB c h) / (Fintype.card F : Real) <=
          8 / (Fintype.card F : Real) ^ 2 := by
  let q : Real := Fintype.card F
  have hq7 : 7 <= q := hq
  have hq0 : 0 < q := by linarith only [hq7]
  have hq3 : 0 < q - 3 := by linarith only [hq7]
  have ha := QuadraticPairEuler.quadraticChar_real_signs ((-h) * c)
    (mul_ne_zero (neg_ne_zero.mpr hh) hc)
  have hb := QuadraticPairEuler.quadraticChar_real_signs (h * (c + h))
    (mul_ne_zero hh hch)
  have hAl : -1 <= characterA c h := by
    dsimp [characterA]
    cases ha with
    | inl he => rw [he]; norm_num
    | inr he => rw [he]
  have hBl : -1 <= characterB c h := by
    dsimp [characterB]
    cases hb with
    | inl he => rw [he]; norm_num
    | inr he => rw [he]
  have hAu : characterA c h <= 1 := character_le_one ((-h) * c)
  have hBu : characterB c h <= 1 := character_le_one (h * (c + h))
  have hslo : 0 <= 2 + characterA c h + characterB c h := by
    linarith only [hAl, hBl]
  have hshi : 2 + characterA c h + characterB c h <= 4 := by
    linarith only [hAu, hBu]
  have hid : localCorrection c h - (characterA c h + characterB c h) / q =
      (2 + characterA c h + characterB c h) / (q * (q - 3)) := by
    rw [local_correction_character_identity c h hc hch hq]
    dsimp [q]
    ring
  change 0 <= localCorrection c h - (characterA c h + characterB c h) / q /\
    localCorrection c h - (characterA c h + characterB c h) / q <= 8 / q ^ 2
  rw [hid]
  refine And.intro (div_nonneg hslo (mul_pos hq0 hq3).le) ?_
  have hden : q ^ 2 / 2 <= q * (q - 3) := by
    have ht := mul_nonneg hq0.le (show 0 <= q - 6 by linarith only [hq7])
    nlinarith only [ht]
  calc
    _ <= 4 / (q * (q - 3)) := div_le_div_of_nonneg_right hshi (mul_pos hq0 hq3).le
    _ <= 4 / (q ^ 2 / 2) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
    _ = _ := by field_simp [ne_of_gt hq0]; ring

theorem local_log_character_bounds (c h : F)
    (hc : Not (c = 0)) (hch : Not (c + h = 0)) (hh : Not (h = 0))
    (hq : 7 <= (Fintype.card F : Real)) :
    -(18 / (Fintype.card F : Real) ^ 2) <=
        Real.log (1 + localCorrection c h) -
          (characterA c h + characterB c h) / (Fintype.card F : Real) /\
      Real.log (1 + localCorrection c h) -
          (characterA c h + characterB c h) / (Fintype.card F : Real) <=
        8 / (Fintype.card F : Real) ^ 2 := by
  let q : Real := Fintype.card F
  let a : Real := localCorrection c h
  have hq7 : 7 <= q := hq
  have hq0 : 0 < q := by linarith only [hq7]
  have ha : abs a <= 3 / q := local_correction_abs_le c h hh hq
  have hhalf : abs a <= 1 / 2 := by
    calc
      _ <= 3 / q := ha
      _ <= (3 : Real) / 7 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hq7
      _ <= _ := by norm_num
  have hTaylor := abs_le.mp (abs_log_one_add_sub_self_le a hhalf)
  have hpos : 0 < 1 + a := by
    have ht := (abs_le.mp hhalf).1
    linarith only [ht]
  have hlog := Real.log_le_sub_one_of_pos hpos
  have hsquare : a ^ 2 <= 9 / q ^ 2 := by
    have ht := mul_self_le_mul_self (abs_nonneg a) ha
    have hid : (3 / q) ^ 2 = 9 / q ^ 2 := by rw [div_pow]; norm_num
    calc
      _ = (abs a) ^ 2 := (sq_abs a).symm
      _ <= (3 / q) ^ 2 := by nlinarith only [ht]
      _ = _ := hid
  have hres := local_correction_character_bounds c h hc hch hh hq
  change 0 <= a - (characterA c h + characterB c h) / q /\
    a - (characterA c h + characterB c h) / q <= 8 / q ^ 2 at hres
  change -(18 / q ^ 2) <= Real.log (1 + a) -
      (characterA c h + characterB c h) / q /\
    Real.log (1 + a) - (characterA c h + characterB c h) / q <= 8 / q ^ 2
  constructor
  . have hsquare2 : 2 * a ^ 2 <= 18 / q ^ 2 := by
      calc
        _ <= 2 * (9 / q ^ 2) := mul_le_mul_of_nonneg_left hsquare (by norm_num)
        _ = _ := by ring
    linarith only [hTaylor.1, hsquare2, hres.1]
  . linarith only [hlog, hres.2]


def jointPrimePhase (h n p : Nat) : Real :=
  (IntegerQuadraticCharacter.numeratorKernel (-((h : Int) * (n : Int))) p +
    IntegerQuadraticCharacter.numeratorKernel ((h : Int) * ((n + h : Nat) : Int)) p).re

def primeCharacterSignal (K h Q n : Nat) : Real :=
  Finset.sum ((Finset.Ico (K + 1) (Q + 1)).filter Nat.Prime)
    (fun p => jointPrimePhase h n p / (p : Real))

theorem prime_signal_attach (K h Q n : Nat) :
    (Finset.Icc 1 Q).attach.sum (fun q =>
      if Nat.Prime q.val /\ K < q.val
        then jointPrimePhase h n q.val / (q.val : Real) else 0) =
      primeCharacterSignal K h Q n := by
  have hset : (Finset.Icc 1 Q).filter (fun p => Nat.Prime p /\ K < p) =
      (Finset.Ico (K + 1) (Q + 1)).filter Nat.Prime := by
    apply Finset.ext
    intro p
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
    constructor
    . intro hp
      exact And.intro (And.intro (by omega) (by omega)) hp.2.1
    . intro hp
      exact And.intro (And.intro (by omega) (by omega)) (And.intro hp.2 (by omega))
  let f : Nat -> Real := fun p =>
    if Nat.Prime p /\ K < p then jointPrimePhase h n p / (p : Real) else 0
  have ht := Finset.sum_attach (Finset.Icc 1 Q) f
  change (Finset.Icc 1 Q).attach.sum (fun q => f q.val) = primeCharacterSignal K h Q n
  rw [ht]
  unfold primeCharacterSignal
  rw [<- hset, Finset.sum_filter]

theorem prime_signal_eq_re (K h Q n : Nat) :
    primeCharacterSignal K h Q n =
      (Finset.sum ((Finset.Ico (K + 1) (Q + 1)).filter Nat.Prime)
        (fun p => HSMul.hSMul (1 / (p : Real))
          (IntegerQuadraticCharacter.numeratorKernel (-((h : Int) * (n : Int))) p +
            IntegerQuadraticCharacter.numeratorKernel ((h : Int) * ((n + h : Nat) : Int)) p))).re := by
  simp [primeCharacterSignal, jointPrimePhase, div_eq_mul_inv, mul_comm]
  apply Finset.sum_congr rfl
  intro p hp
  have hp0 : Not ((p : Real) = 0) := by
    exact_mod_cast (Finset.mem_filter.mp hp).2.ne_zero
  field_simp [hp0]

theorem tail_row_log_character_bounds (K h Q n : Nat)
    (hK : 6 <= K) (hh : 0 < h) (hhK : h <= K) (hQn : Q < n)
    (hn : Nat.Prime n) (hnh : Nat.Prime (n + h)) (q : BoundedModulus Q) :
    -(if K < q.val then 18 / (q.val : Real) ^ 2 else 0) <=
      Real.log (1 + tailCorrection K (h : Int) q (n : ZMod q.val)) -
        (if Nat.Prime q.val /\ K < q.val
          then jointPrimePhase h n q.val / (q.val : Real) else 0) /\
    Real.log (1 + tailCorrection K (h : Int) q (n : ZMod q.val)) -
        (if Nat.Prime q.val /\ K < q.val
          then jointPrimePhase h n q.val / (q.val : Real) else 0) <=
      (if K < q.val then 8 / (q.val : Real) ^ 2 else 0) := by
  by_cases hp : Nat.Prime q.val
  . have : Fact (Nat.Prime q.val) := Fact.mk hp
    by_cases hk : K < q.val
    . have hqQ : q.val <= Q := (Finset.mem_Icc.mp q.property).2
      have hhcast : Not (((h : Int) : ZMod q.val) = 0) := by
        intro hz
        have hd : Dvd.dvd q.val h :=
          (CharP.cast_eq_zero_iff (ZMod q.val) q.val h).mp
            (by simpa only [Int.cast_natCast] using hz)
        have hl := Nat.le_of_dvd hh hd
        omega
      have hhNat : Not ((h : ZMod q.val) = 0) := by
        simpa only [Int.cast_natCast] using hhcast
      have hcast (P : Nat) (hP : Nat.Prime P) (hQP : Q < P) :
          Not ((P : ZMod q.val) = 0) := by
        intro hz
        have hd := (CharP.cast_eq_zero_iff (ZMod q.val) q.val P).mp hz
        cases (Nat.dvd_prime hP).mp hd with
        | inl he => exact hp.ne_one he
        | inr he => omega
      have hc := hcast n hn hQn
      have hch : Not ((n : ZMod q.val) + (h : ZMod q.val) = 0) := by
        intro hz
        apply hcast (n + h) hnh (by omega)
        simpa only [Nat.cast_add] using hz
      have hq7 : 7 <= (Fintype.card (ZMod q.val) : Real) := by
        rw [ZMod.card]
        exact_mod_cast (show 7 <= q.val by omega)
      have hphase : jointPrimePhase h n q.val =
          characterA (n : ZMod q.val) (h : ZMod q.val) +
            characterB (n : ZMod q.val) (h : ZMod q.val) := by
        unfold jointPrimePhase
        rw [<- FiniteFieldIntegerCharacter.integer_characterA h n q.val (by omega),
          <- FiniteFieldIntegerCharacter.integer_characterB h n q.val (by omega)]
        simp
      have hid : tailCorrection K (h : Int) q (n : ZMod q.val) =
          localCorrection (n : ZMod q.val) (h : ZMod q.val) := by
        rw [tailCorrection, dite_eq_left hp, ite_eq_left (And.intro hk hhcast)]
        simp only [Int.cast_natCast]
      have hb := local_log_character_bounds (n : ZMod q.val) (h : ZMod q.val)
        hc hch hhNat hq7
      simp only [ite_eq_left hk, ite_eq_left (And.intro hp hk)]
      rw [hid, hphase]
      simpa only [ZMod.card] using hb
    . simp [tailCorrection, hp, hk]
  . have hnP : Not (Nat.Prime q.val /\ K < q.val) := fun ht => hp ht.1
    simp only [tailCorrection, dite_eq_right hp, ite_eq_right hnP, add_zero, Real.log_one, sub_zero]
    by_cases hk : K < q.val
    . simp only [ite_eq_left hk]
      constructor
      . exact neg_nonpos.mpr (div_nonneg (by norm_num) (sq_nonneg _))
      . exact div_nonneg (by norm_num) (sq_nonneg _)
    . simp [hk]

theorem tail_log_character_band (K h Q n : Nat)
    (hK : 6 <= K) (hh : 0 < h) (hhK : h <= K) (hKQ : K <= Q) (hQn : Q < n)
    (hn : Nat.Prime n) (hnh : Nat.Prime (n + h)) :
    -(18 / (K : Real)) <= tailLogSum K (h : Int) Q n - primeCharacterSignal K h Q n /\
      tailLogSum K (h : Int) Q n - primeCharacterSignal K h Q n <= 8 / (K : Real) := by
  let E : BoundedModulus Q -> Real := fun q =>
    Real.log (1 + tailCorrection K (h : Int) q (n : ZMod q.val)) -
      (if Nat.Prime q.val /\ K < q.val
        then jointPrimePhase h n q.val / (q.val : Real) else 0)
  have hlo := Finset.sum_le_sum (s := (Finset.Icc 1 Q).attach)
    (fun q _ => (tail_row_log_character_bounds K h Q n hK hh hhK hQn hn hnh q).1)
  have hup := Finset.sum_le_sum (s := (Finset.Icc 1 Q).attach)
    (fun q _ => (tail_row_log_character_bounds K h Q n hK hh hhK hQn hn hnh q).2)
  have h18 := tail_envelope_sum_le K hK hKQ 18 (by norm_num)
  have h8 := tail_envelope_sum_le K hK hKQ 8 (by norm_num)
  have hid : (Finset.Icc 1 Q).attach.sum E =
      tailLogSum K (h : Int) Q n - primeCharacterSignal K h Q n := by
    dsimp [E]
    rw [Finset.sum_sub_distrib, prime_signal_attach]
    rfl
  change (Finset.Icc 1 Q).attach.sum (fun q =>
      -(if K < q.val then 18 / (q.val : Real) ^ 2 else 0)) <=
      (Finset.Icc 1 Q).attach.sum E at hlo
  rw [Finset.sum_neg_distrib, hid] at hlo
  change (Finset.Icc 1 Q).attach.sum E <=
    (Finset.Icc 1 Q).attach.sum (fun q => if K < q.val then 8 / (q.val : Real) ^ 2 else 0) at hup
  rw [hid] at hup
  constructor
  . linarith only [hlo, h18]
  . linarith only [hup, h8]


theorem exists_natural_height_packet_comparison :
    exists C : Real, And (0 < C)
      (forall K h Q n : Nat, 6 <= K -> 0 < h -> h <= K -> h < Q -> K <= Q ->
        Q < n -> n + h <= Q * Q ->
        (3 + Real.log ((4 * h * (Q * Q) : Nat) : Real)) ^ 64 <= ((K + 1 : Nat) : Real) ->
        And
          (Real.exp (-(2 * C) - 18 / (K : Real)) * hybridPacket K (h : Int) Q n <=
            actualPacket (h : Int) Q n)
          (actualPacket (h : Int) Q n <=
            Real.exp (2 * C + 8 / (K : Real)) * hybridPacket K (h : Int) Q n)) := by
  let C : Real := Classical.choose FiniteFieldIntegerCharacter.exists_natural_height_joint_tail_bounded
  have hSpec := Classical.choose_spec FiniteFieldIntegerCharacter.exists_natural_height_joint_tail_bounded
  have hC : 0 < C := hSpec.1
  refine Exists.intro C (And.intro hC ?_)
  intro K h Q n hK hh hhK hhQ hKQ hQn hnQ hcut
  have hfactor := full_packet_factorization K (h : Int) hK Q n
  have hV := hybrid_packet_nonneg K (h : Int) Q n
  by_cases hU : actualPacket (h : Int) Q n = 0
  . have hVzero : hybridPacket K (h : Int) Q n = 0 := by
      have ht : hybridPacket K (h : Int) Q n * Real.exp (tailLogSum K (h : Int) Q n) = 0 := by
        rw [<- hfactor]
        exact hU
      exact (mul_eq_zero.mp ht).resolve_right (Real.exp_ne_zero _)
    simp only [hU, hVzero, mul_zero, le_refl, and_self]
  . have hU0 : 0 <= actualPacket (h : Int) Q n := by
      unfold actualPacket
      apply Finset.prod_nonneg
      intro q hq
      exact actual_local_nonneg (h : Int) q _
    have hUpos : 0 < actualPacket (h : Int) Q n := lt_of_le_of_ne hU0 (Ne.symm hU)
    have hpair := FiniteFieldIntegerPrimes.actual_packet_positive_gives_prime_pair
      h Q n (by omega) hQn hnQ hUpos
    have hband := tail_log_character_band K h Q n hK hh hhK hKQ hQn hpair.1 hpair.2
    have hComplex := hSpec.2 h Q n hh (by omega) hhQ hQn hnQ hUpos
      (K + 1) (Q + 1) (by omega) hcut
    have hSignal : abs (primeCharacterSignal K h Q n) <= 2 * C := by
      rw [prime_signal_eq_re]
      exact (Complex.abs_re_le_norm _).trans hComplex
    have hs := abs_le.mp hSignal
    have hlo : -(2 * C) - 18 / (K : Real) <= tailLogSum K (h : Int) Q n := by
      linarith only [hband.1, hs.1]
    have hup : tailLogSum K (h : Int) Q n <= 2 * C + 8 / (K : Real) := by
      linarith only [hband.2, hs.2]
    constructor
    . calc
        _ = hybridPacket K (h : Int) Q n * Real.exp (-(2 * C) - 18 / (K : Real)) :=
          mul_comm _ _
        _ <= hybridPacket K (h : Int) Q n * Real.exp (tailLogSum K (h : Int) Q n) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hlo) hV
        _ = _ := hfactor.symm
    . calc
        _ = hybridPacket K (h : Int) Q n * Real.exp (tailLogSum K (h : Int) Q n) := hfactor
        _ <= hybridPacket K (h : Int) Q n * Real.exp (2 * C + 8 / (K : Real)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hup) hV
        _ = _ := mul_comm _ _

end PrimeFactorOscillations.FiniteFieldIntegerHeight
