/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeHalfSharpness
import PrimeFactorOscillations.Assembly.FiniteFieldNegativeNumerator

/-!
# The complete character mean for native agreement spectra

The fixed-character adapter retains the full numerator modulus, its masks
and the independent prime-field observation scale.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter IntegerQuadraticCharacter
open FiniteFieldIntegerWindowTransfer

theorem exists_eventual_nonprincipal_correlation_bound (D : Int)
    (hD : Not (D = 0)) (hchi : Not (numeratorCharacter D hD = 1)) :
    exists B : Real, And (0 <= B) (Filter.Eventually (fun U : Nat =>
      abs (primeCorrelation D (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1)) <= relativeError B U) atTop) := by
  choose C hCpos hC using QRH.exists_primeCharacter_reciprocal_tail_bound
  let B : Real := C * (3 + Real.log ((4 * D.natAbs : Nat) : Real)) ^ 2
  have hB : 0 <= B := by dsimp [B]; positivity
  have : NeZero (4 * D.natAbs) := NeZero.mk (by
    have hd := Int.natAbs_pos.mpr hD
    omega)
  refine Exists.intro B (And.intro hB ?_)
  have hfit : Filter.Eventually (fun U : Nat =>
      6 <= U /\ 1 <= Real.log (U : Real) /\
        1 <= Real.log (Real.log (U : Real)) /\ preciseCore U <= U) atTop :=
    eventually_atTop.mpr eventually_precise_core_fits
  filter_upwards [hfit] with U hf
  have ht := hC (numeratorCharacter D hD) hchi
    (preciseCore U + 1) (preciseCore U * preciseCore U + 1) (by omega)
  simp only [numerator_character_natCast] at ht
  have hid : primeCorrelation D (preciseCore U + 1)
      (preciseCore U * preciseCore U + 1) =
      (Finset.sum ((Finset.Ico (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1)).filter Nat.Prime)
        (fun p => HSMul.hSMul (1 / (p : Real)) (numeratorKernel D p))).re := by
    simp [primeCorrelation]
  have hb : abs (primeCorrelation D (preciseCore U + 1)
      (preciseCore U * preciseCore U + 1)) <=
      B * ((preciseCore U + 1 : Nat) : Real) ^ (-1 / 32 : Real) := by
    rw [hid]
    exact (Complex.abs_re_le_norm _).trans ht
  have hUpos : 0 < U := by omega
  have hprod : 0 < 4 * 1 * 1 * (U * U) * (U * U) := by positivity
  have hlevel : (1 : Real) <= ((4 * 1 * 1 * (U * U) * (U * U) : Nat) : Real) := by
    exact_mod_cast (show 1 <= 4 * 1 * 1 * (U * U) * (U * U) by omega)
  have hlog := Real.log_nonneg hlevel
  have hsq : (1 : Real) <=
      (3 + Real.log ((4 * 1 * 1 * (U * U) * (U * U) : Nat) : Real)) ^ 2 := by
    nlinarith only [hlog]
  have hscale := mul_le_mul_of_nonneg_left hsq hB
  have heps := mul_le_mul_of_nonneg_right hscale
    (Real.rpow_nonneg (show 0 <= ((preciseCore U + 1 : Nat) : Real) from Nat.cast_nonneg _)
      (-1 / 32 : Real))
  simp only [mul_one] at heps
  have hcost := signature_uniform_cost_le B hB 1 U
    (by decide) (by omega) (by omega) hf.2.1
  exact hb.trans (heps.trans hcost)

theorem fixed_nonprincipal_prime_correlation_tendsto_zero (D : Int)
    (hD : Not (D = 0)) (hchi : Not (numeratorCharacter D hD = 1)) :
    Tendsto (fun U : Nat => primeCorrelation D (preciseCore U + 1)
      (preciseCore U * preciseCore U + 1)) atTop (nhds 0) := by
  choose B hB hbound using exists_eventual_nonprincipal_correlation_bound D hD hchi
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  have herr := (relative_error_tendsto_zero B).eventually (Iio_mem_nhds heps)
  filter_upwards [hbound, herr] with U hb he
  simpa only [Real.dist_eq, sub_zero] using hb.trans_lt he

def nativeAgreementRemainder (n h m k Y X : Nat) : Real :=
  let A : Int := -((h : Int) * (n : Int))
  let B : Int := (h : Int) * ((n + h : Nat) : Int)
  let C : Int := -((k : Int) * (m : Int))
  let D : Int := (k : Int) * ((m + k : Nat) : Int)
  (-(primeCorrelation (A * B) Y X + primeCorrelation (C * D) Y X) +
    primeCorrelation (A * C) Y X + primeCorrelation (A * D) Y X +
    primeCorrelation (B * C) Y X + primeCorrelation (B * D) Y X +
    3 * primeCorrelation (A * B * C * D) Y X) / 8

theorem native_agreement_indicator (n h m k p : Nat) [Fact (Nat.Prime p)]
    (hn : 0 < n) (hh : 0 < h) (hm : 0 < m) (hk : 0 < k)
    (hp5 : 5 <= p) (hnh : n + h < p) (hmk : m + k < p) :
    let A : Int := -((h : Int) * (n : Int))
    let B : Int := (h : Int) * ((n + h : Nat) : Int)
    let C : Int := -((k : Int) * (m : Int))
    let D : Int := (k : Int) * ((m + k : Nat) : Int)
    (if integerNativeWeight n h p = integerNativeWeight m k p then (1 : Real) else 0) =
      (3 - (numeratorKernel (A * B) p).re - (numeratorKernel (C * D) p).re +
        (numeratorKernel (A * C) p).re + (numeratorKernel (A * D) p).re +
        (numeratorKernel (B * C) p).re + (numeratorKernel (B * D) p).re +
        3 * (numeratorKernel (A * B * C * D) p).re) / 8 := by
  classical
  let A : Int := -((h : Int) * (n : Int))
  let B : Int := (h : Int) * ((n + h : Nat) : Int)
  let C : Int := -((k : Int) * (m : Int))
  let D : Int := (k : Int) * ((m + k : Nat) : Int)
  let a : Real := (numeratorKernel A p).re
  let b : Real := (numeratorKernel B p).re
  let c : Real := (numeratorKernel C p).re
  let d : Real := (numeratorKernel D p).re
  change (if integerNativeWeight n h p = integerNativeWeight m k p then (1 : Real) else 0) =
    (3 - (numeratorKernel (A * B) p).re - (numeratorKernel (C * D) p).re +
      (numeratorKernel (A * C) p).re + (numeratorKernel (A * D) p).re +
      (numeratorKernel (B * C) p).re + (numeratorKernel (B * D) p).re +
      3 * (numeratorKernel (A * B * C * D) p).re) / 8
  rw [real_kernel_mul A B p, real_kernel_mul C D p,
    real_kernel_mul A C p, real_kernel_mul A D p,
    real_kernel_mul B C p, real_kernel_mul B D p,
    real_kernel_mul (A * B * C) D p, real_kernel_mul (A * B) C p,
    real_kernel_mul A B p]
  change (if integerNativeWeight n h p = integerNativeWeight m k p then (1 : Real) else 0) =
    (3 - a * b - c * d + a * c + a * d + b * c + b * d + 3 * (a * b * c * d)) / 8
  have hmod (N : Nat) (hN : 0 < N) (hNp : N < p) : Not ((N : ZMod p) = 0) := by
    intro hz
    exact (Nat.not_dvd_of_pos_of_lt hN hNp) ((ZMod.natCast_eq_zero_iff N p).mp hz)
  have hnp := hmod n hn (by omega)
  have hhp := hmod h hh (by omega)
  have hnhp := hmod (n + h) (by omega) hnh
  have hmp := hmod m hm (by omega)
  have hkp := hmod k hk (by omega)
  have hmkp := hmod (m + k) (by omega) hmk
  have hA : Not ((A : ZMod p) = 0) := by
    simpa only [A, Int.cast_neg, Int.cast_mul, Int.cast_natCast] using
      neg_ne_zero.mpr (mul_ne_zero hhp hnp)
  have hB : Not ((B : ZMod p) = 0) := by
    simpa only [B, Int.cast_mul, Int.cast_natCast] using mul_ne_zero hhp hnhp
  have hC : Not ((C : ZMod p) = 0) := by
    simpa only [C, Int.cast_neg, Int.cast_mul, Int.cast_natCast] using
      neg_ne_zero.mpr (mul_ne_zero hkp hmp)
  have hD : Not ((D : ZMod p) = 0) := by
    simpa only [D, Int.cast_mul, Int.cast_natCast] using mul_ne_zero hkp hmkp
  have ha : a ^ 2 = 1 := real_kernel_square_of_nonzero A p (by omega) hA
  have hb : b ^ 2 = 1 := real_kernel_square_of_nonzero B p (by omega) hB
  have hc : c ^ 2 = 1 := real_kernel_square_of_nonzero C p (by omega) hC
  have hd : d ^ 2 = 1 := real_kernel_square_of_nonzero D p (by omega) hD
  have hWn : ((p : Real) - 3) * integerNativeWeight n h p - ((p : Real) - 1) =
      a + b := native_weight_large_prime_trace n h p hn hp5 hnh
  have hWm : ((p : Real) - 3) * integerNativeWeight m k p - ((p : Real) - 1) =
      c + d := native_weight_large_prime_trace m k p hm hp5 hmk
  have hpR : (5 : Real) <= p := by exact_mod_cast hp5
  have hden : Not ((p : Real) - 3 = 0) := by linarith only [hpR]
  have hwiff : (integerNativeWeight n h p = integerNativeWeight m k p) <->
      a + b = c + d := by
    constructor
    . intro hw
      rw [hw] at hWn
      linarith only [hWn, hWm]
    . intro hs
      have hz : ((p : Real) - 3) *
          (integerNativeWeight n h p - integerNativeWeight m k p) = 0 := by
        nlinarith only [hWn, hWm, hs]
      exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hden)
  have hsign (v : Real) (hv : v ^ 2 = 1) : Or (v = 1) (v = -1) := by
    have hf : (v - 1) * (v + 1) = 0 := by nlinarith only [hv]
    cases mul_eq_zero.mp hf with
    | inl hleft => exact Or.inl (by linarith only [hleft])
    | inr hright => exact Or.inr (by linarith only [hright])
  have hcalc : (if a + b = c + d then (1 : Real) else 0) =
      (3 - a * b - c * d + a * c + a * d + b * c + b * d +
        3 * (a * b * c * d)) / 8 := by
    rcases hsign a ha with hsa | hsa <;>
      rcases hsign b hb with hsb | hsb <;>
      rcases hsign c hc with hsc | hsc <;>
      rcases hsign d hd with hsd | hsd <;>
      norm_num [hsa, hsb, hsc, hsd]
  by_cases hw : integerNativeWeight n h p = integerNativeWeight m k p
  . have hs := hwiff.mp hw
    simpa only [ite_eq_left hw, ite_eq_left hs] using hcalc
  . have hs : Not (a + b = c + d) := fun he => hw (hwiff.mpr he)
    simpa only [ite_eq_right hw, ite_eq_right hs] using hcalc

theorem native_agreement_mass_eq_seven_correlations (n h m k Y X : Nat)
    (hn : 0 < n) (hh : 0 < h) (hm : 0 < m) (hk : 0 < k)
    (hY : 5 <= Y) (hnh : n + h < Y) (hmk : m + k < Y) :
    nativeAgreementMass n h m k Y X =
      3 * reciprocalBand Y X / 8 + nativeAgreementRemainder n h m k Y X := by
  classical
  let S : Finset Nat := (Finset.Ico Y X).filter Nat.Prime
  let w : Nat -> Real := fun p => 1 / (p : Real)
  let f : Nat -> Real := fun p =>
    if integerNativeWeight n h p = integerNativeWeight m k p then w p else 0
  let A : Int := -((h : Int) * (n : Int))
  let B : Int := (h : Int) * ((n + h : Nat) : Int)
  let C : Int := -((k : Int) * (m : Int))
  let D : Int := (k : Int) * ((m + k : Nat) : Int)
  let T : Int -> Real := fun E => S.sum (fun p => w p * (numeratorKernel E p).re)
  change S.sum f = 3 * S.sum w / 8 +
    (-(T (A * B) + T (C * D)) + T (A * C) + T (A * D) +
      T (B * C) + T (B * D) + 3 * T (A * B * C * D)) / 8
  have hsum : S.sum f =
      (3 * S.sum w - (T (A * B) + T (C * D)) + T (A * C) + T (A * D) +
        T (B * C) + T (B * D) + 3 * T (A * B * C * D)) / 8 := by
    apply (eq_div_iff (by norm_num : Not ((8 : Real) = 0))).mpr
    rw [Finset.sum_mul]
    calc
      _ = S.sum (fun p =>
          3 * w p - w p * (numeratorKernel (A * B) p).re -
            w p * (numeratorKernel (C * D) p).re +
            w p * (numeratorKernel (A * C) p).re +
            w p * (numeratorKernel (A * D) p).re +
            w p * (numeratorKernel (B * C) p).re +
            w p * (numeratorKernel (B * D) p).re +
            3 * (w p * (numeratorKernel (A * B * C * D) p).re)) := by
        apply Finset.sum_congr rfl
        intro p hp
        have hdata := Finset.mem_filter.mp hp
        have hband := Finset.mem_Ico.mp hdata.1
        have : Fact (Nat.Prime p) := Fact.mk hdata.2
        have hind := native_agreement_indicator n h m k p hn hh hm hk
          (by omega) (by omega) (by omega)
        change (if integerNativeWeight n h p = integerNativeWeight m k p
          then (1 : Real) else 0) =
          (3 - (numeratorKernel (A * B) p).re - (numeratorKernel (C * D) p).re +
            (numeratorKernel (A * C) p).re + (numeratorKernel (A * D) p).re +
            (numeratorKernel (B * C) p).re + (numeratorKernel (B * D) p).re +
            3 * (numeratorKernel (A * B * C * D) p).re) / 8 at hind
        calc
          f p * 8 = w p *
              (if integerNativeWeight n h p = integerNativeWeight m k p
                then (1 : Real) else 0) * 8 := by
            by_cases hw : integerNativeWeight n h p = integerNativeWeight m k p <;>
              simp only [f, hw, ite_true, ite_false, mul_one, mul_zero, zero_mul]
          _ = w p *
              ((3 - (numeratorKernel (A * B) p).re - (numeratorKernel (C * D) p).re +
                (numeratorKernel (A * C) p).re + (numeratorKernel (A * D) p).re +
                (numeratorKernel (B * C) p).re + (numeratorKernel (B * D) p).re +
                3 * (numeratorKernel (A * B * C * D) p).re) / 8) * 8 := by rw [hind]
          _ = _ := by ring
      _ = _ := by
        dsimp only [T]
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
        ring
  rw [hsum]
  ring

end PrimeFactorOscillations.FiniteFieldIntegerSignature
