/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldIntegerCrestEscape

/-!
# A nonasymptotic stretched-exponential crest height bound

The full one-character amplitude estimate forces a logarithmic conductor
cost at every quartic-scale integer crest. Splitting according to whether
the exact character core fits below Q removes that core hypothesis.
The resulting height bound holds for every Q >= 6, with an exponent
defined from the existing absolute amplitude and quartic crest constants.
The same actual CRT family retains all its earlier properties.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerCrestQuantitative

open FiniteFieldIntegerMass
open FiniteFieldIntegerPrimes
open FiniteFieldIntegerExtrema
open FiniteFieldOneCharacterHeight
open FiniteFieldIntegerCrestEscape

def crestExponent (A : Real) (h : Nat) : Real :=
  min 1 (lowerConstant h / A) / 64

def crestHeightBound (A : Real) (h Q : Nat) : Real :=
  Real.exp ((Q : Real) ^ (crestExponent A h) / 2 - 3) / (4 * (h : Real))

theorem crest_exponent_pos (A : Real) (hA : 0 < A) (h : Nat) :
    0 < crestExponent A h := by
  unfold crestExponent
  exact div_pos (lt_min (by norm_num) (div_pos (lower_constant_pos h) hA)) (by norm_num)

theorem crest_exponent_le (A : Real) (h : Nat) :
    crestExponent A h <= 1 / 64 := by
  unfold crestExponent
  exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)

theorem crest_input_pos (h Q n : Nat) (hQ : 6 <= Q)
    (hcrest : lowerConstant h * (Real.log (Q : Real)) ^ 4 <= actualPacket (h : Int) Q n) :
    0 < n := by
  have hL : 0 < Real.log (Q : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < Q from by omega))
  have hp : 0 < lowerConstant h * (Real.log (Q : Real)) ^ 4 :=
    mul_pos (lower_constant_pos h) (pow_pos hL 4)
  by_contra hn
  have hn0 : n = 0 := by omega
  have hz := actual_packet_zero_of_prime_divisor (h : Int) Q n 2
    (by decide : Nat.Prime 2) (by omega) (by rw [hn0]; exact dvd_zero 2)
  rw [hz] at hcrest
  linarith only [hp, hcrest]

theorem crest_log_height_of_amplitude (A : Real) (hA : 0 < A)
    (hBound : forall K h Q n : Nat, 6 <= K -> 0 < h -> 0 < n -> K <= Q ->
      (3 + Real.log ((4 * h * n : Nat) : Real)) ^ 64 <= ((K + 1 : Nat) : Real) ->
      actualPacket (h : Int) Q n <=
        A * (Real.log (Q : Real)) ^ 3 * Real.log (K : Real))
    (h Q n : Nat) (hh : 0 < h) (hQ : 6 <= Q)
    (hcrest : lowerConstant h * (Real.log (Q : Real)) ^ 4 <= actualPacket (h : Int) Q n) :
    min 1 (lowerConstant h / A) * Real.log (Q : Real) <=
      Real.log 2 + 64 * Real.log (3 + Real.log ((4 * h * n : Nat) : Real)) := by
  have hn := crest_input_pos h Q n hQ hcrest
  let H : Real := 3 + Real.log ((4 * h * n : Nat) : Real)
  let K : Nat := Nat.ceil (H ^ 64)
  have hN : 0 < 4 * h * n := by positivity
  have hN1 : (1 : Real) <= ((4 * h * n : Nat) : Real) := by
    exact_mod_cast (show 1 <= 4 * h * n by omega)
  have hH3 : 3 <= H := by
    have ht := Real.log_nonneg hN1
    dsimp [H]
    linarith only [ht]
  have hH : 0 < H := by linarith only [hH3]
  have hpow : (3 : Real) ^ 64 <= H ^ 64 := by gcongr
  have hX6 : (6 : Real) <= H ^ 64 := by
    calc
      _ <= (3 : Real) ^ 64 := by norm_num
      _ <= _ := hpow
  have hK6 : 6 <= K := by
    have ht : (6 : Real) <= (K : Real) := hX6.trans (Nat.le_ceil _)
    exact_mod_cast ht
  have hL : 0 < Real.log (Q : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < Q from by omega))
  have hQR : 0 < (Q : Real) := by exact_mod_cast (show 0 < Q from by omega)
  have hlog2 : 0 <= Real.log 2 := Real.log_nonneg (by norm_num)
  change min 1 (lowerConstant h / A) * Real.log (Q : Real) <=
    Real.log 2 + 64 * Real.log H
  by_cases hKQ : K <= Q
  . have hcut : H ^ 64 <= ((K + 1 : Nat) : Real) := by
      calc
        _ <= (K : Real) := Nat.le_ceil _
        _ <= _ := by simp only [Nat.cast_add, Nat.cast_one]; linarith
    have hu := hBound K h Q n hK6 hh hn hKQ hcut
    have hbase : lowerConstant h * Real.log (Q : Real) <= A * Real.log (K : Real) := by
      by_contra hnot
      have hs := mul_lt_mul_of_pos_right (lt_of_not_ge hnot) (pow_pos hL 3)
      nlinarith only [hcrest, hu, hs]
    have hscaled : (lowerConstant h / A) * Real.log (Q : Real) <= Real.log (K : Real) := by
      calc
        _ = (lowerConstant h * Real.log (Q : Real)) * (1 / A) := by ring
        _ <= (A * Real.log (K : Real)) * (1 / A) :=
          mul_le_mul_of_nonneg_right hbase (one_div_nonneg.mpr hA.le)
        _ = _ := by field_simp [ne_of_gt hA]
    have hsmall : min 1 (lowerConstant h / A) * Real.log (Q : Real) <=
        Real.log (K : Real) :=
      (mul_le_mul_of_nonneg_right (min_le_right _ _) hL.le).trans hscaled
    have hceil := Nat.ceil_lt_add_one (pow_nonneg hH.le 64)
    have hKupper : (K : Real) <= 2 * H ^ 64 := by
      change (K : Real) < H ^ 64 + 1 at hceil
      linarith only [hceil, hX6]
    have hKR : 0 < (K : Real) := by exact_mod_cast (show 0 < K from by omega)
    have hlogK := Real.log_le_log hKR hKupper
    rw [Real.log_mul (by norm_num) (pow_ne_zero 64 (ne_of_gt hH)), Real.log_pow] at hlogK
    exact hsmall.trans hlogK
  . have hlarge : (Q : Real) < H ^ 64 := by
      apply lt_of_not_ge
      intro hx
      exact hKQ (Nat.ceil_le.mpr hx)
    have hlogQ := Real.log_le_log hQR hlarge.le
    rw [Real.log_pow] at hlogQ
    norm_num at hlogQ
    have hsmall : min 1 (lowerConstant h / A) * Real.log (Q : Real) <= Real.log (Q : Real) := by
      calc
        _ <= 1 * Real.log (Q : Real) := mul_le_mul_of_nonneg_right (min_le_left _ _) hL.le
        _ = _ := by ring
    linarith only [hsmall, hlogQ, hlog2]

theorem exists_stretched_exponential_crest_height :
    exists A : Real, And (0 < A)
      (forall h Q n : Nat, 0 < h -> 6 <= Q ->
        lowerConstant h * (Real.log (Q : Real)) ^ 4 <= actualPacket (h : Int) Q n ->
        crestHeightBound A h Q <= (n : Real)) := by
  let A : Real := Classical.choose exists_one_character_split_amplitude
  have hA := Classical.choose_spec exists_one_character_split_amplitude
  refine Exists.intro A (And.intro hA.1 ?_)
  intro h Q n hh hQ hcrest
  have hn := crest_input_pos h Q n hQ hcrest
  have hhR : 0 < (h : Real) := by exact_mod_cast hh
  have hN : 0 < 4 * h * n := by positivity
  have hNR : 0 < ((4 * h * n : Nat) : Real) := by exact_mod_cast hN
  let H : Real := 3 + Real.log ((4 * h * n : Nat) : Real)
  have hH : 0 < H := by
    have ht : 0 <= Real.log ((4 * h * n : Nat) : Real) :=
      Real.log_nonneg (by exact_mod_cast (show 1 <= 4 * h * n by omega))
    dsimp [H]
    linarith only [ht]
  have hlog := crest_log_height_of_amplitude A hA.1 hA.2 h Q n hh hQ hcrest
  have hlog2 : 0 <= Real.log 2 := Real.log_nonneg (by norm_num)
  have hscale : crestExponent A h * Real.log (Q : Real) <= Real.log 2 + Real.log H := by
    dsimp [crestExponent, H]
    linarith only [hlog, hlog2]
  have hQR : 0 < (Q : Real) := by exact_mod_cast (show 0 < Q from by omega)
  have hpower : (Q : Real) ^ (crestExponent A h) <= 2 * H := by
    rw [Real.rpow_def_of_pos hQR]
    calc
      _ <= Real.exp (Real.log 2 + Real.log H) :=
        Real.exp_le_exp.mpr (by linarith only [hscale])
      _ = _ := by rw [Real.exp_add, Real.exp_log (by norm_num), Real.exp_log hH]
  have hprodlog :
      (Q : Real) ^ (crestExponent A h) / 2 - 3 <=
        Real.log ((4 * h * n : Nat) : Real) := by
    dsimp [H] at hpower
    linarith only [hpower]
  have he := Real.exp_le_exp.mpr hprodlog
  rw [Real.exp_log hNR] at he
  unfold crestHeightBound
  calc
    _ <= ((4 * h * n : Nat) : Real) / (4 * (h : Real)) :=
      div_le_div_of_nonneg_right he (by positivity)
    _ = (n : Real) := by
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      field_simp [ne_of_gt hhR]

theorem exists_stretched_exponential_integer_crest_family :
    exists A : Real, And (0 < A)
      (forall h : Nat, 0 < h -> Dvd.dvd 2 h ->
        exists a : Nat -> Nat, And
          (forall Q : Nat, 13 <= Q ->
            And (a Q < primePeriod Q)
              (And
                (forall t : Nat, lowerConstant h * (Real.log (Q : Real)) ^ 4 <=
                  actualPacket (h : Int) Q (a Q + primePeriod Q * t))
                (forall n : Nat, actualPacket (h : Int) Q n <=
                  replacementConstant * (Real.log (Q : Real)) ^ 4)))
          (And
            (forall m : Nat, exists Q0 : Nat, forall Q : Nat, Q0 <= Q -> forall t : Nat,
              Q ^ m < a Q + primePeriod Q * t)
            (forall Q : Nat, 13 <= Q -> forall t : Nat,
              crestHeightBound A h Q <= ((a Q + primePeriod Q * t : Nat) : Real)))) := by
  let A : Real := Classical.choose exists_stretched_exponential_crest_height
  have hA := Classical.choose_spec exists_stretched_exponential_crest_height
  refine Exists.intro A (And.intro hA.1 ?_)
  intro h hh heven
  let a : Nat -> Nat := Classical.choose (exists_superpolynomial_integer_crest_family h hh heven)
  have ha := Classical.choose_spec (exists_superpolynomial_integer_crest_family h hh heven)
  refine Exists.intro a (And.intro ha.1 (And.intro ha.2 ?_))
  intro Q hQ t
  exact hA.2 h Q (a Q + primePeriod Q * t) hh (by omega) ((ha.1 Q hQ).2.1 t)

end PrimeFactorOscillations.FiniteFieldIntegerCrestQuantitative
