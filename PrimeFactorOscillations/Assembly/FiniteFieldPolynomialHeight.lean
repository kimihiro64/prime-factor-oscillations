/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldIntegerNaturalAmplitude
import PrimeFactorOscillations.Assembly.FiniteFieldOneCharacterHeight

/-!
# Uniform packet amplitude on every fixed polynomial integer-height range

One negative numerator character suffices to save one logarithmic power,
even for composite integer inputs. An absolute amplitude constant precedes
the degree; only the eventual cutoff depends on that fixed degree.
No positive prime-pair mass, integer recurrence or new zero-free exponent
is assumed or asserted.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldPolynomialHeight

open FiniteFieldIntegerMass
open FiniteFieldOneCharacterHeight
open Filter

def polynomialCore (m Q : Nat) : Nat :=
  Nat.ceil ((((m : Real) + 10) * Real.log (Q : Real)) ^ 64)

theorem polynomial_log_level_bound (m h Q n : Nat)
    (hh : 0 < h) (hn : 0 < n) (hhQ : h < Q) (hnQ : n <= Q ^ m)
    (hlog : 1 <= Real.log (Q : Real)) :
    And (0 <= 3 + Real.log ((4 * h * n : Nat) : Real))
      (3 + Real.log ((4 * h * n : Nat) : Real) <=
        ((m : Real) + 10) * Real.log (Q : Real)) := by
  have hQ : 0 < Q := by omega
  have hQR : 0 < (Q : Real) := by exact_mod_cast hQ
  have hN : 0 < 4 * h * n := by positivity
  have hNR : 0 < ((4 * h * n : Nat) : Real) := by exact_mod_cast hN
  have hN1 : (1 : Real) <= ((4 * h * n : Nat) : Real) := by
    exact_mod_cast (show 1 <= 4 * h * n by omega)
  have hhR : (h : Real) <= (Q : Real) := by exact_mod_cast hhQ.le
  have hnR : (n : Real) <= (Q : Real) ^ m := by exact_mod_cast hnQ
  have hlevel : ((4 * h * n : Nat) : Real) <= 4 * (Q : Real) ^ (m + 1) := by
    have hm := mul_le_mul hhR hnR (Nat.cast_nonneg n) hQR.le
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    rw [pow_succ]
    nlinarith only [hm]
  have hl := Real.log_le_log hNR hlevel
  have hid :
      Real.log (4 * (Q : Real) ^ (m + 1)) =
        Real.log 4 + ((m : Real) + 1) * Real.log (Q : Real) := by
    rw [Real.log_mul (by norm_num) (pow_ne_zero (m + 1) (ne_of_gt hQR)), Real.log_pow]
    simp only [Nat.cast_add, Nat.cast_one]
  rw [hid] at hl
  have h4 := Real.log_le_sub_one_of_pos (show (0 : Real) < 4 by norm_num)
  refine And.intro ?_ ?_
  . have hln := Real.log_nonneg hN1
    linarith only [hln]
  . nlinarith only [hl, h4, hlog]

theorem polynomial_core_ge_six (m Q : Nat) (hlog : 1 <= Real.log (Q : Real)) :
    6 <= polynomialCore m Q := by
  have hL : 0 <= Real.log (Q : Real) := by linarith only [hlog]
  have hb : (10 : Real) <= ((m : Real) + 10) * Real.log (Q : Real) := by
    have hm := mul_nonneg (Nat.cast_nonneg m) hL
    nlinarith only [hlog, hm]
  have hp : (10 : Real) ^ 64 <= (((m : Real) + 10) * Real.log (Q : Real)) ^ 64 := by
    gcongr
  have h6 : (6 : Real) <= ((polynomialCore m Q : Nat) : Real) := by
    calc
      _ <= (10 : Real) ^ 64 := by norm_num
      _ <= (((m : Real) + 10) * Real.log (Q : Real)) ^ 64 := hp
      _ <= _ := Nat.le_ceil _
  exact_mod_cast h6

theorem polynomial_core_covers_level (m h Q n : Nat)
    (hh : 0 < h) (hn : 0 < n) (hhQ : h < Q) (hnQ : n <= Q ^ m)
    (hlog : 1 <= Real.log (Q : Real)) :
    (3 + Real.log ((4 * h * n : Nat) : Real)) ^ 64 <=
      ((polynomialCore m Q + 1 : Nat) : Real) := by
  have hlevel := polynomial_log_level_bound m h Q n hh hn hhQ hnQ hlog
  have hp : (3 + Real.log ((4 * h * n : Nat) : Real)) ^ 64 <=
      (((m : Real) + 10) * Real.log (Q : Real)) ^ 64 := by
    have hlo := hlevel.1
    have hhi := hlevel.2
    gcongr
  calc
    _ <= (((m : Real) + 10) * Real.log (Q : Real)) ^ 64 := hp
    _ <= ((polynomialCore m Q : Nat) : Real) := Nat.le_ceil _
    _ <= _ := by simp only [Nat.cast_add, Nat.cast_one]; linarith

theorem polynomial_core_log_bound (m Q : Nat)
    (hlog : 1 <= Real.log (Q : Real))
    (hloglog : 1 <= Real.log (Real.log (Q : Real))) :
    Real.log ((polynomialCore m Q : Nat) : Real) <=
      (64 * (m : Real) + 641) * Real.log (Real.log (Q : Real)) := by
  have hK := polynomial_core_ge_six m Q hlog
  have hKR : 0 < ((polynomialCore m Q : Nat) : Real) := by
    exact_mod_cast (show 0 < polynomialCore m Q by omega)
  have hL : 0 < Real.log (Q : Real) := by linarith only [hlog]
  have hm : 0 <= (m : Real) := Nat.cast_nonneg m
  have hm10 : 0 < (m : Real) + 10 := by positivity
  have hB : 0 < ((m : Real) + 10) * Real.log (Q : Real) := mul_pos hm10 hL
  have hb : (10 : Real) <= ((m : Real) + 10) * Real.log (Q : Real) := by
    nlinarith only [hlog, mul_nonneg hm hL.le]
  have hX1 : (1 : Real) <= (((m : Real) + 10) * Real.log (Q : Real)) ^ 64 := by
    calc
      _ <= (10 : Real) ^ 64 := by norm_num
      _ <= _ := by gcongr
  have hceil := Nat.ceil_lt_add_one (pow_nonneg hB.le 64)
  have hKupper : ((polynomialCore m Q : Nat) : Real) <=
      2 * (((m : Real) + 10) * Real.log (Q : Real)) ^ 64 := by
    dsimp [polynomialCore]
    linarith only [hceil, hX1]
  have ht := Real.log_le_log hKR hKupper
  rw [Real.log_mul (by norm_num) (pow_ne_zero 64 (ne_of_gt hB)), Real.log_pow,
    Real.log_mul (ne_of_gt hm10) (ne_of_gt hL)] at ht
  have h2 := Real.log_le_sub_one_of_pos (show (0 : Real) < 2 by norm_num)
  have hM := Real.log_le_sub_one_of_pos hm10
  have hreserve := mul_nonneg (show 0 <= 64 * (m : Real) + 577 by positivity)
    (sub_nonneg.mpr hloglog)
  norm_num at ht
  nlinarith only [ht, h2, hM, hreserve]

theorem eventually_polynomial_core_fits (m : Nat) :
    exists Q0 : Nat, forall Q : Nat, Q0 <= Q ->
      And (6 <= Q) (And (1 <= Real.log (Q : Real))
        (And (1 <= Real.log (Real.log (Q : Real))) (polynomialCore m Q <= Q))) := by
  have hNat : Tendsto (fun Q : Nat => (Q : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlim : Tendsto
      (fun Q : Nat => (((m : Real) + 10) * Real.log (Q : Real)) ^ 64 / (Q : Real))
      atTop (nhds 0) := by
    have ht := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 64 (by norm_num)).comp hNat
    have hc := ht.const_mul (((m : Real) + 10) ^ 64)
    simpa only [Function.comp_apply, one_mul, add_zero, mul_zero, mul_pow, mul_div_assoc] using hc
  have hsmall : Filter.Eventually
      (fun Q : Nat => (((m : Real) + 10) * Real.log (Q : Real)) ^ 64 / (Q : Real) < 1) atTop :=
    hlim.eventually (Iio_mem_nhds (by norm_num))
  have hlog := (Real.tendsto_log_atTop.comp hNat).eventually_ge_atTop 1
  have hloglog :=
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hNat)).eventually_ge_atTop 1
  have hsix : Filter.Eventually (fun Q : Nat => 6 <= Q) atTop :=
    Filter.eventually_atTop.mpr (Exists.intro 6 (fun Q hQ => hQ))
  apply Filter.eventually_atTop.mp
  apply (hsmall.and (hlog.and (hloglog.and hsix))).mono
  intro Q hQ
  refine And.intro hQ.2.2.2 (And.intro hQ.2.1 (And.intro hQ.2.2.1 ?_))
  apply Nat.ceil_le.mpr
  have hQR : 0 < (Q : Real) := by exact_mod_cast (show 0 < Q by omega)
  exact ((div_lt_one hQR).mp hQ.1).le

theorem exists_uniform_polynomial_height_amplitude :
    exists A : Real, And (0 < A) (forall m : Nat, exists Q0 : Nat,
      forall Q : Nat, Q0 <= Q -> forall h n : Nat,
        0 < h -> h < Q -> 0 < n -> n <= Q ^ m ->
        actualPacket (h : Int) Q n <=
          A * (64 * (m : Real) + 641) * (Real.log (Q : Real)) ^ 3 *
            Real.log (Real.log (Q : Real))) := by
  let A : Real := Classical.choose exists_one_character_split_amplitude
  have hA := Classical.choose_spec exists_one_character_split_amplitude
  have hApos : 0 < A := hA.1
  refine Exists.intro A (And.intro hApos ?_)
  intro m
  let Q0 : Nat := Classical.choose (eventually_polynomial_core_fits m)
  have hQ0 := Classical.choose_spec (eventually_polynomial_core_fits m)
  refine Exists.intro Q0 ?_
  intro Q hQQ h n hh hhQ hn hnQ
  have hfit := hQ0 Q hQQ
  have hK := polynomial_core_ge_six m Q hfit.2.1
  have hcut := polynomial_core_covers_level m h Q n hh hn hhQ hnQ hfit.2.1
  have hp := hA.2 (polynomialCore m Q) h Q n hK hh hn hfit.2.2.2 hcut
  have hLK := polynomial_core_log_bound m Q hfit.2.1 hfit.2.2.1
  have hLQ : 0 <= Real.log (Q : Real) := by linarith only [hfit.2.1]
  calc
    _ <= A * (Real.log (Q : Real)) ^ 3 *
        Real.log ((polynomialCore m Q : Nat) : Real) := hp
    _ <= A * (Real.log (Q : Real)) ^ 3 *
        ((64 * (m : Real) + 641) * Real.log (Real.log (Q : Real))) :=
      mul_le_mul_of_nonneg_left hLK (mul_nonneg hApos.le (pow_nonneg hLQ 3))
    _ = _ := by ring

end PrimeFactorOscillations.FiniteFieldPolynomialHeight
