/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldIntegerAmplitude
import PrimeFactorOscillations.Assembly.FiniteFieldIntegerCrestHeight

/-!
# Uniform amplitude at natural integer height

An absolute polylogarithmic core works simultaneously for every 1 <= h < Q.
The resulting actual integer packet is bounded by log(Q)^2 log(log(Q))^2,
uniformly on Q < n and n+h <= Q^2. The theorem is an amplitude bound;
it does not supply positive mass or recurring integer prime pairs.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerNaturalAmplitude

open FiniteFieldIntegerMass
open FiniteFieldIntegerAmplitude
open Filter

def naturalCore (Q : Nat) : Nat :=
  Nat.ceil ((10 * Real.log (Q : Real)) ^ 64)

theorem uniform_log_level_bound (h Q : Nat)
    (hh : 0 < h) (hhQ : h < Q) (hlog : 1 <= Real.log (Q : Real)) :
    And (0 <= 3 + Real.log ((4 * h * (Q * Q) : Nat) : Real))
      (3 + Real.log ((4 * h * (Q * Q) : Nat) : Real) <= 10 * Real.log (Q : Real)) := by
  have hQ : 0 < Q := by omega
  have hQR : 0 < (Q : Real) := by exact_mod_cast hQ
  have hN : 0 < 4 * h * (Q * Q) := by positivity
  have hNR : 0 < ((4 * h * (Q * Q) : Nat) : Real) := by exact_mod_cast hN
  have hN1 : (1 : Real) <= ((4 * h * (Q * Q) : Nat) : Real) := by
    exact_mod_cast (show 1 <= 4 * h * (Q * Q) by omega)
  have hlevel : ((4 * h * (Q * Q) : Nat) : Real) <= 4 * (Q : Real) ^ 3 := by
    have hhR : (h : Real) <= (Q : Real) := by exact_mod_cast hhQ.le
    have hm := mul_le_mul_of_nonneg_right hhR (sq_nonneg (Q : Real))
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith only [hm]
  have hloglevel := Real.log_le_log hNR hlevel
  have hlogid : Real.log (4 * (Q : Real) ^ 3) = Real.log 4 + 3 * Real.log (Q : Real) := by
    rw [Real.log_mul (by norm_num) (pow_ne_zero 3 (ne_of_gt hQR)), Real.log_pow]
    norm_num
  rw [hlogid] at hloglevel
  have h4 := Real.log_le_sub_one_of_pos (show (0 : Real) < 4 by norm_num)
  refine And.intro ?_ ?_
  . have hln := Real.log_nonneg hN1
    linarith only [hln]
  . linarith only [hloglevel, h4, hlog]

theorem natural_core_ge_six (Q : Nat) (hlog : 1 <= Real.log (Q : Real)) :
    6 <= naturalCore Q := by
  have hb : (10 : Real) <= 10 * Real.log (Q : Real) := by linarith only [hlog]
  have hp : (10 : Real) ^ 64 <= (10 * Real.log (Q : Real)) ^ 64 := by
    gcongr
  have h6 : (6 : Real) <= ((naturalCore Q : Nat) : Real) := by
    calc
      _ <= (10 : Real) ^ 64 := by norm_num
      _ <= (10 * Real.log (Q : Real)) ^ 64 := hp
      _ <= _ := Nat.le_ceil _
  exact_mod_cast h6

theorem natural_core_covers_level (h Q : Nat)
    (hh : 0 < h) (hhQ : h < Q) (hlog : 1 <= Real.log (Q : Real)) :
    (3 + Real.log ((4 * h * (Q * Q) : Nat) : Real)) ^ 64 <=
      ((naturalCore Q + 1 : Nat) : Real) := by
  have hlevel := uniform_log_level_bound h Q hh hhQ hlog
  have hp : (3 + Real.log ((4 * h * (Q * Q) : Nat) : Real)) ^ 64 <=
      (10 * Real.log (Q : Real)) ^ 64 := by
    have hlo := hlevel.1
    have hhi := hlevel.2
    gcongr
  calc
    _ <= (10 * Real.log (Q : Real)) ^ 64 := hp
    _ <= ((naturalCore Q : Nat) : Real) := Nat.le_ceil _
    _ <= _ := by simp only [Nat.cast_add, Nat.cast_one]; linarith

theorem natural_core_log_bound (Q : Nat)
    (hlog : 1 <= Real.log (Q : Real))
    (hloglog : 1 <= Real.log (Real.log (Q : Real))) :
    Real.log ((naturalCore Q : Nat) : Real) <=
      641 * Real.log (Real.log (Q : Real)) := by
  have hK := natural_core_ge_six Q hlog
  have hKR : 0 < ((naturalCore Q : Nat) : Real) := by exact_mod_cast (show 0 < naturalCore Q by omega)
  have hL : 0 < Real.log (Q : Real) := by linarith only [hlog]
  have hB : 0 < 10 * Real.log (Q : Real) := by positivity
  have hX1 : (1 : Real) <= (10 * Real.log (Q : Real)) ^ 64 := by
    calc
      _ <= (10 : Real) ^ 64 := by norm_num
      _ <= _ := by gcongr; linarith only [hlog]
  have hceil := Nat.ceil_lt_add_one (pow_nonneg hB.le 64)
  have hKupper : ((naturalCore Q : Nat) : Real) <=
      2 * (10 * Real.log (Q : Real)) ^ 64 := by
    dsimp [naturalCore]
    linarith only [hceil, hX1]
  have ht := Real.log_le_log hKR hKupper
  rw [Real.log_mul (by norm_num) (pow_ne_zero 64 (ne_of_gt hB)), Real.log_pow,
    Real.log_mul (by norm_num) (ne_of_gt hL)] at ht
  have h2 := Real.log_le_sub_one_of_pos (show (0 : Real) < 2 by norm_num)
  have h10 := Real.log_le_sub_one_of_pos (show (0 : Real) < 10 by norm_num)
  norm_num at ht
  linarith only [ht, h2, h10, hloglog]

theorem eventually_natural_core_fits :
    exists Q0 : Nat, forall Q : Nat, Q0 <= Q ->
      And (6 <= Q) (And (1 <= Real.log (Q : Real))
        (And (1 <= Real.log (Real.log (Q : Real))) (naturalCore Q <= Q))) := by
  have hNat : Tendsto (fun Q : Nat => (Q : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun Q : Nat => (10 * Real.log (Q : Real)) ^ 64 / (Q : Real))
      atTop (nhds 0) := by
    have ht := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 64 (by norm_num)).comp hNat
    have hc := ht.const_mul ((10 : Real) ^ 64)
    simpa only [Function.comp_apply, one_mul, add_zero, mul_zero, mul_pow, mul_div_assoc] using hc
  have hsmall : Filter.Eventually
      (fun Q : Nat => (10 * Real.log (Q : Real)) ^ 64 / (Q : Real) < 1) atTop :=
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

theorem exists_uniform_natural_height_amplitude :
    exists B : Real, And (0 < B) (exists Q0 : Nat,
      forall Q : Nat, Q0 <= Q -> forall h n : Nat,
        0 < h -> h < Q -> Q < n -> n + h <= Q * Q ->
        actualPacket (h : Int) Q n <=
          B * (Real.log (Q : Real)) ^ 2 *
            (Real.log (Real.log (Q : Real))) ^ 2) := by
  let A : Real := Classical.choose exists_natural_height_split_amplitude
  have hA := Classical.choose_spec exists_natural_height_split_amplitude
  have hApos : 0 < A := hA.1
  let Q0 : Nat := Classical.choose eventually_natural_core_fits
  have hQ0 := Classical.choose_spec eventually_natural_core_fits
  refine Exists.intro (A * 641 ^ 2) (And.intro (by positivity) ?_)
  refine Exists.intro Q0 ?_
  intro Q hQQ h n hh hhQ hQn hnQ
  have hfit := hQ0 Q hQQ
  have hK := natural_core_ge_six Q hfit.2.1
  have hcut := natural_core_covers_level h Q hh hhQ hfit.2.1
  have hp := hA.2 (naturalCore Q) h Q n hK hh hhQ hfit.2.2.2 hQn hnQ hcut
  have hLK0 : 0 <= Real.log ((naturalCore Q : Nat) : Real) :=
    Real.log_nonneg (by exact_mod_cast (show 1 <= naturalCore Q by omega))
  have hLK := natural_core_log_bound Q hfit.2.1 hfit.2.2.1
  have hs := mul_self_le_mul_self hLK0 hLK
  have hpow : (Real.log ((naturalCore Q : Nat) : Real)) ^ 2 <=
      (641 * Real.log (Real.log (Q : Real))) ^ 2 := by
    nlinarith only [hs]
  calc
    _ <= A * (Real.log (Q : Real)) ^ 2 *
        (Real.log ((naturalCore Q : Nat) : Real)) ^ 2 := hp
    _ <= A * (Real.log (Q : Real)) ^ 2 *
        (641 * Real.log (Real.log (Q : Real))) ^ 2 :=
      mul_le_mul_of_nonneg_left hpow (mul_nonneg hA.1.le (sq_nonneg _))
    _ = _ := by ring

end PrimeFactorOscillations.FiniteFieldIntegerNaturalAmplitude
