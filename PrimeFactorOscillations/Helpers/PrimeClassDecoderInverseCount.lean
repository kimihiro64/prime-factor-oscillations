/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderClassification

/-!
# Retaining the logarithmic divisor in the inverse count bound

The exact growing binary samples preserve the factor b*j in the rank
denominator. This is the sharp shell input for the all-cutoff inverse
estimate, rather than the coarser geometric bound used for capacity.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open Filter
open PrimeFactorOscillations.PrimeClassDecoder

theorem decoderCapacitySample_iterated (b j : Nat) :
    iteratedBinaryCutoff (decoderCapacitySample b j) = b * j := by
  simp only [iteratedBinaryCutoff, decoderCapacitySample_binary,
    Nat.log_pow (by norm_num : 1 < 2)]

theorem decoderRank_capacitySample_le
    (c : Real) (hc : 0 <= c) (b j : Nat) :
    (decoderRank c (decoderCapacitySample b j) : Real) <=
      c * (2 : Real) ^ (b * j) / ((b : Real) * (j : Real)) := by
  unfold decoderRank
  rw [decoderCapacitySample_binary, decoderCapacitySample_iterated]
  have hnonneg : 0 <= c *
      (((2 ^ (b * j) : Nat) : Real) / ((b * j : Nat) : Real)) :=
    mul_nonneg hc (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hfloor := Nat.floor_le hnonneg
  convert hfloor using 1
  push_cast
  ring

theorem integerDecoderAdmissible_sharp_shell_count
    (P : Set Nat) (a b : Nat) (hb : 1 <= b)
    (had : integerDecoderAdmissible P ((a : Rat) / (b : Rat))) :
    exists c : Rat, And (0 < c)
      (Filter.Eventually (fun j : Nat =>
        ((primeClassPrefix P ((2 ^ a) ^ j)).card : Real) <=
          (c : Real) * (2 : Real) ^ (b * j) / ((b : Real) * (j : Real))) atTop) := by
  choose c hc using integerDecoderAdmissible_degree_budget P _ had
  apply Exists.intro c
  apply And.intro hc.1
  have hsample := (decoderCapacitySample_atTop b hb).eventually hc.2
  filter_upwards [hsample] with j hj
  have hratio : (((a : Rat) / (b : Rat) : Rat) : Real) =
      (a : Real) / (b : Real) := by push_cast; rfl
  rw [hratio, decoderCapacitySample_radius a b j hb] at hj
  have hcard := primeClassPrefix_card_mono P (2 ^ (a * j))
    (2 ^ (a * j) + 1) (by omega)
  have hcount : ((primeClassPrefix P (2 ^ (a * j))).card : Real) <=
      (decoderRank (c : Real) (decoderCapacitySample b j) : Real) := by
    exact_mod_cast hcard.trans hj
  have hbound := decoderRank_capacitySample_le (c : Real)
    (by exact_mod_cast (le_of_lt hc.1)) b j
  have htotal := hcount.trans hbound
  rw [pow_mul] at htotal
  exact htotal

def decoderInverseIndex (a X : Nat) : Nat := Nat.log (2 ^ a) X + 1

theorem decoderInverseIndex_atTop (a : Nat) (ha : 1 <= a) :
    Tendsto (decoderInverseIndex a) atTop atTop := by
  have hB : 1 < 2 ^ a := by
    have hpow := Nat.pow_le_pow_right (by norm_num : 1 <= 2) ha
    norm_num at hpow
    omega
  apply tendsto_atTop.2
  intro K
  filter_upwards [eventually_ge_atTop ((2 ^ a) ^ K)] with X hX
  have hlog := Nat.le_log_of_pow_le hB hX
  unfold decoderInverseIndex
  omega

theorem decoderInverseIndex_power_bound
    (a b X : Nat) (ha : 1 <= a) (hX : 1 <= X) :
    (2 : Real) ^ (b * decoderInverseIndex a X) <=
      (2 : Real) ^ b * (X : Real) ^ ((b : Real) / (a : Real)) := by
  let k := Nat.log (2 ^ a) X
  have haR : (0 : Real) < (a : Real) := by exact_mod_cast (show 0 < a by omega)
  have hlow : (2 ^ a) ^ k <= X := Nat.pow_log_le_self _ (by omega)
  have hpower : ((((2 ^ a) ^ k : Nat) : Real) ^ ((b : Real) / (a : Real))) =
      (2 : Real) ^ (b * k) := by
    rw [<- pow_mul, Nat.cast_pow]
    norm_num only [Nat.cast_ofNat]
    rw [<- Real.rpow_natCast, <- Real.rpow_mul (by norm_num : (0 : Real) <= 2)]
    have heq : ((a * k : Nat) : Real) * ((b : Real) / (a : Real)) =
        ((b * k : Nat) : Real) := by
      push_cast
      field_simp
    rw [heq, Real.rpow_natCast]
  have hcomp : (2 : Real) ^ (b * k) <= (X : Real) ^ ((b : Real) / (a : Real)) := by
    rw [<- hpower]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hlow)
      (div_nonneg (Nat.cast_nonneg b) (le_of_lt haR))
  change (2 : Real) ^ (b * (k + 1)) <= _
  rw [Nat.mul_add, Nat.mul_one, pow_add]
  exact (mul_comm _ _).le.trans
    (mul_le_mul_of_nonneg_left hcomp (pow_nonneg (by norm_num) b))

theorem decoderInverseIndex_log_bound
    (a X : Nat) (ha : 1 <= a) (hX : 1 <= X) :
    Real.log (X : Real) <=
      (decoderInverseIndex a X : Real) * (a : Real) * Real.log 2 := by
  have hB : 1 < 2 ^ a := by
    have hpow := Nat.pow_le_pow_right (by norm_num : 1 <= 2) ha
    norm_num at hpow
    omega
  have hbound := Nat.lt_pow_succ_log_self hB X
  have hlog := Real.log_le_log
    (by exact_mod_cast (show 0 < X by omega))
    (by exact_mod_cast (le_of_lt hbound) :
      (X : Real) <= (((2 ^ a) ^ (Nat.log (2 ^ a) X + 1) : Nat) : Real))
  rw [Nat.cast_pow, Real.log_pow, Nat.cast_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  rw [Real.log_pow] at hlog
  change Real.log (X : Real) <=
    ((Nat.log (2 ^ a) X + 1 : Nat) : Real) * (a : Real) * Real.log 2
  simpa only [mul_assoc] using hlog

theorem integerDecoderAdmissible_inverse_count_of_ratio
    (P : Set Nat) (a b : Nat) (ha : 1 <= a) (hb : 1 <= b)
    (had : integerDecoderAdmissible P ((a : Rat) / (b : Rat))) :
    exists K : Real, And (0 < K)
      (Filter.Eventually (fun X : Nat =>
        ((primeClassPrefix P X).card : Real) <=
          K * (X : Real) ^ ((b : Real) / (a : Real)) / Real.log (X : Real)) atTop) := by
  choose c hc using integerDecoderAdmissible_sharp_shell_count P a b hb had
  have hcR : (0 : Real) < (c : Real) := by exact_mod_cast hc.1
  have haR : (0 : Real) < (a : Real) := by exact_mod_cast (show 0 < a by omega)
  have hbR : (0 : Real) < (b : Real) := by exact_mod_cast (show 0 < b by omega)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let K : Real := (c : Real) * (2 : Real) ^ b * ((a : Real) * Real.log 2 / (b : Real))
  apply Exists.intro K
  apply And.intro (by dsimp [K]; positivity)
  have hsample := (decoderInverseIndex_atTop a ha).eventually hc.2
  filter_upwards [hsample, eventually_ge_atTop 2] with X hN hX
  let j := decoderInverseIndex a X
  have hj : 1 <= j := by dsimp [j, decoderInverseIndex]; omega
  have hjR : (0 : Real) < (j : Real) := by exact_mod_cast (show 0 < j by omega)
  have hden : 0 < (b : Real) * (j : Real) := mul_pos hbR hjR
  have hlogpos : 0 < Real.log (X : Real) := Real.log_pos (by exact_mod_cast hX)
  have hcoef : 0 <= (a : Real) * Real.log 2 / (b : Real) :=
    le_of_lt (div_pos (mul_pos haR hlog2) hbR)
  have hB : 1 < 2 ^ a := by
    have hpow := Nat.pow_le_pow_right (by norm_num : 1 <= 2) ha
    norm_num at hpow
    omega
  have hXY : X <= (2 ^ a) ^ j := Nat.le_of_lt (Nat.lt_pow_succ_log_self hB X)
  have hcount : ((primeClassPrefix P X).card : Real) <=
      (c : Real) * (2 : Real) ^ (b * j) / ((b : Real) * (j : Real)) := by
    have hmono : ((primeClassPrefix P X).card : Real) <=
        ((primeClassPrefix P ((2 ^ a) ^ j)).card : Real) := by
      exact_mod_cast primeClassPrefix_card_mono P X _ hXY
    exact hmono.trans hN
  have hpower := decoderInverseIndex_power_bound a b X ha (by omega)
  have hlog := decoderInverseIndex_log_bound a X ha (by omega)
  have hquot : Real.log (X : Real) / ((b : Real) * (j : Real)) <=
      (a : Real) * Real.log 2 / (b : Real) := by
    apply _root_.le_of_mul_le_mul_right ?_ hden
    calc
      (Real.log (X : Real) / ((b : Real) * (j : Real))) *
          ((b : Real) * (j : Real)) = Real.log (X : Real) := by field_simp
      _ <= (j : Real) * (a : Real) * Real.log 2 := hlog
      _ = ((a : Real) * Real.log 2 / (b : Real)) *
          ((b : Real) * (j : Real)) := by field_simp
  apply _root_.le_of_mul_le_mul_right ?_ hlogpos
  calc
    ((primeClassPrefix P X).card : Real) * Real.log (X : Real) <=
        ((c : Real) * (2 : Real) ^ (b * j) / ((b : Real) * (j : Real))) *
          Real.log (X : Real) :=
      mul_le_mul_of_nonneg_right hcount (le_of_lt hlogpos)
    _ = ((c : Real) * (2 : Real) ^ (b * j)) *
        (Real.log (X : Real) / ((b : Real) * (j : Real))) := by ring
    _ <= ((c : Real) * (2 : Real) ^ (b * j)) *
        ((a : Real) * Real.log 2 / (b : Real)) :=
      mul_le_mul_of_nonneg_left hquot (mul_nonneg (le_of_lt hcR) (pow_nonneg (by norm_num) _))
    _ <= ((c : Real) * ((2 : Real) ^ b * (X : Real) ^ ((b : Real) / (a : Real)))) *
        ((a : Real) * Real.log 2 / (b : Real)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpower (le_of_lt hcR)) hcoef
    _ = (K * (X : Real) ^ ((b : Real) / (a : Real)) / Real.log (X : Real)) *
        Real.log (X : Real) := by
      dsimp [K]
      field_simp

theorem integerDecoderAdmissible_all_cutoff_inverse_bound
    (P : Set Nat) (h : Rat) (had : integerDecoderAdmissible P h) :
    exists K : Real, And (0 < K)
      (Filter.Eventually (fun X : Nat =>
        ((primeClassPrefix P X).card : Real) <=
          K * (X : Real) ^ (1 / (h : Real)) / Real.log (X : Real)) atTop) := by
  let a : Nat := h.num.toNat
  let b : Nat := h.den
  have hhR : (0 : Real) < (h : Real) := by exact_mod_cast had.1
  have hbR : (0 : Real) < (b : Real) := by exact_mod_cast Rat.den_pos h
  have hrepr : (h : Real) = (a : Real) / (b : Real) :=
    nonnegativeRat_cast_eq_num_div_den h (le_of_lt had.1)
  have haR : (0 : Real) < (a : Real) := by
    have hm := mul_pos hhR hbR
    have heq : (h : Real) * (b : Real) = (a : Real) := by rw [hrepr]; field_simp
    rw [heq] at hm
    exact hm
  have ha : 1 <= a := by exact_mod_cast (show (0 : Real) < (a : Real) from haR)
  have hb : 1 <= b := Nat.succ_le_of_lt (Rat.den_pos h)
  have hreprQ : h = (a : Rat) / (b : Rat) := by
    have hcast : (h : Real) = (((a : Rat) / (b : Rat) : Rat) : Real) := by
      push_cast
      exact hrepr
    exact Rat.cast_injective hcast
  have hinv : 1 / (h : Real) = (b : Real) / (a : Real) := by rw [hrepr]; field_simp
  rw [hreprQ] at had
  rw [hinv]
  exact integerDecoderAdmissible_inverse_count_of_ratio P a b ha hb had

end PrimeFactorOscillations.PrimeClassSampling
