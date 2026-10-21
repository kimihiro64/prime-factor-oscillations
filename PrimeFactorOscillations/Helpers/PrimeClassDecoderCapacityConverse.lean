/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderCapacity
import PrimeFactorOscillations.Helpers.PrimeClassPowerSummability

/-!
# Exact binary sampling for the converse decoding bound

The growing samples are universal symbolic inputs. Their two integer
logarithms and rational-power radius are exact, so eventual decoding
forces an actual prime-count bound on every geometric shell.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open Filter
open PrimeFactorOscillations.PrimeClassDecoder

def decoderCapacitySample (b j : Nat) : Nat := 2 ^ (2 ^ (b * j))

theorem integerRootCutoff_perfect_power (x b : Nat) (hb : 1 <= b) :
    integerRootCutoff (x ^ b) b = x := by
  refine Nat.le_antisymm ?_
    (integerRootCutoff_maximal (x ^ b) b x hb (le_refl _))
  exact (Nat.pow_le_pow_iff_left (by omega : Not (b = 0))).mp
    (integerRootCutoff_pow_le (x ^ b) b hb)

theorem decoderCapacitySample_binary (b j : Nat) :
    binaryCutoff (decoderCapacitySample b j) = 2 ^ (b * j) := by
  simp only [decoderCapacitySample, binaryCutoff, Nat.log_pow (by norm_num : 1 < 2)]

theorem decoderCapacitySample_radius (a b j : Nat) (hb : 1 <= b) :
    decoderRadius ((a : Real) / (b : Real)) (decoderCapacitySample b j) =
      2 ^ (a * j) := by
  rw [<- rationalDecoderRadius_eq a b _ hb]
  unfold rationalDecoderRadius
  rw [decoderCapacitySample_binary]
  have hpowers : (2 ^ (b * j)) ^ a = (2 ^ (a * j)) ^ b := by
    rw [<- pow_mul, <- pow_mul]
    congr 1
    ring
  rw [hpowers, integerRootCutoff_perfect_power _ b hb]

theorem decoderCapacitySample_atTop (b : Nat) (hb : 1 <= b) :
    Tendsto (decoderCapacitySample b) atTop atTop := by
  have hbj : Tendsto (fun j : Nat => b * j) atTop atTop := by
    apply tendsto_atTop_mono (fun j => ?_) tendsto_id
    change j <= b * j
    calc
      j = 1 * j := by omega
      _ <= b * j := Nat.mul_le_mul_right j hb
  exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : Nat) < 2)).comp
    ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : Nat) < 2)).comp hbj)

theorem decoderRank_le_binaryCutoff (c : Real) (hc : 0 <= c) (N : Nat) :
    (decoderRank c N : Real) <= c * (binaryCutoff N : Real) := by
  unfold decoderRank
  have hU : (0 : Real) <= (binaryCutoff N : Real) := Nat.cast_nonneg _
  have hV : (0 : Real) <= (iteratedBinaryCutoff N : Real) := Nat.cast_nonneg _
  have hfloor := Nat.floor_le (mul_nonneg hc (div_nonneg hU hV))
  apply hfloor.trans
  apply mul_le_mul_of_nonneg_left _ hc
  by_cases hz : iteratedBinaryCutoff N = 0
  case pos => simp only [hz, Nat.cast_zero, div_zero]; exact hU
  case neg =>
    exact div_le_self hU (by exact_mod_cast (show 1 <= iteratedBinaryCutoff N by omega))

theorem integerDecoderAdmissible_geometric_count
    (P : Set Nat) (a b : Nat) (hb : 1 <= b)
    (had : integerDecoderAdmissible P ((a : Rat) / (b : Rat))) :
    exists c : Rat, And (0 < c)
      (Filter.Eventually (fun j : Nat =>
        ((primeClassPrefix P ((2 ^ a) ^ (j + 1))).card : Real) <=
          ((c : Real) * (2 : Real) ^ b) * ((2 : Real) ^ b) ^ j) atTop) := by
  choose c hc using integerDecoderAdmissible_degree_budget P _ had
  apply Exists.intro c
  apply And.intro hc.1
  have hsample := ((decoderCapacitySample_atTop b hb).comp
    (tendsto_add_atTop_nat 1)).eventually hc.2
  filter_upwards [hsample] with j hj
  have hratio : (((a : Rat) / (b : Rat) : Rat) : Real) =
      (a : Real) / (b : Real) := by push_cast; rfl
  simp only [Function.comp_apply] at hj
  rw [hratio, decoderCapacitySample_radius a b (j + 1) hb] at hj
  have hcard := primeClassPrefix_card_mono P (2 ^ (a * (j + 1)))
    (2 ^ (a * (j + 1)) + 1) (by omega)
  have hcount : ((primeClassPrefix P (2 ^ (a * (j + 1)))).card : Real) <=
      (decoderRank (c : Real) (decoderCapacitySample b (j + 1)) : Real) := by
    exact_mod_cast hcard.trans hj
  have hbound := decoderRank_le_binaryCutoff (c : Real)
    (by exact_mod_cast (le_of_lt hc.1)) (decoderCapacitySample b (j + 1))
  rw [decoderCapacitySample_binary] at hbound
  have htotal := hcount.trans hbound
  rw [pow_mul] at htotal
  convert htotal using 1
  push_cast
  rw [pow_mul, pow_succ]
  ring

theorem integerDecoderAdmissible_summable_of_ratio
    (P : Set Nat) (a b : Nat) (ha : 1 <= a) (hb : 1 <= b)
    (had : integerDecoderAdmissible P ((a : Rat) / (b : Rat)))
    (s : Real) (hs : (b : Real) / (a : Real) < s) :
    Summable (classPowerWeight P s) := by
  have haR : (0 : Real) < (a : Real) := by exact_mod_cast (show 0 < a by omega)
  have hbR : (0 : Real) < (b : Real) := by exact_mod_cast (show 0 < b by omega)
  have hs0 : 0 < s := lt_trans (div_pos hbR haR) hs
  have has : (b : Real) < (a : Real) * s := by
    have hm := mul_lt_mul_of_pos_left hs haR
    have heq : (a : Real) * ((b : Real) / (a : Real)) = (b : Real) := by
      field_simp
    rw [heq] at hm
    exact hm
  have hB : 1 < 2 ^ a := by
    have hpow := Nat.pow_le_pow_right (by norm_num : 1 <= 2) ha
    norm_num at hpow
    omega
  have hA : (1 : Real) <= (2 : Real) ^ b := by
    have hp : (0 : Nat) < 2 ^ b := Nat.pow_pos (by norm_num)
    exact_mod_cast hp
  have hden : 0 < (((2 ^ a : Nat) : Real) ^ s) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (Nat.pow_pos (n := a) (by norm_num : 0 < 2))) s
  have hdeneq : (((2 ^ a : Nat) : Real) ^ s) =
      (2 : Real) ^ ((a : Real) * s) := by
    rw [Nat.cast_pow]
    norm_num only [Nat.cast_ofNat]
    rw [<- Real.rpow_natCast, <- Real.rpow_mul (by norm_num : (0 : Real) <= 2)]
  have hsmall : (2 : Real) ^ b < (((2 ^ a : Nat) : Real) ^ s) := by
    rw [hdeneq, <- Real.rpow_natCast]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) has
  have hratio : (2 : Real) ^ b * ((2 ^ a : Nat) : Real) ^ (-s) < 1 := by
    rw [Real.rpow_neg (Nat.cast_nonneg _), <- div_eq_mul_inv]
    exact (div_lt_one hden).mpr hsmall
  choose c hc using integerDecoderAdmissible_geometric_count P a b hb had
  exact classPowerWeight_summable_of_eventual_geometric_prefix_bound P (2 ^ a) hB
    s ((2 : Real) ^ b) ((c : Real) * (2 : Real) ^ b) (le_of_lt hs0) hA
    (mul_nonneg (by exact_mod_cast (le_of_lt hc.1)) (by positivity)) hratio hc.2

theorem integerDecoderAdmissible_summable_above_inverse
    (P : Set Nat) (h : Rat) (had : integerDecoderAdmissible P h)
    (s : Real) (hs : 1 / (h : Real) < s) :
    Summable (classPowerWeight P s) := by
  let a : Nat := h.num.toNat
  let b : Nat := h.den
  have hhR : (0 : Real) < (h : Real) := by exact_mod_cast had.1
  have hbR : (0 : Real) < (b : Real) := by
    exact_mod_cast Rat.den_pos h
  have hrepr : (h : Real) = (a : Real) / (b : Real) :=
    nonnegativeRat_cast_eq_num_div_den h (le_of_lt had.1)
  have haR : (0 : Real) < (a : Real) := by
    have hm := mul_pos hhR hbR
    have heq : (h : Real) * (b : Real) = (a : Real) := by
      rw [hrepr]
      field_simp
    rw [heq] at hm
    exact hm
  have ha : 1 <= a := by exact_mod_cast (show (0 : Real) < (a : Real) from haR)
  have hb : 1 <= b := Nat.succ_le_of_lt (Rat.den_pos h)
  have hreprQ : h = (a : Rat) / (b : Rat) := by
    have hcast : (h : Real) = (((a : Rat) / (b : Rat) : Rat) : Real) := by
      push_cast
      exact hrepr
    exact Rat.cast_injective hcast
  have hinv : 1 / (h : Real) = (b : Real) / (a : Real) := by
    rw [hrepr]
    field_simp
  rw [hinv] at hs
  rw [hreprQ] at had
  exact integerDecoderAdmissible_summable_of_ratio P a b ha hb had s hs

end PrimeFactorOscillations.PrimeClassSampling
