/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderComplexError
import PrimeFactorOscillations.Helpers.PrimeClassDecoderSupplyScale

/-!
# The independent signed model signal survives the actual sampling error

The complete supply loss is compared with the complete power error before
transferring parity. The same eventual threshold works at every tested
half-integer in the growing integer range.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open Filter
open PrimeFactorOscillations.PrimeClassDecoder

theorem eventually_power_error_lt_supply
    (loss : Nat -> Real) (C eta : Real) (heta : 0 < eta)
    (hloss : Tendsto (fun N : Nat => loss N / Real.log (N : Real)) atTop (nhds 0)) :
    Filter.Eventually (fun N : Nat => C * (N : Real) ^ (-eta) < Real.exp (-loss N)) atTop := by
  let epsilon := eta / 2
  have hepsilon : 0 < epsilon := half_pos heta
  have hpow := (tendsto_rpow_neg_atTop hepsilon).comp (tendsto_natCast_atTop_atTop (R := Real))
  have hlimit : Tendsto (fun N : Nat => C * (N : Real) ^ (-epsilon)) atTop (nhds 0) := by
    simpa only [Function.comp_apply, mul_zero] using hpow.const_mul C
  have hsmall := hlimit.eventually (eventually_lt_nhds (by norm_num : (0 : Real) < 1))
  have hlossSmall := hloss.eventually (eventually_lt_nhds hepsilon)
  filter_upwards [hsmall, hlossSmall, eventually_ge_atTop (2 : Nat)] with N hC hL hN
  have hNpos : (0 : Real) < (N : Real) := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : Real) < (N : Real) := by exact_mod_cast (by omega : 1 < N)
  have hlogN : 0 < Real.log (N : Real) := Real.log_pos hN1
  have hmul := mul_le_mul_of_nonneg_right hL.le hlogN.le
  have hcancel : (loss N / Real.log (N : Real)) * Real.log (N : Real) = loss N := by field_simp
  rw [hcancel] at hmul
  have hsupply : (N : Real) ^ (-epsilon) <= Real.exp (-loss N) := by
    rw [Real.rpow_def_of_pos hNpos]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hsplit : (N : Real) ^ (-eta) = (N : Real) ^ (-epsilon) * (N : Real) ^ (-epsilon) := by
    rw [<- Real.rpow_add hNpos]
    congr 1
    dsimp [epsilon]
    ring
  have hCmul := mul_lt_mul_of_pos_right hC (Real.rpow_pos_of_pos hNpos (-epsilon))
  calc
    _ = (C * (N : Real) ^ (-epsilon)) * (N : Real) ^ (-epsilon) := by rw [hsplit]; ring
    _ < (N : Real) ^ (-epsilon) := by simpa only [one_mul] using hCmul
    _ <= _ := hsupply

theorem parity_sign_survives_complex_error
    (k : Nat) (x y : Complex) (supply : Real)
    (hsignal : supply <= (-1 : Real) ^ k * y.re)
    (herror : norm (x - y) < supply) :
    0 < (-1 : Real) ^ k * x.re := by
  have hq : abs ((-1 : Real) ^ k) = 1 := by rw [abs_pow]; norm_num
  have hnorm : abs ((-1 : Real) ^ k * (x.re - y.re)) <= norm (x - y) := by
    rw [abs_mul, hq, one_mul]
    simpa only [Complex.sub_re] using Complex.abs_re_le_norm (x - y)
  have hlow := (neg_le_neg hnorm).trans (neg_abs_le ((-1 : Real) ^ k * (x.re - y.re)))
  nlinarith

theorem truncatedSample_halfInteger_signed_pos
    (P : Set Nat) (sigma h c eta : Real) (hs : 0 < sigma) (hs1 : sigma < 1)
    (hsum : Summable (classPowerWeight P sigma))
    (hh : 0 < h) (hc : 0 < c) (heta : 0 < eta) (hpower : h * sigma < 1)
    (hsampling : eta < 1 - sigma - h * c) (htail : eta < c * (1 / sigma - h)) :
    Filter.Eventually (fun N : Nat => forall n : Nat, n <= decoderRadius h N ->
      0 < (-1 : Real) ^ (primeClassPrefix P (n + 1)).card *
        (truncatedSampleProfile P N (decoderRank c N)
          (((-(n : Real) - 1 / 2 : Real) : Complex))).re) atTop := by
  let C := Real.exp (2 * tsum (classPowerWeight P sigma)) + 2
  have herror := finite_decoding_complex_error P sigma h c eta hs hs1 hsum hh hc heta hsampling htail
  have hsmall := eventually_power_error_lt_supply
    (fun N => decoderSupplyLoss P sigma (decoderRadius h N)) C eta heta
    (decoder_supply_loss_div_log_tendsto_zero P sigma h hs.le hh hpower)
  filter_upwards [herror, hsmall,
    (decoderRadius_real_atTop h hh).eventually (eventually_ge_atTop 1)] with N herrorN hsmallN hR
  intro n hn
  have hRnat : 1 <= decoderRadius h N := by exact_mod_cast hR
  have hnR : (n : Real) <= (decoderRadius h N : Real) := by exact_mod_cast hn
  let w : Complex := (((-(n : Real) - 1 / 2 : Real) : Complex))
  have hw : norm w <= 2 * (decoderRadius h N : Real) := by
    dsimp [w]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by nlinarith [show (0 : Real) <= (n : Real) from Nat.cast_nonneg n] :
        -(n : Real) - 1 / 2 <= 0)]
    linarith
  have hmodel := (classEulerProfile_halfInteger_signed_lower P sigma hs.le hs1.le hsum
    (decoderRadius h N) n hRnat hn).2
  have hsignal : Real.exp (-decoderSupplyLoss P sigma (decoderRadius h N)) <=
      (-1 : Real) ^ (primeClassPrefix P (n + 1)).card * (classEulerProfile P w).re := by
    have hid : -decoderSupplyLoss P sigma (decoderRadius h N) =
        -((6 : Real) ^ sigma * tsum (classPowerWeight P sigma) * (decoderRadius h N : Real) ^ sigma *
          Real.log (12 * (decoderRadius h N : Real))) -
            5 * tsum (classPowerWeight P sigma) * (decoderRadius h N : Real) ^ sigma := by
      unfold decoderSupplyLoss
      ring
    rw [hid]
    exact hmodel
  apply parity_sign_survives_complex_error _ _ _ _ hsignal
  exact lt_of_le_of_lt (herrorN w hw) hsmallN

end PrimeFactorOscillations.PrimeClassSampling
