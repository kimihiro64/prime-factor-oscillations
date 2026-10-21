/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderErrorExponents
import PrimeFactorOscillations.Helpers.PrimeClassDecoderSignedSupply

/-!
# The independent signed supply is subpolynomial in the sample size

The actual floored radius is bounded by the exact binary-log cutoff power.
The full supply loss, including its logarithm and both constants, is o(log N).
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open Filter
open PrimeFactorOscillations.PrimeClassDecoder

noncomputable def decoderSupplyLoss (P : Set Nat) (sigma : Real) (R : Nat) : Real :=
  (6 : Real) ^ sigma * tsum (classPowerWeight P sigma) * (R : Real) ^ sigma *
    Real.log (12 * (R : Real)) + 5 * tsum (classPowerWeight P sigma) * (R : Real) ^ sigma

theorem decoderSupplyLoss_le_majorant
    (P : Set Nat) (sigma h : Real) (hs0 : 0 <= sigma) (N : Nat)
    (hU : (0 : Real) < (binaryCutoff N : Real)) (hR : 1 <= decoderRadius h N) :
    decoderSupplyLoss P sigma (decoderRadius h N) <=
      ((6 : Real) ^ sigma * tsum (classPowerWeight P sigma)) *
        (binaryCutoff N : Real) ^ (h * sigma) *
          (Real.log 12 + h * Real.log (binaryCutoff N : Real)) +
        5 * tsum (classPowerWeight P sigma) * (binaryCutoff N : Real) ^ (h * sigma) := by
  have hS : 0 <= tsum (classPowerWeight P sigma) := tsum_nonneg (classPowerWeight_nonneg P sigma)
  have hRR : (1 : Real) <= (decoderRadius h N : Real) := by exact_mod_cast hR
  have hRpos : (0 : Real) < (decoderRadius h N : Real) := by linarith
  have hfloor : (decoderRadius h N : Real) <= (binaryCutoff N : Real) ^ h :=
    Nat.floor_le (Real.rpow_nonneg hU.le h)
  have hpow := Real.rpow_le_rpow hRpos.le hfloor hs0
  rw [<- Real.rpow_mul hU.le h sigma] at hpow
  have hlog := Real.log_le_log (mul_pos (by norm_num : (0 : Real) < 12) hRpos)
    (mul_le_mul_of_nonneg_left hfloor (by norm_num : (0 : Real) <= 12))
  rw [Real.log_mul (by norm_num : Not ((12 : Real) = 0))
    (ne_of_gt (Real.rpow_pos_of_pos hU h)), Real.log_rpow hU] at hlog
  have hlogR : 0 <= Real.log (12 * (decoderRadius h N : Real)) :=
    Real.log_nonneg (by linarith)
  have hprod := mul_le_mul hpow hlog hlogR (Real.rpow_nonneg hU.le (h * sigma))
  have hfirst := mul_le_mul_of_nonneg_left hprod
    (mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : Real) <= 6) sigma) hS)
  have hsecond := mul_le_mul_of_nonneg_left hpow
    (mul_nonneg (by norm_num : (0 : Real) <= 5) hS)
  unfold decoderSupplyLoss
  nlinarith

theorem decoder_supply_majorant_tendsto_zero
    (P : Set Nat) (sigma h : Real) (hpower : h * sigma < 1) :
    Tendsto (fun N : Nat =>
      (((6 : Real) ^ sigma * tsum (classPowerWeight P sigma)) *
          (binaryCutoff N : Real) ^ (h * sigma) *
            (Real.log 12 + h * Real.log (binaryCutoff N : Real)) +
          5 * tsum (classPowerWeight P sigma) * (binaryCutoff N : Real) ^ (h * sigma)) /
        Real.log (N : Real)) atTop (nhds 0) := by
  let q := 1 - h * sigma
  let C1 := (6 : Real) ^ sigma * tsum (classPowerWeight P sigma)
  let C2 := C1 * Real.log 12 + 5 * tsum (classPowerWeight P sigma)
  have hq : 0 < q := sub_pos.mpr hpower
  have hlog := (isLittleO_log_rpow_atTop hq).tendsto_div_nhds_zero.comp binaryCutoff_real_atTop
  change Tendsto (fun N : Nat => Real.log (binaryCutoff N : Real) /
    (binaryCutoff N : Real) ^ q) atTop (nhds 0) at hlog
  have hinv : Tendsto (fun N : Nat => (1 : Real) / (binaryCutoff N : Real) ^ q)
      atTop (nhds 0) := tendsto_const_nhds.div_atTop
        ((tendsto_rpow_atTop hq).comp binaryCutoff_real_atTop)
  have hlimit := ((hlog.const_mul (C1 * h)).add (hinv.const_mul C2)).mul
    binaryCutoff_div_log_tendsto
  have heq : Filter.EventuallyEq atTop
      (fun N : Nat => (C1 * h * (Real.log (binaryCutoff N : Real) /
          (binaryCutoff N : Real) ^ q) + C2 * (1 / (binaryCutoff N : Real) ^ q)) *
        ((binaryCutoff N : Real) / Real.log (N : Real)))
      (fun N : Nat => (C1 * (binaryCutoff N : Real) ^ (h * sigma) *
          (Real.log 12 + h * Real.log (binaryCutoff N : Real)) +
          5 * tsum (classPowerWeight P sigma) * (binaryCutoff N : Real) ^ (h * sigma)) /
        Real.log (N : Real)) := by
    filter_upwards [binaryCutoff_real_atTop.eventually (eventually_gt_atTop 0)] with N hU
    have hp : (binaryCutoff N : Real) ^ (h * sigma) * (binaryCutoff N : Real) ^ q =
        (binaryCutoff N : Real) := by
      rw [<- Real.rpow_add hU]
      have hexp : h * sigma + q = 1 := by dsimp [q]; ring
      rw [hexp, Real.rpow_one]
    have hrecip : (binaryCutoff N : Real) ^ (h * sigma) =
        (binaryCutoff N : Real) / (binaryCutoff N : Real) ^ q := by
      calc
        _ = ((binaryCutoff N : Real) ^ (h * sigma) * (binaryCutoff N : Real) ^ q) /
            (binaryCutoff N : Real) ^ q := by
          field_simp [ne_of_gt (Real.rpow_pos_of_pos hU q)]
        _ = _ := by rw [hp]
    dsimp [C2]
    rw [hrecip]
    ring
  exact Filter.Tendsto.congr' heq (by simpa only [mul_zero, add_zero, zero_mul] using hlimit)

theorem decoder_supply_loss_div_log_tendsto_zero
    (P : Set Nat) (sigma h : Real) (hs0 : 0 <= sigma) (hh : 0 < h)
    (hpower : h * sigma < 1) :
    Tendsto (fun N : Nat => decoderSupplyLoss P sigma (decoderRadius h N) /
      Real.log (N : Real)) atTop (nhds 0) := by
  have hlogN : Tendsto (fun N : Nat => Real.log (N : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hS : 0 <= tsum (classPowerWeight P sigma) := tsum_nonneg (classPowerWeight_nonneg P sigma)
  have hnonneg : Filter.Eventually (fun N : Nat =>
      0 <= decoderSupplyLoss P sigma (decoderRadius h N) / Real.log (N : Real)) atTop := by
    filter_upwards [(decoderRadius_real_atTop h hh).eventually (eventually_ge_atTop 1),
      hlogN.eventually (eventually_gt_atTop 0)] with N hR hN
    have hlogR : 0 <= Real.log (12 * (decoderRadius h N : Real)) :=
      Real.log_nonneg (by linarith)
    unfold decoderSupplyLoss
    positivity
  have hupper : Filter.Eventually (fun N : Nat =>
      decoderSupplyLoss P sigma (decoderRadius h N) / Real.log (N : Real) <=
      (((6 : Real) ^ sigma * tsum (classPowerWeight P sigma)) *
          (binaryCutoff N : Real) ^ (h * sigma) *
            (Real.log 12 + h * Real.log (binaryCutoff N : Real)) +
          5 * tsum (classPowerWeight P sigma) * (binaryCutoff N : Real) ^ (h * sigma)) /
        Real.log (N : Real)) atTop := by
    filter_upwards [binaryCutoff_real_atTop.eventually (eventually_gt_atTop 0),
      (decoderRadius_real_atTop h hh).eventually (eventually_ge_atTop 1),
      hlogN.eventually (eventually_gt_atTop 0)] with N hU hR hN
    have hRnat : 1 <= decoderRadius h N := by exact_mod_cast hR
    exact div_le_div_of_nonneg_right (decoderSupplyLoss_le_majorant P sigma h hs0 N hU hRnat) hN.le
  exact squeeze_zero' hnonneg hupper (decoder_supply_majorant_tendsto_zero P sigma h hpower)

end PrimeFactorOscillations.PrimeClassSampling
