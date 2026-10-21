/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassCountingExponent

/-!
# Actual lower counts below a positive logarithmic counting index
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open Filter
open PrimeFactorOscillations.PrimeClassDecoder

theorem primeClassPrefix_eventually_rpow_le_countOne
    (P : Set Nat) (alpha t : Real)
    (hindex : Tendsto (primeClassLogCount P) atTop (nhds alpha)) (ht : t < alpha) :
    Filter.Eventually (fun X : Nat =>
      (X : Real) ^ t <= ((primeClassPrefix P X).card : Real) + 1) atTop := by
  filter_upwards [hindex.eventually_const_lt ht, eventually_ge_atTop 2] with X hratio hX
  have hXpos : (0 : Real) < (X : Real) := by exact_mod_cast (show 0 < X by omega)
  have hlogpos : 0 < Real.log (X : Real) := Real.log_pos (by exact_mod_cast hX)
  unfold primeClassLogCount at hratio
  have hm := mul_lt_mul_of_pos_right hratio hlogpos
  have hcancel : (Real.log (((primeClassPrefix P X).card : Real) + 1) /
      Real.log (X : Real)) * Real.log (X : Real) =
      Real.log (((primeClassPrefix P X).card : Real) + 1) := by field_simp
  rw [hcancel] at hm
  have hExp := Real.exp_lt_exp.mpr hm
  rw [Real.exp_log (by positivity :
    (0 : Real) < ((primeClassPrefix P X).card : Real) + 1)] at hExp
  rw [Real.rpow_def_of_pos hXpos]
  have heq : t * Real.log (X : Real) = Real.log (X : Real) * t := mul_comm _ _
  rw [heq] at hExp
  exact le_of_lt hExp

theorem primeClassPrefix_card_real_atTop_of_counting_index
    (P : Set Nat) (alpha : Real) (ha : 0 < alpha)
    (hindex : Tendsto (primeClassLogCount P) atTop (nhds alpha)) :
    Tendsto (fun X : Nat => ((primeClassPrefix P X).card : Real)) atTop atTop := by
  have ht : 0 < alpha / 2 := by linarith
  have hlow := primeClassPrefix_eventually_rpow_le_countOne P alpha (alpha / 2) hindex (by linarith)
  have hpow : Tendsto (fun X : Nat => (X : Real) ^ (alpha / 2)) atTop atTop :=
    (tendsto_rpow_atTop ht).comp tendsto_natCast_atTop_atTop
  apply tendsto_atTop.2
  intro C
  filter_upwards [hlow, hpow.eventually (eventually_ge_atTop (C + 1))] with X hX hXC
  linarith

theorem decoderRadius_succ_atTop (h : Real) (hh : 0 < h) :
    Tendsto (fun N : Nat => decoderRadius h N + 1) atTop atTop := by
  apply tendsto_atTop.2
  intro K
  filter_upwards [(decoderRadius_real_atTop h hh).eventually
    (eventually_ge_atTop (K : Real))] with N hN
  have hKN : K <= decoderRadius h N := by exact_mod_cast hN
  omega

end PrimeFactorOscillations.PrimeClassSampling
