/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldPrimePairHeight

/-!
# A uniform conductor core throughout quasipolynomial height ranges

For each fixed degree m, the height condition log(n+h) <= 2 log(Q)^m
admits a core polynomial in log(Q). Its logarithm costs only
(64m+577) log(log(Q)), and the core fits below Q eventually.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldQuasipolynomialHeight

open FiniteFieldPrimePairHeight
open FiniteFieldIntegerNaturalAmplitude
open FiniteFieldIntegerWeightGrowth
open Filter

def quasiCore (m Q : Nat) : Nat :=
  Nat.ceil ((10 * (Real.log (Q : Real)) ^ m) ^ 64)

def degreeCost (m : Nat) : Real := 64 * (m : Real) + 577

theorem degree_cost_pos (m : Nat) : 0 < degreeCost m := by
  unfold degreeCost
  positivity

theorem base_le_positive_power (L : Real) (m : Nat) (hL : 1 <= L) (hm : 1 <= m) :
    L <= L ^ m := by
  have hp : (1 : Real) <= L ^ (m - 1) := by
    calc
      _ = (1 : Real) ^ (m - 1) := by simp
      _ <= _ := by gcongr
  calc
    _ = 1 * L := by ring
    _ <= L ^ (m - 1) * L :=
      mul_le_mul_of_nonneg_right hp (by linarith only [hL])
    _ = L ^ m := by rw [<- pow_succ, Nat.sub_add_cancel hm]

theorem natural_core_le_quasi_core (m Q : Nat) (hm : 1 <= m)
    (hlog : 1 <= Real.log (Q : Real)) : naturalCore Q <= quasiCore m Q := by
  have hb := base_le_positive_power (Real.log (Q : Real)) m hlog hm
  have hp : (10 * Real.log (Q : Real)) ^ 64 <=
      (10 * (Real.log (Q : Real)) ^ m) ^ 64 := by gcongr
  apply Nat.ceil_le.mpr
  exact hp.trans (Nat.le_ceil _)

theorem quasi_core_supply (m Q : Nat) (hm : 1 <= m)
    (hlog : 1 <= Real.log (Q : Real)) :
    And (12 <= quasiCore m Q) (Real.log (Q : Real) <= ((quasiCore m Q : Nat) : Real)) := by
  have hn := natural_core_log_supply Q hlog
  have hle := natural_core_le_quasi_core m Q hm hlog
  exact And.intro (hn.1.trans hle) (hn.2.trans (Nat.cast_le.mpr hle))

theorem quasi_core_covers_pair_level (m h Q n : Nat) (hm : 1 <= m)
    (hh : 0 < h) (hn : 0 < n) (hhQ : h < Q)
    (hlog : 1 <= Real.log (Q : Real))
    (hheight : Real.log ((n + h : Nat) : Real) <= 2 * (Real.log (Q : Real)) ^ m) :
    (pairHeightLevel h n) ^ 64 <= ((quasiCore m Q + 1 : Nat) : Real) := by
  have hQpos : 0 < (Q : Real) := by exact_mod_cast (show 0 < Q by omega)
  have hhpos : 0 < (h : Real) := by exact_mod_cast hh
  have hnpos : 0 < ((n + h : Nat) : Real) := by exact_mod_cast (show 0 < n + h by omega)
  have hlogh := Real.log_le_log hhpos (show (h : Real) <= (Q : Real) by exact_mod_cast hhQ.le)
  have hp := base_le_positive_power (Real.log (Q : Real)) m hlog hm
  have hp1 : (1 : Real) <= (Real.log (Q : Real)) ^ m := hlog.trans hp
  have hfour := Real.log_le_sub_one_of_pos (show (0 : Real) < 4 by norm_num)
  have hid : pairHeightLevel h n =
      3 + Real.log 4 + Real.log (h : Real) + Real.log ((n + h : Nat) : Real) := by
    unfold pairHeightLevel
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    rw [Real.log_mul (mul_ne_zero (by norm_num) (ne_of_gt hhpos)) (ne_of_gt hnpos),
      Real.log_mul (by norm_num) (ne_of_gt hhpos)]
    ring
  have hupper : pairHeightLevel h n <= 10 * (Real.log (Q : Real)) ^ m := by
    rw [hid]
    linarith only [hlogh, hp, hp1, hfour, hheight]
  have hlo := (pair_height_level_pos h n hh hn).le
  have hpow : (pairHeightLevel h n) ^ 64 <=
      (10 * (Real.log (Q : Real)) ^ m) ^ 64 := by gcongr
  calc
    _ <= (10 * (Real.log (Q : Real)) ^ m) ^ 64 := hpow
    _ <= ((quasiCore m Q : Nat) : Real) := Nat.le_ceil _
    _ <= _ := by simp only [Nat.cast_add, Nat.cast_one]; linarith

theorem quasi_core_log_bound (m Q : Nat) (hm : 1 <= m)
    (hlog : 1 <= Real.log (Q : Real))
    (hloglog : 1 <= Real.log (Real.log (Q : Real))) :
    Real.log ((quasiCore m Q : Nat) : Real) <=
      degreeCost m * Real.log (Real.log (Q : Real)) := by
  have hK := (quasi_core_supply m Q hm hlog).1
  have hKR : 0 < ((quasiCore m Q : Nat) : Real) := by exact_mod_cast (show 0 < quasiCore m Q by omega)
  have hL : 0 < Real.log (Q : Real) := by linarith only [hlog]
  have hB : 0 < 10 * (Real.log (Q : Real)) ^ m := by positivity
  have hp := base_le_positive_power (Real.log (Q : Real)) m hlog hm
  have hX1 : (1 : Real) <= (10 * (Real.log (Q : Real)) ^ m) ^ 64 := by
    calc
      _ <= (10 : Real) ^ 64 := by norm_num
      _ <= _ := by gcongr; linarith only [hlog, hp]
  have hceil := Nat.ceil_lt_add_one (pow_nonneg hB.le 64)
  have hKupper : ((quasiCore m Q : Nat) : Real) <=
      2 * (10 * (Real.log (Q : Real)) ^ m) ^ 64 := by
    dsimp [quasiCore]
    linarith only [hceil, hX1]
  have ht := Real.log_le_log hKR hKupper
  rw [Real.log_mul (by norm_num) (pow_ne_zero 64 (ne_of_gt hB)), Real.log_pow,
    Real.log_mul (by norm_num) (pow_ne_zero m (ne_of_gt hL)), Real.log_pow] at ht
  have htwo := Real.log_le_sub_one_of_pos (show (0 : Real) < 2 by norm_num)
  have hten := Real.log_le_sub_one_of_pos (show (0 : Real) < 10 by norm_num)
  have hreserve := mul_nonneg (show (0 : Real) <= 577 by norm_num)
    (sub_nonneg.mpr hloglog)
  norm_num at ht
  unfold degreeCost
  nlinarith only [ht, htwo, hten, hreserve]

theorem eventually_quasi_core_fits (m : Nat) :
    exists Q0 : Nat, forall Q : Nat, Q0 <= Q ->
      And (6 <= Q) (And (1 <= Real.log (Q : Real))
        (And (1 <= Real.log (Real.log (Q : Real))) (quasiCore m Q <= Q))) := by
  have hNat : Tendsto (fun Q : Nat => (Q : Real)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlim : Tendsto
      (fun Q : Nat => (10 * (Real.log (Q : Real)) ^ m) ^ 64 / (Q : Real))
      atTop (nhds 0) := by
    have ht := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 (m * 64) (by norm_num)).comp hNat
    have hc := ht.const_mul ((10 : Real) ^ 64)
    simpa only [Function.comp_def, one_mul, add_zero, mul_zero, mul_pow,
      pow_mul, mul_div_assoc] using hc
  have hsmall : Filter.Eventually
      (fun Q : Nat => (10 * (Real.log (Q : Real)) ^ m) ^ 64 / (Q : Real) < 1) atTop :=
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

end PrimeFactorOscillations.FiniteFieldQuasipolynomialHeight
