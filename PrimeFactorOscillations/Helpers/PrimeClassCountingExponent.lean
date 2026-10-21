/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderCriticalCapacity

/-!
# Identification of the convergence exponent from the actual counting index

The logarithm uses count plus one, so it is defined uniformly even for
empty prefixes. A positive counting index makes this convention
asymptotically identical to the ordinary logarithmic counting index.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open Filter

noncomputable def primeClassLogCount (P : Set Nat) (X : Nat) : Real :=
  Real.log (((primeClassPrefix P X).card : Real) + 1) / Real.log (X : Real)

theorem primeClassPrefix_card_le_power_mass
    (P : Set Nat) (s : Real) (hs : 0 <= s)
    (hsum : Summable (classPowerWeight P s)) (X : Nat) (hX : 1 <= X) :
    ((primeClassPrefix P X).card : Real) <=
      tsum (classPowerWeight P s) * (X : Real) ^ s := by
  classical
  have hXpos : (0 : Real) < (X : Real) := by exact_mod_cast (show 0 < X by omega)
  have hweighted : ((primeClassPrefix P X).card : Real) * (X : Real) ^ (-s) <=
      tsum (classPowerWeight P s) := by
    apply le_trans _ (primeClassPrefix_powerSum_le P s X hsum)
    have hterm : forall p, Membership.mem (primeClassPrefix P X) p ->
        (X : Real) ^ (-s) <= (p : Real) ^ (-s) := by
      intro p hp
      have hd := Finset.mem_filter.mp hp
      have hi := Finset.mem_Icc.mp hd.1
      exact Real.rpow_le_rpow_of_nonpos
        (by exact_mod_cast (Nat.Prime.pos hd.2.1))
        (by exact_mod_cast hi.2) (by linarith)
    simpa only [Finset.sum_const, nsmul_eq_mul] using
      Finset.sum_le_sum (fun p hp => hterm p hp)
  have hcancel : (X : Real) ^ (-s) * (X : Real) ^ s = 1 := by
    rw [<- Real.rpow_add hXpos]
    simp
  calc
    ((primeClassPrefix P X).card : Real) =
        (((primeClassPrefix P X).card : Real) * (X : Real) ^ (-s)) * (X : Real) ^ s := by
      rw [mul_assoc, hcancel, mul_one]
    _ <= tsum (classPowerWeight P s) * (X : Real) ^ s :=
      mul_le_mul_of_nonneg_right hweighted (Real.rpow_nonneg (Nat.cast_nonneg X) _)

theorem primeClassLogCount_index_le_of_summable
    (P : Set Nat) (alpha s : Real) (hs : 0 <= s)
    (hsum : Summable (classPowerWeight P s))
    (hindex : Tendsto (primeClassLogCount P) atTop (nhds alpha)) :
    alpha <= s := by
  let C : Real := tsum (classPowerWeight P s) + 1
  have hmass : 0 <= tsum (classPowerWeight P s) :=
    tsum_nonneg (classPowerWeight_nonneg P s)
  have hC : 0 < C := by dsimp [C]; linarith
  have hlogTop : Tendsto (fun X : Nat => Real.log (X : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun X : Nat => Real.log C / Real.log (X : Real))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hlogTop
  have hupper : Tendsto (fun X : Nat => s + Real.log C / Real.log (X : Real))
      atTop (nhds s) := by simpa only [add_zero] using tendsto_const_nhds.add hsmall
  apply le_of_tendsto_of_tendsto hindex hupper
  filter_upwards [eventually_ge_atTop 2] with X hX
  have hXpos : (0 : Real) < (X : Real) := by exact_mod_cast (show 0 < X by omega)
  have hXone : (1 : Real) <= (X : Real) := by exact_mod_cast (show 1 <= X by omega)
  have hlogpos : 0 < Real.log (X : Real) := Real.log_pos (by exact_mod_cast hX)
  have hcount := primeClassPrefix_card_le_power_mass P s hs hsum X (by omega)
  have hpow := Real.one_le_rpow hXone hs
  have hcountOne : ((primeClassPrefix P X).card : Real) + 1 <= C * (X : Real) ^ s := by
    dsimp [C]
    nlinarith
  have hlog := Real.log_le_log (by positivity :
    (0 : Real) < ((primeClassPrefix P X).card : Real) + 1) hcountOne
  rw [Real.log_mul (ne_of_gt hC) (ne_of_gt (Real.rpow_pos_of_pos hXpos s)),
    Real.log_rpow hXpos s] at hlog
  unfold primeClassLogCount
  calc
    Real.log (((primeClassPrefix P X).card : Real) + 1) / Real.log (X : Real) <=
        (Real.log C + s * Real.log (X : Real)) / Real.log (X : Real) :=
      div_le_div_of_nonneg_right hlog (le_of_lt hlogpos)
    _ = s + Real.log C / Real.log (X : Real) := by
      field_simp
      ring

theorem primeClassPrefix_eventually_le_rpow_of_counting_index
    (P : Set Nat) (alpha t : Real)
    (hindex : Tendsto (primeClassLogCount P) atTop (nhds alpha)) (ht : alpha < t) :
    Filter.Eventually (fun X : Nat =>
      ((primeClassPrefix P X).card : Real) <= (X : Real) ^ t) atTop := by
  filter_upwards [hindex.eventually_lt_const ht, eventually_ge_atTop 2] with X hratio hX
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
  linarith

theorem classPowerWeight_summable_above_counting_index
    (P : Set Nat) (alpha s : Real) (ha : 0 <= alpha)
    (hindex : Tendsto (primeClassLogCount P) atTop (nhds alpha)) (hs : alpha < s) :
    Summable (classPowerWeight P s) := by
  choose t ht using exists_between hs
  have ht0 : 0 < t := lt_of_le_of_lt ha ht.1
  have hpower := primeClassPrefix_eventually_le_rpow_of_counting_index P alpha t hindex ht.1
  have htendsto : Tendsto (fun j : Nat => (2 : Nat) ^ (j + 1)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : Nat) < 2)).comp
      (tendsto_add_atTop_nat 1)
  have hcount : Filter.Eventually (fun j : Nat =>
      ((primeClassPrefix P (2 ^ (j + 1))).card : Real) <=
        (2 : Real) ^ t * ((2 : Real) ^ t) ^ j) atTop := by
    filter_upwards [htendsto.eventually hpower] with j hj
    have heq : (((2 ^ (j + 1) : Nat) : Real) ^ t) =
        (2 : Real) ^ t * ((2 : Real) ^ t) ^ j := by
      push_cast
      rw [<- Real.rpow_pow_comm (by norm_num : (0 : Real) <= 2), pow_succ]
      ring
    rw [heq] at hj
    exact hj
  have hden : 0 < (2 : Real) ^ s := Real.rpow_pos_of_pos (by norm_num) s
  have hratio : (2 : Real) ^ t * (2 : Real) ^ (-s) < 1 := by
    rw [Real.rpow_neg (by norm_num : (0 : Real) <= 2), <- div_eq_mul_inv]
    exact (div_lt_one hden).mpr (Real.rpow_lt_rpow_of_exponent_lt (by norm_num) ht.2)
  exact classPowerWeight_summable_of_eventual_geometric_prefix_bound P 2 (by norm_num)
    s ((2 : Real) ^ t) ((2 : Real) ^ t) (by linarith) (Real.one_le_rpow (by norm_num) (le_of_lt ht0))
    (Real.rpow_nonneg (by norm_num) _) hratio hcount

theorem primeClassConvergenceExponent_eq_counting_index
    (P : Set Nat) (alpha : Real) (ha : 0 < alpha) (ha1 : alpha < 1)
    (hindex : Tendsto (primeClassLogCount P) atTop (nhds alpha)) :
    primeClassConvergenceExponent P = alpha := by
  choose s0 hs0 using exists_between ha1
  have hs0pos : 0 < s0 := lt_trans ha hs0.1
  have hsum0 := classPowerWeight_summable_above_counting_index P alpha s0 (le_of_lt ha) hindex hs0.1
  have htau0 := primeClassConvergenceExponent_nonneg P s0 hs0pos hsum0
  have hupper : primeClassConvergenceExponent P <= alpha := by
    by_contra hnot
    choose s hs using exists_between (lt_of_not_ge hnot)
    have hsum := classPowerWeight_summable_above_counting_index P alpha s (le_of_lt ha) hindex hs.1
    have hle := primeClassConvergenceExponent_le P s (lt_trans ha hs.1) hsum
    linarith
  have hlower : alpha <= primeClassConvergenceExponent P := by
    by_contra hnot
    choose s hs using exists_between (lt_of_not_ge hnot)
    have hspos : 0 < s := lt_of_le_of_lt htau0 hs.1
    have hsum := classPowerWeight_summable_above_convergenceExponent P s0 s hs0pos hsum0 hs.1
    have hle := primeClassLogCount_index_le_of_summable P alpha s (le_of_lt hspos) hsum hindex
    linarith
  exact le_antisymm hupper hlower

end PrimeFactorOscillations.PrimeClassSampling
