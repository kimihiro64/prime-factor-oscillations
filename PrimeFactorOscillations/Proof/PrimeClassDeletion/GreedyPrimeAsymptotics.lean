/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThetaErrorIntegrability
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyPrimeRegulator

/-!
# Canonical theta input for the actual greedy prime regulator

The all-prime log sum agrees with the existing Chebyshev function at
every natural and real cutoff. The fixed-constant unconditional PNT
provider therefore controls the actual clock errors with no new premise.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open Filter
open PrimeFactorUnimodality
open PrimeFactorOscillations.PrimeClassSampling

theorem primeClassTheta_univ_eq_chebyshev (X : Nat) :
    primeClassTheta Set.univ X = Chebyshev.theta (X : Real) := by
  classical
  have heq : primeClassPrefix Set.univ X = (Finset.Ioc 0 X).filter Nat.Prime := by
    apply Finset.ext
    intro p
    simp only [primeClassPrefix, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc,
      Set.mem_univ, and_true]
    constructor
    case mp =>
      intro hp
      exact And.intro (And.intro hp.2.pos hp.1.2) hp.2
    case mpr =>
      intro hp
      exact And.intro (And.intro hp.2.two_le hp.1.2) hp.2
  unfold primeClassTheta
  rw [heq]
  simp only [Chebyshev.theta, Nat.floor_natCast]

theorem primeClassThetaReal_univ_eq_chebyshev (x : Real) :
    primeClassThetaReal Set.univ x = Chebyshev.theta x := by
  unfold primeClassThetaReal
  rw [primeClassTheta_univ_eq_chebyshev]
  simp only [Chebyshev.theta, Nat.floor_natCast]

theorem primeClockError_bound_of_theta_bound
    (C : Real)
    (hC : forall x : Real, 2 <= x ->
      abs (Chebyshev.theta x - x) <= C * x / Real.log x ^ 2)
    (i : Nat) :
    primeClockError i <= C * (primeAt i : Real) / Real.log (primeAt i : Real) ^ 2 := by
  rw [primeClockError_eq_theta, primeClassTheta_univ_eq_chebyshev]
  exact (le_abs_self _).trans (hC _ (by exact_mod_cast (prime_primeAt i).two_le))

theorem exists_primeClockError_bound_div_log_sq :
    exists C : Real, And (0 <= C) (forall i : Nat,
      primeClockError i <= C * (primeAt i : Real) / Real.log (primeAt i : Real) ^ 2) := by
  choose C hC using PrimeFactorOscillations.exists_thetaError_bound_div_log_sq
  exact Exists.intro C (And.intro hC.1 (primeClockError_bound_of_theta_bound C hC.2))

theorem theta_sqrt_upper_of_uniform_error
    (C : Real) (hC0 : 0 <= C)
    (hC : forall x : Real, 2 <= x ->
      abs (Chebyshev.theta x - x) <= C * x / Real.log x ^ 2)
    (X : Nat) (hX : 4 <= X) :
    Chebyshev.theta (Real.sqrt (X : Real)) <=
      (1 + C / Real.log 2 ^ 2) * Real.sqrt (X : Real) := by
  have hx : (4 : Real) <= (X : Real) := by exact_mod_cast hX
  have hs0 := Real.sqrt_nonneg (X : Real)
  have hsq := Real.sq_sqrt (Nat.cast_nonneg X)
  have hs2 : (2 : Real) <= Real.sqrt (X : Real) := by nlinarith only [hx, hs0, hsq]
  have hl2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hls := Real.log_le_log (by norm_num : (0 : Real) < 2) hs2
  have hden : Real.log 2 ^ 2 <= Real.log (Real.sqrt (X : Real)) ^ 2 := by
    gcongr
  have hratio :
      C * Real.sqrt (X : Real) / Real.log (Real.sqrt (X : Real)) ^ 2 <=
        C * Real.sqrt (X : Real) / Real.log 2 ^ 2 :=
    div_le_div_of_nonneg_left (mul_nonneg hC0 hs0) (sq_pos_of_pos hl2) hden
  have he := (le_abs_self _).trans (hC (Real.sqrt (X : Real)) hs2)
  calc
    Chebyshev.theta (Real.sqrt (X : Real)) <=
        Real.sqrt (X : Real) +
          C * Real.sqrt (X : Real) / Real.log (Real.sqrt (X : Real)) ^ 2 := by
      linarith only [he]
    _ <= Real.sqrt (X : Real) + C * Real.sqrt (X : Real) / Real.log 2 ^ 2 := by
      linarith only [hratio]
    _ = _ := by ring

theorem greedyPrimeRegulator_quantitative_bound
    (C : Real) (hC0 : 0 <= C)
    (hC : forall x : Real, 2 <= x ->
      abs (Chebyshev.theta x - x) <= C * x / Real.log x ^ 2)
    (X : Nat) (hX : 4 <= X) :
    greedyPrimeRegulator X <=
      (1 + C / Real.log 2 ^ 2) * Real.sqrt (X : Real) +
        4 * C * (X : Real) / Real.log (X : Real) ^ 2 := by
  have hx : (4 : Real) <= (X : Real) := by exact_mod_cast hX
  have hx0 : (0 : Real) < (X : Real) := by linarith only [hx]
  have hlx : 0 < Real.log (X : Real) := Real.log_pos (by linarith only [hx])
  have hl2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hs0 := Real.sqrt_nonneg (X : Real)
  have hsq := Real.sq_sqrt (Nat.cast_nonneg X)
  have hs2 : (2 : Real) <= Real.sqrt (X : Real) := by nlinarith only [hx, hs0, hsq]
  have hB : 0 <= (1 + C / Real.log 2 ^ 2) * Real.sqrt (X : Real) := by positivity
  have hlarge : 0 <= 4 * C * (X : Real) / Real.log (X : Real) ^ 2 := by positivity
  unfold greedyPrimeRegulator
  apply clockRecord_le_of_bounds
  case hc => exact add_nonneg hB hlarge
  case he =>
    intro i hi
    have hpX : (primeAt i : Real) <= (X : Real) :=
      Nat.cast_le.mpr ((primeAt_le_cutoff_iff i X).mpr hi)
    have hp0 : (0 : Real) <= (primeAt i : Real) := Nat.cast_nonneg _
    by_cases hsmall : (primeAt i : Real) <= Real.sqrt (X : Real)
    case pos =>
      rw [primeClockError_eq_theta, primeClassTheta_univ_eq_chebyshev]
      have hm := Chebyshev.theta_mono hsmall
      have ht := theta_sqrt_upper_of_uniform_error C hC0 hC X hX
      linarith only [hm, ht, hp0, hlarge]
    case neg =>
      have hroot : Real.sqrt (X : Real) <= (primeAt i : Real) := (lt_of_not_ge hsmall).le
      have hlp : 0 < Real.log (primeAt i : Real) := by
        apply Real.log_pos
        exact_mod_cast (one_lt_primeAt i)
      have hlog := Real.log_le_log (by linarith only [hs2]) hroot
      have hrootlog : Real.log (Real.sqrt (X : Real)) = Real.log (X : Real) / 2 := by
        rw [Real.sqrt_eq_rpow, Real.log_rpow hx0]
        ring
      rw [hrootlog] at hlog
      have hden : (Real.log (X : Real) / 2) ^ 2 <= Real.log (primeAt i : Real) ^ 2 := by
        gcongr
      have hinv := one_div_le_one_div_of_le
        (sq_pos_of_pos (by linarith only [hlx] : 0 < Real.log (X : Real) / 2)) hden
      have hscale := mul_le_mul_of_nonneg_left hinv (mul_nonneg hC0 hp0)
      have hfirst :
          C * (primeAt i : Real) / Real.log (primeAt i : Real) ^ 2 <=
            4 * C * (primeAt i : Real) / Real.log (X : Real) ^ 2 := by
        calc
          _ = C * (primeAt i : Real) * (1 / Real.log (primeAt i : Real) ^ 2) := by ring
          _ <= C * (primeAt i : Real) * (1 / (Real.log (X : Real) / 2) ^ 2) := hscale
          _ = _ := by field_simp [hlx.ne']; ring
      have hnum := mul_le_mul_of_nonneg_left hpX hC0
      have hnum4 := mul_le_mul_of_nonneg_left hnum (by norm_num : (0 : Real) <= 4)
      have hsecond :
          4 * C * (primeAt i : Real) / Real.log (X : Real) ^ 2 <=
            4 * C * (X : Real) / Real.log (X : Real) ^ 2 := by
        have hd := div_le_div_of_nonneg_right hnum4 (sq_nonneg (Real.log (X : Real)))
        simpa only [mul_assoc] using hd
      have he := primeClockError_bound_of_theta_bound C hC i
      exact (he.trans (hfirst.trans hsecond)).trans (by linarith only [hB])

theorem exists_greedyDeletedPrimeClass_quantitative_bound :
    exists C : Real, And (0 <= C) (forall X : Nat, 4 <= X ->
      primeClassTheta greedyDeletedPrimeClass X <=
        (1 + C / Real.log 2 ^ 2) * Real.sqrt (X : Real) +
          4 * C * (X : Real) / Real.log (X : Real) ^ 2 + Real.log (X : Real)) := by
  choose C hC using PrimeFactorOscillations.exists_thetaError_bound_div_log_sq
  apply Exists.intro C
  apply And.intro hC.1
  intro X hX
  have hreg := greedyPrimeRegulator_quantitative_bound C hC.1 hC.2 X hX
  have hmass := (greedyDeletedPrimeClass_record_bounds X (by omega)).2
  linarith only [hreg, hmass]

theorem greedyDeletedPrimeClass_mass_div_tendsto_zero :
    Tendsto (fun X : Nat => primeClassTheta greedyDeletedPrimeClass X / (X : Real))
      atTop (nhds 0) := by
  choose C hC using exists_greedyDeletedPrimeClass_quantitative_bound
  let B : Real := 1 + C / Real.log 2 ^ 2
  have hn : Tendsto (fun X : Nat => (X : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hs : Tendsto (fun X : Nat => Real.sqrt (X : Real)) atTop atTop := by
    simpa only [Function.comp_def, Real.sqrt_eq_rpow] using
      (tendsto_rpow_atTop (by norm_num : (0 : Real) < 1 / 2)).comp hn
  have hl : Tendsto (fun X : Nat => Real.log (X : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp hn
  have hl2 : Tendsto (fun X : Nat => Real.log (X : Real) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by decide : Not ((2 : Nat) = 0))).comp hl
  have hu : Tendsto (fun X : Nat =>
      (B + 2) / Real.sqrt (X : Real) + (4 * C) / Real.log (X : Real) ^ 2)
      atTop (nhds 0) := by
    simpa only [zero_add] using
      (hs.const_div_atTop (B + 2)).add (hl2.const_div_atTop (4 * C))
  apply squeeze_zero_norm' (a := fun X : Nat =>
    (B + 2) / Real.sqrt (X : Real) + (4 * C) / Real.log (X : Real) ^ 2) ?_ hu
  filter_upwards [eventually_ge_atTop (4 : Nat)] with X hX
  have hx : (4 : Real) <= (X : Real) := by exact_mod_cast hX
  have hx0 : (0 : Real) < (X : Real) := by linarith only [hx]
  have hlx : 0 < Real.log (X : Real) := Real.log_pos (by linarith only [hx])
  have hspos : 0 < Real.sqrt (X : Real) := Real.sqrt_pos.mpr hx0
  have hsq := Real.sq_sqrt hx0.le
  have hR0 : 0 <= greedyPrimeRegulator X := clockRecord_nonneg _ _
  have hM0 : 0 <= primeClassTheta greedyDeletedPrimeClass X :=
    hR0.trans (greedyDeletedPrimeClass_record_bounds X (by omega)).1
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hM0 hx0.le)]
  have hlog : Real.log (X : Real) <= 2 * Real.sqrt (X : Real) := by
    have h := Real.log_le_rpow_div hx0.le (by norm_num : (0 : Real) < 1 / 2)
    rw [<- Real.sqrt_eq_rpow] at h
    linarith only [h]
  have hb : primeClassTheta greedyDeletedPrimeClass X <=
      (B + 2) * Real.sqrt (X : Real) +
        4 * C * (X : Real) / Real.log (X : Real) ^ 2 := by
    have hm := hC.2 X hX
    dsimp only [B]
    nlinarith only [hm, hlog]
  have hroot : Real.sqrt (X : Real) / (X : Real) = 1 / Real.sqrt (X : Real) := by
    field_simp [hx0.ne', hspos.ne']
    nlinarith only [hsq]
  calc
    primeClassTheta greedyDeletedPrimeClass X / (X : Real) <=
        ((B + 2) * Real.sqrt (X : Real) +
          4 * C * (X : Real) / Real.log (X : Real) ^ 2) / (X : Real) :=
      div_le_div_of_nonneg_right hb hx0.le
    _ = (B + 2) * (Real.sqrt (X : Real) / (X : Real)) +
        (4 * C) / Real.log (X : Real) ^ 2 := by
      field_simp [hx0.ne', hlx.ne']
    _ = _ := by rw [hroot]; ring

theorem primeClassTheta_univ_div_tendsto_one :
    Tendsto (fun X : Nat => primeClassTheta Set.univ X / (X : Real))
      atTop (nhds 1) := by
  choose C hC using PrimeFactorOscillations.exists_thetaError_bound_div_log_sq
  have hn : Tendsto (fun X : Nat => (X : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun X : Nat => Real.log (X : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp hn
  have hl2 : Tendsto (fun X : Nat => Real.log (X : Real) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by decide : Not ((2 : Nat) = 0))).comp hl
  have he : Tendsto (fun X : Nat =>
      (primeClassTheta Set.univ X - (X : Real)) / (X : Real)) atTop (nhds 0) := by
    apply squeeze_zero_norm' (a := fun X : Nat => C / Real.log (X : Real) ^ 2)
      ?_ (hl2.const_div_atTop C)
    filter_upwards [eventually_ge_atTop (2 : Nat)] with X hX
    have hx : (2 : Real) <= (X : Real) := by exact_mod_cast hX
    have hx0 : (0 : Real) < (X : Real) := by linarith only [hx]
    have hlx : 0 < Real.log (X : Real) := Real.log_pos (by linarith only [hx])
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hx0, primeClassTheta_univ_eq_chebyshev]
    calc
      abs (Chebyshev.theta (X : Real) - (X : Real)) / (X : Real) <=
          (C * (X : Real) / Real.log (X : Real) ^ 2) / (X : Real) :=
        div_le_div_of_nonneg_right (hC.2 (X : Real) hx) hx0.le
      _ = _ := by field_simp [hx0.ne', hlx.ne']
  have ha : Tendsto (fun X : Nat =>
      (primeClassTheta Set.univ X - (X : Real)) / (X : Real) + 1)
      atTop (nhds 1) := by
    simpa only [zero_add] using he.add_const (1 : Real)
  apply ha.congr'
  filter_upwards [eventually_ge_atTop (2 : Nat)] with X hX
  have hx0 : Not ((X : Real) = 0) := by
    have hx : (2 : Real) <= (X : Real) := by exact_mod_cast hX
    linarith only [hx]
  simp only [sub_div, div_self hx0, sub_add_cancel]

theorem greedyPrimeClass_theta_div_tendsto_one :
    Tendsto (fun X : Nat => primeClassTheta greedyPrimeClass X / (X : Real))
      atTop (nhds 1) := by
  have h : Tendsto (fun X : Nat =>
      primeClassTheta Set.univ X / (X : Real) -
        primeClassTheta greedyDeletedPrimeClass X / (X : Real)) atTop (nhds 1) := by
    simpa only [sub_zero] using
      primeClassTheta_univ_div_tendsto_one.sub greedyDeletedPrimeClass_mass_div_tendsto_zero
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro X
  have hpart := greedyPrimeClass_theta_partition X
  have heq : primeClassTheta Set.univ X - primeClassTheta greedyDeletedPrimeClass X =
      primeClassTheta greedyPrimeClass X := by linarith only [hpart]
  dsimp only
  rw [<- sub_div, heq]

end PrimeFactorOscillations.PrimeClassDeletion
