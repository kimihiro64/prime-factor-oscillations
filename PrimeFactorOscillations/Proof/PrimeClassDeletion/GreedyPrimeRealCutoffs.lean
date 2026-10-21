/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeCountingLocation
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyPrimeCountAsymptotics

/-!
# Actual greedy prime classes at real cutoffs

The cap is imposed only at real cutoffs at least two. Small natural
cutoffs have empty prime support. Counts are literal filtered prime counts,
and the regulator is characterized by its least upper bound property.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open Filter
open PrimeFactorUnimodality
open PrimeFactorOscillations.PrimeClassSampling

noncomputable def greedyPrimeRegulatorReal (x : Real) : Real :=
  greedyPrimeRegulator (Nat.floor x)

theorem primeClass_realCap_implies_natCap
    (P : Set Nat) (hP : forall x : Real, 2 <= x -> primeClassThetaReal P x <= x)
    (X : Nat) : primeClassTheta P X <= (X : Real) := by
  classical
  by_cases hX : 2 <= X
  case pos =>
    have hx : (2 : Real) <= (X : Real) := by exact_mod_cast hX
    simpa only [primeClassThetaReal, Nat.floor_natCast] using hP (X : Real) hx
  case neg =>
    have hempty : Finset.Icc 2 X = Finset.empty :=
      Finset.Icc_eq_empty_of_lt (by omega)
    simp only [primeClassTheta, primeClassPrefix, hempty]
    exact Nat.cast_nonneg X

theorem greedyDeletedPrimeClass_real_record_bounds (x : Real) (hx : 2 <= x) :
    greedyPrimeRegulatorReal x <= primeClassThetaReal greedyDeletedPrimeClass x /\
      primeClassThetaReal greedyDeletedPrimeClass x <=
        greedyPrimeRegulatorReal x + Real.log x := by
  have hn : 2 <= Nat.floor x := Nat.le_floor hx
  have hpos : (0 : Real) < (Nat.floor x : Real) := by exact_mod_cast (by omega : 0 < Nat.floor x)
  have hlog : Real.log (Nat.floor x : Real) <= Real.log x :=
    Real.log_le_log hpos (Nat.floor_le (by linarith only [hx]))
  have hb := greedyDeletedPrimeClass_record_bounds (Nat.floor x) hn
  exact And.intro hb.1 (by
    change primeClassTheta greedyDeletedPrimeClass (Nat.floor x) <=
      greedyPrimeRegulator (Nat.floor x) + Real.log x
    linarith only [hb.2, hlog])

theorem greedyDeletedPrimeClass_real_mass_optimal
    (P : Set Nat) (hP : forall t : Real, 2 <= t -> primeClassThetaReal P t <= t)
    (x : Real) (hx : 2 <= x) :
    primeClassThetaReal greedyDeletedPrimeClass x <=
      primeClassThetaReal (fun p => Not (Membership.mem P p)) x + Real.log x := by
  have hb := greedyDeletedPrimeClass_mass_optimal P
    (primeClass_realCap_implies_natCap P hP) (Nat.floor x) (Nat.le_floor hx)
  have hn : 2 <= Nat.floor x := Nat.le_floor hx
  have hpos : (0 : Real) < (Nat.floor x : Real) := by
    exact_mod_cast (by omega : 0 < Nat.floor x)
  have hlog : Real.log (Nat.floor x : Real) <= Real.log x :=
    Real.log_le_log hpos (Nat.floor_le (by linarith only [hx]))
  change primeClassTheta greedyDeletedPrimeClass (Nat.floor x) <=
    primeClassTheta (fun p => Not (Membership.mem P p)) (Nat.floor x) + Real.log x
  linarith only [hb, hlog]

theorem greedyDeletedPrimeClass_real_count_optimal
    (P : Set Nat) (hP : forall t : Real, 2 <= t -> primeClassThetaReal P t <= t)
    (x : Real) :
    (primeClassPrefix greedyDeletedPrimeClass (Nat.floor x)).card <=
      (primeClassPrefix (fun p => Not (Membership.mem P p)) (Nat.floor x)).card :=
  greedyDeletedPrimeClass_count_optimal P (primeClass_realCap_implies_natCap P hP)
    (Nat.floor x)

theorem clockRecord_le_iff (e : Nat -> Real) (n : Nat) (c : Real) :
    clockRecord e n <= c <-> And (0 <= c) (forall i : Nat, i < n -> e i <= c) := by
  induction n with
  | zero => simp [clockRecord]
  | succ n ih =>
    simp only [clockRecord, max_le_iff, ih]
    constructor
    case mp =>
      intro h
      refine And.intro h.1.1 ?_
      intro i hi
      by_cases hin : i < n
      case pos => exact h.1.2 i hin
      case neg =>
        have heq : i = n := by omega
        simpa only [heq] using h.2
    case mpr =>
      intro h
      exact And.intro (And.intro h.1 (fun i hi => h.2 i (by omega)))
        (h.2 n (Nat.lt_succ_self n))

theorem greedyPrimeRegulator_le_iff (X : Nat) (c : Real) :
    greedyPrimeRegulator X <= c <->
      And (0 <= c) (forall p : Nat, Nat.Prime p -> p <= X ->
        primeClassTheta Set.univ p - (p : Real) <= c) := by
  rw [greedyPrimeRegulator, clockRecord_le_iff]
  constructor
  case mp =>
    intro h
    refine And.intro h.1 ?_
    intro p hp hpX
    have hi : Nat.count Nat.Prime p < primeCutoffLength X := by
      apply (primeAt_le_cutoff_iff (Nat.count Nat.Prime p) X).mp
      simpa only [primeAt_count_prime p hp] using hpX
    have hb := h.2 (Nat.count Nat.Prime p) hi
    simpa only [primeClockError_eq_theta, primeAt_count_prime p hp] using hb
  case mpr =>
    intro h
    refine And.intro h.1 ?_
    intro i hi
    simpa only [primeClockError_eq_theta] using
      h.2 (primeAt i) (prime_primeAt i) ((primeAt_le_cutoff_iff i X).mpr hi)

theorem greedyPrimeRegulatorReal_le_iff (x c : Real) (hx : 0 <= x) :
    greedyPrimeRegulatorReal x <= c <->
      And (0 <= c) (forall p : Nat, Nat.Prime p -> (p : Real) <= x ->
        primeClassThetaReal Set.univ (p : Real) - (p : Real) <= c) := by
  simp only [greedyPrimeRegulatorReal, greedyPrimeRegulator_le_iff,
    primeClassThetaReal, Nat.floor_natCast, Nat.le_floor_iff hx]

theorem realFloor_tendsto_atTop :
    Tendsto (fun x : Real => Nat.floor x) atTop atTop := by
  apply tendsto_atTop.2
  intro n
  filter_upwards [eventually_ge_atTop (n : Real)] with x hx
  exact Nat.le_floor hx

theorem realFloor_div_tendsto_one :
    Tendsto (fun x : Real => (Nat.floor x : Real) / x) atTop (nhds 1) := by
  have hl : Tendsto (fun x : Real => 1 - 1 / x) atTop (nhds 1) := by
    simpa only [id_eq, sub_zero] using
      tendsto_const_nhds.sub (tendsto_id.const_div_atTop (1 : Real))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  case hgf =>
    filter_upwards [eventually_ge_atTop (1 : Real)] with x hx
    have hx0 : 0 < x := by linarith only [hx]
    have hb := Nat.lt_floor_add_one x
    have hbound : x - 1 <= (Nat.floor x : Real) := by linarith only [hb]
    have hid : (x - 1) / x = 1 - 1 / x := by field_simp
    simpa only [hid] using div_le_div_of_nonneg_right hbound hx0.le
  case hfh =>
    filter_upwards [eventually_ge_atTop (1 : Real)] with x hx
    have hx0 : 0 < x := by linarith only [hx]
    calc
      (Nat.floor x : Real) / x <= x / x :=
        div_le_div_of_nonneg_right (Nat.floor_le hx0.le) hx0.le
      _ = 1 := div_self hx0.ne'

theorem realFloor_ratio_limit (f : Nat -> Real) (a : Real)
    (hf : Tendsto (fun X : Nat => f X / (X : Real)) atTop (nhds a)) :
    Tendsto (fun x : Real => f (Nat.floor x) / x) atTop (nhds a) := by
  have h := (hf.comp realFloor_tendsto_atTop).mul realFloor_div_tendsto_one
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : Real)] with x hx
  have hn : 2 <= Nat.floor x := Nat.le_floor hx
  have hn0 : Not ((Nat.floor x : Real) = 0) := by
    exact_mod_cast (by omega : Not (Nat.floor x = 0))
  change (f (Nat.floor x) / (Nat.floor x : Real)) * ((Nat.floor x : Real) / x) =
    f (Nat.floor x) / x
  field_simp [hn0]

theorem greedyPrimeClass_thetaReal_div_tendsto_one :
    Tendsto (fun x : Real => primeClassThetaReal greedyPrimeClass x / x)
      atTop (nhds 1) :=
  realFloor_ratio_limit (primeClassTheta greedyPrimeClass) 1
    greedyPrimeClass_theta_div_tendsto_one

theorem greedyDeletedPrimeClass_thetaReal_div_tendsto_zero :
    Tendsto (fun x : Real => primeClassThetaReal greedyDeletedPrimeClass x / x)
      atTop (nhds 0) :=
  realFloor_ratio_limit (primeClassTheta greedyDeletedPrimeClass) 0
    greedyDeletedPrimeClass_mass_div_tendsto_zero

theorem primeClassThetaReal_univ_div_tendsto_one :
    Tendsto (fun x : Real => primeClassThetaReal Set.univ x / x) atTop (nhds 1) :=
  realFloor_ratio_limit (primeClassTheta Set.univ) 1 primeClassTheta_univ_div_tendsto_one

theorem primeClassThetaReal_le_count_mul_log (P : Set Nat) (x : Real) (hx : 2 <= x) :
    primeClassThetaReal P x <=
      ((primeClassPrefix P (Nat.floor x)).card : Real) * Real.log x := by
  have hn : 2 <= Nat.floor x := Nat.le_floor hx
  have hn0 : (0 : Real) < (Nat.floor x : Real) := by
    exact_mod_cast (by omega : 0 < Nat.floor x)
  have hlog := Real.log_le_log hn0 (Nat.floor_le (by linarith only [hx]))
  exact (primeClassTheta_le_card_mul_log P (Nat.floor x)).trans
    (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _))

theorem primeClassPrefix_univ_real_count_ratio_tendsto_one :
    Tendsto (fun x : Real =>
      ((primeClassPrefix Set.univ (Nat.floor x)).card : Real) / (x / Real.log x))
      atTop (nhds 1) := by
  have hne : Filter.Eventually (fun x : Real => Not ((x / Real.log x) = 0)) atTop := by
    filter_upwards [eventually_ge_atTop (2 : Real)] with x hx
    have hx0 : 0 < x := by linarith only [hx]
    have hl : 0 < Real.log x := Real.log_pos (by linarith only [hx])
    exact div_ne_zero hx0.ne' hl.ne'
  have h := (Asymptotics.isEquivalent_iff_tendsto_one hne).mp
    PrimeFactorOscillations.primeCounting_isEquivalent_div_log
  apply h.congr'
  filter_upwards [] with x
  change (Nat.primeCounting (Nat.floor x) : Real) / (x / Real.log x) = _
  rw [primeClassPrefix_univ_card_eq_primeCounting]

theorem greedyPrimeClass_real_count_ratio_tendsto_one :
    Tendsto (fun x : Real =>
      ((primeClassPrefix greedyPrimeClass (Nat.floor x)).card : Real) /
        (x / Real.log x)) atTop (nhds 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    greedyPrimeClass_thetaReal_div_tendsto_one
    primeClassPrefix_univ_real_count_ratio_tendsto_one
  case hgf =>
    filter_upwards [eventually_ge_atTop (2 : Real)] with x hx
    have hx0 : 0 < x := by linarith only [hx]
    have hl : 0 < Real.log x := Real.log_pos (by linarith only [hx])
    calc
      primeClassThetaReal greedyPrimeClass x / x <=
          (((primeClassPrefix greedyPrimeClass (Nat.floor x)).card : Real) *
            Real.log x) / x :=
        div_le_div_of_nonneg_right
          (primeClassThetaReal_le_count_mul_log greedyPrimeClass x hx) hx0.le
      _ = _ := by field_simp [hx0.ne', hl.ne']
  case hfh =>
    filter_upwards [eventually_ge_atTop (2 : Real)] with x hx
    have hx0 : 0 < x := by linarith only [hx]
    have hl : 0 < Real.log x := Real.log_pos (by linarith only [hx])
    exact div_le_div_of_nonneg_right
      (Nat.cast_le.mpr (primeClassPrefix_card_le_univ greedyPrimeClass (Nat.floor x)))
      (div_nonneg hx0.le hl.le)

theorem greedyPrimeClass_complete_cap :
    (forall x : Real, 2 <= x -> primeClassThetaReal greedyPrimeClass x <= x) /\
    (forall x : Real, 2 <= x ->
      greedyPrimeRegulatorReal x <= primeClassThetaReal greedyDeletedPrimeClass x /\
      primeClassThetaReal greedyDeletedPrimeClass x <=
        greedyPrimeRegulatorReal x + Real.log x) /\
    (forall P : Set Nat,
      (forall t : Real, 2 <= t -> primeClassThetaReal P t <= t) ->
      forall x : Real, 2 <= x ->
        primeClassThetaReal greedyDeletedPrimeClass x <=
          primeClassThetaReal (fun p => Not (Membership.mem P p)) x + Real.log x /\
        (primeClassPrefix greedyDeletedPrimeClass (Nat.floor x)).card <=
          (primeClassPrefix (fun p => Not (Membership.mem P p)) (Nat.floor x)).card) /\
    Tendsto (fun x : Real => primeClassThetaReal greedyPrimeClass x / x)
      atTop (nhds 1) /\
    Tendsto (fun x : Real =>
      ((primeClassPrefix greedyPrimeClass (Nat.floor x)).card : Real) /
        (x / Real.log x)) atTop (nhds 1) := by
  refine And.intro (fun x hx => greedyPrimeClass_thetaReal_le x (by linarith only [hx]))
    (And.intro greedyDeletedPrimeClass_real_record_bounds (And.intro ?_
      (And.intro greedyPrimeClass_thetaReal_div_tendsto_one
        greedyPrimeClass_real_count_ratio_tendsto_one)))
  intro P hP x hx
  exact And.intro (greedyDeletedPrimeClass_real_mass_optimal P hP x hx)
    (greedyDeletedPrimeClass_real_count_optimal P hP x)

end PrimeFactorOscillations.PrimeClassDeletion
