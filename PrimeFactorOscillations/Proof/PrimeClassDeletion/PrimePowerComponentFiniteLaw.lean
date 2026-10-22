/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimePowerComponentArithmetic

/-!
# The normalized finite-prime component law

Literal integer samples have mass one. Their full l1 distance to c_S/a
on all supported positive integers obeys the complete Euler budget.
The same estimate proves normalization of that reference law.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open Filter

def literalPrimePowerComponentCount (s : Finset Nat) (N a : Nat) : Nat :=
  ((Finset.Icc 1 N).filter (fun m => finitePrimePowerComponent s m = a)).card

noncomputable def literalPrimePowerComponentProbability
    (s : Finset Nat) (N a : Nat) : Real :=
  (literalPrimePowerComponentCount s N a : Real) / (N : Real)

noncomputable def finitePrimePowerReference (s : Finset Nat) (a : Nat) : Real := by
  classical
  exact if primePowerSupportedOn s a then finitePrimeComponentSurvival s / (a : Real) else 0

theorem literalPrimePowerComponentCount_eq_zero_of_gt
    (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p)
    (N a : Nat) (hNa : N < a) :
    literalPrimePowerComponentCount s N a = 0 := by
  unfold literalPrimePowerComponentCount
  apply Finset.card_eq_zero.mpr
  apply Finset.ext
  intro m
  constructor
  case mp =>
    intro hm
    have hdata := Finset.mem_filter.mp hm
    have hinterval := Finset.mem_Icc.mp hdata.1
    have hm0 : 0 < m := Nat.lt_of_lt_of_le Nat.zero_lt_one hinterval.1
    have hd := (finitePrimePowerComponent_fiber_conditions s hprime m hm0).1
    have hle := (Nat.le_of_dvd hm0 hd).trans hinterval.2
    rw [hdata.2] at hle
    exact False.elim (Nat.not_le_of_gt hNa hle)
  case mpr =>
    intro hm
    simp at hm

theorem literalPrimePowerComponentCount_sum
    (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p) (N : Nat) :
    (Finset.range (N + 1)).sum (literalPrimePowerComponentCount s N) = N := by
  classical
  have hcount (a : Nat) :
      literalPrimePowerComponentCount s N a =
        (Finset.Icc 1 N).sum (fun m =>
          if finitePrimePowerComponent s m = a then 1 else 0) := by
    simp [literalPrimePowerComponentCount]
  calc
    _ = (Finset.range (N + 1)).sum (fun a =>
        (Finset.Icc 1 N).sum (fun m =>
          if finitePrimePowerComponent s m = a then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact hcount a
    _ = (Finset.Icc 1 N).sum (fun m =>
        (Finset.range (N + 1)).sum (fun a =>
          if finitePrimePowerComponent s m = a then 1 else 0)) :=
      Finset.sum_comm
    _ = (Finset.Icc 1 N).sum (fun _ => 1) := by
      apply Finset.sum_congr rfl
      intro m hm
      have hinterval := Finset.mem_Icc.mp hm
      have hm0 : 0 < m := Nat.lt_of_lt_of_le Nat.zero_lt_one hinterval.1
      have hd := (finitePrimePowerComponent_fiber_conditions s hprime m hm0).1
      have hcnt : finitePrimePowerComponent s m < N + 1 :=
        Nat.lt_succ_of_le ((Nat.le_of_dvd hm0 hd).trans hinterval.2)
      simp [Finset.mem_range, hcnt]
    _ = N := by simp

theorem literalPrimePowerComponentProbability_hasSum_one
    (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p)
    (N : Nat) (hN : 0 < N) :
    HasSum (literalPrimePowerComponentProbability s N) 1 := by
  have hfinite : HasSum (literalPrimePowerComponentProbability s N)
      ((Finset.range (N + 1)).sum (literalPrimePowerComponentProbability s N)) :=
    hasSum_sum_of_ne_finset_zero (s := Finset.range (N + 1)) (by
      intro a ha
      have hNa : N < a := Nat.lt_of_not_ge (fun hle =>
        ha (Finset.mem_range.mpr (Nat.lt_succ_of_le hle)))
      unfold literalPrimePowerComponentProbability
      rw [literalPrimePowerComponentCount_eq_zero_of_gt s hprime N a hNa,
        Nat.cast_zero, zero_div])
  have hmass :
      (Finset.range (N + 1)).sum (literalPrimePowerComponentProbability s N) = 1 := by
    unfold literalPrimePowerComponentProbability
    simp only [div_eq_mul_inv]
    rw [<- Finset.sum_mul, <- Nat.cast_sum, literalPrimePowerComponentCount_sum s hprime]
    change (N : Real) / (N : Real) = 1
    exact div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN))
  rw [hmass] at hfinite
  exact hfinite

theorem literalPrimePowerComponentProbability_eq_piecewise_fiber
    (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p)
    (N a : Nat) :
    literalPrimePowerComponentProbability s N a =
      @ite Real (primePowerSupportedOn s a) (Classical.propDecidable _)
        (((primePowerComponentFiber s N a).card : Real) / (N : Real)) 0 := by
  classical
  by_cases ha : primePowerSupportedOn s a
  case pos =>
    rw [ite_eq_left ha, primePowerComponentFiber_eq_actual_fiber s hprime N a ha]
    rfl
  case neg =>
    rw [ite_eq_right ha]
    have hempty :
        (Finset.Icc 1 N).filter (fun m => finitePrimePowerComponent s m = a) =
          ({} : Finset Nat) := by
      apply Finset.ext
      intro m
      constructor
      case mp =>
        intro hm
        have hdata := Finset.mem_filter.mp hm
        have hs := finitePrimePowerComponent_supported s hprime m
        rw [hdata.2] at hs
        exact False.elim (ha hs)
      case mpr =>
        intro hm
        simp at hm
    simp only [literalPrimePowerComponentProbability, literalPrimePowerComponentCount,
      hempty, Finset.card_empty, Nat.cast_zero, zero_div]

theorem literalPrimePowerComponentProbability_abs_error_eq
    (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p)
    (N a : Nat) :
    abs (literalPrimePowerComponentProbability s N a - finitePrimePowerReference s a) =
      supportedPrimePowerComponentError s N a := by
  classical
  rw [literalPrimePowerComponentProbability_eq_piecewise_fiber s hprime N a]
  unfold finitePrimePowerReference supportedPrimePowerComponentError
  split_ifs <;> simp

theorem literalPrimePowerComponentProbability_full_l1_error
    (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p)
    (N : Nat) (hN : 0 < N) (sigma : Real) (hs0 : 0 < sigma) (hs1 : sigma <= 1) :
    And (Summable (fun a => abs
      (literalPrimePowerComponentProbability s N a - finitePrimePowerReference s a)))
      (tsum (fun a => abs
        (literalPrimePowerComponentProbability s N a - finitePrimePowerReference s a)) <=
      (N : Real) ^ (sigma - 1) *
        s.prod (fun p => (1 + (p : Real) ^ (-sigma)) /
          (1 - (p : Real) ^ (-sigma)))) := by
  have heq : (fun a => abs
      (literalPrimePowerComponentProbability s N a - finitePrimePowerReference s a)) =
      supportedPrimePowerComponentError s N :=
    funext (literalPrimePowerComponentProbability_abs_error_eq s hprime N)
  rw [heq]
  exact And.intro
    (supportedPrimePowerComponentError_summable s hprime N hN sigma hs0 hs1)
    (supportedPrimePowerComponentError_tsum_le_euler s hprime N hN sigma hs0 hs1)

theorem finitePrimePowerReference_hasSum_one
    (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p) :
    HasSum (finitePrimePowerReference s) 1 := by
  let B := s.prod (fun p => (1 + (p : Real) ^ (-(1 / 2 : Real))) /
    (1 - (p : Real) ^ (-(1 / 2 : Real))))
  have hactual := literalPrimePowerComponentProbability_hasSum_one s hprime 1 (by norm_num)
  have hdiff := (literalPrimePowerComponentProbability_full_l1_error
    s hprime 1 (by norm_num) (1 / 2) (by norm_num) (by norm_num)).1.of_abs
  have href : Summable (finitePrimePowerReference s) := by
    have h := hactual.summable.sub hdiff
    simpa only [sub_sub_cancel] using h
  have hbound : Filter.Eventually (fun N : Nat =>
      abs (1 - tsum (finitePrimePowerReference s)) <=
        (N : Real) ^ ((1 / 2 : Real) - 1) * B) atTop := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : 0 < N := Nat.lt_of_lt_of_le Nat.zero_lt_one hN
    have hsample := literalPrimePowerComponentProbability_hasSum_one s hprime N hNpos
    have herror := literalPrimePowerComponentProbability_full_l1_error
      s hprime N hNpos (1 / 2) (by norm_num) (by norm_num)
    have hnorm := norm_tsum_le_tsum_norm
      (f := fun a => literalPrimePowerComponentProbability s N a -
        finitePrimePowerReference s a)
      (by simpa only [Real.norm_eq_abs] using herror.1)
    rw [hsample.summable.tsum_sub href, hsample.tsum_eq] at hnorm
    exact le_trans (by simpa only [Real.norm_eq_abs] using hnorm) herror.2
  have hpow := (tendsto_rpow_neg_atTop (by norm_num : 0 < (1 / 2 : Real))).comp
    (tendsto_natCast_atTop_atTop (R := Real))
  have hlimit : Tendsto (fun N : Nat =>
      (N : Real) ^ ((1 / 2 : Real) - 1) * B) atTop (nhds 0) := by
    have heq : -(1 / 2 : Real) = (1 / 2 : Real) - 1 := by norm_num
    simpa only [Function.comp_apply, heq, zero_mul] using hpow.mul_const B
  have hzero := ge_of_tendsto hlimit hbound
  have habs : abs (1 - tsum (finitePrimePowerReference s)) = 0 :=
    le_antisymm hzero (abs_nonneg _)
  have heq : tsum (finitePrimePowerReference s) = 1 :=
    (sub_eq_zero.mp (abs_eq_zero.mp habs)).symm
  rw [<- heq]
  exact href.hasSum

theorem finitePrimeComponentSurvival_pos
    (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p) :
    0 < finitePrimeComponentSurvival s := by
  apply Finset.prod_pos
  intro p hp
  have hp1 : (1 : Real) < (p : Real) := by exact_mod_cast (hprime p hp).one_lt
  have hp0 : (0 : Real) < (p : Real) := lt_trans zero_lt_one hp1
  apply sub_pos.mpr
  by_contra hnot
  have hge : (1 : Real) <= 1 / (p : Real) := le_of_not_gt hnot
  have hmul := mul_le_mul_of_nonneg_right hge hp0.le
  have hcancel : (1 / (p : Real)) * (p : Real) = 1 := by
    field_simp [ne_of_gt hp0]
  rw [one_mul, hcancel] at hmul
  exact not_le_of_gt hp1 hmul

theorem finitePrimePowerReference_nonneg
    (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p) (a : Nat) :
    0 <= finitePrimePowerReference s a := by
  unfold finitePrimePowerReference
  split_ifs
  case pos =>
    exact div_nonneg (finitePrimeComponentSurvival_pos s hprime).le (Nat.cast_nonneg a)
  case neg => exact le_refl 0

theorem finitePrimePowerComponent_totalVariation_le
    (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p)
    (N : Nat) (hN : 0 < N) (sigma : Real) (hs0 : 0 < sigma) (hs1 : sigma <= 1) :
    tsum (fun a => abs
        (literalPrimePowerComponentProbability s N a - finitePrimePowerReference s a)) / 2 <=
      min 1 ((N : Real) ^ (sigma - 1) *
        s.prod (fun p => (1 + (p : Real) ^ (-sigma)) /
          (1 - (p : Real) ^ (-sigma))) / 2) := by
  have hsample := literalPrimePowerComponentProbability_hasSum_one s hprime N hN
  have href := finitePrimePowerReference_hasSum_one s hprime
  have herror := literalPrimePowerComponentProbability_full_l1_error
    s hprime N hN sigma hs0 hs1
  have hpoint (a : Nat) :
      abs (literalPrimePowerComponentProbability s N a - finitePrimePowerReference s a) <=
        literalPrimePowerComponentProbability s N a + finitePrimePowerReference s a := by
    have ha : 0 <= literalPrimePowerComponentProbability s N a :=
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hb := finitePrimePowerReference_nonneg s hprime a
    apply abs_le.mpr
    constructor <;> linarith
  have htwo : tsum (fun a => abs
      (literalPrimePowerComponentProbability s N a - finitePrimePowerReference s a)) <= 2 := by
    calc
      _ <= tsum (fun a => literalPrimePowerComponentProbability s N a +
          finitePrimePowerReference s a) :=
        Summable.tsum_le_tsum hpoint herror.1 (hsample.summable.add href.summable)
      _ = 2 := by
        rw [hsample.summable.tsum_add href.summable, hsample.tsum_eq, href.tsum_eq]
        norm_num
  exact le_min (by linarith) (by linarith [herror.2])

end PrimeFactorOscillations.PrimeClassSampling
