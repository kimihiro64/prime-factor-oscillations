/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeProfileThetaClock

/-!
# Prime-counting and strict-prefix PNT estimates

The cached Chebyshev remainder transfers the established theta PNT to prime
counting. The resulting estimates retain every natural endpoint P and every
count N below pi(P), as required by the last-ascent location argument.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open Filter Asymptotics

theorem primeCounting_isEquivalent_div_log :
    Asymptotics.IsEquivalent atTop
      (fun x : Real => (Nat.primeCounting (Nat.floor x) : Real))
      (fun x : Real => x / Real.log x) := by
  have hinv : Tendsto (fun x : Real => 1 / Real.log x)
      atTop (nhds (0 : Real)) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hsmall := (Asymptotics.isLittleO_one_iff Real).mpr hinv
  have hprod := hsmall.mul_isBigO
    (Asymptotics.isBigO_refl (fun x : Real => x / Real.log x) atTop)
  have herrorScale : Asymptotics.IsLittleO atTop
      (fun x : Real => x / Real.log x ^ 2) (fun x : Real => x / Real.log x) := by
    apply hprod.congr'
    . filter_upwards [] with x
      ring
    . filter_upwards [] with x
      simp
  have hrem := Chebyshev.primeCounting_sub_theta_div_log_isBigO.trans_isLittleO herrorScale
  have htheta : Asymptotics.IsLittleO atTop
      (Chebyshev.theta - (fun x : Real => x)) (fun x : Real => x) :=
    primeProfile_theta_isEquivalent_id
  have hthetaScaled := htheta.mul_isBigO
    (Asymptotics.isBigO_refl (fun x : Real => 1 / Real.log x) atTop)
  have ht : Asymptotics.IsLittleO atTop
      (fun x : Real => Chebyshev.theta x / Real.log x - x / Real.log x)
      (fun x : Real => x / Real.log x) := by
    apply hthetaScaled.congr'
    . filter_upwards [] with x
      dsimp
      ring
    . filter_upwards [] with x
      ring
  change Asymptotics.IsLittleO atTop
    ((fun x : Real => (Nat.primeCounting (Nat.floor x) : Real)) -
      (fun x : Real => x / Real.log x)) (fun x : Real => x / Real.log x)
  apply (hrem.add ht).congr'
  . filter_upwards [] with x
    dsimp
    ring
  . exact Filter.EventuallyEq.refl _ _

theorem tendsto_primeCounting_div_mainTerm :
    Tendsto (fun P : Nat => (Nat.primeCounting P : Real) /
      ((P : Real) / Real.log (P : Real))) atTop (nhds (1 : Real)) := by
  have hn : Tendsto (fun P : Nat => (P : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have heq := primeCounting_isEquivalent_div_log.comp_tendsto hn
  have hne : Filter.Eventually (fun P : Nat =>
      Not (((P : Real) / Real.log (P : Real)) = 0)) atTop := by
    filter_upwards [eventually_ge_atTop (2 : Nat)] with P hP
    have hp : (1 : Real) < P := by exact_mod_cast (show 1 < P by omega)
    exact div_ne_zero (lt_trans zero_lt_one hp).ne' (Real.log_pos hp).ne'
  have hratio := (Asymptotics.isEquivalent_iff_tendsto_one hne).mp heq
  apply hratio.congr'
  filter_upwards [] with P
  simp only [Pi.div_apply, Function.comp_apply, Nat.floor_natCast]

theorem tendsto_thetaPrefix_div_endpoint :
    Tendsto (fun P : Nat => Chebyshev.theta ((P - 1 : Nat) : Real) / (P : Real))
      atTop (nhds (1 : Real)) := by
  have hshift : Tendsto (fun P : Nat => P - 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (b + 1)] with P hP
    omega
  have hinv : Tendsto (fun P : Nat => 1 / (P : Real))
      atTop (nhds (0 : Real)) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun P : Nat => (P : Real)) atTop atTop)
  have hraw : Tendsto (fun P : Nat => (1 : Real) - 1 / (P : Real))
      atTop (nhds (1 : Real)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hinv
  have hsub : Tendsto (fun P : Nat => ((P - 1 : Nat) : Real) / (P : Real))
      atTop (nhds (1 : Real)) := by
    apply hraw.congr'
    filter_upwards [eventually_ge_atTop (2 : Nat)] with P hP
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    have hp : Not ((P : Real) = 0) := by
      exact_mod_cast (show Not (P = 0) by omega)
    field_simp
  have hprod := (tendsto_primeProfile_theta_ratio.comp hshift).mul hsub
  apply (show Tendsto
    (fun P : Nat => Chebyshev.theta ((P - 1 : Nat) : Real) /
      ((P - 1 : Nat) : Real) * (((P - 1 : Nat) : Real) / (P : Real)))
    atTop (nhds (1 : Real)) by
      simpa only [mul_one, Function.comp_def] using hprod).congr'
  filter_upwards [eventually_ge_atTop (2 : Nat)] with P hP
  have hp : Not ((P : Real) = 0) := by
    exact_mod_cast (show Not (P = 0) by omega)
  have hprev : Not (((P - 1 : Nat) : Real) = 0) := by
    exact_mod_cast (show Not (P - 1 = 0) by omega)
  field_simp

theorem eventually_thetaPrefix_and_primeCounting_bounds (delta : Real) (hd : 0 < delta) :
    Filter.Eventually (fun P : Nat =>
      2 <= P /\
      (1 - delta) * (P : Real) <= Chebyshev.theta ((P - 1 : Nat) : Real) /\
      (Nat.primeCounting P : Real) <= (1 + delta) * (P : Real) / Real.log (P : Real))
      atTop := by
  have ht := tendsto_thetaPrefix_div_endpoint.eventually
    (lt_mem_nhds (show (1 : Real) - delta < 1 by linarith))
  have hp := tendsto_primeCounting_div_mainTerm.eventually
    (gt_mem_nhds (show (1 : Real) < 1 + delta by linarith))
  filter_upwards [eventually_ge_atTop (2 : Nat), ht, hp] with P hP htP hpP
  have hPR : (1 : Real) < P := by exact_mod_cast (show 1 < P by omega)
  have hPpos : (0 : Real) < P := zero_lt_one.trans hPR
  have hlog : 0 < Real.log (P : Real) := Real.log_pos hPR
  have hg : 0 < (P : Real) / Real.log (P : Real) := div_pos hPpos hlog
  refine And.intro hP (And.intro ?_ ?_)
  . have h := mul_lt_mul_of_pos_right htP hPpos
    have heq : Chebyshev.theta ((P - 1 : Nat) : Real) / (P : Real) * P =
        Chebyshev.theta ((P - 1 : Nat) : Real) := by field_simp
    rw [heq] at h
    exact h.le
  . have h := mul_lt_mul_of_pos_right hpP hg
    have heq : (Nat.primeCounting P : Real) /
        ((P : Real) / Real.log (P : Real)) * ((P : Real) / Real.log (P : Real)) =
        Nat.primeCounting P := by field_simp
    rw [heq] at h
    have heq2 : (1 + delta) * ((P : Real) / Real.log (P : Real)) =
        (1 + delta) * (P : Real) / Real.log (P : Real) := by ring
    rw [heq2] at h
    exact h.le

theorem eventually_count_log_count_le_thetaPrefix (epsilon : Real) (he : 0 < epsilon) :
    exists N0 : Nat, 2 <= N0 /\ forall N : Nat, N0 <= N ->
      forall P : Nat, N <= Nat.primeCounting P ->
        (1 - epsilon) * (N : Real) * Real.log (N : Real) <=
          Chebyshev.theta ((P - 1 : Nat) : Real) := by
  have hself (P : Nat) : Nat.primeCounting P <= P := by
    rw [<- Nat.primesLE_card_eq_primeCounting]
    have hs : (Nat.primesLE P).card <= (Finset.Icc 1 P).card := by
      apply Finset.card_le_card
      intro p hp
      have h := Nat.mem_primesLE.mp hp
      exact Finset.mem_Icc.mpr (And.intro h.2.one_lt.le h.1)
    simpa using hs
  by_cases he1 : epsilon < 1
  case neg =>
    refine Exists.intro 2 (And.intro le_rfl ?_)
    intro N hN P hNP
    have hNR : (1 : Real) <= N := by exact_mod_cast (show 1 <= N by omega)
    have hlog : 0 <= Real.log (N : Real) := Real.log_nonneg hNR
    have hcoef : 1 - epsilon <= 0 := by linarith
    have hneg : (1 - epsilon) * (N : Real) * Real.log (N : Real) <= 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hcoef (Nat.cast_nonneg N)) hlog
    exact hneg.trans (Chebyshev.theta_nonneg _)
  case pos =>
    let delta := epsilon / 4
    have hd : 0 < delta := by dsimp [delta]; positivity
    choose P0 hP0 using
      (eventually_thetaPrefix_and_primeCounting_bounds delta hd).exists_forall_of_atTop
    refine Exists.intro (max P0 2) (And.intro (le_max_right _ _) ?_)
    intro N hN P hNP
    have hN2 : 2 <= N := (le_max_right _ _).trans hN
    have hNP' : N <= P := hNP.trans (hself P)
    have hP0' : P0 <= P := (le_max_left _ _).trans (hN.trans hNP')
    have hbounds := hP0 P hP0'
    have hPR : (1 : Real) < P := by exact_mod_cast (show 1 < P by omega)
    have hNR : (0 : Real) < N := by exact_mod_cast (show 0 < N by omega)
    have hlogP : 0 < Real.log (P : Real) := Real.log_pos hPR
    have hNPR : (N : Real) <= P := by exact_mod_cast hNP'
    have hNpi : (N : Real) <= Nat.primeCounting P := by exact_mod_cast hNP
    have hclear := mul_le_mul_of_nonneg_right (hNpi.trans hbounds.2.2) hlogP.le
    have hcancel : ((1 + delta) * (P : Real) / Real.log (P : Real)) *
        Real.log (P : Real) = (1 + delta) * (P : Real) := by field_simp
    rw [hcancel] at hclear
    have hlogs : Real.log (N : Real) <= Real.log (P : Real) :=
      Real.log_le_log hNR hNPR
    have hNmain : (N : Real) * Real.log (N : Real) <= (1 + delta) * (P : Real) :=
      (mul_le_mul_of_nonneg_left hlogs hNR.le).trans hclear
    have hcoef : (1 - epsilon) * (1 + delta) <= 1 - delta := by
      dsimp [delta]
      nlinarith [sq_nonneg epsilon]
    calc
      (1 - epsilon) * (N : Real) * Real.log (N : Real) =
          (1 - epsilon) * ((N : Real) * Real.log (N : Real)) := by ring
      _ <= (1 - epsilon) * ((1 + delta) * (P : Real)) :=
        mul_le_mul_of_nonneg_left hNmain (by linarith)
      _ = ((1 - epsilon) * (1 + delta)) * (P : Real) := by ring
      _ <= (1 - delta) * (P : Real) :=
        mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg P)
      _ <= Chebyshev.theta ((P - 1 : Nat) : Real) := hbounds.2.1

end PrimeFactorOscillations
