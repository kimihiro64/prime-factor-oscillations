/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyPrimeGapDeficit

/-!
# A uniform negative area from the selected theta cap alone

Short intervals after the actual selected jumps cover at most one eighth
of the dyadic window. Its complement supplies the signed integral.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter MeasureTheory
open PrimeFactorOscillations.PrimeClassSampling
open Robin1984

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def greedyPrimeAreaBadSet (x : Real) : Set Real :=
  Set.iUnion (fun p : Nat => Set.iUnion
    (fun _ : Membership.mem (greedyPrimeAreaPrimes x) p =>
      Set.Ico (p : Real) ((p : Real) + Real.log x / 32)))

noncomputable def greedyPrimeAreaGoodSet (x : Real) : Set Real :=
  Set.Ioc x (2 * x) \ greedyPrimeAreaBadSet x

theorem greedyPrimeAreaBadSet_measurable (x : Real) :
    MeasurableSet (greedyPrimeAreaBadSet x) :=
  MeasurableSet.iUnion (fun _ => MeasurableSet.iUnion (fun _ => measurableSet_Ico))

theorem greedyPrimeAreaGoodSet_measurable (x : Real) :
    MeasurableSet (greedyPrimeAreaGoodSet x) :=
  measurableSet_Ioc.diff (greedyPrimeAreaBadSet_measurable x)

theorem greedyPrimeAreaBadSet_measure_bound (x : Real) (hx : 4 <= x) :
    volume (greedyPrimeAreaBadSet x) <= ENNReal.ofReal (x / 8) := by
  classical
  have hUnion : volume (greedyPrimeAreaBadSet x) <=
      (greedyPrimeAreaPrimes x).sum (fun p =>
        volume (Set.Ico (p : Real) ((p : Real) + Real.log x / 32))) :=
    measure_biUnion_finset_le (greedyPrimeAreaPrimes x) _
  have hSum : (greedyPrimeAreaPrimes x).sum (fun p =>
        volume (Set.Ico (p : Real) ((p : Real) + Real.log x / 32))) =
      ENNReal.ofReal (((greedyPrimeAreaPrimes x).card : Real) * (Real.log x / 32)) := by
    simp only [Real.volume_Ico, add_sub_cancel_left, Finset.sum_const, nsmul_eq_mul]
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  rw [hSum] at hUnion
  apply hUnion.trans (ENNReal.ofReal_le_ofReal _)
  have hCount := greedyPrimeAreaPrimes_log_budget x hx
  linarith only [hCount]

theorem greedyPrimeAreaGoodSet_measure_lower (x : Real) (hx : 4 <= x) :
    7 * x / 8 <= volume.real (greedyPrimeAreaGoodSet x) := by
  let I : Set Real := Set.Ioc x (2 * x)
  let B : Set Real := greedyPrimeAreaBadSet x
  have hx0 : 0 <= x := by linarith only [hx]
  have hBFin : Not (volume B = Top.top) :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (greedyPrimeAreaBadSet_measure_bound x hx)
  have hB : volume.real B <= x / 8 := by
    change (volume (greedyPrimeAreaBadSet x)).toReal <= x / 8
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (greedyPrimeAreaBadSet_measure_bound x hx)
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 <= x / 8)] using h
  have hIFin : Not (volume I = Top.top) := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hI : volume.real I = x := by
    change (volume I).toReal = x
    rw [Real.volume_Ioc, show 2 * x - x = x by ring, ENNReal.toReal_ofReal hx0]
  let C : Set Real := {t : Real | And (Membership.mem I t) (Membership.mem B t)}
  have hCMeas : MeasurableSet C :=
    measurableSet_Ioc.inter (greedyPrimeAreaBadSet_measurable x)
  have hClip : volume.real C <= volume.real B :=
    measureReal_mono (fun _ ht => ht.2) hBFin
  have hEq : greedyPrimeAreaGoodSet x = I \ C := by
    ext t
    change (And (Membership.mem I t) (Not (Membership.mem B t))) <->
      And (Membership.mem I t) (Not (And (Membership.mem I t) (Membership.mem B t)))
    tauto
  have hDiff : volume.real (I \ C) = volume.real I - volume.real C :=
    measureReal_sdiff (fun _ ht => ht.1) hCMeas hIFin
  rw [hEq, hDiff, hI]
  linarith only [hB, hClip]

theorem greedyPrimeAreaGoodSet_deficit (x t : Real) (hx : 4 <= x)
    (ht : Membership.mem (greedyPrimeAreaGoodSet x) t) :
    Real.log x / 32 <= t - primeClassThetaReal greedyPrimeClass t := by
  have hI : And (x < t) (t <= 2 * x) := ht.1
  have hSmall : Real.log x / 32 <= x / 2 := by
    have h := Real.log_le_sub_one_of_pos (by linarith only [hx] : 0 < x)
    linarith only [h, hx]
  apply greedyPrimeClass_deficit_of_no_selected_prime t (Real.log x / 32)
    (by linarith only [hSmall, hI.1, hx]) _
    (div_nonneg (Real.log_nonneg (by linarith only [hx])) (by norm_num))
  intro p hp hSel hLow hHigh
  have hP : Membership.mem (greedyPrimeAreaPrimes x) p := by
    classical
    apply Finset.mem_filter.mpr
    refine And.intro ?_ (by linarith only [hLow, hSmall, hI.1])
    exact (primeClassPrefix_mem_iff greedyPrimeClass (Nat.floor (2 * x)) p).mpr
      (And.intro hp.two_le (And.intro (Nat.le_floor (hHigh.trans hI.2)) (And.intro hp hSel)))
  have hBad : Membership.mem (greedyPrimeAreaBadSet x) t :=
    Set.mem_iUnion.mpr (Exists.intro p
      (Set.mem_iUnion.mpr (Exists.intro hP
        (And.intro hHigh (by linarith only [hLow])))))
  exact ht.2 hBad

theorem greedyPrimeNicolasIntegral_negative_area (x : Real) (hx : 4 <= x) :
    greedyPrimeNicolasIntegral x <= -(7 / (2048 * x)) := by
  let f : Real -> Real := fun t =>
    (t - primeClassThetaReal greedyPrimeClass t) * nicolasTailKernel t
  let G : Set Real := greedyPrimeAreaGoodSet x
  let c : Real := 1 / (256 * x ^ 2)
  have hx0 : 0 < x := by linarith only [hx]
  have hL : 0 < Real.log x := Real.log_pos (by linarith only [hx])
  have hc : 0 <= c := by dsimp only [c]; positivity
  have hSub : forall t, Membership.mem G t -> Membership.mem (Set.Ioi x) t :=
    fun _ ht => ht.1.1
  have hIFin : Not (volume (Set.Ioc x (2 * x)) = Top.top) := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hGFin : Not (volume G = Top.top) :=
    ne_top_of_le_ne_top hIFin (measure_mono (fun _ ht => ht.1))
  have hInt : IntegrableOn f (Set.Ioi x) := by
    convert (greedyPrimeNicolasIntegral_integrable x (by linarith only [hx])).neg using 1
    funext t
    change (t - primeClassThetaReal greedyPrimeClass t) * nicolasTailKernel t =
      -((primeClassThetaReal greedyPrimeClass t - t) * nicolasTailKernel t)
    ring
  have hNonneg : forall t : Real, x < t -> 0 <= f t := by
    intro t ht
    exact mul_nonneg (sub_nonneg.mpr
      (greedyPrimeClass_thetaReal_le t (by linarith only [hx, ht])))
      (nicolasTailKernel_nonneg (by linarith only [hx, ht]))
  have hSupply : forall t, Membership.mem G t -> c <= f t := by
    intro t ht
    have hDef := greedyPrimeAreaGoodSet_deficit x t hx ht
    have hKer := nicolasTailKernel_dyadic_lower x t hx (And.intro ht.1.1.le ht.1.2)
    have h := mul_le_mul hDef hKer (by positivity : 0 <= 1 / (8 * x ^ 2 * Real.log x))
      (by linarith only [hDef, hL] : 0 <= t - primeClassThetaReal greedyPrimeClass t)
    have heq : (Real.log x / 32) * (1 / (8 * x ^ 2 * Real.log x)) = c := by
      dsimp only [c]
      field_simp [hL.ne', hx0.ne']; ring
    rw [heq] at h
    exact h
  have hLocal : volume.real G * c <= integral (volume.restrict G) f := by
    have hConst : IntegrableOn (fun _ : Real => c) G := integrableOn_const hGFin
    have h : integral (volume.restrict G) (fun _ : Real => c) <=
        integral (volume.restrict G) f :=
      integral_mono_ae hConst (hInt.mono_set hSub)
      (by
        filter_upwards [ae_restrict_mem (greedyPrimeAreaGoodSet_measurable x)] with t ht
        exact hSupply t ht)
    simpa only [setIntegral_const, smul_eq_mul] using h
  have hGlobal : integral (volume.restrict G) f <=
      integral (volume.restrict (Set.Ioi x)) f :=
    setIntegral_mono_set hInt
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact hNonneg t ht)
      (Filter.Eventually.of_forall (fun t ht => hSub t ht))
  have hMeasure : 7 * x / 8 <= volume.real G :=
    greedyPrimeAreaGoodSet_measure_lower x hx
  have hMain : 7 / (2048 * x) <= integral (volume.restrict (Set.Ioi x)) f := by
    calc
      7 / (2048 * x) = (7 * x / 8) * c := by
        dsimp only [c]
        field_simp [hx0.ne']; ring
      _ <= volume.real G * c := mul_le_mul_of_nonneg_right hMeasure hc
      _ <= integral (volume.restrict G) f := hLocal
      _ <= integral (volume.restrict (Set.Ioi x)) f := hGlobal
  have hSigned : integral (volume.restrict (Set.Ioi x)) f =
      -greedyPrimeNicolasIntegral x := by
    rw [greedyPrimeNicolasIntegral, <- integral_neg]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t => by dsimp only [f]; ring)
  rw [hSigned] at hMain
  linarith only [hMain]

theorem greedyPrimeCalibratedError_negative_bound
    (x : Real) (hx : 4 <= x) (hLog : 131072 / 7 <= Real.log x)
    (hS : 1 < primeClassThetaReal greedyPrimeClass x) :
    greedyPrimeCalibratedError x <= -(7 / 4096) / x := by
  have hx0 : 0 < x := by linarith only [hx]
  have hL : 0 < Real.log x := by linarith only [hLog]
  have hScalar : 32 / Real.log x <= (7 / 4096 : Real) := by
    calc
      32 / Real.log x <= 32 / (131072 / 7 : Real) :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hLog
      _ = 7 / 4096 := by norm_num
  have hTail : 32 / (x * Real.log x) <= (7 / 4096) / x := by
    calc
      32 / (x * Real.log x) = (32 / Real.log x) / x := by
        field_simp
      _ <= (7 / 4096) / x := div_le_div_of_nonneg_right hScalar hx0.le
  have hBound := greedyPrimeCalibratedError_le_integral_add_log_tail x hx hS
  have hArea := greedyPrimeNicolasIntegral_negative_area x hx
  have hCancel : -(7 / (2048 * x)) + (7 / 4096) / x = -(7 / 4096) / x := by
    field_simp; ring
  linarith only [hBound, hArea, hTail, hCancel]

theorem greedyPrimeClass_eventually_thetaReal_gt_one :
    Filter.Eventually (fun x : Real => 1 < primeClassThetaReal greedyPrimeClass x) atTop := by
  have hRatio : Filter.Eventually
      (fun x : Real => (1 / 2 : Real) < primeClassThetaReal greedyPrimeClass x / x) atTop :=
    (tendsto_order.mp greedyPrimeClass_thetaReal_div_tendsto_one).1 _ (by norm_num)
  filter_upwards [hRatio, eventually_ge_atTop (4 : Real)] with x hR hx
  have hx0 : 0 < x := by linarith only [hx]
  have hScaled := mul_lt_mul_of_pos_right hR hx0
  have hEq : primeClassThetaReal greedyPrimeClass x / x * x =
      primeClassThetaReal greedyPrimeClass x := by field_simp
  rw [hEq] at hScaled
  linarith only [hScaled, hx]

theorem greedyPrimeCalibratedError_strict_product_sign :
    Exists (fun c0 : Real => And (0 < c0) (Exists (fun X0 : Real =>
      forall x : Real, X0 <= x -> And
        (greedyPrimeCalibratedError x <= -c0 / x) (-c0 / x < 0)))) := by
  have hEv : Filter.Eventually (fun x : Real => And
      (greedyPrimeCalibratedError x <= -(7 / 4096) / x)
      (-(7 / 4096) / x < 0)) atTop := by
    filter_upwards [greedyPrimeClass_eventually_thetaReal_gt_one,
      eventually_ge_atTop (4 : Real),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (131072 / 7 : Real))]
      with x hS hx hL
    exact And.intro (greedyPrimeCalibratedError_negative_bound x hx hL hS)
      (div_neg_of_neg_of_pos (by norm_num) (by linarith only [hx]))
  exact Exists.intro (7 / 4096) (And.intro (by norm_num) (eventually_atTop.mp hEv))

end PrimeFactorOscillations.PrimeClassDeletion
