/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Detector.FiniteProductBounds
import PrimeFactorOscillations.Assembly.DetectorPackets.GeneralPrincipalSlotError

/-!
# GeneralPrincipalSlots

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

/-!
# Actual finite slots with the principal correction

The enlarged-strip local estimate is carried through the original weighted
prime sums and finite products,with the complete Euler correction retained.
Local and slot multiplier analytic slices are extended on the same region.
No zero-free boundary follows without the remaining contour and high bounds.
-/


noncomputable section
namespace PrimeFactorOscillations.GeneralPrincipalRegion
open scoped Classical
open OAI OAI.SevenEighths
open ActualEisensteinCubic CompletedGauss ProbePhysical ProbeEuler ProbeLocal
open HeckeFamily ProbeFiniteProductBounds PrincipalSlotEstimate
open PrincipalMellinResidues ProbeMellinBoundary
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem principal_weighted_region_slot_norm {iota : Type*}
    (I : Finset iota) (b Q : iota->Real) (A eta : iota->Complex)
    (s w z : Complex) (P : Real) (hP : 480<=P)
    (hb : forall i, Membership.mem I i -> 0<=b i)
    (hQ : forall i, Membership.mem I i -> P<=Q i)
    (hA : forall i, Membership.mem I i -> norm (A i)<=1)
    (heta : forall i, Membership.mem I i -> norm (eta i)=1)
    (hs : (3/4:Real)<=s.re) (hw : (19/20:Real)<=w.re) (hz : (33/200:Real)<=z.re) :
    norm (I.sum fun i=>(b i:Complex)*(Q i:Complex)^(z-1)*
      regionSlot (Q i) (A i) (eta i) s w z)<=
      (1+1440*P^(-(37/50:Real)))*(I.sum fun i=>b i*(Q i)^(z.re-1)) := by
  calc
    _ <= I.sum (fun i=>norm ((b i:Complex)*(Q i:Complex)^(z-1)*
        regionSlot (Q i) (A i) (eta i) s w z)) := norm_sum_le _ _
    _ <= I.sum (fun i=>(1+1440*P^(-(37/50:Real)))*(b i*(Q i)^(z.re-1))) := by
      apply Finset.sum_le_sum
      intro i hi
      have hQi : 0<Q i := by linarith [hQ i hi]
      have he := principal_region_slot_norm_extended (hP.trans (hQ i hi))
        (hA i hi) (heta i hi) hs hw hz
      have he' : norm (regionSlot (Q i) (A i) (eta i) s w z)<=
          1+1440*P^(-(37/50:Real)) := by
        apply he.trans
        apply add_le_add le_rfl
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Real.rpow_le_rpow_of_nonpos (by linarith) (hQ i hi) (by norm_num)
      rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hb i hi),
        Complex.norm_cpow_eq_rpow_re_of_pos hQi]
      simp only [Complex.sub_re,Complex.one_re]
      exact (mul_le_mul_of_nonneg_left he'
        (mul_nonneg (hb i hi) (Real.rpow_nonneg hQi.le _))).trans_eq (mul_comm _ _)
    _ = _ := by rw [Finset.mul_sum]

theorem principal_slot_norm_bound_sharp {iota : Type*} (eta : Character)
    (J : Finset iota) (T : iota->Finset PrimeIdeal) (b : iota->PrimeIdeal->Real)
    (Pmin : Real) (hPmin : 480<=Pmin)
    (hb : forall j, Membership.mem J j -> forall P, Membership.mem (T j) P -> 0<=b j P)
    (hQ : forall j, Membership.mem J j -> forall P, Membership.mem (T j) P ->
      Pmin<=(Ideal.absNorm P.val:Real))
    (heta : forall j, Membership.mem J j -> forall P, Membership.mem (T j) P ->
      norm (idealCoeff eta P.val)=1)
    (s w z : Complex) (hs : (3/4:Real)<=s.re) (hw : (19/20:Real)<=w.re)
    (hz : (33/200:Real)<=z.re) :
    norm (slotMultiplier eta J T (fun j P=>(b j P:Complex)) s w z)<=
      J.prod (fun j=>(1+1440*Pmin^(-(37/50:Real)))*
        ((T j).sum fun P=>b j P*(Ideal.absNorm P.val:Real)^(z.re-1))) := by
  simp only [slotMultiplier,local_eq_regionSlot,norm_prod]
  gcongr with j hj
  simpa only [mul_assoc,Complex.ofReal_natCast] using
    principal_weighted_region_slot_norm (T j) (b j)
      (fun P=>(Ideal.absNorm P.val:Real))
      (fun P=>actualAPhase eta (primaryGenerator P.val)) (fun P=>idealCoeff eta P.val)
      s w z Pmin hPmin (hb j hj) (hQ j hj)
      (fun P _=>actualAPhase_norm_le_one eta _) (heta j hj) hs hw hz

theorem principal_global_norm_bound (eta : Character) (S : Finset Id)
    (hS : PrincipalCorrectionTail S) (x w z : Complex)
    (hx : (3/4:Real)<=x.re) (hw : (9/10:Real)<=w.re) (hz : (4/25:Real)<=z.re) :
    norm (globalClosedCorrection eta S x w z)<=3/2 := by
  have hb := globalClosedCorrection_principal_extended_bound eta S hS x w z hx hw hz
  have hn := norm_add_le (globalClosedCorrection eta S x w z-1) (1:Complex)
  rw [sub_add_cancel,norm_one] at hn
  linarith

theorem principal_combined_slot_bound_sharp {iota : Type*} (eta : Character)
    (S : Finset Id) (hS : PrincipalCorrectionTail S)
    (J : Finset iota) (T : iota->Finset PrimeIdeal) (b : iota->PrimeIdeal->Real)
    (Pmin : Real) (hPmin : 480<=Pmin)
    (hb : forall j, Membership.mem J j -> forall P, Membership.mem (T j) P -> 0<=b j P)
    (hQ : forall j, Membership.mem J j -> forall P, Membership.mem (T j) P ->
      Pmin<=(Ideal.absNorm P.val:Real))
    (heta : forall j, Membership.mem J j -> forall P, Membership.mem (T j) P ->
      norm (idealCoeff eta P.val)=1)
    (s w z : Complex) (hs : (3/4:Real)<=s.re) (hw : (19/20:Real)<=w.re)
    (hz : (33/200:Real)<=z.re) :
    norm (globalClosedCorrection eta S s w z*
      slotMultiplier eta J T (fun j P=>(b j P:Complex)) s w z)<=
      (3/2)*(J.prod fun j=>(1+1440*Pmin^(-(37/50:Real)))*
        ((T j).sum fun P=>b j P*(Ideal.absNorm P.val:Real)^(z.re-1))) := by
  rw [norm_mul]
  exact mul_le_mul
    (principal_global_norm_bound eta S hS s w z hs (by linarith) (by linarith))
    (principal_slot_norm_bound_sharp eta J T b Pmin hPmin hb hQ heta s w z hs hw hz)
    (norm_nonneg _) (by norm_num)

lemma principal_marked_differentiableAt_w (eta : Character) (P : PrimeIdeal) (x w z : Complex)
    (hQ : 4 <= (Ideal.absNorm P.val : Real)) (hx : 3/4 <= x.re) (hz : 4/25 <= z.re) :
    DifferentiableAt Complex (fun w => idealMarkedClosed eta P x w z) w := by
  have hQ0 : 0 < (Ideal.absNorm P.val : Real) := by linarith
  have hd := principal_region_denominators (Ideal.absNorm P.val)
    (actualAPhase eta (primaryGenerator P.val)) (idealCoeff eta P.val) 1 x z hQ
    (actualAPhase_norm_le_one eta _) (idealCoeff_norm_le_one eta _) (by simp) hx hz
  have hw := coordW_differentiable (Ideal.absNorm P.val) hQ0 1
  have hk := coordK_w_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff eta P.val) x
  unfold idealMarkedClosed markedFactor
  dsimp only
  fun_prop (disch := aesop)

lemma principal_marked_differentiableAt_z (eta : Character) (P : PrimeIdeal) (x w z : Complex)
    (hQ : 4 <= (Ideal.absNorm P.val : Real)) (hx : 3/4 <= x.re) (hz : 4/25 <= z.re) :
    DifferentiableAt Complex (fun z => idealMarkedClosed eta P x w z) z := by
  have hQ0 : 0 < (Ideal.absNorm P.val : Real) := by linarith
  have hd := principal_region_denominators (Ideal.absNorm P.val)
    (actualAPhase eta (primaryGenerator P.val)) (idealCoeff eta P.val) 1 x z hQ
    (actualAPhase_norm_le_one eta _) (idealCoeff_norm_le_one eta _) (by simp) hx hz
  have hv := coordV_differentiable (Ideal.absNorm P.val) hQ0
  have hr := coordR_z_differentiable (Ideal.absNorm P.val) hQ0
    (actualAPhase eta (primaryGenerator P.val)) x
  unfold idealMarkedClosed markedFactor
  dsimp only
  fun_prop (disch := aesop)

theorem principal_local_analytic_w (eta : Character) (S : Finset Id) (hS : PrincipalCorrectionTail S)
    (P : PrimeIdeal) (hP : Not (Membership.mem S P.val)) (x z : Complex)
    (hx : 3/4 <= x.re) (hz : 4/25 <= z.re) :
    AnalyticOnNhd Complex (fun w => localMultiplier eta P x w z) {w : Complex | 9/10 < w.re} := by
  have hQ : 4 <= (Ideal.absNorm P.val : Real) := by exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < (Ideal.absNorm P.val : Real) := by linarith
  have hn : Not ((Ideal.absNorm P.val : Complex)=0) := by exact_mod_cast hQ0.ne'
  have hd := principal_region_denominators (Ideal.absNorm P.val)
    (actualAPhase eta (primaryGenerator P.val)) (idealCoeff eta P.val) 1 x z hQ
    (actualAPhase_norm_le_one eta _) (idealCoeff_norm_le_one eta _) (by simp) hx hz
  have hc := unramifiedClosed_principal_analytic_w (Ideal.absNorm P.val)
    (actualAPhase eta (primaryGenerator P.val)) (idealCoeff eta P.val) 1 x z hQ
    (actualAPhase_norm_le_one eta _) (idealCoeff_norm_le_one eta _) (by simp) hx hz
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro w hw
  have hmc := principal_marked_differentiableAt_w eta P x w z hQ hx hz
  have hcc : DifferentiableAt Complex (fun w => idealClosedCorrection eta P x w z) w :=
    (hc w hw).differentiableAt
  have hh := idealClosedCorrection_principal_ne_zero eta S hS P hP x w z hx hw.le hz
  have hcw := coordW_differentiable (Ideal.absNorm P.val) hQ0 1
  apply DifferentiableAt.differentiableWithinAt
  unfold localMultiplier compensatedReplacement
  dsimp only
  fun_prop (disch := first | assumption | exact hd.2.2 | exact Or.inl hn)

theorem principal_local_analytic_z (eta : Character) (S : Finset Id) (hS : PrincipalCorrectionTail S)
    (P : PrimeIdeal) (hP : Not (Membership.mem S P.val)) (x w : Complex)
    (hx : 3/4 <= x.re) (hw : 9/10 <= w.re) :
    AnalyticOnNhd Complex (fun z => localMultiplier eta P x w z) {z : Complex | 4/25 < z.re} := by
  have hQ : 4 <= (Ideal.absNorm P.val : Real) := by exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < (Ideal.absNorm P.val : Real) := by linarith
  have hn : Not ((Ideal.absNorm P.val : Complex)=0) := by exact_mod_cast hQ0.ne'
  have hc := unramifiedClosed_principal_analytic_z (Ideal.absNorm P.val)
    (actualAPhase eta (primaryGenerator P.val)) (idealCoeff eta P.val) 1 x w hQ
    (actualAPhase_norm_le_one eta _) (idealCoeff_norm_le_one eta _) (by simp) hx
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro z hz
  have hd := principal_region_denominators (Ideal.absNorm P.val)
    (actualAPhase eta (primaryGenerator P.val)) (idealCoeff eta P.val) 1 x z hQ
    (actualAPhase_norm_le_one eta _) (idealCoeff_norm_le_one eta _) (by simp) hx hz.le
  have hmc := principal_marked_differentiableAt_z eta P x w z hQ hx hz.le
  have hcc : DifferentiableAt Complex (fun z => idealClosedCorrection eta P x w z) z :=
    (hc z hz).differentiableAt
  have hh := idealClosedCorrection_principal_ne_zero eta S hS P hP x w z hx hw hz.le
  have hcv := coordV_differentiable (Ideal.absNorm P.val) hQ0
  apply DifferentiableAt.differentiableWithinAt
  unfold localMultiplier compensatedReplacement
  dsimp only
  fun_prop (disch := first | assumption | exact hd.2.2 | exact Or.inl hn)


theorem principal_slot_analytic_w {iota : Type*} (eta : Character) (S : Finset Id)
    (hS : PrincipalCorrectionTail S) (J : Finset iota) (T : iota->Finset PrimeIdeal)
    (b : iota->PrimeIdeal->Complex)
    (hT : forall j, Membership.mem J j -> forall P, Membership.mem (T j) P ->
      Not (Membership.mem S P.val))
    (x z : Complex) (hx : (3/4:Real)<=x.re) (hz : (4/25:Real)<=z.re) :
    AnalyticOnNhd Complex (fun w=>slotMultiplier eta J T b x w z)
      {w : Complex | (9/10:Real)<w.re} := by
  apply J.analyticOnNhd_fun_prod
  intro j hj
  apply (T j).analyticOnNhd_fun_sum
  intro P hp
  exact analyticOnNhd_const.mul
    (principal_local_analytic_w eta S hS P (hT j hj P hp) x z hx hz)

theorem principal_slot_analytic_z {iota : Type*} (eta : Character) (S : Finset Id)
    (hS : PrincipalCorrectionTail S) (J : Finset iota) (T : iota->Finset PrimeIdeal)
    (b : iota->PrimeIdeal->Complex)
    (hT : forall j, Membership.mem J j -> forall P, Membership.mem (T j) P ->
      Not (Membership.mem S P.val))
    (x w : Complex) (hx : (3/4:Real)<=x.re) (hw : (9/10:Real)<=w.re) :
    AnalyticOnNhd Complex (fun z=>slotMultiplier eta J T b x w z)
      {z : Complex | (4/25:Real)<z.re} := by
  apply J.analyticOnNhd_fun_prod
  intro j hj
  apply (T j).analyticOnNhd_fun_sum
  intro P hp
  exact analyticOnNhd_const.mul
    (principal_local_analytic_z eta S hS P (hT j hj P hp) x w hx hw)

theorem principal_combined_slot_analytic_w {iota : Type*} (eta : Character)
    (S : Finset Id) (hS : PrincipalCorrectionTail S) (J : Finset iota)
    (T : iota->Finset PrimeIdeal) (b : iota->PrimeIdeal->Complex)
    (hT : forall j, Membership.mem J j -> forall P, Membership.mem (T j) P ->
      Not (Membership.mem S P.val))
    (x z : Complex) (hx : (3/4:Real)<=x.re) (hz : (4/25:Real)<=z.re) :
    AnalyticOnNhd Complex (fun w=>globalClosedCorrection eta S x w z*
      slotMultiplier eta J T b x w z) {w : Complex | (9/10:Real)<w.re} :=
  (globalClosedCorrection_principal_analytic_w eta S hS x z hx hz).mul
    (principal_slot_analytic_w eta S hS J T b hT x z hx hz)

theorem principal_combined_slot_analytic_z {iota : Type*} (eta : Character)
    (S : Finset Id) (hS : PrincipalCorrectionTail S) (J : Finset iota)
    (T : iota->Finset PrimeIdeal) (b : iota->PrimeIdeal->Complex)
    (hT : forall j, Membership.mem J j -> forall P, Membership.mem (T j) P ->
      Not (Membership.mem S P.val))
    (x w : Complex) (hx : (3/4:Real)<=x.re) (hw : (9/10:Real)<=w.re) :
    AnalyticOnNhd Complex (fun z=>globalClosedCorrection eta S x w z*
      slotMultiplier eta J T b x w z) {z : Complex | (4/25:Real)<z.re} :=
  (globalClosedCorrection_principal_analytic_z eta S hS x w hx hw).mul
    (principal_slot_analytic_z eta S hS J T b hT x w hx hw)

end PrimeFactorOscillations.GeneralPrincipalRegion

