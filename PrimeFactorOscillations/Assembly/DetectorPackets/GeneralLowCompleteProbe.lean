/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Detector.LowCommonBound
import PrimeFactorOscillations.Assembly.DetectorPackets.GeneralLowGaussianEnergy

/-!
# GeneralLowCompleteProbe

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
# The full variable-geometry compensated probe

The actual central bound is completed with remote dyads and all subset sums.
Tuple count and physical scale costs cancel before Gaussian decay is applied.
The complete physical probe and original ray pools keep the new exponent.
This is an unconditional probe input, not a zero-free theorem.
-/


noncomputable section
namespace PrimeFactorOscillations.GeneralLowGeometry
open scoped Classical SchwartzMap
open OAI OAI.SevenEighths
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic
open CanonicalQuadraticSieve InverseTerminalWidths InverseMoment InverseReflectedPhase
open CanonicalRowCompletion RayFourExpansion OAI.SevenEighths.ProbePhysical
local notation "Eis" => ActualEisensteinCubic.O
local notation "Id" => Ideal Eis
local instance : Fintype (Units Eis) :=
  @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

theorem canonicalTuple_count_general {K : Nat} (ell : Fin K->Real)
    (hell : forall i, 0<=ell i) (Lambda : Real) (hsum : (Finset.univ.sum ell)<=Lambda)
    (b Z : Real) (hZ : 1<=Z) (T : Fin K->Finset PrimeIdeal)
    (hT : forall i P, Membership.mem (T i) P -> Supported P.val)
    (hnorm : forall i P, Membership.mem (T i) P -> (Ideal.absNorm P.val:Real)<=b*Z^(ell i)) :
    (Fintype.card (forall i,canonicalSlotSupport (T i)):Real)<=(128*max 1 b)^K*Z^Lambda := by
  have hterms (i : Fin K) : (Fintype.card (canonicalSlotSupport (T i)):Real)<=
      128*(max 1 b*Z^(ell i)) := by
    simp only [Fintype.card_coe]
    apply canonicalSlot_count _ (hT i) _
      (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (Real.one_le_rpow hZ (hell i)))
    intro P hP
    exact (hnorm i P hP).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  rw [Fintype.card_pi,Nat.cast_prod]
  calc
    _ <= Finset.univ.prod (fun i=>128*(max 1 b*Z^(ell i))) := by
      gcongr <;> first | (intro i hi; exact Nat.cast_nonneg _) | exact hterms _
    _ = (128*max 1 b)^K*Z^(Finset.univ.sum ell) := by
      simp_rw [<-mul_assoc]
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
        <-Real.rpow_sum_of_pos (lt_of_lt_of_le zero_lt_one hZ)]
    _ <= _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ hsum) (by positivity)

theorem compensation_scale_mass_bound_general {K : Nat}
    (eta : HeckeFamily.Character) (C : CalibrationData)
    (ell : Fin K->Real) (hell : forall i, 0<=ell i) (Lambda lx ly : Real)
    (hsum : (Finset.univ.sum ell)<=Lambda) (hgeom : lx+ly=1-Lambda)
    (b Z : Real) (hZ : 1<=Z) (T : Fin K->Finset PrimeIdeal)
    (hT : forall i P, Membership.mem (T i) P -> Supported P.val)
    (hnorm : forall i P, Membership.mem (T i) P -> (Ideal.absNorm P.val:Real)<=b*Z^(ell i))
    (J : Finset (Fin K)) (W : Fin K->Real->Complex) (hW : forall i x, norm (W i x)<=1) :
    gaussianPhysicalScaleMass C (Finset.univ : Finset (forall i,canonicalSlotSupport (T i)))
      (fun p=>compensationSubsetWeight eta W (fun i=>Z^(ell i)) (fun i=>(p i).val) J)
      (fun p=>Z^lx/elementNorm (slotProduct (fun i=>(p i).val) J))
      (fun p=>Z^ly/elementNorm (slotProduct (fun i=>(p i).val) J))
      (fun i : SelectedSlot J=>W i.val)
      (fun p i=>elementNorm (p i.val).val/Z^(ell i.val))<=
        (elementNorm C.generator*(128*max 1 b)^K)*Z := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hp (p : forall i,canonicalSlotSupport (T i)) (i : Fin K) : Not ((p i).val=0) :=
    canonicalSlotSupport_nonzero _ (hT i) _ (p i).property
  have hterm (p : forall i,canonicalSlotSupport (T i)) :
      norm (compensationSubsetWeight eta W (fun i=>Z^(ell i)) (fun i=>(p i).val) J)*
        (Finset.univ.prod fun i : SelectedSlot J=>
          norm (W i.val (elementNorm (p i.val).val/Z^(ell i.val))))*
        lowPhysicalScale C (Z^lx/elementNorm (slotProduct (fun i=>(p i).val) J))
          (Z^ly/elementNorm (slotProduct (fun i=>(p i).val) J))<=
      elementNorm C.generator*Z^(1-Lambda) := by
    have hselected : (Finset.univ.prod fun i : SelectedSlot J=>
        norm (W i.val (elementNorm (p i.val).val/Z^(ell i.val))))<=1 := by
      calc
        _ <= Finset.univ.prod (fun _i : SelectedSlot J=>(1:Real)) := by
          gcongr <;> first | (intro i hi; exact norm_nonneg _) | exact hW _ _
        _ = 1 := by simp
    have hcoeff : norm (compensationSubsetWeight eta W (fun i=>Z^(ell i))
        (fun i=>(p i).val) J)*
        (Finset.univ.prod fun i : SelectedSlot J=>
          norm (W i.val (elementNorm (p i.val).val/Z^(ell i.val))))<=1 :=
      (mul_le_of_le_one_left (Finset.prod_nonneg (fun _ _=>norm_nonneg _))
        (compensationSubsetWeight_norm_le_one eta W hW _ _ (hp p) J)).trans hselected
    have hL := slotProduct_norm_ge_one _ (hp p) J
    have hLsq : 1<=(elementNorm (slotProduct (fun i=>(p i).val) J))^2 := by
      simpa only [pow_two] using one_le_mul_of_one_le_of_one_le hL hL
    rw [lowPhysicalScale_source_general C Z _ lx ly (1-Lambda) hz hgeom]
    apply (mul_le_of_le_one_left (by unfold elementNorm;positivity) hcoeff).trans
    exact div_le_self (by unfold elementNorm;positivity) hLsq
  unfold gaussianPhysicalScaleMass
  apply (Finset.sum_le_sum (fun p _=>hterm p)).trans
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hc := mul_le_mul_of_nonneg_right
    (canonicalTuple_count_general ell hell Lambda hsum b Z hZ T hT hnorm)
    (show 0<=elementNorm C.generator*Z^(1-Lambda) by unfold elementNorm;positivity)
  apply hc.trans_eq
  calc
    _ = (elementNorm C.generator*(128*max 1 b)^K)*(Z^Lambda*Z^(1-Lambda)) := by ring
    _ = _ := by rw [<-Real.rpow_add hz,show Lambda+(1-Lambda)=1 by ring,Real.rpow_one]

theorem eventually_low_physical_scales_general {K : Nat}
    (ell : Fin K->Real) (hell : forall i, 0<=ell i) (b : Real) :
    Filter.Eventually (fun Z : Real=>1<Z /\
      forall Lambda : Real, 0<=Lambda -> Lambda<=1/5 -> (Finset.univ.sum ell)<=Lambda ->
      forall slots : Fin K->Finset Eis,
      (forall i x, Membership.mem (slots i) x -> Not (x=0)) ->
      (forall i x, Membership.mem (slots i) x -> elementNorm x<=b*Z^(ell i)) ->
      forall (J : Finset (Fin K)) (p : forall i,slots i),
        1<=Z^(7/16-Lambda/2)/elementNorm (slotProduct (fun i=>(p i).val) J) /\
        1<=Z^(9/16-Lambda/2)/elementNorm (slotProduct (fun i=>(p i).val) J)) Filter.atTop := by
  let B := (max 1 b)^K
  have hB : 0<B := by dsimp [B];positivity
  filter_upwards [Filter.eventually_gt_atTop (1:Real),
    (tendsto_rpow_atTop (show (0:Real)<1/8 by norm_num)).eventually
      (Filter.eventually_ge_atTop B)] with Z hZ hc
  refine And.intro hZ ?_
  intro Lambda hLambda0 hLambda1 hsum slots hn hnorm J p
  have hz : 0<Z := lt_trans zero_lt_one hZ
  have hl : 0<elementNorm (slotProduct (fun i=>(p i).val) J) :=
    slotProduct_norm_pos _ (fun i=>hn i _ (p i).property) J
  have hb := lowUnselectedProduct_norm_upper_nominal ell b Z hz slots hnorm J
    (fun i=>p i.val)
  rw [<-slotProduct_subtype (fun i=>(p i).val) J] at hb
  have hlength := lowLength_bounds_general ell hell Lambda hsum J
  have hcap : elementNorm (slotProduct (fun i=>(p i).val) J)<=B*Z^Lambda :=
    hb.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.le hlength.2.1) hB.le)
  have hLX : elementNorm (slotProduct (fun i=>(p i).val) J)<=Z^(7/16-Lambda/2) := by
    apply hcap.trans
    calc
      _ <= Z^(1/8:Real)*Z^Lambda :=
        mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hz.le _)
      _ = Z^((1/8:Real)+Lambda) := (Real.rpow_add hz _ _).symm
      _ <= _ := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  exact And.intro ((one_le_div hl).mpr hLX)
    ((one_le_div hl).mpr (hLX.trans
      (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))))

theorem low_remote_power_general (Z ell eps : Real) (N : Nat) (hZ : 1<=Z)
    (hell : ell<=1/5) (hN : (22/5:Real)<=(eps/2)*(N:Real)) :
    Z*(Z^(1+ell))^2/(Z^(eps/2))^N<=Z^(-1:Real) := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hsq : (Z^(1+ell))^2=Z^(2*(1+ell)) := by
    rw [<-Real.rpow_natCast,<-Real.rpow_mul hz.le]
    congr 1
    push_cast
    ring
  have hn : (Z^(eps/2))^N=Z^((eps/2)*(N:Real)) := by
    rw [<-Real.rpow_natCast,<-Real.rpow_mul hz.le]
  rw [hsq,hn,show Z*Z^(2*(1+ell))=Z^(1+2*(1+ell)) by rw [Real.rpow_add hz,Real.rpow_one],
    <-Real.rpow_sub hz]
  exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

theorem low_remote_gaussian_dyads_general (S : Finset Id)
    (hS : forall P, Membership.mem S P -> P.IsMaximal)
    {K : Nat} (ell : Fin K->Real) (hell : forall i, 0<=ell i)
    (b eps : Real) (heps : 0<eps) (V : SchwartzMap Real Complex)
    (hV : HasCompactSupport (V:Real->Complex))
    (W0 W1 : Real->Complex) (a0 b0 a1 b1 B0 B1 : Real) (ha0 : 0<a0) (ha1 : 0<a1)
    (hB0 : 0<=B0) (hB1 : 0<=B1)
    (hW0 : Set.Subset (Function.support W0) (Set.Icc a0 b0))
    (hW1 : Set.Subset (Function.support W1) (Set.Icc a1 b1))
    (hWB0 : forall x, norm (W0 x)<=B0) (hWB1 : forall x, norm (W1 x)<=B1) :
    Exists fun C : Real=>0<C /\
    Filter.Eventually (fun Z : Real=>1<Z /\
      forall Lambda : Real, 0<=Lambda -> Lambda<=1/5 -> (Finset.univ.sum ell)<=Lambda ->
      forall (eta : HeckeFamily.Character) (T : Fin K->Finset PrimeIdeal),
      (forall i P, Membership.mem (T i) P -> Supported P.val) ->
      (forall i P, Membership.mem (T i) P -> (Ideal.absNorm P.val:Real)<=b*Z^(ell i)) ->
      forall (J : Finset (Fin K)) (W : Fin K->Real->Complex),
      (forall i x, norm (W i x)<=1) ->
      let f := fun j : Nat=>if lowRemote Z (lowSelectedLength ell J) eps ((2:Real)^j) then
        norm (lowCommonDyad eta (calibrationForSet S hS) W0 W1
          (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(ell i)) J
          (Z^(7/16-Lambda/2)) (Z^(9/16-Lambda/2)) ((2:Real)^j)
          (Z^(1+lowSelectedLength ell J)) V hV) else 0
      Summable f /\ tsum f<=C*Z^(-1:Real)) Filter.atTop := by
  have hep : 0<eps/2 := by linarith
  have hNexists := exists_nat_gt ((22/5:Real)/(eps/2))
  choose N hN using hNexists
  have hN' : (22/5:Real)<=(eps/2)*(N:Real) := by
    have hh := mul_lt_mul_of_pos_right hN hep
    have heq : ((22/5:Real)/(eps/2))*(eps/2)=(22/5:Real) := by
      field_simp [ne_of_gt heps]
    rw [heq] at hh
    nlinarith
  have hg := gaussianPhysicalFamily_remote_polynomial V hV N
    a0 b0 a1 b1 B0 B1 ha0 ha1 hB0 hB1
  choose Cg hCg he using hg
  let q := elementNorm (calibrationForSet S hS).generator
  let C0 := Cg*(q*(128*max 1 b)^K)
  have hq : 0<q := calibration_elementNorm_pos _
  refine Exists.intro C0 (And.intro (by dsimp [C0];positivity) ?_)
  filter_upwards [eventually_low_physical_scales_general ell hell b] with Z hZ
  refine And.intro hZ.1 ?_
  intro Lambda hLambda0 hLambda1 hsum eta T hT hnorm J W hW
  dsimp only [lowRemote]
  have hz : 0<Z := lt_trans zero_lt_one hZ.1
  have hslots : forall i n, Membership.mem (canonicalSlotSupport (T i)) n -> Not (n=0) :=
    fun i=>canonicalSlotSupport_nonzero _ (hT i)
  have hnormE : forall i n, Membership.mem (canonicalSlotSupport (T i)) n ->
      elementNorm n<=b*Z^(ell i) := by
    intro i n hn
    cases Finset.mem_image.mp hn with
    | intro P hP =>
      cases hP with
      | intro hPT heq =>
        subst n
        rw [primaryTuple_norm P (hT i P hPT)]
        exact hnorm i P hPT
  have hs := hZ.2 Lambda hLambda0 hLambda1 hsum _ hslots hnormE J
  have hh := he eta S hS W0 W1
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW0)
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1)
    hW0 hW1 hWB0 hWB1 (Finset.univ : Finset (forall i,canonicalSlotSupport (T i)))
    (fun p=>compensationSubsetWeight eta W (fun i=>Z^(ell i)) (fun i=>(p i).val) J)
    (fun p=>Ideal.span {slotProduct (fun i=>(p i).val)
      (SDiff.sdiff (Finset.univ : Finset (Fin K)) J)})
    (fun p=>Z^(7/16-Lambda/2)/elementNorm (slotProduct (fun i=>(p i).val) J))
    (fun p=>Z^(9/16-Lambda/2)/elementNorm (slotProduct (fun i=>(p i).val) J))
    (fun p _=>(hs p).1) (fun p _=>(hs p).2)
    (fun i : SelectedSlot J=>W i.val) (fun p i=>elementNorm (p i.val).val/Z^(ell i.val))
    (Z^(1+lowSelectedLength ell J)) (Z^(eps/2)) (by positivity) (Real.one_le_rpow hZ.1.le hep.le)
  simp only [<-lowCommonDyad_eq_family] at hh
  refine And.intro ?_ ?_
  . convert hh.1 using 1
    funext j
    split_ifs with h <;> simp_all only [ite_true,ite_false]
  . have hhFinal := hh.2.trans (show _<=C0*Z^(-1:Real) from by
      have hm := compensation_scale_mass_bound_general eta (calibrationForSet S hS)
        ell hell Lambda (7/16-Lambda/2) (9/16-Lambda/2) hsum (by ring)
        b Z hZ.1.le T hT hnorm J W hW
      calc
        _ <= Cg*((q*(128*max 1 b)^K)*Z)*(Z^(1+lowSelectedLength ell J))^2/(Z^(eps/2))^N := by
          gcongr
        _ = C0*(Z*(Z^(1+lowSelectedLength ell J))^2/(Z^(eps/2))^N) := by
          dsimp [C0]
          ring
        _ <= _ := mul_le_mul_of_nonneg_left
          (low_remote_power_general Z (lowSelectedLength ell J) eps N hZ.1.le
            (by
              have hl := lowLength_bounds_general ell hell Lambda hsum J
              linarith [hl.1,hl.2.2.2]) hN') (by dsimp [C0];positivity))
    convert hhFinal using 1
    apply tsum_congr
    intro j
    split_ifs with h <;> simp_all only [ite_true,ite_false]

theorem low_all_gaussian_dyads_general (eta : HeckeFamily.Character) (S : Finset Id)
    (hS : forall P, Membership.mem S P -> P.IsMaximal) (hbad : fixedBadPrimes<=S)
    {K : Nat} (ell : Fin K->Real) (hell : forall i, 0<=ell i)
    (a b eps : Real) (ha : 0<a) (heps : 0<eps) (heps1 : eps<1)
    (V : SchwartzMap Real Complex) (hV : HasCompactSupport (V:Real->Complex))
    (W0 W1 : Real->Complex) (a0 b0 a1 b1 B0 B1 : Real) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hB0 : 0<=B0) (hB1 : 0<=B1)
    (hW0 : Set.Subset (Function.support W0) (Set.Icc a0 b0))
    (hW1 : Set.Subset (Function.support W1) (Set.Icc a1 b1))
    (hW0s : ContDiff Real ((Top.top : ENat) : WithTop ENat) W0)
    (hW1s : ContDiff Real ((Top.top : ENat) : WithTop ENat) W1)
    (hWB0 : forall x, norm (W0 x)<=B0) (hWB1 : forall x, norm (W1 x)<=B1) :
    Exists fun C : Real=>0<C /\
    Filter.Eventually (fun Z : Real=>1<Z /\
      forall Lambda : Real, 0<=Lambda -> Lambda<=1/5 -> (Finset.univ.sum ell)<=Lambda ->
      forall T : Fin K->Finset PrimeIdeal,
      (forall i P, Membership.mem (T i) P -> Supported P.val) ->
      (forall i P, Membership.mem (T i) P -> Not (Membership.mem S P.val)) ->
      Pairwise (fun i j=>Disjoint (T i) (T j)) ->
      (forall i P, Membership.mem (T i) P ->
        a*Z^(ell i)<=(Ideal.absNorm P.val:Real) /\ (Ideal.absNorm P.val:Real)<=b*Z^(ell i)) ->
      forall (J : Finset (Fin K)) (W : Fin K->Real->Complex),
      (forall i x, norm (W i x)<=1) ->
      let f := fun j : Nat=>lowCommonDyad eta (calibrationForSet S hS) W0 W1
        (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(ell i)) J
        (Z^(7/16-Lambda/2)) (Z^(9/16-Lambda/2)) ((2:Real)^j)
        (Z^(1+lowSelectedLength ell J)) V hV
      Summable f /\ norm (tsum f)<=C*Z^(11/48-Lambda/4+256*eps)) Filter.atTop := by
  have hcb := low_central_gaussian_dyads_general eta S hS hbad ell hell a b eps ha heps heps1
    W0 W1 a0 b0 a1 b1 B1 ha0 ha1 hab1 hB1 hW0 hW1 hW0s hW1s hWB1 V hV
  choose Cc hCc hcentral using hcb
  have hrb := low_remote_gaussian_dyads_general S hS ell hell b eps heps V hV
    W0 W1 a0 b0 a1 b1 B0 B1 ha0 ha1 hB0 hB1 hW0 hW1 hWB0 hWB1
  choose Cr hCr hremote using hrb
  refine Exists.intro (Cc+Cr) (And.intro (add_pos hCc hCr) ?_)
  filter_upwards [hcentral,hremote] with Z hc hr
  refine And.intro hc.1 ?_
  intro Lambda hLambda0 hLambda1 hsum T hT hout hdis hnorm J W hW
  have hc' := hc.2 Lambda hLambda0 hLambda1 hsum T hT hout hdis hnorm J W hW
  have hr' := hr.2 Lambda hLambda0 hLambda1 hsum eta T hT (fun i P hP=>(hnorm i P hP).2) J W hW
  dsimp only at hc' hr'
  dsimp only
  have hh := low_dyad_norm_split _
    (fun j=>lowRemote Z (lowSelectedLength ell J) eps ((2:Real)^j)) hc'.1 hr'.1
  refine And.intro hh.1 (hh.2.trans ?_)
  have hp : Z^(-1:Real)<=Z^(11/48-Lambda/4+256*eps) :=
    Real.rpow_le_rpow_of_exponent_le hc.1.le (by linarith)
  calc
    _ <= Cc*Z^(11/48-Lambda/4+256*eps)+Cr*Z^(-1:Real) := add_le_add hc'.2 hr'.2
    _ <= Cc*Z^(11/48-Lambda/4+256*eps)+Cr*Z^(11/48-Lambda/4+256*eps) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hp hCr.le)
    _ = _ := by ring

theorem compensatedPhysicalProbe_low_general (eta : HeckeFamily.Character) (S : Finset Id)
    (hS : forall P, Membership.mem S P -> P.IsMaximal) (hbad : fixedBadPrimes<=S)
    {K : Nat} (ell : Fin K->Real) (hell : forall i, 0<=ell i)
    (a b eps : Real) (ha : 0<a) (heps : 0<eps) (heps1 : eps<1)
    (W : Fin K->Real->Complex)
    (hW : forall i, Set.Subset (Function.support (W i)) (Set.Icc a b))
    (hWnorm : forall i x, norm (W i x)<=1)
    (W0 W1 : Real->Complex) (a0 b0 a1 b1 B0 B1 : Real) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hB0 : 0<=B0) (hB1 : 0<=B1)
    (hW0 : Set.Subset (Function.support W0) (Set.Icc a0 b0))
    (hW1 : Set.Subset (Function.support W1) (Set.Icc a1 b1))
    (hW0s : ContDiff Real ((Top.top : ENat) : WithTop ENat) W0)
    (hW1s : ContDiff Real ((Top.top : ENat) : WithTop ENat) W1)
    (hWB0 : forall x, norm (W0 x)<=B0) (hWB1 : forall x, norm (W1 x)<=B1) :
    Exists fun C : Real=>0<C /\
    Filter.Eventually (fun Z : Real=>1<Z /\
      forall Lambda : Real, 0<=Lambda -> Lambda<=1/5 -> (Finset.univ.sum ell)<=Lambda ->
      forall T : Fin K->Finset PrimeIdeal,
      (forall i P, Membership.mem (T i) P -> Supported P.val) ->
      (forall i P, Membership.mem (T i) P -> Not (Membership.mem S P.val)) ->
      Pairwise (fun i j=>Disjoint (T i) (T j)) ->
      (forall i P, Membership.mem (T i) P ->
        a*Z^(ell i)<=(Ideal.absNorm P.val:Real) /\ (Ideal.absNorm P.val:Real)<=b*Z^(ell i)) ->
      norm (compensatedPhysicalProbe eta (calibrationForSet S hS) W0 W1
        (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(ell i))
        (Z^(7/16-Lambda/2)) (Z^(9/16-Lambda/2)) Z)<=
          C*Z^(11/48-Lambda/4+256*eps)) Filter.atTop := by
  have hgauss := compensatedPhysicalProbe_common_gaussian W
    (fun _=>abs (Real.log a)+abs (Real.log b)) (fun _=>by positivity)
    (fun i=>low_window_log_support (W i) a b ha (hW i))
  choose V hV hbudget hidentity using hgauss
  have hb := fun A : Finset (Fin K)=>low_all_gaussian_dyads_general eta S hS hbad ell hell
    a b eps ha heps heps1 (V A) (hV A) W0 W1 a0 b0 a1 b1 B0 B1 ha0 ha1 hab1 hB0 hB1
    hW0 hW1 hW0s hW1s hWB0 hWB1
  choose C hC he using hb
  let C0 := ((Finset.univ : Finset (Fin K)).powerset.sum fun A=>C A)+1
  have hC0 : 0<C0 := by
    have hn := Finset.sum_nonneg
      (fun A (_ : Membership.mem (Finset.univ : Finset (Fin K)).powerset A)=>(hC A).le)
    dsimp only [C0]
    linarith
  refine Exists.intro C0 (And.intro hC0 ?_)
  filter_upwards [Filter.eventually_all.mpr he] with Z hZ
  have hz1 : 1<Z := (hZ (Finset.empty : Finset (Fin K))).1
  have hz : 0<Z := lt_trans zero_lt_one hz1
  refine And.intro hz1 ?_
  intro Lambda hLambda0 hLambda1 hsum T hT hout hdis hnorm
  have hslots : forall i n, Membership.mem (canonicalSlotSupport (T i)) n -> Not (n=0) :=
    fun i=>canonicalSlotSupport_nonzero _ (hT i)
  rw [hidentity eta (calibrationForSet S hS) W0 W1
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW0)
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1)
    _ hslots (fun i=>Z^(ell i)) (fun i=>by positivity)
    (Z^(7/16-Lambda/2)) (Z^(9/16-Lambda/2)) Z (by positivity) (by positivity) hz]
  apply (norm_sum_le _ _).trans
  have hterm (A : Finset (Fin K)) :
      norm (tsum fun j : Nat=>lowCommonDyad eta (calibrationForSet S hS) W0 W1
        (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(ell i)) A
        (Z^(7/16-Lambda/2)) (Z^(9/16-Lambda/2)) ((2:Real)^j)
        (Z*((SDiff.sdiff (Finset.univ : Finset (Fin K)) A).prod fun i=>Z^(ell i))) (V A) (hV A))<=
        C A*Z^(11/48-Lambda/4+256*eps) := by
    have hc : Z*((SDiff.sdiff (Finset.univ : Finset (Fin K)) A).prod fun i=>Z^(ell i))=
        Z^(1+lowSelectedLength ell A) := by
      rw [lowSelectedScale_product ell A Z hz,Real.rpow_add hz,Real.rpow_one]
    rw [hc]
    exact ((hZ A).2 Lambda hLambda0 hLambda1 hsum T hT hout hdis hnorm A W hWnorm).2
  have hh := Finset.sum_le_sum
    (fun A (_ : Membership.mem (Finset.univ : Finset (Fin K)).powerset A)=>hterm A)
  apply hh.trans
  rw [<-Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (by dsimp [C0];linarith) (Real.rpow_nonneg hz.le _)

theorem original_ray_compensatedPhysicalProbe_low_general (eta : HeckeFamily.Character)
    (S : Finset Id) (hS : SourceExclusions S) (hmax : forall P, Membership.mem S P -> P.IsMaximal)
    {K : Nat} (ell : Fin K->Real) (hell : forall i, 0<=ell i) (hinj : Function.Injective ell)
    (R : Set Id) (a b eps : Real) (ha : 0<a) (hab : a<=b) (heps : 0<eps) (heps1 : eps<1)
    (W : Fin K->Real->Complex)
    (hW : forall i, Set.Subset (Function.support (W i)) (Set.Icc a b))
    (hWnorm : forall i x, norm (W i x)<=1)
    (W0 W1 : Real->Complex) (a0 b0 a1 b1 B0 B1 : Real) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hB0 : 0<=B0) (hB1 : 0<=B1)
    (hW0 : Set.Subset (Function.support W0) (Set.Icc a0 b0))
    (hW1 : Set.Subset (Function.support W1) (Set.Icc a1 b1))
    (hW0s : ContDiff Real ((Top.top : ENat) : WithTop ENat) W0)
    (hW1s : ContDiff Real ((Top.top : ENat) : WithTop ENat) W1)
    (hWB0 : forall x, norm (W0 x)<=B0) (hWB1 : forall x, norm (W1 x)<=B1) :
    Exists fun C : Real=>0<C /\
    Filter.Eventually (fun Z : Real=>
      forall Lambda : Real, 0<=Lambda -> Lambda<=1/5 -> (Finset.univ.sum ell)<=Lambda ->
      norm (compensatedPhysicalProbe eta (calibrationForSet S hmax) W0 W1
        (fun i=>canonicalSlotSupport (ProbeRaySlots.pool R S a b (Z^(ell i)))) W (fun i=>Z^(ell i))
        (Z^(7/16-Lambda/2)) (Z^(9/16-Lambda/2)) Z)<=
          C*Z^(11/48-Lambda/4+256*eps)) Filter.atTop := by
  have hb := compensatedPhysicalProbe_low_general eta S hmax hS.bad ell hell
    a b eps ha heps heps1 W hW hWnorm W0 W1 a0 b0 a1 b1 B0 B1 ha0 ha1 hab1 hB0 hB1
    hW0 hW1 hW0s hW1s hWB0 hWB1
  choose C hC he using hb
  refine Exists.intro C (And.intro hC ?_)
  filter_upwards [he,ProbeRaySlots.power_pools_eventually_disjoint R S (fun _=>a) (fun _=>b) ell
    (fun _=>ha) (fun _=>hab) hinj] with Z hZ hd
  intro Lambda hLambda0 hLambda1 hsum
  have hz : 0<Z := lt_trans zero_lt_one hZ.1
  apply hZ.2 Lambda hLambda0 hLambda1 hsum _
    (fun i=>ProbeRaySlots.pool_supported R S hS a b (Z^(ell i)))
    (fun i P hP=>((ProbeRaySlots.mem_pool R S a b (Z^(ell i)) P).mp hP).2.2.2)
    (fun i j hij=>hd i j hij)
  intro i P hP
  have hh := ProbeRaySlots.pool_norm_bounds R S ha.le hab (Real.rpow_pos_of_pos hz _) P hP
  simpa only [mul_comm] using And.intro hh.1.le hh.2

end PrimeFactorOscillations.GeneralLowGeometry

