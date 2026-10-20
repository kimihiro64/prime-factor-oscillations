/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Detector.LowPhysicalInverseBound
import PrimeFactorOscillations.Assembly.DetectorPackets.GeneralLowCompletedEnergy

/-!
# GeneralLowPhysicalEnergy

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
# Variable-geometry physical inverse energy

The actual completed-source estimate is transported to the selected physical
row and normalized using genuine physical exponents with lx+ly=1-Lambda.
Every max excess, phase, exclusion, slot cap and fixed-character cost remains.
This is an unconditional probe input, not a zero-free theorem.
-/


noncomputable section
namespace PrimeFactorOscillations.GeneralLowGeometry
open scoped Classical
open OAI OAI.SevenEighths
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic
open CanonicalQuadraticSieve InverseTerminalWidths InverseMoment InverseReflectedPhase
open CanonicalRowCompletion RayFourExpansion OAI.SevenEighths.ProbePhysical
local notation "Eis" => ActualEisensteinCubic.O
local notation "Id" => Ideal Eis
local instance : Fintype (Units Eis) :=
  @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

theorem low_selected_physical_energy_general (eta : HeckeFamily.Character) (S : Finset Id)
    (hS : forall P, Membership.mem S P -> P.IsMaximal) (hbad : fixedBadPrimes<=S)
    (K : Nat) (Ck eps : Real) (hCk : 0<Ck) (heps : 0<eps) (heps1 : eps<=1) :
    Exists fun degree : Nat => Exists fun C : Real => Exists fun Z0 : Real =>
    0<C /\ 1<Z0 /\
    forall (Z Lambda d ell0 shift : Real),
      Z0<=Z -> 0<=Lambda -> Lambda<=1/5 -> 0<=d -> d<=Lambda ->
      0<=ell0 -> ell0<=Lambda-d+eps -> abs shift<=eps ->
    forall R : Finset Eis,
      (forall z, Membership.mem R z ->
        Not (z=0) /\ elementNorm z<=Ck*Z^(1-Lambda-2*d)) ->
    forall T : Fin K->Finset PrimeIdeal,
      (forall i P, Membership.mem (T i) P -> Supported P.val) ->
      (forall i P, Membership.mem (T i) P -> Not (Membership.mem S P.val)) ->
      Pairwise (fun i j=>Disjoint (T i) (T j)) ->
    forall (J : Finset (Fin K)) (H : SelectedSlot J->Real),
      (forall i, 1<=H i) ->
      (forall i P, Membership.mem (T i.val) P -> (Ideal.absNorm P.val:Real)<=H i) ->
      (Finset.univ.prod H)<=Z^ell0 ->
    forall W : Fin K->Real->Complex, (forall i x, norm (W i x)<=1) ->
    forall (Y : Fin K->Real) (t : Real) (sigma : RayRing),
      (R.sum fun z=>norm (lowSelectedInverseRow Finset.univ
        (lowSelectedWeight eta (fun i=>canonicalSlotSupport (T i)) J W Y t)
        eta S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J)
        (Z^(1+ell0+shift)) t sigma z)^2)<=
        C*(1+norm t)^degree*
          Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+507*eps) := by
  have hb := low_original_completed_energy_general
    (lowReflectionPeriod eta S hS) (lowReflectionPeriod_ne_zero eta S hS)
    (1:Id) squarefree_one (lowReflectionMask eta S hS) (lowReflectionMask_ne_zero eta S hS)
    (lowReflectionMask_bad eta S hS hbad).1 (lowReflectionMask_bad eta S hS hbad).2
    (lowReflectionMask_period eta S hS) (lowReflectionMask_bad_ideals eta S hS hbad)
    (1/2) 2 (by norm_num) gaussianFixedWindow gaussianFixedWindow_support gaussianFixedWindow_contDiff
    Ck eps hCk heps heps1 K
  choose degree C Z0 hC hZ0 he using hb
  let C0 := (lowCorrectionEnergy+1)*((Fintype.card RayCharacter:Real)+1)*6*C
  have hC0 : 0<C0 := by
    have hh := lowCorrectionEnergy_nonneg
    dsimp [C0]
    positivity
  refine Exists.intro degree (Exists.intro C0
    (Exists.intro Z0 (And.intro hC0 (And.intro hZ0 ?_))))
  intro Z Lambda d ell0 shift hZ hLambda0 hLambda1 hd hd1 hell hellcap hshift
    R hR T hT hout hdis J H hH1 hH hprod W hW Y t sigma
  let L := fun i : SelectedSlot J=>lowPrimeIdealList (lowPeriodPrimeList eta S hS (T i.val))
  have hLP (i : SelectedSlot J) : lowPeriodPrimeList eta S hS (T i.val)<=T i.val :=
    Finset.filter_subset _ _
  have hLS (i : SelectedSlot J) :
      forall P, Membership.mem (lowPeriodPrimeList eta S hS (T i.val)) P -> Supported P.val :=
    fun P hP=>hT i.val P (hLP i hP)
  have hlists : Pairwise (fun i j=>Disjoint (L i) (L j)) :=
    lowPrimeIdealList_disjoint _ (lowPeriodPrimeList_disjoint eta S hS _
      (fun i j hij=>hdis (fun h=>hij (Subtype.ext h))))
  have hparents : forall I, Membership.mem (lowIdealRows R) I ->
      Not (I=0) /\ (Ideal.absNorm I:Real)<=Ck*Z^(1-Lambda-2*d) :=
    fun I hI=>And.intro (lowIdealRows_nonzero R (fun z hz=>(hR z hz).1) I hI)
      (lowIdealRows_norm_bound R _ (fun z hz=>(hR z hz).2) I hI)
  have hcard : Fintype.card (SelectedSlot J)<=K := by
    simpa only [Fintype.card_coe,Finset.card_univ,Fintype.card_fin] using
      Finset.card_le_card
        (Finset.subset_univ (SDiff.sdiff (Finset.univ : Finset (Fin K)) J))
  have hrow (chi : RayCharacter) (u : Units Eis) :
      ((lowIdealRows R).sum fun I=>norm (lowActualIdealPolynomial L
        (fun i I=>lowSingleSlotWeight eta (W i.val) (Y i.val) t (primaryGenerator I))
        (rowTwist (physicalRayPeriodicBase eta S hS sigma chi) (lowReflectionMask eta S hS)
          (ConcretePrimeRowBridge.idealGenerator (1:Id))
          (u.val*ConcretePrimeRowBridge.idealGenerator I))
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) (Z^(1+ell0+shift)))^2)<=
        C*(1+norm t)^degree*
          Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+507*eps) := by
    convert he Z Lambda d ell0 shift hZ hLambda0 hLambda1 hd hd1 hell hellcap hshift
      (lowIdealRows R) hparents hcard L H hlists (fun i=>lowPrimeIdealList_maximal _)
      (fun i P hP=>(lowPrimeIdealList_good_odd _ (hLS i) P hP).1)
      (fun i=>lowPrimeIdealList_prime _)
      (fun i P hP=>(lowPrimeIdealList_good_odd _ (hLS i) P hP).2)
      hH1 (fun i=>lowPrimeIdealList_norm _ _ (fun P hP=>hH i P (hLP i hP))) hprod
      (physicalRayPeriodicBase eta S hS sigma chi)
      (lowReflectionPeriod_actual eta S hS sigma chi).2
      (lowReflectionPeriod_actual eta S hS sigma chi).1 u t
      (fun i P=>lowSingleSlotWeight eta (W i.val) (Y i.val) t (primaryGenerator P.val))
      (fun i P=>low_actual_ideal_weight_bound eta (W i.val) (hW i.val) (Y i.val) t P.val)
      using 1
    apply Finset.sum_congr rfl
    intro I hI
    congr 2
    unfold lowActualIdealPolynomial
    congr 1
    ext p
    simp
  apply (lowSelectedInverseRow_actual_reflected_energy eta S hS hbad T hT hout hdis J W Y
    (Z^(1+ell0+shift)) t sigma R (fun z hz=>(hR z hz).1)).trans
  have hh := Finset.sum_le_sum
    (fun chi (_ : Membership.mem (Finset.univ : Finset RayCharacter) chi)=>
      Finset.sum_le_sum (fun u (_ : Membership.mem (Finset.univ : Finset (Units Eis)) u)=>
        hrow chi u))
  have hm := mul_le_mul_of_nonneg_left hh lowCorrectionEnergy_nonneg
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,low_unit_card] at hm
  simp only [Nat.cast_ofNat,Real.norm_eq_abs] at hm
  simp only [Real.norm_eq_abs]
  apply hm.trans
  dsimp [C0]
  have hc0 := lowCorrectionEnergy_nonneg
  have hcount : 0<=(Fintype.card RayCharacter:Real) := Nat.cast_nonneg _
  have hzpos : 0<=Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+507*eps) :=
    Real.rpow_nonneg (le_trans zero_le_one (hZ0.le.trans hZ)) _
  have htpos : 0<=(1+abs t)^degree := by positivity
  calc
    _ = (lowCorrectionEnergy*(Fintype.card RayCharacter:Real)*6*C)*(1+abs t)^degree*
        Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+507*eps) := by ring
    _ <= _ := by gcongr <;> linarith

theorem lowLength_bounds_general {K : Nat} (ell : Fin K->Real)
    (hell : forall i, 0<=ell i) (Lambda : Real)
    (hsum : (Finset.univ.sum ell)<=Lambda) (J : Finset (Fin K)) :
    0<=lowUnselectedLength ell J /\ lowUnselectedLength ell J<=Lambda /\
    0<=lowSelectedLength ell J /\ lowSelectedLength ell J<=Lambda-lowUnselectedLength ell J := by
  have hu : 0<=lowUnselectedLength ell J :=
    Finset.sum_nonneg (fun i _=>hell i)
  have hs : 0<=lowSelectedLength ell J :=
    Finset.sum_nonneg (fun i _=>hell i.val)
  have he := lowLength_sum ell J
  exact And.intro hu (And.intro (by linarith) (And.intro hs (by linarith)))

theorem lowPhysicalScale_source_general (C : CalibrationData) (Z L lx ly M : Real)
    (hZ : 0<Z) (hgeom : lx+ly=M) :
    lowPhysicalScale C (Z^lx/L) (Z^ly/L)=elementNorm C.generator*Z^M/L^2 := by
  unfold lowPhysicalScale
  have he : Z^lx*Z^ly=Z^M := by rw [<-Real.rpow_add hZ,hgeom]
  rw [<-he]
  ring

theorem lowPhysicalScale_nominal_bound_general (C : CalibrationData)
    (Z L c d lx ly M : Real) (hZ : 0<Z) (hc : 0<c)
    (hL : c*Z^d<=L) (hgeom : lx+ly=M) :
    lowPhysicalScale C (Z^lx/L) (Z^ly/L)<=(elementNorm C.generator/c^2)*Z^(M-2*d) := by
  have hl : 0<L := lt_of_lt_of_le (by positivity) hL
  rw [lowPhysicalScale_source_general C Z L lx ly M hZ hgeom]
  have hsq : (c*Z^d)^2<=L^2 := by
    simpa only [pow_two] using
      (mul_le_mul hL hL (by positivity) hl.le)
  calc
    _ <= elementNorm C.generator*Z^M/(c*Z^d)^2 :=
      div_le_div_of_nonneg_left (by unfold elementNorm;positivity) (by positivity) hsq
    _ = _ := by
      have hp : (Z^d)^2=Z^(2*d) := by
        rw [<-Real.rpow_natCast,<-Real.rpow_mul hZ.le]
        congr 1
        push_cast
        ring
      rw [mul_pow,hp,Real.rpow_sub hZ]
      ring

theorem low_inverse_power_cancel_general (Z M d alpha : Real) (hZ : 0<Z) :
    Z^(M-2*d+alpha)*(Z^d)^2/Z^M=Z^alpha := by
  have hp : (Z^d)^2=Z^(2*d) := by
    rw [<-Real.rpow_natCast,<-Real.rpow_mul hZ.le]
    congr 1
    push_cast
    ring
  rw [hp,<-Real.rpow_add hZ,<-Real.rpow_sub hZ]
  congr 1
  ring

theorem low_inverse_sqrt_normalized_general
    (q C B Z L M d alpha H E : Real) (n : Nat)
    (hq : 0<q) (hC : 0<=C) (_hB : 0<=B) (hZ : 0<Z) (hL : 0<L) (hH : 1<=H)
    (hE : 0<=E) (hEL : E<=C*H^n*Z^(M-2*d+alpha)) (hLB : L<=B*Z^d) :
    Real.sqrt E/Real.sqrt (q*Z^M/L^2)<=
      Real.sqrt (C*B^2/q)*H^n*Z^(alpha/2) := by
  have hratio : E/(q*Z^M/L^2)<=(C*B^2/q)*H^n*Z^alpha := by
    calc
      _ <= (C*H^n*Z^(M-2*d+alpha))/(q*Z^M/L^2) :=
        div_le_div_of_nonneg_right hEL (by positivity)
      _ = (C*H^n*Z^(M-2*d+alpha))*L^2/(q*Z^M) := by field_simp
      _ <= (C*H^n*Z^(M-2*d+alpha))*(B*Z^d)^2/(q*Z^M) := by
        gcongr
      _ = (C*B^2/q)*H^n*(Z^(M-2*d+alpha)*(Z^d)^2/Z^M) := by ring
      _ = _ := by rw [low_inverse_power_cancel_general Z M d alpha hZ]
  rw [<-Real.sqrt_div hE]
  apply (Real.sqrt_le_sqrt hratio).trans
  rw [Real.sqrt_mul (by positivity),Real.sqrt_mul (by positivity)]
  have hp : Real.sqrt (Z^alpha)=Z^(alpha/2) := by
    rw [Real.sqrt_eq_rpow,<-Real.rpow_mul hZ.le]
    congr 1
    ring
  rw [hp]
  have hPow (k : Nat) : 1<=H^k := by
    induction k with
    | zero => simp
    | succ k hk =>
      simpa only [pow_succ] using one_le_mul_of_one_le_of_one_le hk hH
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_self_iff.mpr (Or.inr (hPow n))) (by positivity))
    (by positivity)

theorem low_selected_nominal_energy_general (eta : HeckeFamily.Character) (S : Finset Id)
    (hS : forall P, Membership.mem S P -> P.IsMaximal) (hbad : fixedBadPrimes<=S)
    {K : Nat} (ell : Fin K->Real) (hell : forall i, 0<=ell i)
    (Ck b eps : Real) (hCk : 0<Ck) (heps : 0<eps) (heps1 : eps<=1) :
    Exists fun degree : Nat => Exists fun C : Real =>
    0<C /\ Filter.Eventually (fun Z : Real=>1<Z /\
    forall Lambda : Real, 0<=Lambda -> Lambda<=1/5 -> (Finset.univ.sum ell)<=Lambda ->
    forall T : Fin K->Finset PrimeIdeal,
      (forall i P, Membership.mem (T i) P -> Supported P.val) ->
      (forall i P, Membership.mem (T i) P -> Not (Membership.mem S P.val)) ->
      Pairwise (fun i j=>Disjoint (T i) (T j)) ->
      (forall i P, Membership.mem (T i) P -> (Ideal.absNorm P.val:Real)<=b*Z^(ell i)) ->
    forall (J : Finset (Fin K)) (R : Finset Eis),
      (forall z, Membership.mem R z -> Not (z=0) /\
        elementNorm z<=Ck*Z^(1-Lambda-2*lowUnselectedLength ell J)) ->
    forall X : Real, 0<X ->
      Z^(1+lowSelectedLength ell J-eps/2)<=X ->
      X<=Z^(1+lowSelectedLength ell J+eps/2) ->
    forall W : Fin K->Real->Complex, (forall i x, norm (W i x)<=1) ->
    forall (Y : Fin K->Real) (t : Real) (sigma : RayRing),
      (R.sum fun z=>norm (lowSelectedInverseRow Finset.univ
        (lowSelectedWeight eta (fun i=>canonicalSlotSupport (T i)) J W Y t)
        eta S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J) X t sigma z)^2)<=
        C*(1+norm t)^degree*Z^((1-Lambda-2*lowUnselectedLength ell J)+
          max 0 ((5*Lambda+lowUnselectedLength ell J-1)/4)+507*eps)) Filter.atTop := by
  have hb := low_selected_physical_energy_general eta S hS hbad K Ck eps hCk heps heps1
  choose degree C Z0 hC hZ0 he using hb
  refine Exists.intro degree (Exists.intro C (And.intro hC ?_))
  filter_upwards [eventually_low_selected_caps ell hell b eps heps,
    Filter.eventually_ge_atTop Z0] with Z hc hZ
  refine And.intro hc.1 ?_
  intro Lambda hLambda0 hLambda1 hsum T hT hout hdis hnorm J R hR
    X hX hXlo hXhi W hW Y t sigma
  have hl := lowLength_bounds_general ell hell Lambda hsum J
  have hd : 0<=lowUnselectedLength ell J := hl.1
  have hd1 : lowUnselectedLength ell J<=Lambda := hl.2.1
  have hs : 0<=lowSelectedLength ell J := hl.2.2.1
  have hscap : lowSelectedLength ell J<=Lambda-lowUnselectedLength ell J := hl.2.2.2
  have hscale := lowCentralShift_scale Z X (lowSelectedLength ell J+eps/2) hc.1 hX
  rw [<-hscale]
  apply he Z Lambda (lowUnselectedLength ell J) (lowSelectedLength ell J+eps/2)
    (lowCentralShift Z X (lowSelectedLength ell J+eps/2))
    hZ hLambda0 hLambda1 hd hd1 (by linarith) (by linarith)
    (lowCentralShift_bound Z X (lowSelectedLength ell J) eps hc.1 hX heps.le hXlo hXhi)
    R hR T hT hout hdis J (fun i=>max 1 (b*Z^(ell i.val)))
    (fun i=>le_max_left _ _)
    (fun i P hP=>(hnorm i.val P hP).trans (le_max_right _ _))
    (hc.2 J) W hW Y t sigma

theorem low_physical_inverse_normalized_general (eta : HeckeFamily.Character) (S : Finset Id)
    (hS : forall P, Membership.mem S P -> P.IsMaximal) (hbad : fixedBadPrimes<=S)
    {K : Nat} (ell : Fin K->Real) (hell : forall i, 0<=ell i)
    (a b aCut bCut eps : Real) (ha : 0<a) (haCut : 0<aCut) (hbCut : 0<bCut)
    (heps : 0<eps) (heps1 : eps<=1) :
    Exists fun degree : Nat => Exists fun C : Real =>
    0<C /\ Filter.Eventually (fun Z : Real=>1<Z /\
    forall (Lambda lx ly : Real),
      0<=Lambda -> Lambda<=1/5 -> (Finset.univ.sum ell)<=Lambda -> lx+ly=1-Lambda ->
    forall T : Fin K->Finset PrimeIdeal,
      (forall i P, Membership.mem (T i) P -> Supported P.val) ->
      (forall i P, Membership.mem (T i) P -> Not (Membership.mem S P.val)) ->
      Pairwise (fun i j=>Disjoint (T i) (T j)) ->
      (forall i P, Membership.mem (T i) P ->
        a*Z^(ell i)<=(Ideal.absNorm P.val:Real) /\
          (Ideal.absNorm P.val:Real)<=b*Z^(ell i)) ->
    forall (J : Finset (Fin K))
      (p : LowUnselectedTuple (fun i=>canonicalSlotSupport (T i)) J),
    forall X : Real, 0<X ->
      Z^(1+lowSelectedLength ell J-eps/2)<=X ->
      X<=Z^(1+lowSelectedLength ell J+eps/2) ->
    forall W : Fin K->Real->Complex, (forall i x, norm (W i x)<=1) ->
    forall t : Real,
      let L := elementNorm (Finset.univ.prod fun i : J=>(p i).val)
      let Q := lowPhysicalScale (calibrationForSet S hS) (Z^lx/L) (Z^ly/L)
      forall (hX0 : 0<Z^lx/L) (hY0 : 0<Z^ly/L),
      Inv.inv (Real.sqrt Q)/(2*Real.pi)*
        lowInverseMass (calibrationForSet S hS) aCut bCut haCut hbCut
          (Z^lx/L) (Z^ly/L) hX0 hY0
          (lowSelectedInverseRow Finset.univ
            (lowSelectedWeight eta (fun i=>canonicalSlotSupport (T i)) J W
              (fun i=>Z^(ell i)) t)
            eta S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J) X t)<=
        C*(1+norm t)^degree*
          Z^((max 0 ((5*Lambda+lowUnselectedLength ell J-1)/4)+507*eps)/2)) Filter.atTop := by
  let q := elementNorm (calibrationForSet S hS).generator
  let c := (min 1 a)^K
  let B := (max 1 b)^K
  have hq : 0<q := calibration_elementNorm_pos _
  have hc : 0<c := by dsimp [c];positivity
  have hB : 0<B := by dsimp [B];positivity
  let Ck := 2*bCut*(q/c^2)
  have hCk : 0<Ck := by dsimp [Ck];positivity
  have hb := low_selected_nominal_energy_general eta S hS hbad ell hell Ck b eps hCk heps heps1
  choose degree C hC hbound using hb
  let C0 := ((Fintype.card RayRing:Real)+1)*Real.sqrt (C*B^2/q)/(2*Real.pi)
  have hC0 : 0<C0 := by dsimp [C0];positivity
  refine Exists.intro degree (Exists.intro C0 (And.intro hC0 ?_))
  filter_upwards [hbound] with Z hZ
  refine And.intro hZ.1 ?_
  intro Lambda lx ly hLambda0 hLambda1 hsum hgeom T hT hout hdis hnorm J p
    X hX hXlo hXhi W hW t
  dsimp only
  let L := elementNorm (Finset.univ.prod fun i : J=>(p i).val)
  let Q := lowPhysicalScale (calibrationForSet S hS) (Z^lx/L) (Z^ly/L)
  intro hX0 hY0
  have hz : 0<Z := lt_trans zero_lt_one hZ.1
  have hL : 0<L := lowUnselectedProduct_norm_pos _
    (fun i n hn=>canonicalSlotSupport_nonzero _ (hT i) n hn) J p
  have hnormE (i : Fin K) (n : Eis) (hn : Membership.mem (canonicalSlotSupport (T i)) n) :
      a*Z^(ell i)<=elementNorm n /\ elementNorm n<=b*Z^(ell i) := by
    cases Finset.mem_image.mp hn with
    | intro P hP =>
      cases hP with
      | intro hPT heq =>
        subst n
        rw [primaryTuple_norm P (hT i P hPT)]
        exact hnorm i P hPT
  have hLlo : c*Z^(lowUnselectedLength ell J)<=L :=
    lowUnselectedProduct_norm_lower ell a Z ha hz _
      (fun i n hn=>(hnormE i n hn).1) J p
  have hLhi : L<=B*Z^(lowUnselectedLength ell J) :=
    lowUnselectedProduct_norm_upper_nominal ell b Z hz _
      (fun i n hn=>(hnormE i n hn).2) J p
  have hQ : 0<Q := lowPhysicalScale_pos _ _ _ hX0 hY0
  let R := lowNumeratorRows aCut bCut haCut hbCut Q hQ
  let row := lowSelectedInverseRow Finset.univ
    (lowSelectedWeight eta (fun i=>canonicalSlotSupport (T i)) J W (fun i=>Z^(ell i)) t)
    eta S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J) X t
  have hrows : forall z, Membership.mem R z ->
      Not (z=0) /\ elementNorm z<=Ck*Z^(1-Lambda-2*lowUnselectedLength ell J) := by
    intro z hzR
    refine And.intro (lowNumeratorRows_nonzero aCut bCut haCut hbCut Q hQ z hzR) ?_
    apply (lowNumeratorRows_norm_bound aCut bCut haCut hbCut Q hQ z hzR).trans
    have hh := mul_le_mul_of_nonneg_left
      (lowPhysicalScale_nominal_bound_general (calibrationForSet S hS)
        Z L c (lowUnselectedLength ell J) lx ly (1-Lambda) hz hc hLlo hgeom)
      (show 0<=2*bCut by positivity)
    simpa only [Ck,mul_assoc] using hh
  have he (sigma : RayRing) : (R.sum fun z=>norm (row sigma z)^2)<=
      C*(1+norm t)^degree*Z^((1-Lambda-2*lowUnselectedLength ell J)+
        max 0 ((5*Lambda+lowUnselectedLength ell J-1)/4)+507*eps) :=
    hZ.2 Lambda hLambda0 hLambda1 hsum T hT hout hdis
      (fun i P hP=>(hnorm i P hP).2) J R hrows X hX hXlo hXhi W hW (fun i=>Z^(ell i)) t sigma
  have hn (sigma : RayRing) : Real.sqrt (R.sum fun z=>norm (row sigma z)^2)/Real.sqrt Q<=
      Real.sqrt (C*B^2/q)*(1+norm t)^degree*
        Z^((max 0 ((5*Lambda+lowUnselectedLength ell J-1)/4)+507*eps)/2) := by
    dsimp only [Q]
    rw [lowPhysicalScale_source_general _ Z L lx ly (1-Lambda) hz hgeom]
    exact low_inverse_sqrt_normalized_general q C B Z L (1-Lambda)
      (lowUnselectedLength ell J)
      (max 0 ((5*Lambda+lowUnselectedLength ell J-1)/4)+507*eps) (1+norm t)
      (R.sum fun z=>norm (row sigma z)^2) degree hq hC.le hB.le hz hL
      (le_add_of_nonneg_right (norm_nonneg t))
      (Finset.sum_nonneg (fun _ _=>sq_nonneg _))
      (by simpa only [add_assoc] using he sigma) hLhi
  change Inv.inv (Real.sqrt Q)/(2*Real.pi)*
    (Finset.univ.sum fun sigma : RayRing=>Real.sqrt (R.sum fun z=>norm (row sigma z)^2))<=_
  calc
    _ = (Finset.univ.sum fun sigma : RayRing=>
          Real.sqrt (R.sum fun z=>norm (row sigma z)^2)/Real.sqrt Q)/(2*Real.pi) := by
      rw [<-Finset.sum_div]
      ring
    _ <= (Finset.univ.sum fun _sigma : RayRing=>
          Real.sqrt (C*B^2/q)*(1+norm t)^degree*
            Z^((max 0 ((5*Lambda+lowUnselectedLength ell J-1)/4)+507*eps)/2))/(2*Real.pi) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun sigma _=>hn sigma)) (by positivity)
    _ <= _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      dsimp [C0]
      calc
        _ = ((Fintype.card RayRing:Real)*Real.sqrt (C*B^2/q)/(2*Real.pi))*
            (1+abs t)^degree*Z^((max 0 ((5*Lambda+lowUnselectedLength ell J-1)/4)+507*eps)/2) := by
          ring
        _ <= _ := by gcongr;linarith

end PrimeFactorOscillations.GeneralLowGeometry

