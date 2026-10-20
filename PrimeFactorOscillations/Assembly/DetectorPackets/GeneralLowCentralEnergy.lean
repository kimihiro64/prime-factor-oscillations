/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Detector.LowCentralTuple
import PrimeFactorOscillations.Assembly.DetectorPackets.GeneralLowPhysicalEnergy

/-!
# GeneralLowCentralEnergy

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
# Variable-geometry compensated tuple energy

The actual normalized inverse estimate is combined with the full tuple Gram
identity. The excess is paid by inverse norm weights with exponent 15/8.
The independent Gram exponent 1/6 is unchanged.
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

theorem canonical_slot_inverse_eighth :
    Exists fun C : Real=>0<C /\
    forall (T : Finset PrimeIdeal) (_hT : forall P, Membership.mem T P -> Supported P.val),
      (Finset.univ.sum fun a : canonicalSlotSupport T=>elementNorm a.val^(-(15/8:Real)))<=C := by
  have hb := ProbeGramCommon.supportedIdeal_rpow_finite_bound (-(15/8)) (by norm_num)
  choose C hC hb using hb
  refine Exists.intro C (And.intro hC ?_)
  intro T hT
  let f : T->{I : Ideal Eis // Supported I} :=
    fun P=>Subtype.mk P.val.val (hT P.val P.property)
  have hf : Function.Injective f := by
    intro P Q h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun I : {I : Ideal Eis // Supported I}=>I.val) h
  have he : (Finset.univ.sum fun a : canonicalSlotSupport T=>
      elementNorm a.val^(-(15/8:Real)))=
      (Finset.univ.image f).sum (fun I=>ProbeGramCommon.gramIdealNorm I^(-(15/8:Real))) := by
    rw [Finset.sum_image (fun P _ Q _ h=>hf h)]
    have hh := (canonicalSlotEquiv T hT).sum_comp
      (fun a=>elementNorm a.val^(-(15/8:Real)))
    rw [<-hh]
    apply Finset.sum_congr rfl
    intro P hP
    rw [canonicalSlotEquiv_norm]
    rfl
  rw [he]
  exact hb _

theorem lowUnselectedWeight_norm_eighth_identity {K : Nat}
    (slots : Fin K->Finset Eis) (hslots : forall i x, Membership.mem (slots i) x -> Not (x=0))
    (J : Finset (Fin K)) (W : Fin K->Real->Complex) (P : Fin K->Real)
    (a : LowUnselectedTuple slots J) :
    norm (lowUnselectedWeight slots J W P a)*
        elementNorm (Finset.univ.prod fun i : J=>(a i).val)^(-(3/8:Real))=
      Finset.univ.prod (fun i : J=>elementNorm (a i).val^(-(15/8:Real))*
        norm (W i.val (elementNorm (a i).val/P i.val))) := by
  have hL := lowUnselectedProduct_norm_pos slots hslots J a
  rw [lowUnselectedWeight,norm_mul,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hL.le _),norm_prod]
  calc
    _ = (elementNorm (Finset.univ.prod fun i : J=>(a i).val)^(-(3/2:Real))*
        elementNorm (Finset.univ.prod fun i : J=>(a i).val)^(-(3/8:Real)))*
        Finset.univ.prod (fun i : J=>norm (W i.val (elementNorm (a i).val/P i.val))) := by ring
    _ = elementNorm (Finset.univ.prod fun i : J=>(a i).val)^(-(15/8:Real))*
        Finset.univ.prod (fun i : J=>norm (W i.val (elementNorm (a i).val/P i.val))) := by
      rw [<-Real.rpow_add hL]
      norm_num
    _ = _ := by
      rw [elementNorm_finset_prod,Finset.prod_mul_distrib,
        Real.finsetProd_rpow Finset.univ (fun i : J=>elementNorm (a i).val)
          (fun i _=>by unfold elementNorm;positivity)]

theorem lowUnselectedMass_eighth_bound (K : Nat) :
    Exists fun C : Real=>0<C /\
    forall (T : Fin K->Finset PrimeIdeal)
      (_hT : forall i P, Membership.mem (T i) P -> Supported P.val)
      (J : Finset (Fin K)) (W : Fin K->Real->Complex) (P : Fin K->Real),
      (forall i x, norm (W i x)<=1) ->
      (Finset.univ.sum fun a : LowUnselectedTuple (fun i=>canonicalSlotSupport (T i)) J=>
        norm (lowUnselectedWeight (fun i=>canonicalSlotSupport (T i)) J W P a)*
          elementNorm (Finset.univ.prod fun i : J=>(a i).val)^(-(3/8:Real)))<=C := by
  have hb := canonical_slot_inverse_eighth
  choose C hC hb using hb
  let B := max 1 C
  have hB1 : 1<=B := le_max_left _ _
  refine Exists.intro (B^K) (And.intro (by dsimp [B];positivity) ?_)
  intro T hT J W P hW
  simp_rw [lowUnselectedWeight_norm_eighth_identity _
    (fun i=>canonicalSlotSupport_nonzero _ (hT i))]
  rw [<-Fintype.prod_sum (fun (i : J) (a : canonicalSlotSupport (T i.val))=>
    elementNorm a.val^(-(15/8:Real))*norm (W i.val (elementNorm a.val/P i.val)))]
  have hterms (i : J) : (Finset.univ.sum fun a : canonicalSlotSupport (T i.val)=>
      elementNorm a.val^(-(15/8:Real))*norm (W i.val (elementNorm a.val/P i.val)))<=B := by
    apply le_trans ?_ (le_max_right _ _)
    apply le_trans ?_ (hb _ (hT i.val))
    apply Finset.sum_le_sum
    intro a ha
    exact (mul_le_mul_of_nonneg_left (hW i.val _)
      (Real.rpow_nonneg (by unfold elementNorm;positivity) _)).trans_eq (mul_one _)
  have hc : J.card<=K := by
    simpa using Finset.card_le_card (Finset.subset_univ J)
  calc
    _ <= Finset.univ.prod (fun _i : J=>B) := by
      gcongr <;> first
        | (intro i hi; exact Finset.sum_nonneg (fun a _=>
            mul_nonneg (Real.rpow_nonneg (by unfold elementNorm;positivity) _) (norm_nonneg _)))
        | positivity
        | exact hterms _
    _ = B^J.card := by simp only [Finset.prod_const,Finset.card_univ,Fintype.card_coe]
    _ <= B^K := by gcongr

theorem eventually_compensated_scales_general (C : CalibrationData) (B : Real) :
    Filter.Eventually (fun Z : Real=>1<Z /\
      forall (Lambda L : Real), 0<=Lambda -> Lambda<=1/5 ->
      1<=L -> L<=B*Z^Lambda ->
      let lx := 7/16-Lambda/2
      let ly := 9/16-Lambda/2
      1<=Z^ly/L /\
      1<=(Z^ly/L)^2/lowPhysicalScale C (Z^lx/L) (Z^ly/L) /\
      forall delta : Real, 0<=delta ->
        lowGramFactor C (Z^lx/L) (Z^ly/L) delta<=
          Real.sqrt (3*elementNorm C.generator/L)*
            Z^(11/48-Lambda/4+(9/32)*delta)) Filter.atTop := by
  let q := elementNorm C.generator
  have hq : 0<q := calibration_elementNorm_pos C
  have hq1 : 1<=q := by
    change (1:Real)<=(Ideal.absNorm (Ideal.span {C.generator}):Real)
    have hn : 0<Ideal.absNorm (Ideal.span {C.generator}) := by
      change 0<(Ideal.absNorm (Ideal.span {C.generator}):Real) at hq
      exact_mod_cast hq
    exact_mod_cast (Nat.succ_le_iff.mpr hn)
  have he : (0:Real)<1/80 := by norm_num
  filter_upwards [Filter.eventually_gt_atTop (1:Real),
    (tendsto_rpow_atTop he).eventually (Filter.eventually_ge_atTop (max B q))] with Z hZ hbudget
  refine And.intro hZ ?_
  intro Lambda L hLambda0 hLambda1 hL1 hLcap
  dsimp only
  let lx : Real := 7/16-Lambda/2
  let ly : Real := 9/16-Lambda/2
  have hz : 0<Z := lt_trans zero_lt_one hZ
  have hl : 0<L := lt_of_lt_of_le zero_lt_one hL1
  have hx : 0<Z^lx := Real.rpow_pos_of_pos hz _
  have hy : 0<Z^ly := Real.rpow_pos_of_pos hz _
  have hBZ : B<=Z^(1/80:Real) := (le_max_left _ _).trans hbudget
  have hqZ : q<=Z^(1/80:Real) := (le_max_right _ _).trans hbudget
  have hBY : B*Z^Lambda<=Z^ly := by
    calc
      _ <= Z^(1/80:Real)*Z^Lambda :=
        mul_le_mul_of_nonneg_right hBZ (Real.rpow_nonneg hz.le _)
      _ = Z^((1/80:Real)+Lambda) := (Real.rpow_add hz _ _).symm
      _ <= _ := Real.rpow_le_rpow_of_exponent_le hZ.le (by dsimp [ly];linarith)
  have hYOne : 1<=Z^ly/L := by
    have hh := div_le_div_of_nonneg_right (hLcap.trans hBY) hl.le
    simpa [ne_of_gt hl] using hh
  have hrho : q<=Z^(1/8:Real) :=
    hqZ.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num))
  have hP : q*Z^lx<=Z^ly := by
    calc
      _ <= Z^(1/8:Real)*Z^lx :=
        mul_le_mul_of_nonneg_right hrho hx.le
      _ = _ := by
        rw [<-Real.rpow_add hz]
        congr 1
        dsimp [lx,ly]
        ring
  have hxsq : (Z^lx)^2=Z^(2*lx) := by
    rw [<-Real.rpow_natCast,<-Real.rpow_mul hz.le]
    congr 1
    push_cast
    ring
  have hq2 : 1<=q^2 := by
    simpa only [pow_two] using one_le_mul_of_one_le_of_one_le hq1 hq1
  have htail : L*Z^ly<=q^2*(Z^lx)^2 := by
    calc
      _ <= (B*Z^Lambda)*Z^ly := mul_le_mul_of_nonneg_right hLcap hy.le
      _ <= (Z^(1/80:Real)*Z^Lambda)*Z^ly := by gcongr
      _ = Z^((1/80:Real)+Lambda+ly) := by
        rw [<-Real.rpow_add hz,<-Real.rpow_add hz]
      _ <= Z^(2*lx) :=
        Real.rpow_le_rpow_of_exponent_le hZ.le (by dsimp [lx,ly];linarith)
      _ <= q^2*(Z^lx)^2 := by
        rw [<-hxsq]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hq2 (sq_nonneg (Z^lx))
  have hRatioOne : 1<=(Z^ly/L)^2/lowPhysicalScale C (Z^lx/L) (Z^ly/L) := by
    change 1<=(Z^ly/L)^2/(q*(Z^lx/L)*(Z^ly/L))
    rw [compensated_gram_ratio q (Z^lx) (Z^ly) L hq hx hy hl]
    have hh := div_le_div_of_nonneg_right hP (mul_pos hq hx).le
    simpa [ne_of_gt (mul_pos hq hx)] using hh
  refine And.intro hYOne (And.intro hRatioOne ?_)
  intro delta hdelta
  have hr : Z^ly/(q*Z^lx)<=Z^(1/8:Real) := by
    calc
      _ = (Z^ly/Z^lx)/q := by ring
      _ = Z^(ly-lx)/q :=
        congrArg (fun x : Real=>x/q) (Real.rpow_sub hz ly lx).symm
      _ = Z^(1/8:Real)/q := by congr 1;dsimp [lx,ly];ring
      _ <= _ := div_le_self (Real.rpow_nonneg hz.le _) hq1
  have hb := compensated_gram_scale_bound q (Z^lx) (Z^ly) L delta
    hq hx hy hL1 hdelta hP htail
  have hb' :
      (q*(Z^lx/L)*(Z^ly/L)/(Z^ly/L))*
        (1+((Z^ly/L)^2/(q*(Z^lx/L)*(Z^ly/L)))^(1/6:Real)+
          ((Z^ly/L)^2/(q*(Z^lx/L)*(Z^ly/L)))^2/(Z^ly/L))*(Z^ly/L)^delta<=
      (3*q/L)*(Z^lx*(Z^(1/8:Real))^(1/6:Real)*(Z^ly)^delta) := by
    apply hb.trans
    calc
      _ <= 3*(q*Z^lx/L)*(Z^(1/8:Real))^(1/6:Real)*(Z^ly)^delta := by
        gcongr
      _ = _ := by ring
  have hpow : Z^lx*(Z^(1/8:Real))^(1/6:Real)*(Z^ly)^delta=
      Z^((11/24-Lambda/2)+ly*delta) := by
    rw [<-Real.rpow_mul hz.le,<-Real.rpow_mul hz.le,
      <-Real.rpow_add hz,<-Real.rpow_add hz]
    congr 1
    dsimp [lx,ly]
    ring
  rw [hpow] at hb'
  have hsqrt : Real.sqrt (Z^((11/24-Lambda/2)+ly*delta))=
      Z^(11/48-Lambda/4+ly*delta/2) := by
    rw [Real.sqrt_eq_rpow,<-Real.rpow_mul hz.le]
    congr 1
    ring
  have hdel : ly*delta<=(9/16:Real)*delta :=
    mul_le_mul_of_nonneg_right (by dsimp [ly];linarith) hdelta
  calc
    lowGramFactor C (Z^lx/L) (Z^ly/L) delta <=
        Real.sqrt ((3*q/L)*Z^((11/24-Lambda/2)+ly*delta)) := Real.sqrt_le_sqrt hb'
    _ = Real.sqrt (3*q/L)*Z^(11/48-Lambda/4+ly*delta/2) := by
      rw [Real.sqrt_mul (by positivity),hsqrt]
    _ <= _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)) (Real.sqrt_nonneg _)

theorem low_central_compensated_tuple_general (eta : HeckeFamily.Character) (S : Finset Id)
    (hS : forall P, Membership.mem S P -> P.IsMaximal) (hbad : fixedBadPrimes<=S)
    {K : Nat} (ell : Fin K->Real) (hell : forall i, 0<=ell i)
    (a b eps : Real) (ha : 0<a) (heps : 0<eps) (heps1 : eps<1)
    (W0 W1 : Real->Complex) (a0 b0 a1 b1 M : Real) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hM : 0<=M)
    (hW0 : Set.Subset (Function.support W0) (Set.Icc a0 b0))
    (hW1 : Set.Subset (Function.support W1) (Set.Icc a1 b1))
    (hW0s : ContDiff Real ((Top.top : ENat) : WithTop ENat) W0)
    (hW1s : ContDiff Real ((Top.top : ENat) : WithTop ENat) W1)
    (hWM : forall x, norm (W1 x)<=M) :
    Exists fun degree : Nat=>Exists fun C : Real=>
    0<C /\ Filter.Eventually (fun Z : Real=>1<Z /\
    forall Lambda : Real, 0<=Lambda -> Lambda<=1/5 -> (Finset.univ.sum ell)<=Lambda ->
    forall T : Fin K->Finset PrimeIdeal,
      (forall i P, Membership.mem (T i) P -> Supported P.val) ->
      (forall i P, Membership.mem (T i) P -> Not (Membership.mem S P.val)) ->
      Pairwise (fun i j=>Disjoint (T i) (T j)) ->
      (forall i P, Membership.mem (T i) P ->
        a*Z^(ell i)<=(Ideal.absNorm P.val:Real) /\
          (Ideal.absNorm P.val:Real)<=b*Z^(ell i)) ->
    forall (J : Finset (Fin K)) (X : Real), 0<X ->
      Z^(1+lowSelectedLength ell J-eps/2)<=X ->
      X<=Z^(1+lowSelectedLength ell J+eps/2) ->
    forall W : Fin K->Real->Complex, (forall i x, norm (W i x)<=1) ->
    forall t : Real,
      norm (Finset.univ.sum fun p : forall i,canonicalSlotSupport (T i)=>
        compensationSubsetWeight eta W (fun i=>Z^(ell i)) (fun i=>(p i).val) J*
          compensationRowTest eta (calibrationForSet S hS) W0 W1 (fun i=>(p i).val) J
            (Z^(7/16-Lambda/2)) (Z^(9/16-Lambda/2)) X t*
          selectedSlotFactor W (fun i=>Z^(ell i)) (fun i=>(p i).val) J t)<=
        C*(1+norm t)^degree*Z^(11/48-Lambda/4+254*eps)) Filter.atTop := by
  have hgb := compensation_tuple_actual_gram eps heps heps1 W0 W1
    a0 b0 a1 b1 M ha0 ha1 hab1 hM hW0 hW1 hW0s hW1s hWM S hS hbad
  choose Cg hCg hgram using hgb
  have hib := low_physical_inverse_normalized_general eta S hS hbad ell hell
    a b (a0*a1) (max 1 (b0*b1)) eps ha (mul_pos ha0 ha1)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) heps heps1.le
  choose degree Ci hCi hinverse using hib
  have hub := lowUnselectedMass_eighth_bound K
  choose Cu hCu hmass using hub
  let q := elementNorm (calibrationForSet S hS).generator
  let c := (min 1 a)^K
  let B := (max 1 b)^K
  have hq : 0<q := calibration_elementNorm_pos _
  have hc : 0<c := by dsimp [c];positivity
  have hB : 0<B := by dsimp [B];positivity
  let C0 := Cg*Ci*Real.sqrt (3*q)*c^(-(1/8:Real))*Cu
  have hC0 : 0<C0 := by dsimp [C0];positivity
  refine Exists.intro degree (Exists.intro C0 (And.intro hC0 ?_))
  filter_upwards [hinverse,eventually_compensated_scales_general (calibrationForSet S hS) B]
    with Z hInv hScale
  refine And.intro hInv.1 ?_
  intro Lambda hLambda0 hLambda1 hsum T hT hout hdis hnorm J X hX hXlo hXhi W hW t
  let slots := fun i=>canonicalSlotSupport (T i)
  let Yp := fun i=>Z^(ell i)
  let lx : Real := 7/16-Lambda/2
  let ly : Real := 9/16-Lambda/2
  let d := lowUnselectedLength ell J
  let R := max 0 ((5*Lambda+d-1)/4)
  let g : Real := 11/48-Lambda/4
  have hgeom : lx+ly=1-Lambda := by dsimp [lx,ly];ring
  have hz : 0<Z := lt_trans zero_lt_one hInv.1
  have hx : 0<Z^lx := Real.rpow_pos_of_pos hz _
  have hy : 0<Z^ly := Real.rpow_pos_of_pos hz _
  have hslots : forall i n, Membership.mem (slots i) n -> Not (n=0) :=
    fun i=>canonicalSlotSupport_nonzero _ (hT i)
  have hnormE (i : Fin K) (n : Eis) (hn : Membership.mem (slots i) n) :
      a*Z^(ell i)<=elementNorm n /\ elementNorm n<=b*Z^(ell i) := by
    cases Finset.mem_image.mp hn with
    | intro P hP =>
      cases hP with
      | intro hPT heq =>
        subst n
        rw [primaryTuple_norm P (hT i P hPT)]
        exact hnorm i P hPT
  have hlength := lowLength_bounds_general ell hell Lambda hsum J
  have hd : 0<=d := hlength.1
  have hd1 : d<=Lambda := hlength.2.1
  have hR : R<=d/4 := by
    apply max_le
    . linarith
    . linarith
  have hcap (p : LowUnselectedTuple slots J) :
      elementNorm (Finset.univ.prod fun i : J=>(p i).val)<=B*Z^Lambda := by
    apply (lowUnselectedProduct_norm_upper_nominal ell b Z hz slots
      (fun i n hn=>(hnormE i n hn).2) J p).trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hInv.1.le hd1) hB.le
  have hs (p : LowUnselectedTuple slots J) :=
    hScale.2 Lambda (elementNorm (Finset.univ.prod fun i : J=>(p i).val))
      hLambda0 hLambda1 (lowUnselectedProduct_norm_ge_one slots hslots J p) (hcap p)
  have hg := hgram K eta slots hslots J W Yp (Z^lx) (Z^ly) X t hx hy hX
    (fun p=>(hs p).1) (fun p=>(hs p).2.1)
  apply hg.trans
  let G := Z^(g+(9/32)*eps)
  let V := Ci*(1+norm t)^degree*Z^((R+507*eps)/2)
  have hV : 0<=V := by dsimp [V];positivity
  have hterm (p : LowUnselectedTuple slots J) :
      let L := elementNorm (Finset.univ.prod fun i : J=>(p i).val)
      let Q := lowPhysicalScale (calibrationForSet S hS) (Z^lx/L) (Z^ly/L)
      norm (lowUnselectedWeight slots J W Yp p)*(Inv.inv (Real.sqrt Q)/(2*Real.pi))*
        lowGramFactor (calibrationForSet S hS) (Z^lx/L) (Z^ly/L) eps*
        lowInverseMass (calibrationForSet S hS) (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
          (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (Z^lx/L) (Z^ly/L)
          (div_pos hx (lowUnselectedProduct_norm_pos slots hslots J p))
          (div_pos hy (lowUnselectedProduct_norm_pos slots hslots J p))
          (lowSelectedInverseRow Finset.univ (lowSelectedWeight eta slots J W Yp t)
            eta S hS (lowSelectedIdeal slots J) X t)<=
      (Ci*Real.sqrt (3*q)*c^(-(1/8:Real))*(1+norm t)^degree*Z^(g+254*eps))*
        (norm (lowUnselectedWeight slots J W Yp p)*L^(-(3/8:Real))) := by
    dsimp only
    let L := elementNorm (Finset.univ.prod fun i : J=>(p i).val)
    let Q := lowPhysicalScale (calibrationForSet S hS) (Z^lx/L) (Z^ly/L)
    have hL : 0<L := lowUnselectedProduct_norm_pos slots hslots J p
    have hLlo : c*Z^d<=L :=
      lowUnselectedProduct_norm_lower ell a Z ha hz slots
        (fun i n hn=>(hnormE i n hn).1) J p
    have hcost : Z^(d/8)<=c^(-(1/8:Real))*L^(1/8:Real) := by
      have hh := Real.rpow_le_rpow (by positivity) hLlo (show (0:Real)<=1/8 by norm_num)
      rw [Real.mul_rpow hc.le (Real.rpow_nonneg hz.le _),<-Real.rpow_mul hz.le,
        show d*(1/8:Real)=d/8 by ring] at hh
      have hdv : Z^(d/8)<=L^(1/8:Real)/(c^(1/8:Real)) := by
        have hcp : Not (c^(1/8:Real)=0) := ne_of_gt (Real.rpow_pos_of_pos hc _)
        have hdiv :
            (c^(1/8:Real)*Z^(d/8))/(c^(1/8:Real))<=L^(1/8:Real)/(c^(1/8:Real)) :=
          div_le_div_of_nonneg_right hh (Real.rpow_nonneg hc.le (1/8:Real))
        have hcancel : (c^(1/8:Real)*Z^(d/8))/(c^(1/8:Real))=Z^(d/8) := by
          calc
            _ = Z^(d/8)*(c^(1/8:Real)/c^(1/8:Real)) := by ring
            _ = _ := by rw [div_self hcp,mul_one]
        exact hcancel.symm.trans_le hdiv
      simpa only [Real.rpow_neg hc.le,div_eq_mul_inv,mul_comm] using hdv
    have hGV : G*V<=c^(-(1/8:Real))*L^(1/8:Real)*
        (Ci*(1+norm t)^degree*Z^(g+254*eps)) := by
      dsimp only [G,V]
      calc
        _ = (Ci*(1+norm t)^degree)*(Z^(g+(9/32)*eps)*Z^((R+507*eps)/2)) := by ring
        _ = Ci*(1+norm t)^degree*Z^(g+(9/32)*eps+(R+507*eps)/2) := by
          rw [<-Real.rpow_add hz]
        _ <= Ci*(1+norm t)^degree*Z^(g+254*eps+d/8) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hInv.1.le (by linarith)) (by positivity)
        _ = (Ci*(1+norm t)^degree*Z^(g+254*eps))*Z^(d/8) := by
          rw [Real.rpow_add hz]
          ring
        _ <= (Ci*(1+norm t)^degree*Z^(g+254*eps))*(c^(-(1/8:Real))*L^(1/8:Real)) :=
          mul_le_mul_of_nonneg_left hcost (by positivity)
        _ = _ := by ring
    have hgb := (hs p).2.2 eps heps.le
    have hib := hInv.2 Lambda lx ly hLambda0 hLambda1 hsum hgeom T hT hout hdis hnorm
      J p X hX hXlo hXhi W hW t (div_pos hx hL) (div_pos hy hL)
    have hgn : 0<=lowGramFactor (calibrationForSet S hS) (Z^lx/L) (Z^ly/L) eps :=
      Real.sqrt_nonneg _
    have hh := mul_le_mul_of_nonneg_left hib
      (mul_nonneg (norm_nonneg (lowUnselectedWeight slots J W Yp p)) hgn)
    have hh2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hgb (norm_nonneg (lowUnselectedWeight slots J W Yp p))) hV
    have hpower : L^(-(1/2:Real))*L^(1/8:Real)=L^(-(3/8:Real)) := by
      rw [<-Real.rpow_add hL]
      congr 1
      ring
    calc
      _ = (norm (lowUnselectedWeight slots J W Yp p)*
          lowGramFactor (calibrationForSet S hS) (Z^lx/L) (Z^ly/L) eps)*
          (Inv.inv (Real.sqrt Q)/(2*Real.pi)*
            lowInverseMass (calibrationForSet S hS) (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
              (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (Z^lx/L) (Z^ly/L)
              (div_pos hx hL) (div_pos hy hL)
              (lowSelectedInverseRow Finset.univ (lowSelectedWeight eta slots J W Yp t)
                eta S hS (lowSelectedIdeal slots J) X t)) := by ring
      _ <= (norm (lowUnselectedWeight slots J W Yp p)*Real.sqrt (3*q/L))*(G*V) :=
        (hh.trans hh2).trans_eq (by ring)
      _ <= (norm (lowUnselectedWeight slots J W Yp p)*Real.sqrt (3*q/L))*
          (c^(-(1/8:Real))*L^(1/8:Real)*
            (Ci*(1+norm t)^degree*Z^(g+254*eps))) :=
        mul_le_mul_of_nonneg_left hGV (by positivity)
      _ = _ := by
        rw [low_compensated_sqrt_factor q L hq.le hL]
        calc
          _ = (Ci*Real.sqrt (3*q)*c^(-(1/8:Real))*(1+norm t)^degree*Z^(g+254*eps))*
              (norm (lowUnselectedWeight slots J W Yp p)*(L^(-(1/2:Real))*L^(1/8:Real))) := by ring
          _ = _ := by rw [hpower]
  have hh := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (s:=Finset.univ) (fun p _=>hterm p)) hCg.le
  apply hh.trans
  rw [<-Finset.mul_sum]
  have hm := hmass T hT J W Yp hW
  calc
    _ <= Cg*((Ci*Real.sqrt (3*q)*c^(-(1/8:Real))*(1+norm t)^degree*Z^(g+254*eps))*Cu) := by
      gcongr
    _ = _ := by dsimp [C0];ring

end PrimeFactorOscillations.GeneralLowGeometry

