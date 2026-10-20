/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Reflection.LowFrozenEnergy
import PrimeFactorOscillations.Assembly.DetectorPackets.GeneralLowChoiceEnergy

/-!
# GeneralLowFrozenEnergy

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
# Inactive and frozen source energy with a variable slot budget

Carries the complete supported-choice bound through inactive rows and
frozen source completion. All arithmetic phases, inactive harmonic costs,
finite source labels and the reflected max excess are retained.
This is an input to the inverse probe, not a zero-free theorem.
-/


noncomputable section
namespace PrimeFactorOscillations.GeneralLowGeometry
open scoped Classical
open OAI OAI.SevenEighths
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic
open CanonicalQuadraticSieve InverseTerminalWidths InverseMoment InverseReflectedPhase
open CanonicalRowCompletion
local notation "Eis" => ActualEisensteinCubic.O
universe u v
variable {Nlevel : Eis}

theorem low_original_inactive_energy_general
    {gamma : Type u} [Fintype gamma] (a c0 : gamma->Eis) (mode : gamma->Bool)
    [Fintype (HasQuotient.Quotient Eis (Ideal.span {Nlevel^2}))]
    (lo hi : Real) (hlo : 0<lo) (W : Real->Complex)
    (hWs : Set.Subset (Function.support W) (Set.Icc lo hi))
    (hW : ContDiff Real ((Top.top : ENat) : WithTop ENat) W)
    (s : forall i, FixedCuspShape
      (ControlledStratumArithmetic.fixedCusp (a i) (c0 i) (mode i)))
    (hc0 : forall i, Not (c0 i=0))
    (hNlevel : forall i, Dvd.dvd ((9:Eis)*c0 i) Nlevel)
    (hbase : forall i, if mode i then Dvd.dvd (ConcretePrimeRowBridge.goodLambda^2) (a i-1)
      else Dvd.dvd (ConcretePrimeRowBridge.goodLambda^2) (c0 i-1))
    (hac : forall i, IsCoprime (a i) (c0 i))
    (Q : Ideal Eis) (hQ : Not (Q=0))
    (Ck eta : Real) (hCk : 0<Ck) (heta : 0<eta) (heta1 : eta<=1) :
    Exists fun degree : Nat => Exists fun C : Real => Exists fun Z0 : Real =>
    0<C /\ 1<Z0 /\
    forall g : gamma, forall {sigma : Type v} [Fintype sigma] [DecidableEq sigma],
    forall (J F Q0 : Ideal Eis) (_hJ : Not (J=0)) (_hF : Not (F=0)),
    forall (A : Finset (FreeReflection.pool J Q Q0))
      (Z Lambda d ell0 shift O0 : Real),
      Z0<=Z -> 0<=Lambda -> Lambda<=1/5 -> 0<=d -> d<=Lambda ->
      0<=ell0 -> ell0<=Lambda-d+eta -> abs shift<=eta ->
      O0=normWidth Z (rowPowerfulPart J) ->
    forall (parents rows : Finset (Ideal Eis)),
      (forall I, Membership.mem parents I ->
        Not (I=0) /\ (Ideal.absNorm I:Real)<=Ck*Z^(1-Lambda-2*d)) ->
      rows<=originalResidualRows parents J Q ->
      (forall P, Membership.mem fixedBadPrimes P -> Dvd.dvd P Q) ->
      let G := (poolPrimeFamily J Q Q0).restrict A
      let jF := fun b : A => completedLocalExponent J F b.val.val
    forall (lists : sigma->Finset (Ideal Eis)) (H : sigma->Real)
      (_hdis : Pairwise (fun i j=>Disjoint (lists i) (lists j)))
      (hmax : forall i, forall P, Membership.mem (lists i) P -> P.IsMaximal)
      (hgood : forall i, forall P, Membership.mem (lists i) P ->
        Not (Membership.mem P ConcretePrimeRowBridge.goodLambda))
      (_hprime : forall i, forall P, Membership.mem (lists i) P -> Prime P)
      (hrows : forall K, Membership.mem rows K -> Admissible K),
      (forall i, 1<=H i) ->
      (forall i, forall P, Membership.mem (lists i) P -> (Ideal.absNorm P:Real)<=H i) ->
      (Finset.univ.prod H)<=Z^ell0 ->
      (forall f, IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) ->
      (forall f, Not (ringChar (HasQuotient.Quotient Eis (G.ideal f))=2)) ->
      (forall K, Membership.mem rows K ->
        (forall f, IsCoprime (G.ideal f) K) /\ IsCoprime (Ideal.span {Nlevel}) K) ->
      (forall i, forall P, Membership.mem (lists i) P -> IsCoprime (Ideal.span {Nlevel}) P) ->
      (forall i, forall P, Membership.mem (lists i) P ->
        Not (ringChar (HasQuotient.Quotient Eis P)=2)) ->
    forall T : Finset sigma,
    Exists (fun D :
      (forall K : rows,
       forall _b : supportedSlotChoices
         (fun i : {i : sigma // Not (Membership.mem T i)}=>lists i.val)
           (poolPrimeFamily J Q Q0).ideal K.val,
       forall p : supportedSlotChoices (fun i : T=>lists i.val) (poolPrimeFamily J Q Q0).ideal K.val,
        ControlledStratumArithmetic
          (G.reflected K.val (hrows K.val K.property)
            (slotChoiceFamily (fun i : T=>lists i.val)
              (fun i=>hmax i.val) (fun i=>hgood i.val) p.val)).generator
          Nlevel (a g) (c0 g) (mode g)) =>
    forall (theta : Real) (w : forall i, lists i->Complex),
      (forall i P, norm (w i P)<=1) ->
      (Finset.univ.sum fun K : rows=>norm (Finset.univ.sum
        fun b : supportedSlotChoices
          (fun i : {i : sigma // Not (Membership.mem T i)}=>lists i.val)
          (poolPrimeFamily J Q Q0).ideal K.val=>
        ((Finset.univ.prod fun i : {i : sigma // Not (Membership.mem T i)}=>
            Inv.inv (Ideal.absNorm (b.val i).val:Complex))*
          (Finset.univ.prod fun i : {i : sigma // Not (Membership.mem T i)}=>w i.val (b.val i)))*
        Finset.univ.sum (fun p : supportedSlotChoices (fun i : T=>lists i.val)
          (poolPrimeFamily J Q Q0).ideal K.val=>
          (Finset.univ.prod fun i : T=>w i.val (p.val i))*mixedReflectedValue (D K b p) (s g)
            (G.reflected K.val (hrows K.val K.property)
              (slotChoiceFamily (fun i : T=>lists i.val)
                (fun i=>hmax i.val) (fun i=>hgood i.val) p.val)).generator_ne_zero (hc0 g)
            (G.reflected K.val (hrows K.val K.property)
              (slotChoiceFamily (fun i : T=>lists i.val)
                (fun i=>hmax i.val) (fun i=>hgood i.val) p.val)).generator_good
            (OAI.SevenEighths.InverseReflectedPhase.reflectedExponent jF)
            (slotIndices A (PrimeIndex K.val) T)
            (CompletedHeight.normTwistedSource W theta) (Z^(1+ell0+shift))))^2)<=
        (Finset.univ.prod fun i : {i : sigma // Not (Membership.mem T i)}=>
          256*(columnDyadicLength (H i.val)+1:Real))^2*
        (C*(1+norm theta)^degree*
          Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+505*eta-O0/2))) := by
  have hb := low_original_choice_energy_general a c0 mode lo hi hlo W hWs hW
    s hc0 hNlevel hbase hac Q hQ Ck eta hCk heta heta1
  choose degree C Z0 hC hZ0 he using hb
  refine Exists.intro degree (Exists.intro C
    (Exists.intro Z0 (And.intro hC (And.intro hZ0 ?_))))
  intro g sigma _ _ J F Q0 hJ hF A Z Lambda d ell0 shift O0
    hZ hLambda0 hLambda1 hd hd1 hell hellcap hshift hOeq parents rows hparents hsub hbad
  dsimp only
  intro lists H hdis hmax hgood hprime hrows hH1 hH hprod hGN hGchar hrowcop hLN hLchar T
  let G := (poolPrimeFamily J Q Q0).restrict A
  let FF := (poolPrimeFamily J Q Q0).ideal
  let rowsb := fun b : forall i : {i : sigma // Not (Membership.mem T i)},lists i.val=>
    inactiveRowSet rows lists T FF b
  have hbsub (b : forall i : {i : sigma // Not (Membership.mem T i)},lists i.val) :
      rowsb b<=rows := by
    intro K hK
    exact ((inactiveRows_mem rows lists T FF b K).mp hK).1
  have hbr (b : forall i : {i : sigma // Not (Membership.mem T i)},lists i.val) :
      forall K, Membership.mem (rowsb b) K -> Admissible K :=
    fun K hK=>hrows K (hbsub b hK)
  have hdisT : Pairwise (fun i j : T=>Disjoint (lists i.val) (lists j.val)) := by
    intro i j hij
    exact hdis (fun hv=>hij (Subtype.ext hv))
  have hpT : (Finset.univ.prod fun i : T=>H i.val)<=Z^ell0 := by
    have hu : (Finset.univ : Finset T)=
        @Finset.univ T (Subtype.fintype (fun i : sigma=>Membership.mem T i)) := by
      apply Finset.ext
      intro i
      simp only [Finset.mem_univ]
    rw [hu]
    exact (subtype_product_le_full
      (fun i : sigma=>Membership.mem T i) H hH1).trans hprod
  have hall := fun b : forall i : {i : sigma // Not (Membership.mem T i)},lists i.val=>
    he g J F Q0 hJ hF A Z Lambda d ell0 shift O0
      hZ hLambda0 hLambda1 hd hd1 hell hellcap hshift hOeq
      parents (rowsb b) hparents ((hbsub b).trans hsub) hbad
      (fun i : T=>lists i.val) (fun i : T=>H i.val) hdisT
      (fun i=>hmax i.val) (fun i=>hgood i.val) (fun i=>hprime i.val) (hbr b)
      (fun i=>hH i.val) hpT hGN hGchar (fun K hK=>hrowcop K (hbsub b hK))
      (fun i=>hLN i.val) (fun i=>hLchar i.val)
  choose Db hDb using hall
  let D := fun (K : rows)
    (b : supportedSlotChoices (fun i : {i : sigma // Not (Membership.mem T i)}=>lists i.val) FF K.val)
    (p : supportedSlotChoices (fun i : T=>lists i.val) FF K.val)=>
      Db b.val (Subtype.mk K.val
        ((inactiveRows_mem rows lists T FF b.val K.val).mpr
          (And.intro K.property b.property))) p
  refine Exists.intro D ?_
  intro theta w hw
  let f := fun (K : rows)
    (b : supportedSlotChoices (fun i : {i : sigma // Not (Membership.mem T i)}=>lists i.val) FF K.val)=>
    Finset.univ.sum (fun p : supportedSlotChoices (fun i : T=>lists i.val) FF K.val=>
      (Finset.univ.prod fun i : T=>w i.val (p.val i))*mixedReflectedValue (D K b p) (s g)
        (G.reflected K.val (hrows K.val K.property)
          (slotChoiceFamily (fun i : T=>lists i.val)
            (fun i=>hmax i.val) (fun i=>hgood i.val) p.val)).generator_ne_zero (hc0 g)
        (G.reflected K.val (hrows K.val K.property)
          (slotChoiceFamily (fun i : T=>lists i.val)
            (fun i=>hmax i.val) (fun i=>hgood i.val) p.val)).generator_good
        (OAI.SevenEighths.InverseReflectedPhase.reflectedExponent
          (fun b : A=>completedLocalExponent J F b.val.val))
        (slotIndices A (PrimeIndex K.val) T)
        (CompletedHeight.normTwistedSource W theta) (Z^(1+ell0+shift)))
  have hzpos : 0<Z := lt_trans zero_lt_one (lt_of_lt_of_le hZ0 hZ)
  apply supported_inactive_source_energy rows lists T FF H
    (fun i P hP=>(hprime i P hP).ne_zero) hH w hw f
    (C*(1+norm theta)^degree*
      Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+505*eta-O0/2)) (by positivity)
  intro b
  exact hDb b theta (fun i : T=>w i.val) (fun i P=>hw i.val P)

theorem low_original_frozen_energy_general
    {gamma : Type u} [Fintype gamma] (a c0 : gamma->Eis) (mode : gamma->Bool)
    [Fintype (HasQuotient.Quotient Eis (Ideal.span {Nlevel^2}))]
    (lo hi : Real) (hlo : 0<lo) (W : Real->Complex)
    (hWs : Set.Subset (Function.support W) (Set.Icc lo hi))
    (hW : ContDiff Real ((Top.top : ENat) : WithTop ENat) W)
    (s : forall i, FixedCuspShape
      (ControlledStratumArithmetic.fixedCusp (a i) (c0 i) (mode i)))
    (hc0 : forall i, Not (c0 i=0))
    (hNlevel : forall i, Dvd.dvd ((9:Eis)*c0 i) Nlevel)
    (hbase : forall i, if mode i then Dvd.dvd (ConcretePrimeRowBridge.goodLambda^2) (a i-1)
      else Dvd.dvd (ConcretePrimeRowBridge.goodLambda^2) (c0 i-1))
    (hac : forall i, IsCoprime (a i) (c0 i))
    (Q : Ideal Eis) (hQ : Not (Q=0))
    (Ck eta : Real) (hCk : 0<Ck) (heta : 0<eta) (heta1 : eta<=1) (rmax : Nat) :
    Exists fun degree : Nat => Exists fun C : Real => Exists fun Z0 : Real =>
    0<C /\ 1<Z0 /\
    forall {sigma : Type v} [Fintype sigma] [DecidableEq sigma],
    forall (J F Q0 : Ideal Eis) (_hJ : Not (J=0)) (_hF : Not (F=0)),
    forall (Z Lambda d ell0 shift O0 : Real),
      Z0<=Z -> 0<=Lambda -> Lambda<=1/5 -> 0<=d -> d<=Lambda ->
      0<=ell0 -> ell0<=Lambda-d+eta -> abs shift<=eta ->
      O0=normWidth Z (rowPowerfulPart J) ->
      (Ideal.absNorm J:Real)<=Ck*Z^(1-Lambda-2*d) ->
    forall (parents rows : Finset (Ideal Eis)),
      (forall I, Membership.mem parents I ->
        Not (I=0) /\ (Ideal.absNorm I:Real)<=Ck*Z^(1-Lambda-2*d)) ->
      rows<=originalResidualRows parents J Q ->
      (forall P, Membership.mem fixedBadPrimes P -> Dvd.dvd P Q) ->
      Fintype.card sigma<=rmax ->
    forall (lists : sigma->Finset (Ideal Eis)) (H : sigma->Real)
      (_hdis : Pairwise (fun i j=>Disjoint (lists i) (lists j)))
      (hmax : forall i, forall P, Membership.mem (lists i) P -> P.IsMaximal)
      (hgood : forall i, forall P, Membership.mem (lists i) P ->
        Not (Membership.mem P ConcretePrimeRowBridge.goodLambda))
      (_hprime : forall i, forall P, Membership.mem (lists i) P -> Prime P)
      (hrows : forall K, Membership.mem rows K -> Admissible K),
      (forall i, 1<=H i) ->
      (forall i, forall P, Membership.mem (lists i) P -> (Ideal.absNorm P:Real)<=H i) ->
      (Finset.univ.prod H)<=Z^ell0 ->
      (forall f, IsCoprime (Ideal.span {Nlevel}) ((poolPrimeFamily J Q Q0).ideal f)) ->
      (forall f, Not (ringChar (HasQuotient.Quotient Eis ((poolPrimeFamily J Q Q0).ideal f))=2)) ->
      (forall K, Membership.mem rows K ->
        (forall f, IsCoprime ((poolPrimeFamily J Q Q0).ideal f) K) /\
          IsCoprime (Ideal.span {Nlevel}) K) ->
      (forall i, forall P, Membership.mem (lists i) P -> IsCoprime (Ideal.span {Nlevel}) P) ->
      (forall i, forall P, Membership.mem (lists i) P ->
        Not (ringChar (HasQuotient.Quotient Eis P)=2)) ->
    Exists (fun D :
      (forall g : gamma, forall A : Finset (FreeReflection.pool J Q Q0), forall T : Finset sigma,
        OriginalSplitCompletion (N:=Nlevel) (a:=a g) (c:=c0 g) (mode:=mode g)
          ((poolPrimeFamily J Q Q0).restrict A) (poolPrimeFamily J Q Q0).ideal
          rows hrows lists hmax hgood T) =>
    forall (theta : Real) (w : forall i, lists i->Complex) (scalar : gamma->rows->Complex),
      (forall i P, norm (w i P)<=1) ->
      (forall g K, norm (scalar g K)<=1) ->
      (Finset.univ.sum fun K : rows=>norm (Inv.inv thetaDerivativeScalar*
        Finset.univ.sum (fun g : gamma=>scalar g K*
          Finset.univ.sum (fun A : Finset (FreeReflection.pool J Q Q0)=>
            frozenInactiveWeight J F Q Q0 A*
            Finset.univ.sum (fun T : Finset sigma=>originalInactivePhysical
              ((poolPrimeFamily J Q Q0).restrict A) (poolPrimeFamily J Q Q0).ideal
              rows hrows lists hmax hgood T (D g A T) (s g) (hc0 g)
              (fun b : A=>completedLocalExponent J F b.val.val)
              (CompletedHeight.normTwistedSource W theta) (Z^(1+ell0+shift)) w K))))^2)<=
        C*(1+norm theta)^degree*
          Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+506*eta-O0/2)) := by
  have hb := low_original_inactive_energy_general a c0 mode lo hi hlo W hWs hW
    s hc0 hNlevel hbase hac Q hQ Ck eta hCk heta heta1
  choose degree C Z1 hC hZ1 he using hb
  let eps := eta/8
  have heps : 0<eps := by dsimp [eps];positivity
  have hbudget := @original_source_cost_budget gamma inferInstance rmax eps heps
  cases hbudget with
  | intro Cb hb0 =>
    have hCb : 0<Cb := hb0.1
    let Z0 := max Z1 (max 2 (max Ck (Ideal.absNorm Q:Real)))
    refine Exists.intro degree
      (Exists.intro ((norm (Inv.inv thetaDerivativeScalar)^2+1)*Cb*C)
        (Exists.intro Z0 (And.intro (by positivity)
          (And.intro (hZ1.trans_le (le_max_left _ _)) ?_))))
    intro sigma _ _ J F Q0 hJ hF Z Lambda d ell0 shift O0
      hZ hLambda0 hLambda1 hd hd1 hell hellcap hshift hOeq hJn
      parents rows hparents hsub hbad hcard lists H hdis hmax hgood hprime
      hrows hH1 hH hprod hGN hGchar hrowcop hLN hLchar
    have hz1 : Z1<=Z := (le_max_left _ _).trans hZ
    have hz : 1<Z := lt_of_lt_of_le hZ1 hz1
    have hzp : 0<Z := lt_trans zero_lt_one hz
    let FF := (poolPrimeFamily J Q Q0).ideal
    have hall := fun (g : gamma) (A : Finset (FreeReflection.pool J Q Q0)) (T : Finset sigma)=>
      he g J F Q0 hJ hF A Z Lambda d ell0 shift O0
        hz1 hLambda0 hLambda1 hd hd1 hell hellcap hshift hOeq
        parents rows hparents hsub hbad lists H hdis hmax hgood hprime hrows hH1 hH hprod
        (fun f=>hGN f.val) (fun f=>hGchar f.val)
        (fun K hK=>And.intro (fun f=>(hrowcop K hK).1 f.val) (hrowcop K hK).2)
        hLN hLchar T
    choose D hD using hall
    refine Exists.intro D ?_
    intro theta w scalar hw hscalar
    let energy := C*(1+norm theta)^degree*
      Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+505*eta-O0/2)
    let harm := (Finset.univ.prod fun i=>256*(columnDyadicLength (H i)+1:Real))^2
    let source := fun (g : gamma) (A : Finset (FreeReflection.pool J Q Q0))
      (T : Finset sigma) (K : rows)=>
      originalInactivePhysical ((poolPrimeFamily J Q Q0).restrict A) FF
        rows hrows lists hmax hgood T (D g A T) (s g) (hc0 g)
        (fun b : A=>completedLocalExponent J F b.val.val)
        (CompletedHeight.normTwistedSource W theta) (Z^(1+ell0+shift)) w K
    have hs (g : gamma) (A : Finset (FreeReflection.pool J Q Q0)) (T : Finset sigma) :
        (Finset.univ.sum fun K : rows=>norm (source g A T K)^2)<=harm*energy := by
      apply (hD g A T theta w hw).trans
      apply mul_le_mul_of_nonneg_right ?_ (by dsimp [energy];positivity)
      have hterms : forall i, 1<=256*(columnDyadicLength (H i)+1:Real) := by
        intro i
        have hn : (0:Real)<=(columnDyadicLength (H i):Real) := Nat.cast_nonneg _
        linarith
      have hp := subtype_product_le_full
        (fun i : sigma=>Not (Membership.mem T i))
        (fun i=>256*(columnDyadicLength (H i)+1:Real)) hterms
      dsimp only [harm]
      simpa only [pow_two] using
        (mul_le_mul hp hp (by positivity) (by positivity))
    let Labels := Prod gamma (Prod (Finset (FreeReflection.pool J Q Q0)) (Finset sigma))
    let f := fun (b : Labels) (K : rows)=>
      (scalar b.1 K*frozenInactiveWeight J F Q Q0 b.2.1)*source b.1 b.2.1 b.2.2 K
    have hf (b : Labels) : (Finset.univ.sum fun K : rows=>norm (f b K)^2)<=harm*energy := by
      apply (bounded_row_multiplier_energy Finset.univ _ _ (fun K hK=>?_)).trans
        (hs b.1 b.2.1 b.2.2)
      rw [norm_mul]
      exact (mul_le_mul (hscalar b.1 K) (frozenInactiveWeight_norm J F Q Q0 b.2.1)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    have hfam := weighted_finite_row_energy_uniform
      (Finset.univ : Finset Labels) (Finset.univ : Finset rows)
      (fun _=>(1:Complex)) f (harm*energy) (fun b _=>hf b)
    simp only [one_mul,norm_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hfam
    have hid (K : rows) : (Finset.univ.sum fun b : Labels=>f b K)=
        Finset.univ.sum (fun g : gamma=>scalar g K*
          Finset.univ.sum (fun A : Finset (FreeReflection.pool J Q Q0)=>
            frozenInactiveWeight J F Q Q0 A*
              Finset.univ.sum (fun T : Finset sigma=>source g A T K))) := by
      simp only [Labels,f,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]
    have hsource : (Finset.univ.sum fun K : rows=>norm (Inv.inv thetaDerivativeScalar*
        Finset.univ.sum (fun g : gamma=>scalar g K*
          Finset.univ.sum (fun A : Finset (FreeReflection.pool J Q Q0)=>
            frozenInactiveWeight J F Q Q0 A*
              Finset.univ.sum (fun T : Finset sigma=>source g A T K))))^2)<=
        norm (Inv.inv thetaDerivativeScalar)^2*(Fintype.card Labels:Real)^2*harm*energy := by
      simp_rw [<-hid]
      simp only [norm_mul,mul_pow,<-Finset.mul_sum]
      exact (mul_le_mul_of_nonneg_left hfam (sq_nonneg _)).trans_eq (by ring)
    apply hsource.trans
    have hQn : (Ideal.absNorm Q:Real)<=Z :=
      (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hZ))
    have hCkZ : Ck<=Z :=
      (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hZ))
    have hJcap : (Ideal.absNorm J:Real)<=Z^(2:Real) := by
      apply hJn.trans
      calc
        Ck*Z^(1-Lambda-2*d) <= Z*Z^(1-Lambda-2*d) :=
          mul_le_mul_of_nonneg_right hCkZ (Real.rpow_nonneg hzp.le _)
        _ = Z^(1+(1-Lambda-2*d)) := by rw [Real.rpow_add hzp,Real.rpow_one]
        _ <= _ := Real.rpow_le_rpow_of_exponent_le hz.le (by linarith)
    have hpool : (Ideal.absNorm (J*Q):Real)<=Z^(3:Real) := by
      rw [map_mul,Nat.cast_mul]
      calc
        _ <= Z^(2:Real)*Z :=
          mul_le_mul hJcap hQn (Nat.cast_nonneg _) (Real.rpow_nonneg hzp.le _)
        _ = _ := by norm_num;ring
    have hslot : (Finset.univ.prod H)<=Z^(2:Real) :=
      hprod.trans (Real.rpow_le_rpow_of_exponent_le hz.le (by linarith))
    have hcst := hb0.2 H hcard hH1 J Q Q0 hJ hQ Z 3 2 eta hz hpool hslot
      (by dsimp [eps];linarith)
    calc
      _ = norm (Inv.inv thetaDerivativeScalar)^2*
          ((Fintype.card Labels:Real)^2*harm)*energy := by ring
      _ <= (norm (Inv.inv thetaDerivativeScalar)^2+1)*(Cb*Z^eta)*energy := by
        apply mul_le_mul_of_nonneg_right ?_ (by dsimp [energy];positivity)
        exact mul_le_mul (by linarith) hcst (by dsimp [harm];positivity) (by positivity)
      _ = ((norm (Inv.inv thetaDerivativeScalar)^2+1)*Cb*C)*(1+norm theta)^degree*
          Z^(eta+((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+505*eta-O0/2)) := by
        dsimp only [energy]
        rw [Real.rpow_add hzp]
        ring
      _ <= _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hz.le (by linarith)) (by positivity)

end PrimeFactorOscillations.GeneralLowGeometry

