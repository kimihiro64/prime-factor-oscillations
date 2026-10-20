/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Reflection.LowChoiceEnergy
import PrimeFactorOscillations.Assembly.DetectorPackets.GeneralLowFixedMember

/-!
# GeneralLowChoiceEnergy

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
# The full original-choice energy with a variable slot budget

Uses the actual dyadic count budget before transporting the complete
coupled member sum to supported original slot choices. All arithmetic
completion phases and the reflected max excess are retained.
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

theorem low_original_choice_energy_general
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
    Exists (fun degree : Nat => Exists (fun C : Real => Exists (fun Z0 : Real =>
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
      (forall i, forall P, Membership.mem (lists i) P -> (Ideal.absNorm P:Real)<=H i) ->
      (Finset.univ.prod H)<=Z^ell0 ->
      (forall f, IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) ->
      (forall f, Not (ringChar (HasQuotient.Quotient Eis (G.ideal f))=2)) ->
      (forall K, Membership.mem rows K ->
        (forall f, IsCoprime (G.ideal f) K) /\ IsCoprime (Ideal.span {Nlevel}) K) ->
      (forall i, forall P, Membership.mem (lists i) P -> IsCoprime (Ideal.span {Nlevel}) P) ->
      (forall i, forall P, Membership.mem (lists i) P ->
        Not (ringChar (HasQuotient.Quotient Eis P)=2)) ->
    Exists (fun D :
      (forall K : rows,
       forall p : supportedSlotChoices lists (poolPrimeFamily J Q Q0).ideal K.val,
        ControlledStratumArithmetic
          (G.reflected K.val (hrows K.val K.property)
            (slotChoiceFamily lists hmax hgood p.val)).generator
          Nlevel (a g) (c0 g) (mode g)) =>
    forall (theta : Real) (w : forall i, lists i->Complex),
      (forall i P, norm (w i P)<=1) ->
      (Finset.univ.sum fun K : rows=>
        norm (Finset.univ.sum fun p : supportedSlotChoices lists (poolPrimeFamily J Q Q0).ideal K.val=>
          (Finset.univ.prod fun i=>w i (p.val i))*mixedReflectedValue (D K p) (s g)
            (G.reflected K.val (hrows K.val K.property)
              (slotChoiceFamily lists hmax hgood p.val)).generator_ne_zero (hc0 g)
            (G.reflected K.val (hrows K.val K.property)
              (slotChoiceFamily lists hmax hgood p.val)).generator_good
            (OAI.SevenEighths.InverseReflectedPhase.reflectedExponent jF)
            (slotIndices A (PrimeIndex K.val) sigma)
            (CompletedHeight.normTwistedSource W theta) (Z^(1+ell0+shift)))^2)<=
        C*(1+norm theta)^degree*Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+505*eta-O0/2))))) := by
  have hbase := low_dyadic_geometry_uniform_general a c0 mode lo hi hlo W hWs hW
    s hc0 hNlevel hbase hac Q hQ Ck eta hCk heta heta1
  cases hbase with
  | intro degree h0 =>
    cases h0 with
    | intro C h1 =>
      cases h1 with
      | intro Z0 he =>
        have hbins := actual_dyad_count_budget 8 eta (by norm_num) heta
        cases hbins with
        | intro Cb hb0 =>
          have hC : 0<C := he.1
          have hZ0 : 1<Z0 := he.2.1
          have hCb : 0<Cb := hb0.1
          refine Exists.intro degree (Exists.intro (Cb*C)
            (Exists.intro (max Z0 (max 2 Ck)) (And.intro (mul_pos hCb hC)
              (And.intro (hZ0.trans_le (le_max_left _ _)) ?_))))
          intro g sigma _ _ J F Q0 hJ hF A Z Lambda d ell0 shift O0
            hZ hLambda0 hLambda1 hd hd1 hell hellcap hshift hOeq parents rows hparents hsub hbad
          have hZbase : Z0<=Z := (le_max_left _ _).trans hZ
          have hCkZ : Ck<=Z := (le_max_right _ _).trans ((le_max_right _ _).trans hZ)
          dsimp only
          intro lists H hdis hmax hgood hprime hrows hH hprod hGN hGchar hrowcop hLN hLchar
          let G := (poolPrimeFamily J Q Q0).restrict A
          let FF := (poolPrimeFamily J Q Q0).ideal
          let tuples := fixedSlotTupleSet lists FF
          let hm := originalTupleMax lists FF hmax
          let hg := originalTupleGood lists FF hgood
          have htuples : forall p, Membership.mem tuples p -> forall i,
              Membership.mem (lists i) (p i) :=
            fun p hp=>((mem_fixedSlotTupleSet lists FF p).mp hp).1
          have hpair : forall p : tuples, Pairwise
              (Function.onFun IsCoprime (G.sum (memberTupleFamily tuples hm hg p)).ideal) := by
            intro p
            refine PrimeFamily.sum_pairwise G _
              ((poolPrimeFamily J Q Q0).restrict_pairwise (poolPrimeFamily_pairwise J Q Q0) A) ?_ ?_
            . intro i j hij
              apply Ideal.isCoprime_of_isMaximal
              intro heq
              change p.val i=p.val j at heq
              have hjmem : Membership.mem (lists j) (p.val i) := by
                rw [heq]
                exact htuples p.val p.property j
              exact Finset.disjoint_left.mp (hdis hij) (htuples p.val p.property i) hjmem
            . intro f i
              apply Ideal.isCoprime_of_isMaximal
              exact (((mem_fixedSlotTupleSet lists FF p.val).mp p.property).2 f.val i).symm
          have hPN : forall p : tuples, forall b, IsCoprime (Ideal.span {Nlevel})
              ((G.sum (memberTupleFamily tuples hm hg p)).ideal b) := by
            intro p b
            cases b with
            | inl f => exact hGN f
            | inr i => exact hLN i _ (htuples p.val p.property i)
          have hPchar : forall p : tuples, forall b,
              Not (ringChar (HasQuotient.Quotient Eis
                ((G.sum (memberTupleFamily tuples hm hg p)).ideal b))=2) := by
            intro p b
            cases b with
            | inl f => exact hGchar f
            | inr i => exact hLchar i _ (htuples p.val p.property i)
          have hPnorm : forall p, Membership.mem tuples p ->
              CubicSieve.Admissible (slotTupleProduct p) /\
                (Ideal.absNorm (slotTupleProduct p):Real)<=Z^ell0 := by
            intro p hp
            refine And.intro (slotTupleProduct_admissible lists hdis hprime ?_ p (htuples p hp)) ?_
            . intro i P hPi
              let : P.IsMaximal := hmax i P hPi
              rw [<-primaryPrime_eq_primaryGenerator P]
              exact primaryPrime_ne_zero P (hgood i P hPi)
            . exact (slotTupleProduct_norm_bound lists H
                (fun i P hPi=>(hprime i P hPi).ne_zero) hH p (htuples p hp)).2.trans hprod
          let Hrow := (Ck*Z^(1-Lambda-2*d))/
            ((Ideal.absNorm (rowPowerfulPart J):Real)*(Ideal.absNorm (rowMaskPart J Q):Real))
          let Hslot := Z^ell0
          have hdyads := he.2.2 g J F Q0 hJ hF A Z Lambda d ell0 shift O0
            hZbase hLambda0 hLambda1 hd hd1 hell hellcap hshift hOeq
            parents rows hparents hsub hbad tuples hm hg
            (fixedSlotTupleSet_product_injective lists FF hdis hprime)
            hrows hGN hGchar hrowcop hpair hPN hPchar hPnorm
          cases hdyads with
          | intro Dc hDc =>
            let D := fun (K : rows) (p : supportedSlotChoices lists FF K.val) =>
              memberChoiceControlled lists FF hmax hgood G K.val (hrows K.val K.property)
                (dyadicTupleControlled G rows hrows tuples hm hg Hrow Hslot Dc K) p
            refine Exists.intro D ?_
            intro theta w hw
            let tupleRow := fun K : rows=>Finset.univ.sum (fun p : tuples=>
              dyadicPhysicalTerm G rows hrows tuples hm hg Hrow Hslot Dc
                (s g) (hc0 g) (fun b : A=>completedLocalExponent J F b.val.val)
                W theta (Z^(1+ell0+shift)) (fun _=>1) (fixedTupleCoefficient lists w) K p)
            let choiceRow := fun K : rows=>Finset.univ.sum
              (fun p : supportedSlotChoices lists FF K.val=>
                (Finset.univ.prod fun i=>w i (p.val i))*mixedReflectedValue (D K p) (s g)
                  (G.reflected K.val (hrows K.val K.property)
                    (slotChoiceFamily lists hmax hgood p.val)).generator_ne_zero (hc0 g)
                  (G.reflected K.val (hrows K.val K.property)
                    (slotChoiceFamily lists hmax hgood p.val)).generator_good
                  (OAI.SevenEighths.InverseReflectedPhase.reflectedExponent
                    (fun b : A=>completedLocalExponent J F b.val.val))
                  (slotIndices A (PrimeIndex K.val) sigma)
                  (CompletedHeight.normTwistedSource W theta) (Z^(1+ell0+shift)))
            have hsource (K : rows) : tupleRow K=choiceRow K := by
              simpa only [tupleRow,choiceRow,dyadicPhysicalTerm,D,one_mul] using
                member_source_eq_original_choices lists FF hmax hgood G K.val
                  (hrows K.val K.property) (dyadicTupleControlled G rows hrows tuples hm hg Hrow Hslot Dc K)
                  (s g) (hc0 g) (fun b : A=>completedLocalExponent J F b.val.val)
                  (CompletedHeight.normTwistedSource W theta) (Z^(1+ell0+shift)) 1 w
            have hb := hDc theta (fun _=>1) (fixedTupleCoefficient lists w)
              (by simp) (fun p hp=>fixedTupleCoefficient_norm lists w hw p)
            have hid : (Finset.univ.sum fun K : rows=>norm (tupleRow K)^2)=
                Finset.univ.sum (fun K : rows=>norm (choiceRow K)^2) := by
              apply Finset.sum_congr rfl
              intro K hK
              exact congrArg (fun z : Complex=>norm z^2) (hsource K)
            apply (hid.symm.trans_le hb).trans
            have hz : 1<Z := lt_of_lt_of_le hZ0 hZbase
            have hzpos : 0<Z := lt_trans zero_lt_one hz
            have hp : (1:Real)<=(Ideal.absNorm (rowPowerfulPart J):Real) :=
              QuadraticMainBoundary.norm_one_le (rowPowerfulPart_ne_zero J)
            have hMask : (1:Real)<=(Ideal.absNorm (rowMaskPart J Q):Real) :=
              QuadraticMainBoundary.norm_one_le (squarefreeMaskPart_ne_zero (rowSimplePart J) Q)
            have hRpos : 0<Hrow := by dsimp [Hrow];positivity
            have hScap : Hslot<=Z^(8:Real) :=
              Real.rpow_le_rpow_of_exponent_le hz.le (by linarith)
            have hRcap : Hrow<=Z^(8:Real) := by
              apply (div_le_self (by positivity) (one_le_mul_of_one_le_of_one_le hp hMask)).trans
              calc
                Ck*Z^(1-Lambda-2*d) <= Z*Z^(1-Lambda-2*d) :=
                  mul_le_mul_of_nonneg_right hCkZ (Real.rpow_nonneg hzpos.le _)
                _ = Z^(1+(1-Lambda-2*d)) := by rw [Real.rpow_add hzpos,Real.rpow_one]
                _ <= _ := Real.rpow_le_rpow_of_exponent_le hz.le (by linarith)
            have hcount := hb0.2 Z Hrow Hslot hz.le hRpos
              (Real.rpow_pos_of_pos hzpos _) hRcap hScap
            calc
              _ <= (Cb*Z^eta)*(C*(1+norm theta)^degree*Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+504*eta-O0/2)) :=
                mul_le_mul_of_nonneg_right hcount (by positivity)
              _ = (Cb*C)*(1+norm theta)^degree*Z^(eta+((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+504*eta-O0/2)) := by
                rw [Real.rpow_add hzpos]
                ring
              _ <= _ := mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow_of_exponent_le hz.le (by linarith)) (by positivity)

end PrimeFactorOscillations.GeneralLowGeometry
