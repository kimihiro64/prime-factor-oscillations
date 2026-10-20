/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Reflection.LowOriginalEnergy
import PrimeFactorOscillations.Assembly.DetectorPackets.GeneralLowFrozenEnergy

/-!
# GeneralLowCompletedEnergy

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
# Actual completed-source energy with a variable slot budget

Carries the full frozen source through the exact completed-fiber identity,
weighted parent aggregation and actual puncture removal. The reflected max
excess remains explicit throughout.
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

theorem low_completed_fiber_energy_general (Q : Ideal Eis) (hQ : Not (Q=0))
    (F : Ideal Eis) (hF : Squarefree F) (m : Eis) (hm : Not (m=0))
    (hmLam : Dvd.dvd ConcretePrimeRowBridge.goodLambda m) (hm2 : Dvd.dvd (2:Eis) m)
    (hperiod : Dvd.dvd (Q*Ideal.span {(72:Eis)}) (Ideal.span {m}))
    (hbad : forall P, Membership.mem fixedBadPrimes P -> Dvd.dvd P (Ideal.span {m}*F))
    (lo hi : Real) (hlo : 0<lo) (W : Real->Complex)
    (hWs : Set.Subset (Function.support W) (Set.Icc lo hi))
    (hW : ContDiff Real ((Top.top : ENat) : WithTop ENat) W)
    (Ck eta : Real) (hCk : 0<Ck) (heta : 0<eta) (heta1 : eta<=1) (rmax : Nat) :
    Exists fun degree : Nat => Exists fun C : Real => Exists fun Z0 : Real =>
    0<C /\ 1<Z0 /\
    forall {sigma : Type v} [Fintype sigma] [DecidableEq sigma],
    forall (J : Ideal Eis) (_hJ : Not (J=0)) (Z Lambda d ell0 shift : Real),
      Z0<=Z -> 0<=Lambda -> Lambda<=1/5 -> 0<=d -> d<=Lambda ->
      0<=ell0 -> ell0<=Lambda-d+eta -> abs shift<=eta ->
      (Ideal.absNorm J:Real)<=Ck*Z^(1-Lambda-2*d) ->
    forall parents : Finset (Ideal Eis),
      (forall I, Membership.mem parents I ->
        Not (I=0) /\ (Ideal.absNorm I:Real)<=Ck*Z^(1-Lambda-2*d)) ->
      Fintype.card sigma<=rmax -> forall (lists : sigma->Finset (Ideal Eis)) (H : sigma->Real),
      Pairwise (fun i j=>Disjoint (lists i) (lists j)) ->
      (forall i, forall P, Membership.mem (lists i) P -> P.IsMaximal) ->
      (forall i, forall P, Membership.mem (lists i) P ->
        Not (Membership.mem P ConcretePrimeRowBridge.goodLambda)) ->
      (forall i, forall P, Membership.mem (lists i) P -> Prime P) ->
      (forall i, forall P, Membership.mem (lists i) P ->
        Not (ringChar (HasQuotient.Quotient Eis P)=2)) ->
      (forall i, forall P, Membership.mem (lists i) P ->
        IsCoprime (Q*Ideal.span {(72:Eis)}) P) ->
      (forall i, 1<=H i) ->
      (forall i, forall P, Membership.mem (lists i) P -> (Ideal.absNorm P:Real)<=H i) ->
      (Finset.univ.prod H)<=Z^ell0 ->
    forall (Psi : MonoidHom Eis Complex), (forall n, norm (Psi n)<=1) ->
      CanonicalCoefficientClass.FactorsModulo Q Psi ->
    forall (u : Units Eis) (theta : Real) (w : forall i, lists i->Complex),
      (forall i P, norm (w i P)<=1) ->
      ((representativeRowFiber parents J (Ideal.span {m}*F)).sum fun I=>norm (Finset.univ.sum fun p : forall i,lists i=>
          (Finset.univ.prod fun i=>w i (p i))*markedCompletedT
            (rowTwist Psi m (ConcretePrimeRowBridge.idealGenerator F)
              (u.val*ConcretePrimeRowBridge.idealGenerator I))
            (CompletedHeight.normTwistedSource W theta) (Z^(1+ell0+shift))
            (fun A=>Finset.univ.prod fun i=>if Dvd.dvd (p i).val A then (1:Complex) else 0))^2)<=
        C*(1+norm theta)^degree*Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+506*eta)*
          (Ideal.absNorm (rowPowerfulPart J):Real)^(-(1/2:Real)) := by
  let Q0 := Q*Ideal.span {(72:Eis)}
  let c : Eis := (9:Eis)*(ConcretePrimeRowBridge.idealGenerator Q)*(72:Eis)
  have hc : Not (c=0) := mul_ne_zero
    (mul_ne_zero (by norm_num) (ConcretePrimeRowBridge.idealGenerator_ne_zero Q hQ))
    (by norm_num)
  have hcQ : Ideal.span {c}=Ideal.span {(9:Eis)}*Q0 := by
    dsimp only [c,Q0]
    rw [<-Ideal.span_singleton_mul_span_singleton,<-Ideal.span_singleton_mul_span_singleton,
      ConcretePrimeRowBridge.span_idealGenerator]
    ring
  let : Finite (HasQuotient.Quotient Eis (Ideal.span {c})) :=
    ConcreteTraceCRT.finite_quotient_span hc
  let : Fintype (HasQuotient.Quotient Eis (Ideal.span {c})) := Fintype.ofFinite _
  let : Finite (HasQuotient.Quotient Eis (Ideal.span {((9:Eis)*c)^2})) :=
    ConcreteTraceCRT.finite_quotient_span (pow_ne_zero 2 (mul_ne_zero (by norm_num) hc))
  let : Fintype (HasQuotient.Quotient Eis (Ideal.span {((9:Eis)*c)^2})) := Fintype.ofFinite _
  let mask := Ideal.span {m}*F
  have hmask0 : Not (mask=0) :=
    mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm) hF.ne_zero
  let E := fixedFourierGeometry c hc
  have hEc : forall h, Not ((E h).c0=0) := fun h=>(E h).denominator_ne_zero
  have hEN : forall h, Dvd.dvd ((9:Eis)*(E h).c0) ((9:Eis)*c) :=
    fun h=>mul_dvd_mul_left (9:Eis) (E h).denominator_dvd
  have hb := low_original_frozen_energy_general
    (fun h=>(E h).a0) (fun h=>(E h).c0) (fun h=>(E h).mode)
    lo hi hlo W hWs hW (fun h=>(E h).shape) hEc hEN
    (fun h=>(E h).primary) (fun h=>(E h).coprime) mask hmask0 Ck eta hCk heta heta1 rmax
  choose degree C Z0 hC hZ0 he using hb
  refine Exists.intro degree (Exists.intro C
    (Exists.intro Z0 (And.intro hC (And.intro hZ0 ?_))))
  intro sigma _ _ J hJ Z Lambda d ell0 shift hZ hLambda0 hLambda1 hd hd1 hell hellcap hshift hJn
    parents hparents hcard lists H hdis hmax hgood hprime hodd hLP hH1 hH hprod
    Psi hPsinorm hPsiperiod u theta w hw
  let rows := originalResidualRows parents J mask
  have hparents0 : forall I, Membership.mem parents I -> Not (I=0) :=
    fun I hI=>(hparents I hI).1
  let hrows : forall K, Membership.mem rows K -> Admissible K :=
    originalResidualAdmissible parents J F m hbad
  have hcop : forall K, Membership.mem rows K -> IsCoprime Q0 K := by
    intro K hK
    cases Finset.mem_image.mp hK with
    | intro I hI =>
      cases hI with
      | intro hIf heq =>
        subst K
        exact rowResidualPart_coprime_period I F Q0 m hperiod
  have hGN : forall f,
      IsCoprime (Ideal.span {(9:Eis)*c}) ((poolPrimeFamily J mask Q0).ideal f) :=
    (poolPrimeFamily J mask Q0).level_coprime Q0 c hcQ (poolPrimeFamily_period J mask Q0)
  have hrowcop : forall K, Membership.mem rows K ->
      (forall f, IsCoprime ((poolPrimeFamily J mask Q0).ideal f) K) /\
        IsCoprime (Ideal.span {(9:Eis)*c}) K := by
    intro K hK
    refine And.intro ?_ (residual_level_coprime K Q0 (hrows K hK) c hcQ (hcop K hK))
    cases Finset.mem_image.mp hK with
    | intro I hI =>
      cases hI with
      | intro hIf heq =>
        subst K
        have hparts := Finset.mem_filter.mp hIf
        exact poolPrimeFamily_fiber_row_coprime J I mask Q0 hJ (hparents0 I hparts.1)
          hmask0 hparts.2.1.symm hparts.2.2.symm
  have hLN : forall i, forall P, Membership.mem (lists i) P ->
      IsCoprime (Ideal.span {(9:Eis)*c}) P :=
    fun i P hP=>maximal_prime_level_coprime P (hmax i P hP)
      (hgood i P hP) Q0 c hcQ (hLP i P hP)
  have hz : 1<Z := lt_of_lt_of_le hZ0 hZ
  have hzp : 0<Z := lt_trans zero_lt_one hz
  let O := normWidth Z (rowPowerfulPart J)
  have hPowPos : 0<(Ideal.absNorm (rowPowerfulPart J):Real) := by
    have hp := QuadraticMainBoundary.norm_one_le (rowPowerfulPart_ne_zero J)
    linarith
  have hcompletion := he (sigma:=sigma) J F Q0 hJ hF.ne_zero
    Z Lambda d ell0 shift O hZ hLambda0 hLambda1 hd hd1 hell hellcap hshift rfl hJn
    parents rows hparents (Finset.Subset.refl _) hbad hcard lists H hdis hmax hgood hprime
    hrows hH1 hH hprod hGN (poolPrimeFamily_odd J mask Q0) hrowcop hLN hodd
  cases hcompletion with
  | intro D hD =>
    let scalar := fun h (K : rows)=>fixedThetaRowCoeff c hc
      ((residualOriginalData parents J F hF m hm hparents0 u K).fixedFactor Psi Q) h
    have hscalar : forall h K, norm (scalar h K)<=1 :=
      fun h K=>(residualOriginalData parents J F hF m hm hparents0 u K).fixedCoefficient_norm
        Psi Q hPsinorm c hc h
    have henergy := hD theta w scalar hw hscalar
    have hTw : ContDiff Real ((Top.top : ENat) : WithTop ENat)
        (CompletedHeight.normTwistedSource W theta) :=
      CanonicalRowCompletion.normTwistedSource_contDiff W lo hi hlo hWs hW theta
    have hTs := (CompletedHeight.normTwistedSource_support W theta).trans hWs
    have hTc : HasCompactSupport (CompletedHeight.normTwistedSource W theta) :=
      HasCompactSupport.intro isCompact_Icc (fun x hx=>by
        by_contra hn
        exact hx (hTs hn))
    have hid (K : rows) := original_completed_residual_source
      parents J F hJ hF m hm hparents0 u hbad Q hQ c hc hcQ E hcop
      lists hmax hgood hdis hodd hLP D Psi hPsinorm hPsiperiod hmLam hm2
      (CompletedHeight.normTwistedSource W theta) hTc lo hi hlo hTs hTw
      (Z^(1+ell0+shift)) (Real.rpow_pos_of_pos hzp _) w K
    let physicalRow : Ideal Eis->Complex := fun I=>
      Finset.univ.sum fun p : forall i,lists i=>
        (Finset.univ.prod fun i=>w i (p i))*markedCompletedT
          (rowTwist Psi m (ConcretePrimeRowBridge.idealGenerator F)
            (u.val*ConcretePrimeRowBridge.idealGenerator I))
          (CompletedHeight.normTwistedSource W theta) (Z^(1+ell0+shift))
          (fun A=>Finset.univ.prod fun i=>if Dvd.dvd (p i).val A then (1:Complex) else 0)
    have hre := original_fiber_energy_reindex parents J mask hparents0 physicalRow
    rw [hre]
    have heq : (Finset.univ.sum fun K : rows=>
        norm (Finset.univ.sum fun p : forall i,lists i=>
          (Finset.univ.prod fun i=>w i (p i))*markedCompletedT
            (rowTwist Psi m (ConcretePrimeRowBridge.idealGenerator F)
              (u.val*ConcretePrimeRowBridge.idealGenerator (reconstructFiberRow J mask K.val)))
            (CompletedHeight.normTwistedSource W theta) (Z^(1+ell0+shift))
            (fun A=>Finset.univ.prod fun i=>if Dvd.dvd (p i).val A then (1:Complex) else 0))^2)=
        Finset.univ.sum (fun K : rows=>norm (Inv.inv thetaDerivativeScalar*
          Finset.univ.sum (fun h=>scalar h K*
            Finset.univ.sum (fun A : Finset (FreeReflection.pool J mask Q0)=>
              frozenInactiveWeight J F mask Q0 A*
              Finset.univ.sum (fun T : Finset sigma=>
                originalInactivePhysical ((poolPrimeFamily J mask Q0).restrict A)
                  (poolPrimeFamily J mask Q0).ideal rows hrows lists hmax hgood T (D h A T)
                  (E h).shape (E h).denominator_ne_zero
                  (fun b : A=>completedLocalExponent J F b.val.val)
                  (CompletedHeight.normTwistedSource W theta) (Z^(1+ell0+shift)) w K))))^2) := by
      apply Finset.sum_congr rfl
      intro K hK
      exact congrArg (fun z : Complex=>norm z^2) (hid K)
    have hbound := heq.trans_le henergy
    have hp : Z^O=(Ideal.absNorm (rowPowerfulPart J):Real) :=
      Real.rpow_logb hzp (ne_of_gt hz) hPowPos
    let Eexp := (1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+506*eta
    have hR : C*(1+norm theta)^degree*Z^(Eexp-O/2)=
        C*(1+norm theta)^degree*Z^Eexp*
          (Ideal.absNorm (rowPowerfulPart J):Real)^(-(1/2:Real)) := by
      rw [show Eexp-O/2=Eexp+O*(-(1/2:Real)) by ring,
        Real.rpow_add hzp,Real.rpow_mul hzp.le,hp]
      ring
    have hs := Finset.sum_coe_sort rows (fun K : Ideal Eis=>
      norm (Finset.univ.sum fun p : forall i,lists i=>
        (Finset.univ.prod fun i=>w i (p i))*markedCompletedT
          (rowTwist Psi m (ConcretePrimeRowBridge.idealGenerator F)
            (u.val*ConcretePrimeRowBridge.idealGenerator (reconstructFiberRow J mask K)))
          (CompletedHeight.normTwistedSource W theta) (Z^(1+ell0+shift))
          (fun A=>Finset.univ.prod fun i=>if Dvd.dvd (p i).val A then (1:Complex) else 0))^2)
    exact hs.symm.trans_le (hbound.trans_eq hR)

theorem low_completed_rows_energy_general (Q : Ideal Eis) (hQ : Not (Q=0))
    (F : Ideal Eis) (hF : Squarefree F) (m : Eis) (hm : Not (m=0))
    (hmLam : Dvd.dvd ConcretePrimeRowBridge.goodLambda m) (hm2 : Dvd.dvd (2:Eis) m)
    (hperiod : Dvd.dvd (Q*Ideal.span {(72:Eis)}) (Ideal.span {m}))
    (hbad : forall P, Membership.mem fixedBadPrimes P -> Dvd.dvd P (Ideal.span {m}*F))
    (lo hi : Real) (hlo : 0<lo) (W : Real->Complex)
    (hWs : Set.Subset (Function.support W) (Set.Icc lo hi))
    (hW : ContDiff Real ((Top.top : ENat) : WithTop ENat) W)
    (Ck eta : Real) (hCk : 0<Ck) (heta : 0<eta) (heta1 : eta<=1) (rmax : Nat) :
    Exists fun degree : Nat => Exists fun C : Real => Exists fun Z0 : Real =>
    0<C /\ 1<Z0 /\
    forall {sigma : Type v} [Fintype sigma] [DecidableEq sigma],
    forall (Z Lambda d ell0 shift : Real),
      Z0<=Z -> 0<=Lambda -> Lambda<=1/5 -> 0<=d -> d<=Lambda ->
      0<=ell0 -> ell0<=Lambda-d+eta -> abs shift<=eta ->
    forall parents : Finset (Ideal Eis),
      (forall I, Membership.mem parents I ->
        Not (I=0) /\ (Ideal.absNorm I:Real)<=Ck*Z^(1-Lambda-2*d)) ->
      Fintype.card sigma<=rmax -> forall (lists : sigma->Finset (Ideal Eis)) (H : sigma->Real),
      Pairwise (fun i j=>Disjoint (lists i) (lists j)) ->
      (forall i, forall P, Membership.mem (lists i) P -> P.IsMaximal) ->
      (forall i, forall P, Membership.mem (lists i) P ->
        Not (Membership.mem P ConcretePrimeRowBridge.goodLambda)) ->
      (forall i, forall P, Membership.mem (lists i) P -> Prime P) ->
      (forall i, forall P, Membership.mem (lists i) P ->
        Not (ringChar (HasQuotient.Quotient Eis P)=2)) ->
      (forall i, forall P, Membership.mem (lists i) P ->
        IsCoprime (Q*Ideal.span {(72:Eis)}) P) ->
      (forall i, 1<=H i) ->
      (forall i, forall P, Membership.mem (lists i) P -> (Ideal.absNorm P:Real)<=H i) ->
      (Finset.univ.prod H)<=Z^ell0 ->
    forall (Psi : MonoidHom Eis Complex), (forall n, norm (Psi n)<=1) ->
      CanonicalCoefficientClass.FactorsModulo Q Psi ->
    forall (u : Units Eis) (theta : Real) (w : forall i, lists i->Complex),
      (forall i P, norm (w i P)<=1) ->
      (parents.sum fun I=>norm (Finset.univ.sum fun p : forall i,lists i=>
          (Finset.univ.prod fun i=>w i (p i))*markedCompletedT
            (rowTwist Psi m (ConcretePrimeRowBridge.idealGenerator F)
              (u.val*ConcretePrimeRowBridge.idealGenerator I))
            (CompletedHeight.normTwistedSource W theta) (Z^(1+ell0+shift))
            (fun A=>Finset.univ.prod fun i=>if Dvd.dvd (p i).val A then (1:Complex) else 0))^2)<=
        C*(1+norm theta)^degree*Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+507*eta) := by
  have hb := low_completed_fiber_energy_general Q hQ F hF m hm hmLam hm2 hperiod hbad
    lo hi hlo W hWs hW Ck eta hCk heta heta1 rmax
  choose degree C Z0 hC hZ0 he using hb
  have hagg := completed_representative_aggregation 2 eta (by norm_num) heta
  choose D hD ha using hagg
  let mask := Ideal.span {m}*F
  let Z1 := max Z0 (max 2 (max Ck (Ideal.absNorm mask:Real)))
  refine Exists.intro degree (Exists.intro (D*C)
    (Exists.intro Z1 (And.intro (mul_pos hD hC)
      (And.intro (lt_of_lt_of_le hZ0 (le_max_left _ _)) ?_))))
  intro sigma _ _ Z Lambda d ell0 shift hZ hLambda0 hLambda1 hd hd1 hell hellcap hshift
    parents hparents hcard lists H hdis hmax hgood hprime hodd hLP hH1 hH hprod
    Psi hPsinorm hPsiperiod u theta w hw
  have hZZ : Z0<=Z := (le_max_left _ _).trans hZ
  have hZ2 : 2<=Z := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hZ
  have hz : 0<Z := by linarith
  have hz1 : 1<=Z := by linarith
  have hCkZ : Ck<=Z :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hZ))
  have hmaskZ : (Ideal.absNorm mask:Real)<=Z :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hZ))
  have hmaskn : (Ideal.absNorm mask:Real)<=Z^(2:Real) :=
    hmaskZ.trans (by simpa using
      Real.rpow_le_rpow_of_exponent_le hz1 (show (1:Real)<=2 by norm_num))
  have hparentn : forall I, Membership.mem parents I ->
      Not (I=0) /\ (Ideal.absNorm I:Real)<=Z^(2:Real) := by
    intro I hI
    refine And.intro (hparents I hI).1 ((hparents I hI).2.trans ?_)
    calc
      _ <= Z*Z^(1-Lambda-2*d) :=
        mul_le_mul_of_nonneg_right hCkZ (Real.rpow_nonneg hz.le _)
      _ = Z^(1+(1-Lambda-2*d)) := by rw [Real.rpow_add hz,Real.rpow_one]
      _ <= _ := Real.rpow_le_rpow_of_exponent_le hz1 (by linarith)
  have hh := ha Z hZ2 parents mask hparentn
    (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hm) hF.ne_zero) hmaskn
    (C*(1+norm theta)^degree*Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+506*eta))
    (fun I=>norm (Finset.univ.sum fun p : forall i,lists i=>
      (Finset.univ.prod fun i=>w i (p i))*markedCompletedT
        (rowTwist Psi m (ConcretePrimeRowBridge.idealGenerator F)
          (u.val*ConcretePrimeRowBridge.idealGenerator I))
        (CompletedHeight.normTwistedSource W theta) (Z^(1+ell0+shift))
        (fun A=>Finset.univ.prod fun i=>if Dvd.dvd (p i).val A then (1:Complex) else 0))^2)
    (by positivity) (fun J hJ=>he (sigma:=sigma) J (hparents J hJ).1 Z Lambda d ell0 shift
      hZZ hLambda0 hLambda1 hd hd1 hell hellcap hshift (hparents J hJ).2
      parents hparents hcard lists H hdis hmax hgood hprime hodd hLP hH1 hH hprod
      Psi hPsinorm hPsiperiod u theta w hw)
  apply hh.trans_eq
  calc
    _ = (D*C)*(1+norm theta)^degree*
        (Z^eta*Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+506*eta)) := by ring
    _ = _ := by rw [<-Real.rpow_add hz];congr 2;ring

theorem low_original_completed_energy_general (Q : Ideal Eis) (hQ : Not (Q=0))
    (F : Ideal Eis) (hF : Squarefree F) (m : Eis) (hm : Not (m=0))
    (hmLam : Dvd.dvd ConcretePrimeRowBridge.goodLambda m) (hm2 : Dvd.dvd (2:Eis) m)
    (hperiod : Dvd.dvd (Q*Ideal.span {(72:Eis)}) (Ideal.span {m}))
    (hbad : forall P, Membership.mem fixedBadPrimes P -> Dvd.dvd P (Ideal.span {m}*F))
    (lo hi : Real) (hlo : 0<lo) (W : Real->Complex)
    (hWs : Set.Subset (Function.support W) (Set.Icc lo hi))
    (hW : ContDiff Real ((Top.top : ENat) : WithTop ENat) W)
    (Ck eta : Real) (hCk : 0<Ck) (heta : 0<eta) (heta1 : eta<=1) (rmax : Nat) :
    Exists fun degree : Nat => Exists fun C : Real => Exists fun Z0 : Real =>
    0<C /\ 1<Z0 /\
    forall {sigma : Type v} [Fintype sigma] [DecidableEq sigma],
    forall (Z Lambda d ell0 shift : Real),
      Z0<=Z -> 0<=Lambda -> Lambda<=1/5 -> 0<=d -> d<=Lambda ->
      0<=ell0 -> ell0<=Lambda-d+eta -> abs shift<=eta ->
    forall parents : Finset (Ideal Eis),
      (forall I, Membership.mem parents I ->
        Not (I=0) /\ (Ideal.absNorm I:Real)<=Ck*Z^(1-Lambda-2*d)) ->
      Fintype.card sigma<=rmax -> forall (lists : sigma->Finset (Ideal Eis)) (H : sigma->Real),
      Pairwise (fun i j=>Disjoint (lists i) (lists j)) ->
      (forall i, forall P, Membership.mem (lists i) P -> P.IsMaximal) ->
      (forall i, forall P, Membership.mem (lists i) P ->
        Not (Membership.mem P ConcretePrimeRowBridge.goodLambda)) ->
      (forall i, forall P, Membership.mem (lists i) P -> Prime P) ->
      (forall i, forall P, Membership.mem (lists i) P ->
        Not (ringChar (HasQuotient.Quotient Eis P)=2)) ->
      (forall i, 1<=H i) ->
      (forall i, forall P, Membership.mem (lists i) P -> (Ideal.absNorm P:Real)<=H i) ->
      (Finset.univ.prod H)<=Z^ell0 ->
    forall (Psi : MonoidHom Eis Complex), (forall n, norm (Psi n)<=1) ->
      CanonicalCoefficientClass.FactorsModulo Q Psi ->
    forall (u : Units Eis) (theta : Real) (w : forall i, lists i->Complex),
      (forall i P, norm (w i P)<=1) ->
      (parents.sum fun I=>norm (Finset.univ.sum fun p : forall i,lists i=>
          (Finset.univ.prod fun i=>w i (p i))*markedCompletedT
            (rowTwist Psi m (ConcretePrimeRowBridge.idealGenerator F)
              (u.val*ConcretePrimeRowBridge.idealGenerator I))
            (CompletedHeight.normTwistedSource W theta) (Z^(1+ell0+shift))
            (fun A=>Finset.univ.prod fun i=>if Dvd.dvd (p i).val A then (1:Complex) else 0))^2)<=
        C*(1+norm theta)^degree*Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+507*eta) := by
  have hb := low_completed_rows_energy_general Q hQ F hF m hm hmLam hm2 hperiod hbad
    lo hi hlo W hWs hW Ck eta hCk heta heta1 rmax
  choose degree C Z0 hC hZ0 he using hb
  refine Exists.intro degree (Exists.intro C
    (Exists.intro Z0 (And.intro hC (And.intro hZ0 ?_))))
  intro sigma _ _ Z Lambda d ell0 shift hZ hLambda0 hLambda1 hd hd1 hell hellcap hshift
    parents hparents hcard lists H hdis hmax hgood hprime hodd hH1 hH hprod
    Psi hPsinorm hPsiperiod u theta w hw
  let S := actualPuncturePrimes lists m
  let lists' := punctureLists lists S
  have hsub (i : sigma) : lists' i<=lists i := Finset.filter_subset _ _
  let w' : forall i, lists' i->Complex :=
    fun i P=>w i (Subtype.mk P.val (hsub i P.property))
  have hLP (i : sigma) (P : Ideal Eis) (hP : Membership.mem (lists' i) P) :
      IsCoprime (Q*Ideal.span {(72:Eis)}) P := by
    apply puncture_period_coprime _ m hperiod P (hmax i P (hsub i hP))
    intro hmP
    exact (Finset.mem_filter.mp hP).2
      ((actualPuncturePrimes_mem lists m i P (hsub i hP)).mpr hmP)
  have hh := he (sigma:=sigma) Z Lambda d ell0 shift hZ hLambda0 hLambda1 hd hd1
    hell hellcap hshift parents hparents hcard lists' H
    (fun i j hij=>(hdis hij).mono (hsub i) (hsub j))
    (fun i P hP=>hmax i P (hsub i hP)) (fun i P hP=>hgood i P (hsub i hP))
    (fun i P hP=>hprime i P (hsub i hP)) (fun i P hP=>hodd i P (hsub i hP))
    hLP hH1 (fun i P hP=>hH i P (hsub i hP)) hprod
    Psi hPsinorm hPsiperiod u theta w'
    (fun i P=>hw i (Subtype.mk P.val (hsub i P.property)))
  apply le_trans (le_of_eq ?_) hh
  apply Finset.sum_congr rfl
  intro I hI
  exact congrArg (fun z : Complex=>norm z^2)
    (original_completed_actual_puncture_lists lists hprime Psi m
      (ConcretePrimeRowBridge.idealGenerator F) (u.val*ConcretePrimeRowBridge.idealGenerator I)
      (CompletedHeight.normTwistedSource W theta) (Z^(1+ell0+shift)) w)

end PrimeFactorOscillations.GeneralLowGeometry

