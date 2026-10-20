/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Reflection.LowDyads
import PrimeFactorOscillations.Assembly.DetectorPackets.GeneralLowGlobalEnergy

/-!
# GeneralLowFixedMember

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
# Uniform physical geometry with a variable slot budget

Makes the actual member-row bound uniform over a fixed finite cusp family,
proves its scale caps from the arithmetic row hypotheses, then inserts the
physical geometric parameters. The reflected max excess remains explicit.
This is an input to the physical low estimate, not a zero-free theorem.
-/


noncomputable section
namespace PrimeFactorOscillations.GeneralLowGeometry
open scoped Classical
open OAI OAI.SevenEighths
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic
open CanonicalQuadraticSieve InverseTerminalWidths InverseMoment InverseReflectedPhase
local notation "Eis" => ActualEisensteinCubic.O
universe u v
variable {Nlevel : Eis}

theorem original_low_member_geometry_uniform_general
    {gamma : Type u} [Fintype gamma] (a c0 : gamma->Eis) (mode : gamma->Bool)
    [Fintype (HasQuotient.Quotient Eis (Ideal.span {Nlevel^2}))]
    (epsilon : Real) (hepsilon : 0<epsilon) (lo hi : Real) (hlo : 0<lo)
    (W : Real->Complex) (hWs : Set.Subset (Function.support W) (Set.Icc lo hi))
    (hW : ContDiff Real ((Top.top : ENat) : WithTop ENat) W)
    (s : forall i, FixedCuspShape
      (ControlledStratumArithmetic.fixedCusp (a i) (c0 i) (mode i)))
    (hc0 : forall i, Not (c0 i=0))
    (hNlevel : forall i, Dvd.dvd ((9:Eis)*c0 i) Nlevel)
    (hbase : forall i, if mode i then Dvd.dvd (ConcretePrimeRowBridge.goodLambda^2) (a i-1)
      else Dvd.dvd (ConcretePrimeRowBridge.goodLambda^2) (c0 i-1))
    (hac : forall i, IsCoprime (a i) (c0 i))
    (rho : Real) (hrho : 0<rho) (eta : Real) (heta : 0<eta)
    (kappa delta Lscale Lpool : Real) (hkappa : 0<kappa)
    (hdeltaL : 0<=delta+Lscale) (hLpool : 0<=Lpool)
    (Lcap saving : Real) (hdeltaPos : 0<delta) :
    Exists (fun degree : Nat => Exists (fun C : Real => Exists (fun Z0 : Real =>
    0<C /\ 1<Z0 /\
    forall i : gamma,
      let a := a i
      let c0 := c0 i
      let mode := mode i
      let s := s i
      let hc0 := hc0 i
    forall {sigma : Type v} [Fintype sigma] [DecidableEq sigma],
    forall (J I F Q Q0 : Ideal Eis) (_hJ : Not (J=0))
      (_hI : Not (I=0)) (_hQ : Not (Q=0)),
      rowPowerfulPart J=rowPowerfulPart I ->
      rowMaskPart J Q=rowMaskPart I Q ->
    forall (A : Finset (FreeReflection.pool J Q Q0))
      (Z O0 H za Nstar Lambda d ell0 shift pi Ck CO CH X QK QP
        Lrow Lslot : Real),
      Z0<=Z -> 0<Ck -> 0<CO -> 0<CH -> 0<X -> 0<QK -> 0<QP ->
      (Ideal.absNorm I:Real)<=Ck*Z^(1-Lambda-2*d) ->
      Z^O0/CO<=(Ideal.absNorm (rowPowerfulPart I):Real) ->
      Z^H/CH<=(Ideal.absNorm (rowResidualPart I Q):Real) ->
      Real.log (CH*Ck*CO)/Real.log Z<=eta ->
      normWidth Z (rowPowerfulPart I)<=O0+eta -> normWidth Z Q<=eta ->
      0<=Lambda -> Lambda<=1/5 -> 0<=d -> d<=Lambda ->
      ell0<=Lambda-d+eta -> 0<=O0 -> za<=ell0+eta -> abs shift<=eta ->
      Nstar=1+ell0+shift -> H=Real.logb Z (QK) ->
      za=Real.logb Z (QP/2) -> Nstar=Real.logb Z X ->
      0<=delta -> delta<=eta ->
      QK<=Z^Lrow -> QP/2<=Z^Lslot ->
      Real.logb Z 16<=eta ->
      epsilon*(Lrow+Lslot+2*(delta+Lscale+eta))+eta/2<=pi ->
      Inv.inv X<=Z^Lcap -> QK<=Z^Lcap -> QP<=Z^Lcap ->
      -saving<=(1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+200*eta+pi+kappa+rho*Lpool-O0/2 ->
      let G := (poolPrimeFamily J Q Q0).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (Ideal.absNorm (Finset.univ.prod fun b=>G.ideal b):Real)<=Z^Lcap ->
      Inv.inv (familyRawScale G s X QK QP)<=Z^Lscale ->
      (Ideal.absNorm (Finset.univ.prod fun b=>G.ideal b):Real)<=Z^Lpool ->
    forall (rows : Finset (Ideal Eis)) (tuples : Finset (sigma->Ideal Eis))
      (hne : tuples.Nonempty)
      (hmax : forall p, Membership.mem tuples p -> forall i, (p i).IsMaximal)
      (hgood : forall p, Membership.mem tuples p -> forall i,
        Not (Membership.mem (p i) ConcretePrimeRowBridge.goodLambda))
      (hinj : Set.InjOn slotTupleProduct (tuples : Set (sigma->Ideal Eis))),
      let S := tuplePrimeFamily tuples hne hmax hgood
      let Pset := tuples.image slotTupleProduct
      forall (hrows : forall K, Membership.mem rows K -> Admissible K),
      (forall f, IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) ->
      (forall f, Not (ringChar (HasQuotient.Quotient Eis (G.ideal f))=2)) ->
      (forall K, Membership.mem rows K ->
        (forall f, IsCoprime (G.ideal f) K) /\ IsCoprime (Ideal.span {Nlevel}) K) ->
      (forall P, Membership.mem Pset P -> (Finset.univ.prod fun b=>(S P).ideal b)=P) ->
      (forall P, Membership.mem Pset P ->
        Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) ->
      (forall P, Membership.mem Pset P -> forall b,
        IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) ->
      (forall P, Membership.mem Pset P -> forall b,
        Not (ringChar (HasQuotient.Quotient Eis ((G.sum (S P)).ideal b))=2)) ->
    Exists (fun D :
      (forall (K : rows) (P : Pset), IsCoprime K.val P.val ->
        ControlledStratumArithmetic
          (G.reflected K.val (hrows K.val K.property) (S P.val)).generator
          Nlevel a c0 mode) =>
    forall (theta : Real) (r : Ideal Eis->Complex) (aw : (sigma->Ideal Eis)->Complex),
      1<=QK -> 2<=QP ->
      (forall K, Membership.mem rows K ->
        QK/2<=(Ideal.absNorm K:Real) /\ (Ideal.absNorm K:Real)<=QK) ->
      (forall P, Membership.mem Pset P ->
        CubicSieve.Admissible P /\ QP/2<=(Ideal.absNorm P:Real) /\
          (Ideal.absNorm P:Real)<=QP) ->
      (forall K, Membership.mem rows K -> norm (r K)<=1) ->
      (forall p, Membership.mem tuples p -> norm (aw p)<=1) ->
      (Finset.univ.sum fun K : rows=>
        norm (memberTupleRow tuples hmax hgood G K.val (hrows K.val K.property)
          hne hinj (D K) s hc0 j W theta X r aw)^2)<=
        C*(1+norm theta)^degree*Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+200*eta+pi+kappa+rho*Lpool-O0/2))))) := by
  have hb (i : gamma) := original_low_member_tuple_full_budget_general (Nlevel:=Nlevel)
    epsilon hepsilon lo hi hlo W hWs hW (s i) (hc0 i) (hNlevel i) (hbase i) (hac i)
    rho hrho eta heta kappa delta Lscale Lpool hkappa hdeltaL hLpool Lcap saving hdeltaPos
  choose degree C Z0 hC hZ0 henergy using hb
  let degreeAll := Finset.univ.sum degree
  let CAll := Finset.univ.sum C+1
  let ZAll := (Finset.univ.sum fun i=>abs (Z0 i))+2
  have hn (i : gamma) : degree i<=degreeAll :=
    Finset.single_le_sum (fun j _=>Nat.zero_le _) (Finset.mem_univ i)
  have hc (i : gamma) : C i<=CAll := by
    have hh : C i<=Finset.univ.sum C :=
      Finset.single_le_sum (fun j _=>(hC j).le) (Finset.mem_univ i)
    dsimp only [CAll]
    linarith
  have hz (i : gamma) : Z0 i<=ZAll := by
    have hh : abs (Z0 i)<=Finset.univ.sum (fun j=>abs (Z0 j)) :=
      Finset.single_le_sum (fun j _=>abs_nonneg (Z0 j)) (Finset.mem_univ i)
    have hi := le_abs_self (Z0 i)
    dsimp only [ZAll]
    linarith
  have hCA : 0<CAll := by
    have hh : 0<=Finset.univ.sum C := Finset.sum_nonneg (fun i _=>(hC i).le)
    dsimp only [CAll]
    linarith
  have hZA : 1<ZAll := by
    have hh : 0<=Finset.univ.sum (fun i=>abs (Z0 i)) :=
      Finset.sum_nonneg (fun i _=>abs_nonneg _)
    dsimp only [ZAll]
    linarith
  refine Exists.intro degreeAll (Exists.intro CAll
    (Exists.intro ZAll (And.intro hCA (And.intro hZA ?_))))
  intro i
  dsimp only
  intro sigma _ _ J I F Q Q0 hJ hI hQ hpower hmask A
    Z O0 H za Nstar Lambda d ell0 shift pi Ck CO CH X QK QP
    Lrow Lslot hZ hCk hCO hCH hX hK hP hIn hPow hRow
    hlog hPowUpper hQwidth hLambda0 hLambda1 hd hd1 hell0 hO hza hshift
    hNs heH heza heN hdelta hdeta hrowcap hslotcap hconst hbudget
    hXi hKcap hPcap hexp hFcap hscale hpool
    rows tuples hne hmax hgood hinj hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  have hrow := henergy i J I F Q Q0 hJ hI hQ hpower hmask A
    Z O0 H za Nstar Lambda d ell0 shift pi Ck CO CH X QK QP
    Lrow Lslot ((hz i).trans hZ) hCk hCO hCH hX hK hP hIn hPow hRow
    hlog hPowUpper hQwidth hLambda0 hLambda1 hd hd1 hell0 hO hza hshift
    hNs heH heza heN hdelta hdeta hrowcap hslotcap hconst hbudget
    hXi hKcap hPcap hexp hFcap hscale hpool
    rows tuples hne hmax hgood hinj hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  cases hrow with
  | intro D hD =>
    refine Exists.intro D ?_
    intro theta r aw hqk hqp hKr hPr hr haw
    apply (hD theta r aw hqk hqp hKr hPr hr haw).trans
    have hZpos : 0<Z := lt_trans zero_lt_one (lt_of_lt_of_le hZA hZ)
    have hheight : 1<=1+norm theta := by linarith [norm_nonneg theta]
    have hpow : (1+norm theta)^(degree i)<=(1+norm theta)^degreeAll := by
      gcongr; exact hn i
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZpos.le _)
    exact mul_le_mul (hc i) hpow (by positivity) hCA.le

lemma low_actual_scale_caps_general
    (J I Q Q0 : Ideal Eis) (hJ : Not (J=0)) (hI : Not (I=0)) (hQ : Not (Q=0))
    (hpower : rowPowerfulPart J=rowPowerfulPart I)
    (hmask : rowMaskPart J Q=rowMaskPart I Q)
    (A : Finset (FreeReflection.pool J Q Q0))
    (Z Ck Lambda d ell0 shift eta QK QP : Real)
    (hZ : 2<=Z) (hCkp : 0<Ck) (hCk : Ck<=Z)
    (hQn : (Ideal.absNorm Q:Real)<=Z)
    (hLambda0 : 0<=Lambda) (hLambda1 : Lambda<=1/5)
    (hd : 0<=d) (hell : 0<=ell0)
    (hellcap : ell0<=Lambda-d+eta) (hshift : abs shift<=eta) (heta : eta<=1)
    (hIn : (Ideal.absNorm I:Real)<=Ck*Z^(1-Lambda-2*d))
    (hK : QK<=2*Ck*Z^(1-Lambda-2*d)) (hP : QP/2<=Z^ell0) :
    (Ideal.absNorm I:Real)<=Z^2 /\
    (Ideal.absNorm (Finset.univ.prod fun b : A=>
      ((poolPrimeFamily J Q Q0).restrict A).ideal b):Real)<=Z^(8:Real) /\
    QK<=Z^(8:Real) /\ QP<=Z^(8:Real) /\
    Inv.inv (Z^(1+ell0+shift))<=Z^(8:Real) := by
  have hz : 0<Z := by linarith
  have hz1 : 1<=Z := by linarith
  have hcp : Ck*Z^(1-Lambda-2*d)<=Z^2 := by
    calc
      _ <= Z*Z^(1-Lambda-2*d) :=
        mul_le_mul_of_nonneg_right hCk (Real.rpow_nonneg hz.le _)
      _ = Z^(1+(1-Lambda-2*d)) := by rw [Real.rpow_add hz,Real.rpow_one]
      _ <= _ := by
        rw [<-Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hz1 (by norm_num;linarith)
  have hi := hIn.trans hcp
  have hFcap :
      (Ideal.absNorm (Finset.univ.prod fun b : A=>
        ((poolPrimeFamily J Q Q0).restrict A).ideal b):Real)<=Z^(8:Real) := by
    calc
      _ <= (Ideal.absNorm I:Real)*(Ideal.absNorm Q:Real) :=
        original_pool_restricted_norm J I Q Q0 hJ hI hQ hpower hmask A
      _ <= Z^2*Z := mul_le_mul hi hQn (Nat.cast_nonneg _) (sq_nonneg _)
      _ = Z^(3:Real) := by norm_num;ring
      _ <= _ := Real.rpow_le_rpow_of_exponent_le hz1 (by norm_num)
  have hKcap : QK<=Z^(8:Real) := by
    calc
      QK <= 2*(Ck*Z^(1-Lambda-2*d)) := by linarith
      _ <= Z*Z^2 := mul_le_mul hZ hcp (by positivity) hz.le
      _ = Z^(3:Real) := by norm_num;ring
      _ <= _ := Real.rpow_le_rpow_of_exponent_le hz1 (by norm_num)
  have hPcap : QP<=Z^(8:Real) := by
    calc
      QP <= 2*Z^ell0 := by linarith
      _ <= Z*Z^ell0 := mul_le_mul_of_nonneg_right hZ (Real.rpow_nonneg hz.le _)
      _ = Z^(1+ell0) := by rw [Real.rpow_add hz,Real.rpow_one]
      _ <= _ := Real.rpow_le_rpow_of_exponent_le hz1 (by linarith)
  have hXcap : Inv.inv (Z^(1+ell0+shift))<=Z^(8:Real) := by
    rw [<-Real.rpow_neg hz.le]
    exact Real.rpow_le_rpow_of_exponent_le hz1
      (by have hs := (abs_le.mp hshift).1;linarith)
  exact And.intro hi (And.intro hFcap (And.intro hKcap (And.intro hPcap hXcap)))

theorem low_fixed_member_geometry_uniform_general
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
    forall i : gamma,
      let a := a i
      let c0 := c0 i
      let mode := mode i
      let s := s i
      let hc0 := hc0 i
    forall {sigma : Type v} [Fintype sigma] [DecidableEq sigma],
    forall (J I F Q0 : Ideal Eis) (_hJ : Not (J=0)) (_hI : Not (I=0)) (_hF : Not (F=0)),
      rowPowerfulPart J=rowPowerfulPart I -> rowMaskPart J Q=rowMaskPart I Q ->
    forall (A : Finset (FreeReflection.pool J Q Q0))
      (Z Lambda d ell0 shift O0 QK QP : Real),
      Z0<=Z -> 0<=Lambda -> Lambda<=1/5 -> 0<=d -> d<=Lambda ->
      0<=ell0 -> ell0<=Lambda-d+eta -> abs shift<=eta ->
      O0=normWidth Z (rowPowerfulPart I) ->
      (Ideal.absNorm I:Real)<=Ck*Z^(1-Lambda-2*d) ->
      QK/2<=(Ideal.absNorm (rowResidualPart I Q):Real) ->
      1<=QK -> QK<=2*Ck*Z^(1-Lambda-2*d) -> 2<=QP -> QP/2<=Z^ell0 ->
      let G := (poolPrimeFamily J Q Q0).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
    forall (rows : Finset (Ideal Eis)) (tuples : Finset (sigma->Ideal Eis))
      (hne : tuples.Nonempty)
      (hmax : forall p, Membership.mem tuples p -> forall i, (p i).IsMaximal)
      (hgood : forall p, Membership.mem tuples p -> forall i,
        Not (Membership.mem (p i) ConcretePrimeRowBridge.goodLambda))
      (hinj : Set.InjOn slotTupleProduct (tuples : Set (sigma->Ideal Eis))),
      let S := tuplePrimeFamily tuples hne hmax hgood
      let Pset := tuples.image slotTupleProduct
      forall (hrows : forall K, Membership.mem rows K -> Admissible K),
      (forall f, IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) ->
      (forall f, Not (ringChar (HasQuotient.Quotient Eis (G.ideal f))=2)) ->
      (forall K, Membership.mem rows K ->
        (forall f, IsCoprime (G.ideal f) K) /\ IsCoprime (Ideal.span {Nlevel}) K) ->
      (forall P, Membership.mem Pset P -> (Finset.univ.prod fun b=>(S P).ideal b)=P) ->
      (forall P, Membership.mem Pset P ->
        Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) ->
      (forall P, Membership.mem Pset P -> forall b,
        IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) ->
      (forall P, Membership.mem Pset P -> forall b,
        Not (ringChar (HasQuotient.Quotient Eis ((G.sum (S P)).ideal b))=2)) ->
    Exists (fun D :
      (forall (K : rows) (P : Pset), IsCoprime K.val P.val ->
        ControlledStratumArithmetic
          (G.reflected K.val (hrows K.val K.property) (S P.val)).generator
          Nlevel a c0 mode) =>
    forall (theta : Real) (r : Ideal Eis->Complex) (aw : (sigma->Ideal Eis)->Complex),
      1<=QK -> 2<=QP ->
      (forall K, Membership.mem rows K ->
        QK/2<=(Ideal.absNorm K:Real) /\ (Ideal.absNorm K:Real)<=QK) ->
      (forall P, Membership.mem Pset P ->
        CubicSieve.Admissible P /\ QP/2<=(Ideal.absNorm P:Real) /\
          (Ideal.absNorm P:Real)<=QP) ->
      (forall K, Membership.mem rows K -> norm (r K)<=1) ->
      (forall p, Membership.mem tuples p -> norm (aw p)<=1) ->
      (Finset.univ.sum fun K : rows=>
        norm (memberTupleRow tuples hmax hgood G K.val (hrows K.val K.property)
          hne hinj (D K) s hc0 j W theta (Z^(1+ell0+shift)) r aw)^2)<=
        C*(1+norm theta)^degree*Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+504*eta-O0/2))))) := by
  let eps := eta/(200*(1+eta))
  have heps : 0<eps := (low_reflection_parameters eta heta).1
  have hbaseMain := original_low_member_geometry_uniform_general a c0 mode
    eps heps lo hi hlo W hWs hW s hc0 hNlevel hbase hac (eta/8) (by positivity)
    eta heta eta (eta/2) 57 8 heta (by positivity) (by norm_num) 8 2 (by positivity)
  cases hbaseMain with
  | intro degree hm0 =>
    cases hm0 with
    | intro C hm1 =>
      cases hm1 with
      | intro Z1 hmain0 =>
        have hC : 0<C := hmain0.1
        have hZ1 : 1<Z1 := hmain0.2.1
        have hscaleBase := geometry_source_scale_cap a c0 mode s
        let Z2 : Real := Classical.choose hscaleBase
        have hZ2 : 1<Z2 := (Classical.choose_spec hscaleBase).1
        have hlogQBase := constant_log_error (Ideal.absNorm Q:Real) eta
          (actual_ideal_norm_pos Q hQ) heta
        let Z3 : Real := Classical.choose hlogQBase
        have hZ3 : 1<Z3 := (Classical.choose_spec hlogQBase).1
        have hlogCBase := constant_log_error (2*Ck) eta (by positivity) heta
        let Z4 : Real := Classical.choose hlogCBase
        have hZ4 : 1<Z4 := (Classical.choose_spec hlogCBase).1
        have hlog16Base := constant_log_error 16 eta (by norm_num) heta
        let Z5 : Real := Classical.choose hlog16Base
        have hZ5 : 1<Z5 := (Classical.choose_spec hlog16Base).1
        let Z0 := max Z1 (max Z2 (max Z3 (max Z4 (max Z5
          (max 2 (max Ck (Ideal.absNorm Q:Real)))))))
        have hz1 : Z1<=Z0 := le_max_left _ _
        have hz2 : Z2<=Z0 := (le_max_left _ _).trans (le_max_right _ _)
        have hz3 : Z3<=Z0 := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
        have hz4 : Z4<=Z0 := (le_max_left _ _).trans
          ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
        have hz5 : Z5<=Z0 := (le_max_left _ _).trans
          ((le_max_right _ _).trans ((le_max_right _ _).trans
            ((le_max_right _ _).trans (le_max_right _ _))))
        have hzcap : max 2 (max Ck (Ideal.absNorm Q:Real))<=Z0 :=
          (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
            ((le_max_right _ _).trans (le_max_right _ _))))
        refine Exists.intro degree (Exists.intro C
          (Exists.intro Z0 (And.intro hC (And.intro (hZ1.trans_le hz1) ?_))))
        intro i
        dsimp only
        intro sigma _ _ J I F Q0 hJ hI hF hpower hmask A
          Z Lambda d ell0 shift O0 QK QP hZ hLambda0 hLambda1 hd hd1 hell hellcap hshift
          hOeq hIn hKr hK1 hKcap hP2 hPcap
        have hz : 1<Z := lt_of_lt_of_le hZ1 (hz1.trans hZ)
        have hzpos : 0<Z := lt_trans zero_lt_one hz
        have hZtwo : 2<=Z := (le_max_left _ _).trans (hzcap.trans hZ)
        have hCkZ : Ck<=Z :=
          (le_max_left _ _).trans ((le_max_right _ _).trans (hzcap.trans hZ))
        have hQZ : (Ideal.absNorm Q:Real)<=Z :=
          (le_max_right _ _).trans ((le_max_right _ _).trans (hzcap.trans hZ))
        have hcaps := low_actual_scale_caps_general J I Q Q0 hJ hI hQ hpower hmask A
          Z Ck Lambda d ell0 shift eta QK QP hZtwo hCk hCkZ hQZ
          hLambda0 hLambda1 hd hell hellcap hshift heta1 hIn hKcap hPcap
        have hIcap := hcaps.1
        have hFcap := hcaps.2.1
        have hK8 := hcaps.2.2.1
        have hP8 := hcaps.2.2.2.1
        have hX8 := hcaps.2.2.2.2
        let G := (poolPrimeFamily J Q Q0).restrict A
        have hXp : 0<Z^(1+ell0+shift) := Real.rpow_pos_of_pos hzpos _
        have hQK : 0<QK := by linarith
        have hQP : 0<QP := by linarith
        have hsc := (Classical.choose_spec hscaleBase).2 i G Z
          (Z^(1+ell0+shift)) QK QP 8 (hz2.trans hZ) hXp hQK.le hQP.le
          hFcap hK8 hP8 hX8
        norm_num only at hsc
        have hO : 0<=O0 := by
          rw [hOeq]
          exact normWidth_nonneg Z hz _ (rowPowerfulPart_ne_zero I)
        have hOp : 0<(Ideal.absNorm (rowPowerfulPart I):Real) :=
          actual_ideal_norm_pos _ (rowPowerfulPart_ne_zero I)
        have hOn : Z^O0=(Ideal.absNorm (rowPowerfulPart I):Real) := by
          rw [hOeq]
          exact Real.rpow_logb hzpos (ne_of_gt hz) hOp
        have hOtwo : O0<=2 := by
          have hh := Real.logb_le_logb_of_le hz hOp ((original_powerful_norm_le I hI).trans hIcap)
          rw [<-Real.rpow_natCast,Real.logb_rpow hzpos (ne_of_gt hz)] at hh
          norm_num at hh
          rw [hOeq]
          exact hh
        have hza : Real.logb Z (QP/2)<=ell0+eta := by
          have hh := Real.logb_le_logb_of_le hz (by positivity : 0<QP/2) hPcap
          rw [Real.logb_rpow hzpos (ne_of_gt hz)] at hh
          linarith
        have hrowlower : Z^(Real.logb Z QK)/2<=(Ideal.absNorm (rowResidualPart I Q):Real) := by
          rw [Real.rpow_logb hzpos (ne_of_gt hz) hQK]
          exact hKr
        have hslot8 : QP/2<=Z^(8:Real) := by linarith
        have hbudget : eps*(8+8+2*(eta/2+57+eta))+eta/2<=2*eta :=
          (low_reflection_parameters eta heta).2
        have hExtra : 0<=max 0 ((5*Lambda+d-1)/4) := le_max_left _ _
        have hh := hmain0.2.2 i (sigma:=sigma) J I F Q Q0 hJ hI hQ hpower hmask A
          Z O0 (Real.logb Z QK) (Real.logb Z (QP/2)) (1+ell0+shift) Lambda d ell0 shift (2*eta)
          Ck 1 2 (Z^(1+ell0+shift)) QK QP 8 8
          (hz1.trans hZ) hCk (by norm_num) (by norm_num) hXp hQK hQP hIn
          (by simpa only [div_one,hOn] using le_refl (Ideal.absNorm (rowPowerfulPart I):Real))
          hrowlower
          (by simpa only [mul_one] using (Classical.choose_spec hlogCBase).2 Z (hz4.trans hZ))
          (by rw [hOeq];linarith)
          ((Classical.choose_spec hlogQBase).2 Z (hz3.trans hZ))
          hLambda0 hLambda1 hd hd1 hellcap hO hza hshift rfl rfl rfl
          (by rw [Real.logb_rpow hzpos (ne_of_gt hz)]) (by positivity) (by linarith)
          hK8 hslot8 ((Classical.choose_spec hlog16Base).2 Z (hz5.trans hZ))
          hbudget hX8 hK8 hP8 (by linarith) hFcap hsc hFcap
        dsimp only at hh
        intro rows tuples hne hmax hgood hinj hrows hGN hGchar hrowcop hprod hScop hSN hSchar
        have hrow := hh rows tuples hne hmax hgood hinj
          hrows hGN hGchar hrowcop hprod hScop hSN hSchar
        cases hrow with
        | intro D hD =>
          refine Exists.intro D ?_
          intro theta r aw hqk hqp hKn hPn hr haw
          apply (hD theta r aw hqk hqp hKn hPn hr haw).trans
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Real.rpow_le_rpow_of_exponent_le hz.le (by linarith)

open CanonicalRowCompletion

theorem low_dyadic_geometry_uniform_general
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
      let Hrow := (Ck*Z^(1-Lambda-2*d))/
        ((Ideal.absNorm (rowPowerfulPart J):Real)*(Ideal.absNorm (rowMaskPart J Q):Real))
      let Hslot := Z^ell0
      let G := (poolPrimeFamily J Q Q0).restrict A
      let jF := fun b : A => completedLocalExponent J F b.val.val
    forall (tuples : Finset (sigma->Ideal Eis))
      (hmax : forall p, Membership.mem tuples p -> forall i, (p i).IsMaximal)
      (hgood : forall p, Membership.mem tuples p -> forall i,
        Not (Membership.mem (p i) ConcretePrimeRowBridge.goodLambda))
      (_hinj : Set.InjOn slotTupleProduct (tuples : Set (sigma->Ideal Eis)))
      (hrows : forall K, Membership.mem rows K -> Admissible K),
      (forall f, IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) ->
      (forall f, Not (ringChar (HasQuotient.Quotient Eis (G.ideal f))=2)) ->
      (forall K, Membership.mem rows K ->
        (forall f, IsCoprime (G.ideal f) K) /\ IsCoprime (Ideal.span {Nlevel}) K) ->
      (forall p : tuples, Pairwise
        (Function.onFun IsCoprime (G.sum (memberTupleFamily tuples hmax hgood p)).ideal)) ->
      (forall p : tuples, forall b, IsCoprime (Ideal.span {Nlevel})
        ((G.sum (memberTupleFamily tuples hmax hgood p)).ideal b)) ->
      (forall p : tuples, forall b, Not (ringChar (HasQuotient.Quotient Eis
        ((G.sum (memberTupleFamily tuples hmax hgood p)).ideal b))=2)) ->
      (forall p, Membership.mem tuples p ->
        CubicSieve.Admissible (slotTupleProduct p) /\
          (Ideal.absNorm (slotTupleProduct p):Real)<=Hslot) ->
    Exists (fun D :
      (forall i : Fin (columnDyadicLength Hrow+1),
       forall j : Fin (columnDyadicLength Hslot+1),
        CellCompletion (N:=Nlevel) (a:=a g) (c:=c0 g) (mode:=mode g)
          G rows hrows tuples hmax hgood Hrow Hslot i j) =>
    forall (theta : Real) (r : Ideal Eis->Complex) (aw : (sigma->Ideal Eis)->Complex),
      (forall K, Membership.mem rows K -> norm (r K)<=1) ->
      (forall p, Membership.mem tuples p -> norm (aw p)<=1) ->
      (Finset.univ.sum fun K : rows=>
        norm (Finset.univ.sum fun p : tuples=>
          dyadicPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot D
            (s g) (hc0 g) jF W theta (Z^(1+ell0+shift)) r aw K p)^2)<=
        (columnDyadicLength Hrow+1:Real)*(columnDyadicLength Hslot+1:Real)^2*
          (C*(1+norm theta)^degree*Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+504*eta-O0/2)))) )) := by
  have hb := low_fixed_member_geometry_uniform_general a c0 mode lo hi hlo W hWs hW
    s hc0 hNlevel hbase hac Q hQ Ck eta hCk heta heta1
  cases hb with
  | intro degree h0 =>
    cases h0 with
    | intro C h1 =>
      cases h1 with
      | intro Z0 he =>
        have hC : 0<C := he.1
        have hZ0 : 1<Z0 := he.2.1
        refine Exists.intro degree (Exists.intro C
          (Exists.intro Z0 (And.intro hC (And.intro hZ0 ?_))))
        intro g sigma _ _ J F Q0 hJ hF A Z Lambda d ell0 shift O0
          hZ hLambda0 hLambda1 hd hd1 hell hellcap hshift hOeq parents rows hparents hsub hbad
        dsimp only
        intro tuples hmax hgood hinj hrows hGN hGchar hrowcop hpair hPN hPchar hPnorm
        let Hrow := (Ck*Z^(1-Lambda-2*d))/
          ((Ideal.absNorm (rowPowerfulPart J):Real)*(Ideal.absNorm (rowMaskPart J Q):Real))
        let Hslot := Z^ell0
        let G := (poolPrimeFamily J Q Q0).restrict A
        let jF := fun b : A => completedLocalExponent J F b.val.val
        have hz : 1<Z := lt_of_lt_of_le hZ0 hZ
        have hzp : 0<Z := lt_trans zero_lt_one hz
        have hrowNorm : forall K, Membership.mem rows K ->
            1<=(Ideal.absNorm K:Real) /\ (Ideal.absNorm K:Real)<=Hrow :=
          fun K hK=>original_residual_norm_bounds parents J Q hbad
            (Ck*Z^(1-Lambda-2*d)) hparents K (hsub hK)
        have htupleNorm : forall p, Membership.mem tuples p ->
            1<=(Ideal.absNorm (slotTupleProduct p):Real) /\
              (Ideal.absNorm (slotTupleProduct p):Real)<=Hslot :=
          fun p hp=>And.intro
            (QuadraticMainBoundary.norm_one_le (primaryGenerator_ne_zero_ideal _ (hPnorm p hp).1.2))
            (hPnorm p hp).2
        apply physical_dyad_selection_energy G rows hrows tuples hmax hgood Hrow Hslot
          (s g) (hc0 g) jF W (Z^(1+ell0+shift))
          (fun theta=>C*(1+norm theta)^degree*Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+504*eta-O0/2)) (fun theta=>by positivity)
        intro i j hi hj
        let Rc := divisorDyadicBin rows Hrow i
        let Tc := activeTupleDyad tuples Hslot j
        let hm := fun p hp k=>hmax p (activeTupleDyad_subset tuples Hslot j hp) k
        let hg := fun p hp k=>hgood p (activeTupleDyad_subset tuples Hslot j hp) k
        have hTc : Tc.Nonempty := hj
        have hRi : forall K, Membership.mem Rc K -> Admissible K :=
          fun K hK=>hrows K (divisorDyadicBin_subset rows Hrow i hK)
        have hti : Set.InjOn slotTupleProduct (Tc : Set (sigma->Ideal Eis)) :=
          hinj.mono (activeTupleDyad_subset tuples Hslot j)
        have hKr := divisorDyadicBin_bounds rows Hrow hrowNorm i
        have hPr := activeTupleDyad_bounds tuples Hslot htupleNorm j
        let K : Ideal Eis := Classical.choose hi
        have hK : Membership.mem Rc K := Classical.choose_spec hi
        have howner := Finset.mem_image.mp (hsub (divisorDyadicBin_subset rows Hrow i hK))
        let I : Ideal Eis := Classical.choose howner
        have hI := (Classical.choose_spec howner).1
        have heI := (Classical.choose_spec howner).2
        have hparts := Finset.mem_filter.mp hI
        have hIp := hparts.1
        have hpow := hparts.2.1
        have hmask := hparts.2.2
        have hI0 := (hparents I hIp).1
        have hIn := (hparents I hIp).2
        have hKlower : (2*divisorDyadicScale i.val)/2<=
            (Ideal.absNorm (rowResidualPart I Q):Real) := by
          rw [heI]
          convert (hKr K hK).1 using 1;ring
        have hKupper : 2*divisorDyadicScale i.val<=2*Ck*Z^(1-Lambda-2*d) := by
          have hres : (Ideal.absNorm (rowResidualPart I Q):Real)<=(Ideal.absNorm I:Real) := by
            rw [rowResidualPart_norm I Q hI0]
            apply div_le_self (Nat.cast_nonneg _)
            exact one_le_mul_of_one_le_of_one_le
              (QuadraticMainBoundary.norm_one_le (rowPowerfulPart_ne_zero I))
              (QuadraticMainBoundary.norm_one_le (squarefreeMaskPart_ne_zero (rowSimplePart I) Q))
          have hs := hKlower.trans (hres.trans hIn)
          linarith
        have hPupper : (2*divisorDyadicScale j.val)/2<=Z^ell0 := by
          convert activeTupleDyad_scale_le tuples Hslot htupleNorm j hj using 1
          dsimp [Hslot]
          ring
        let S := tuplePrimeFamily Tc hTc hm hg
        have hScop : forall P, Membership.mem (Tc.image slotTupleProduct) P ->
            Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal) := by
          intro P hP
          exact hpair (Subtype.mk (tupleRepresentative Tc hTc P)
            (activeTupleDyad_subset tuples Hslot j (tupleRepresentative_mem Tc hTc P)))
        have hSN : forall P, Membership.mem (Tc.image slotTupleProduct) P ->
            forall b, IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b) := by
          intro P hP
          exact hPN (Subtype.mk (tupleRepresentative Tc hTc P)
            (activeTupleDyad_subset tuples Hslot j (tupleRepresentative_mem Tc hTc P)))
        have hSchar : forall P, Membership.mem (Tc.image slotTupleProduct) P ->
            forall b, Not (ringChar (HasQuotient.Quotient Eis ((G.sum (S P)).ideal b))=2) := by
          intro P hP
          exact hPchar (Subtype.mk (tupleRepresentative Tc hTc P)
            (activeTupleDyad_subset tuples Hslot j (tupleRepresentative_mem Tc hTc P)))
        have hcell := he.2.2 g J I F Q0 hJ hI0 hF hpow.symm hmask.symm A
          Z Lambda d ell0 shift O0 (2*divisorDyadicScale i.val) (2*divisorDyadicScale j.val)
          hZ hLambda0 hLambda1 hd hd1 hell hellcap hshift (by rw [hpow];exact hOeq)
          hIn hKlower (by linarith [divisorDyadicScale_ge_one i.val]) hKupper
          (by linarith [divisorDyadicScale_ge_one j.val]) hPupper
          Rc Tc hTc hm hg hti hRi hGN hGchar
          (fun K hK=>hrowcop K (divisorDyadicBin_subset rows Hrow i hK))
          (tuplePrimeFamily_product Tc hTc hm hg) hScop hSN hSchar
        cases hcell with
        | intro D hD =>
          let Dc : CellCompletion (N:=Nlevel) (a:=a g) (c:=c0 g) (mode:=mode g)
              G rows hrows tuples hmax hgood Hrow Hslot i j :=
            fun K p hp=>memberTupleControlled Tc hm hg G K.val (hRi K.val K.property)
              hTc hti (D K) p hp
          refine Exists.intro Dc ?_
          intro theta r aw hr haw
          have hb := hD theta r aw
            (by linarith [divisorDyadicScale_ge_one i.val])
            (by linarith [divisorDyadicScale_ge_one j.val])
            (fun K hK=>by convert hKr K hK using 1;ring_nf)
            (by
              intro P hP
              have hpImage := Finset.mem_image.mp hP
              cases hpImage with
              | intro p hp =>
                cases hp with
                | intro hp heq =>
                  subst P
                  refine And.intro (hPnorm p (activeTupleDyad_subset tuples Hslot j hp)).1 ?_
                  convert hPr p hp using 1;ring_nf)
            (fun K hK=>hr K (divisorDyadicBin_subset rows Hrow i hK))
            (fun p hp=>haw p (activeTupleDyad_subset tuples Hslot j hp))
          exact hb

end PrimeFactorOscillations.GeneralLowGeometry
