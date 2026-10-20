/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Reflection.LowFullBudget
import PrimeFactorOscillations.Proof.DetectorPackets.GeneralLowEnergyExponent

/-!
# GeneralLowFullEnergy

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
# Whole arithmetic rows with a variable slot budget

Adds the actual unretained source tail to the generalized retained-row
energy, keeping the cusp phase, shape weights and normalization. The
budgeted theorem absorbs that tail under explicit polynomial caps.
This does not assert a zero-free region or a six-family Z estimate.
-/


noncomputable section
namespace PrimeFactorOscillations.GeneralLowGeometry
open OAI OAI.SevenEighths
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic
open CanonicalQuadraticSieve InverseTerminalWidths InverseMoment InverseReflectedPhase
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c0 : Eis} {mode : Bool}

theorem original_low_sector_full_energy_general
    (Adecay : Nat) (epsilon : Real) (hepsilon : 0<epsilon)
    (lo hi : Real) (hlo : 0<lo) (W : Real->Complex)
    (hWs : Set.Subset (Function.support W) (Set.Icc lo hi))
    (hW : ContDiff Real ((Top.top : ENat) : WithTop ENat) W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c0 mode))
    (hc0 : Not (c0=0)) (hNlevel : Dvd.dvd ((9:Eis)*c0) Nlevel)
    (hbase : if mode then Dvd.dvd (ConcretePrimeRowBridge.goodLambda^2) (a-1)
      else Dvd.dvd (ConcretePrimeRowBridge.goodLambda^2) (c0-1))
    (hac : IsCoprime a c0) (rho : Real) (hrho : 0<rho)
    (eta : Real) (heta : 0<eta)
    (kappa delta Lscale Lpool : Real) (hkappa : 0<kappa)
    (hdeltaL : 0<=delta+Lscale) (hLpool : 0<=Lpool) :
    Exists (fun degree : Nat => Exists (fun degreeTail : Nat =>
    Exists (fun C : Real => Exists (fun Ctail : Real => Exists (fun Z0 : Real =>
    0<C /\ 0<Ctail /\ 1<Z0 /\
    forall {sigma : Type v} [Fintype sigma],
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
      let G := (poolPrimeFamily J Q Q0).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      Inv.inv (familyRawScale G s X QK QP)<=Z^Lscale ->
      (Ideal.absNorm (Finset.univ.prod fun b=>G.ideal b):Real)<=Z^Lpool ->
    forall (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis->PrimeFamily sigma)
      (hrows : forall K, Membership.mem rows K -> Admissible K)
      (E : SectorArithmetic (N:=Nlevel) G rows Pset S hrows s hc0),
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
    forall (theta : Real) (r aw : Ideal Eis->Complex),
      1<=QK -> 2<=QP ->
      (forall K, Membership.mem rows K ->
        QK/2<=(Ideal.absNorm K:Real) /\ (Ideal.absNorm K:Real)<=QK) ->
      (forall P, Membership.mem Pset P ->
        CubicSieve.Admissible P /\ QP/2<=(Ideal.absNorm P:Real) /\
          (Ideal.absNorm P:Real)<=QP) ->
      (forall K, Membership.mem rows K -> norm (r K)<=1) ->
      (forall P, Membership.mem Pset P -> norm (aw P)<=1) ->
      (Finset.univ.sum fun K : rows=>
        norm (literalWholeRow G K.val (hrows K.val K.property) S j Pset
          (E.completion K) s hc0 W theta X r aw)^2)<=
        C*(1+norm theta)^degree*Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+200*eta+pi+kappa+rho*Lpool-O0/2)+
          2*(rows.card:Real)*((Pset.card:Real)*Ctail*(1+norm theta)^degreeTail*
            ((Ideal.absNorm (Finset.univ.prod fun b=>G.ideal b):Real)*QK*QP)*
            (Z^delta)^(-(Adecay:Real))*
            Inv.inv ((familyRawScale G s X QK QP)^2))^2))))) := by
  have hb := original_low_sector_retained_budget_general (Nlevel:=Nlevel)
    epsilon hepsilon lo hi hlo W hWs hW s hc0 hNlevel hbase hac rho hrho eta heta
    kappa delta Lscale Lpool hkappa hdeltaL hLpool
  cases hb with
  | intro degree hb0 =>
    cases hb0 with
    | intro Cm hb1 =>
      cases hb1 with
      | intro Z0 hb2 =>
        have htbase := original_family_whole_tail
          (N:=Nlevel) (a:=a) (c:=c0) (mode:=mode) lo hi hlo Adecay W hWs hW
        cases htbase with
        | intro degreeTail ht0 =>
          cases ht0 with
          | intro Ct ht1 =>
            have hCm : 0<Cm := hb2.1
            have hZ0 : 1<Z0 := hb2.2.1
            have hCt : 0<Ct := ht1.1
            let Cshape := norm fixedRadialCoefficientScalar*norm (s.stratumShapeFactor c0)
            let Ctail := 6*Cshape*Ct+1
            have hshape : 0<=Cshape := by dsimp [Cshape];positivity
            have hCtail : 0<Ctail := by dsimp [Ctail];positivity
            refine Exists.intro degree (Exists.intro degreeTail
              (Exists.intro (2*Cshape^2*Cm+1) (Exists.intro Ctail
                (Exists.intro Z0 (And.intro (by positivity)
                  (And.intro hCtail (And.intro hZ0 ?_)))))))
            intro sigma _ J I F Q Q0 hJ hI hQ hpower hmask A
              Z O0 H za Nstar Lambda d ell0 shift pi Ck CO CH X QK QP
              Lrow Lslot hZ hCk hCO hCH hX hK hP hIn hPow hRow
              hlog hPowUpper hQwidth hLambda0 hLambda1 hd hd1 hell0 hO hza hshift
              hNs heH heza heN hdelta hdeta hrowcap hslotcap hconst hbudget
            dsimp only
            intro hscale hpool rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar
              theta r aw hqk hqp hKr hPr hr haw
            let G := (poolPrimeFamily J Q Q0).restrict A
            let j := fun b : A => completedLocalExponent J F b.val.val
            let rr := fun K => r K*shapeArgument (primaryGenerator K)
            let aa := fun P => aw P*shapeArgument (primaryGenerator P)
            let phi := fixedRadialCoefficientScalar*
              s.stratumShapeFactor (c0*primaryGenerator (Finset.univ.prod fun b=>G.ideal b))
            let g := fun K : rows => tsum (fun u : Units Eis=>
              Finset.sum (retainedDyads (familyRawScale G s X QK QP) (16*Z^delta)) (fun i=>
                literalDyadicRow G K.val (hrows K.val K.property) S j Pset
                  (E.completion K) s hc0 u i W theta X rr aa))
            let f := fun K : rows => literalWholeRow G K.val (hrows K.val K.property)
              S j Pset (E.completion K) s hc0 W theta X r aw
            let Et := (Pset.card:Real)*Ctail*(1+norm theta)^degreeTail*
              ((Ideal.absNorm (Finset.univ.prod fun b=>G.ideal b):Real)*QK*QP)*
              (Z^delta)^(-(Adecay:Real))*Inv.inv ((familyRawScale G s X QK QP)^2)
            have hzpos : 0<Z := lt_trans zero_lt_one (lt_of_lt_of_le hZ0 hZ)
            have hEt : 0<=Et := by dsimp [Et];positivity
            have hphi : norm phi=Cshape := by
              dsimp only [phi,Cshape]
              rw [norm_mul,stratumShapeFactor_frozen_norm]
            have hmain := hb2.2.2 J I F Q Q0 hJ hI hQ hpower hmask A
              Z O0 H za Nstar Lambda d ell0 shift pi Ck CO CH X QK QP
              Lrow Lslot hZ hCk hCO hCH hX hK hP hIn hPow hRow
              hlog hPowUpper hQwidth hLambda0 hLambda1 hd hd1 hell0 hO hza hshift
              hNs heH heza heN hdelta hdeta hrowcap hslotcap hconst hbudget hscale hpool
              rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar theta rr aa
              hqk hqp hKr hPr
              (fun K hK => by simpa only [rr,row_shape_weight_norm r K (hrows K hK)] using hr K hK)
              (fun P hP => by simpa only [aa,slot_shape_weight_norm aw P (hPr P hP).1] using haw P hP)
            have hrem (K : rows) : norm (f K-phi*g K)<=Et := by
              have hodd : forall P, Membership.mem Pset P -> forall b,
                  Not (ringChar (HasQuotient.Quotient Eis
                    ((G.reflected K.val (hrows K.val K.property) (S P)).ideal b))=2) := by
                intro P hP b
                cases b with
                | inl b => exact hGchar b
                | inr bb =>
                  cases bb with
                  | inl b =>
                    exact ((hrows K.val K.property).2.2 b.val
                      (Multiset.mem_toFinset.mp b.property)).2
                  | inr b => exact hSchar P hP (Sum.inr b)
              have hj : forall b : A, j b<6 := by
                intro b
                exact Nat.mod_lt _ (by norm_num)
              have hh := ht1.2 G K.val (hrows K.val K.property) S j Pset (E.completion K)
                s hc0 hNlevel hbase hodd hj hprod (fun P hP => (hPr P hP).1)
                theta X (Z^delta) QK QP r aw hX (Real.rpow_pos_of_pos hzpos _)
                hK hP (hKr K.val K.property).2 (fun P hP => (hPr P hP).2.2)
                (hr K.val K.property) haw
              apply hh.trans
              change _<=Et
              dsimp only [Et,Ctail,Cshape]
              have he : (6*norm fixedRadialCoefficientScalar*norm (s.stratumShapeFactor c0))*
                  (Pset.card:Real)*(Ct*(1+norm theta)^degreeTail*
                    ((Ideal.absNorm (Finset.univ.prod fun b=>G.ideal b):Real)*QK*QP)*
                    (Z^delta)^(-(Adecay:Real))*Inv.inv ((familyRawScale G s X QK QP)^2))=
                (Pset.card:Real)*(6*(norm fixedRadialCoefficientScalar*
                  norm (s.stratumShapeFactor c0))*Ct)*(1+norm theta)^degreeTail*
                  ((Ideal.absNorm (Finset.univ.prod fun b=>G.ideal b):Real)*QK*QP)*
                  (Z^delta)^(-(Adecay:Real))*Inv.inv ((familyRawScale G s X QK QP)^2) := by ring
              rw [he]
              gcongr
              linarith only
            have hh := row_energy_le_retained (Finset.univ : Finset rows)
              f (fun K=>phi*g K) Et hEt (fun K _=>hrem K)
            simp only [norm_mul,mul_pow,hphi,<-Finset.mul_sum,Finset.card_univ,Fintype.card_coe] at hh
            apply hh.trans
            calc
              _ <= 2*(Cshape^2*(Cm*(1+norm theta)^degree*Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+200*eta+pi+kappa+rho*Lpool-O0/2)))+
                  2*(rows.card:Real)*Et^2 := by gcongr
              _ <= _ := by
                dsimp only [Et]
                have hp : 0<=(1+norm theta)^degree*Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+200*eta+pi+kappa+rho*Lpool-O0/2) := by positivity
                nlinarith only [hp]

theorem original_low_sector_full_budget_general
    (epsilon : Real) (hepsilon : 0<epsilon)
    (lo hi : Real) (hlo : 0<lo) (W : Real->Complex)
    (hWs : Set.Subset (Function.support W) (Set.Icc lo hi))
    (hW : ContDiff Real ((Top.top : ENat) : WithTop ENat) W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c0 mode))
    (hc0 : Not (c0=0)) (hNlevel : Dvd.dvd ((9:Eis)*c0) Nlevel)
    (hbase : if mode then Dvd.dvd (ConcretePrimeRowBridge.goodLambda^2) (a-1)
      else Dvd.dvd (ConcretePrimeRowBridge.goodLambda^2) (c0-1))
    (hac : IsCoprime a c0) (rho : Real) (hrho : 0<rho)
    (eta : Real) (heta : 0<eta)
    (kappa delta Lscale Lpool : Real) (hkappa : 0<kappa)
    (hdeltaL : 0<=delta+Lscale) (hLpool : 0<=Lpool)
    (Lcap saving : Real) (hdeltaPos : 0<delta) :
    Exists (fun degree : Nat => Exists (fun C : Real => Exists (fun Z0 : Real =>
    0<C /\ 1<Z0 /\
    forall {sigma : Type v} [Fintype sigma],
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
    forall (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis->PrimeFamily sigma)
      (hrows : forall K, Membership.mem rows K -> Admissible K)
      (E : SectorArithmetic (N:=Nlevel) G rows Pset S hrows s hc0),
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
    forall (theta : Real) (r aw : Ideal Eis->Complex),
      1<=QK -> 2<=QP ->
      (forall K, Membership.mem rows K ->
        QK/2<=(Ideal.absNorm K:Real) /\ (Ideal.absNorm K:Real)<=QK) ->
      (forall P, Membership.mem Pset P ->
        CubicSieve.Admissible P /\ QP/2<=(Ideal.absNorm P:Real) /\
          (Ideal.absNorm P:Real)<=QP) ->
      (forall K, Membership.mem rows K -> norm (r K)<=1) ->
      (forall P, Membership.mem Pset P -> norm (aw P)<=1) ->
      (Finset.univ.sum fun K : rows=>
        norm (literalWholeRow G K.val (hrows K.val K.property) S j Pset
          (E.completion K) s hc0 W theta X r aw)^2)<=
        C*(1+norm theta)^degree*Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+200*eta+pi+kappa+rho*Lpool-O0/2)))) := by
  have htbase := actual_finite_source_tail_budget s Lcap delta saving hdeltaPos
  cases htbase with
  | intro Adecay htail =>
    have hebase := original_low_sector_full_energy_general (Nlevel:=Nlevel)
      Adecay epsilon hepsilon lo hi hlo W hWs hW s hc0 hNlevel hbase hac rho hrho eta heta
      kappa delta Lscale Lpool hkappa hdeltaL hLpool
    cases hebase with
    | intro degree he0 =>
      cases he0 with
      | intro degreeTail he1 =>
        cases he1 with
        | intro Cm he2 =>
          cases he2 with
          | intro Ct he3 =>
            cases he3 with
            | intro Z0 he4 =>
              have hCm : 0<Cm := he4.1
              have hCt : 0<Ct := he4.2.1
              have hZ0 : 1<Z0 := he4.2.2.1
              let cusp := 27*(sourceCuspScale s.index)^2*
                (Ideal.absNorm (Ideal.span {c0}):Real)^2
              let deg := max degree (degreeTail*2)
              refine Exists.intro deg (Exists.intro (Cm+2*Ct^2*cusp^4+1)
                (Exists.intro (max Z0 128) (And.intro (by positivity)
                  (And.intro (lt_of_lt_of_le hZ0 (le_max_left _ _)) ?_))))
              intro sigma _ J I F Q Q0 hJ hI hQ hpower hmask A
                Z O0 H za Nstar Lambda d ell0 shift pi Ck CO CH X QK QP
                Lrow Lslot hZ hCk hCO hCH hX hK hP hIn hPow hRow
                hlog hPowUpper hQwidth hLambda0 hLambda1 hd hd1 hell0 hO hza hshift
                hNs heH heza heN hdelta hdeta hrowcap hslotcap hconst hbudget
                hXi hKcap hPcap hexp
              dsimp only
              intro hFcap hscale hpool rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar
                theta r aw hqk hqp hKr hPr hr haw
              let G := (poolPrimeFamily J Q Q0).restrict A
              have hz : 1<Z := lt_of_lt_of_le hZ0 ((le_max_left _ _).trans hZ)
              have hzpos : 0<Z := lt_trans zero_lt_one hz
              have h128 : 128<=Z := (le_max_right _ _).trans hZ
              have hs := he4.2.2.2 J I F Q Q0 hJ hI hQ hpower hmask A
                Z O0 H za Nstar Lambda d ell0 shift pi Ck CO CH X QK QP
                Lrow Lslot ((le_max_left _ _).trans hZ)
                hCk hCO hCH hX hK hP hIn hPow hRow hlog hPowUpper hQwidth
                hLambda0 hLambda1 hd hd1 hell0 hO hza hshift hNs heH heza heN
                hdelta hdeta hrowcap hslotcap hconst hbudget hscale hpool
                rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar
                theta r aw hqk hqp hKr hPr hr haw
              have ht := htail G rows Pset Z X QK QP h128 hX hqk (by linarith only [hqp])
                (fun K hK => And.intro (hrows K hK).1 (hKr K hK).2)
                (fun P hP => And.intro (hPr P hP).1.1.ne_zero (hPr P hP).2.2)
                hFcap hKcap hPcap hXi
              have hheight : 1<=1+norm theta := by linarith only [norm_nonneg theta]
              have hdm : (1+norm theta)^degree<=(1+norm theta)^deg := by
                dsimp only [deg]
                gcongr; exact le_max_left _ _
              have hdt : (1+norm theta)^(degreeTail*2)<=(1+norm theta)^deg := by
                dsimp only [deg]
                gcongr; exact le_max_right _ _
              have hexponent := Real.rpow_le_rpow_of_exponent_le hz.le hexp
              apply hs.trans
              have htailbound : 2*(rows.card:Real)*((Pset.card:Real)*Ct*
                    (1+norm theta)^degreeTail*
                    ((Ideal.absNorm (Finset.univ.prod fun b=>G.ideal b):Real)*QK*QP)*
                    (Z^delta)^(-(Adecay:Real))*Inv.inv ((familyRawScale G s X QK QP)^2))^2<=
                  (2*Ct^2*cusp^4)*(1+norm theta)^deg*Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+200*eta+pi+kappa+rho*Lpool-O0/2) := by
                calc
                  _ = (2*Ct^2*(1+norm theta)^(degreeTail*2))*
                      ((rows.card:Real)*((Pset.card:Real)*
                        ((Ideal.absNorm (Finset.univ.prod fun b=>G.ideal b):Real)*QK*QP)*
                        (Z^delta)^(-(Adecay:Real))*Inv.inv ((familyRawScale G s X QK QP)^2))^2) := by
                    rw [pow_mul]
                    ring
                  _ <= (2*Ct^2*(1+norm theta)^(degreeTail*2))*(cusp^4*Z^(-saving)) := by
                    exact mul_le_mul_of_nonneg_left ht (by positivity)
                  _ <= (2*Ct^2*(1+norm theta)^deg)*(cusp^4*Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+200*eta+pi+kappa+rho*Lpool-O0/2)) := by gcongr
                  _ = _ := by ring
              have hmain : Cm*(1+norm theta)^degree*Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+200*eta+pi+kappa+rho*Lpool-O0/2)<=
                  Cm*(1+norm theta)^deg*Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+200*eta+pi+kappa+rho*Lpool-O0/2) := by gcongr
              apply (add_le_add hmain htailbound).trans
              have hp : 0<=(1+norm theta)^deg*Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+200*eta+pi+kappa+rho*Lpool-O0/2) := by positivity
              nlinarith only [hp]

end PrimeFactorOscillations.GeneralLowGeometry
