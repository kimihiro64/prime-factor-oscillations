/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Reflection.LowMemberBudget
import PrimeFactorOscillations.Assembly.DetectorPackets.GeneralLowFullEnergy

/-!
# GeneralLowGlobalEnergy

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
# Global arithmetic rows with a variable slot budget

Combines the generalized whole-sector bound using the actual global
completion, retaining its fixed-level residue-sector cost. Then transports
the result to member tuples with injective product indexing. No zero-free
boundary or varying-level uniformity is asserted here.
-/


noncomputable section
namespace PrimeFactorOscillations.GeneralLowGeometry
open scoped Classical
open OAI OAI.SevenEighths
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic
open CanonicalQuadraticSieve InverseTerminalWidths InverseMoment InverseReflectedPhase
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c0 : Eis} {mode : Bool}

theorem original_low_global_full_budget_general
    [Fintype (HasQuotient.Quotient Eis (Ideal.span {Nlevel^2}))]
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
      (hrows : forall K, Membership.mem rows K -> Admissible K),
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
          (D K) s hc0 W theta X r aw)^2)<=
        C*(1+norm theta)^degree*Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+200*eta+pi+kappa+rho*Lpool-O0/2))))) := by
  have hb := original_low_sector_full_budget_general (Nlevel:=Nlevel)
    epsilon hepsilon lo hi hlo W hWs hW s hc0 hNlevel hbase hac rho hrho eta heta
    kappa delta Lscale Lpool hkappa hdeltaL hLpool Lcap saving hdeltaPos
  cases hb with
  | intro degree h0 =>
    cases h0 with
    | intro C h1 =>
      cases h1 with
      | intro Z0 he =>
        have hC : 0<C := he.1
        have hZ0 : 1<Z0 := he.2.1
        let q := (Fintype.card (HasQuotient.Quotient Eis (Ideal.span {Nlevel^2})):Real)
        have hq : 0<=q := Nat.cast_nonneg _
        refine Exists.intro degree (Exists.intro (q^3*C+1)
          (Exists.intro Z0 (And.intro (by positivity) (And.intro hZ0 ?_))))
        intro sigma _ J I F Q Q0 hJ hI hQ hpower hmask A
          Z O0 H za Nstar Lambda d ell0 shift pi Ck CO CH X QK QP
          Lrow Lslot hZ hCk hCO hCH hX hK hP hIn hPow hRow
          hlog hPowUpper hQwidth hLambda0 hLambda1 hd hd1 hell0 hO hza hshift
          hNs heH heza heN hdelta hdeta hrowcap hslotcap hconst hbudget
          hXi hKcap hPcap hexp
        dsimp only
        intro hFcap hscale hpool rows Pset S hrows hGN hGchar hrowcop hprod hScop hSN hSchar
        let G := (poolPrimeFamily J Q Q0).restrict A
        let j := fun b : A => completedLocalExponent J F b.val.val
        have hpair := (poolPrimeFamily J Q Q0).restrict_pairwise
          (poolPrimeFamily_pairwise J Q Q0) A
        have hcomp := exists_global_sector_completion G rows Pset S hrows s hc0
          hNlevel hbase hac hpair hGN hrowcop hprod hScop
          (fun P hP b=>hSN P hP (Sum.inr b))
        cases hcomp with
        | intro D hD =>
          refine Exists.intro D ?_
          intro theta r aw hqk hqp hKr hPr hr haw
          have hzpos : 0<Z := lt_trans zero_lt_one (lt_of_lt_of_le hZ0 hZ)
          have hs := literal_global_sector_energy G rows Pset S hrows j D s hc0 W theta X r aw
            (C*(1+norm theta)^degree*Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+200*eta+pi+kappa+rho*Lpool-O0/2)) (by
              intro r0 p0
              have hsector := hD r0 p0
              cases hsector with
              | intro E hE =>
                refine Exists.intro E (And.intro hE ?_)
                exact he.2.2 J I F Q Q0 hJ hI hQ hpower hmask A
                  Z O0 H za Nstar Lambda d ell0 shift pi Ck CO CH X QK QP
                  Lrow Lslot hZ hCk hCO hCH hX hK hP hIn hPow hRow
                  hlog hPowUpper hQwidth hLambda0 hLambda1 hd hd1 hell0 hO hza hshift
                  hNs heH heza heN hdelta hdeta hrowcap hslotcap hconst hbudget
                  hXi hKcap hPcap hexp hFcap hscale hpool
                  (fullRaySector Nlevel rows r0) (fullRaySector Nlevel Pset p0) S
                  (fun K hK=>hrows K (Finset.mem_filter.mp hK).1) E hGN hGchar
                  (fun K hK=>hrowcop K (Finset.mem_filter.mp hK).1)
                  (fun P hP=>hprod P (Finset.mem_filter.mp hP).1)
                  (fun P hP=>hScop P (Finset.mem_filter.mp hP).1)
                  (fun P hP=>hSN P (Finset.mem_filter.mp hP).1)
                  (fun P hP=>hSchar P (Finset.mem_filter.mp hP).1)
                  theta r aw hqk hqp
                  (fun K hK=>hKr K (Finset.mem_filter.mp hK).1)
                  (fun P hP=>hPr P (Finset.mem_filter.mp hP).1)
                  (fun K hK=>hr K (Finset.mem_filter.mp hK).1)
                  (fun P hP=>haw P (Finset.mem_filter.mp hP).1))
          apply hs.trans
          change q^3*(C*(1+norm theta)^degree*Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+200*eta+pi+kappa+rho*Lpool-O0/2))<=_
          have hp : 0<=(1+norm theta)^degree*Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+200*eta+pi+kappa+rho*Lpool-O0/2) := by positivity
          nlinarith

theorem original_low_member_tuple_full_budget_general
    [Fintype (HasQuotient.Quotient Eis (Ideal.span {Nlevel^2}))]
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
  have hb := original_low_global_full_budget_general (Nlevel:=Nlevel)
    epsilon hepsilon lo hi hlo W hWs hW s hc0 hNlevel hbase hac rho hrho eta heta
    kappa delta Lscale Lpool hkappa hdeltaL hLpool Lcap saving hdeltaPos
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
        intro sigma _ _ J I F Q Q0 hJ hI hQ hpower hmask A
          Z O0 H za Nstar Lambda d ell0 shift pi Ck CO CH X QK QP
          Lrow Lslot hZ hCk hCO hCH hX hK hP hIn hPow hRow
          hlog hPowUpper hQwidth hLambda0 hLambda1 hd hd1 hell0 hO hza hshift
          hNs heH heza heN hdelta hdeta hrowcap hslotcap hconst hbudget
          hXi hKcap hPcap hexp
        dsimp only
        intro hFcap hscale hpool rows tuples hne hmax hgood hinj
          hrows hGN hGchar hrowcop hprod hScop hSN hSchar
        let G := (poolPrimeFamily J Q Q0).restrict A
        let j := fun b : A => completedLocalExponent J F b.val.val
        have hglobal := he.2.2 J I F Q Q0 hJ hI hQ hpower hmask A
          Z O0 H za Nstar Lambda d ell0 shift pi Ck CO CH X QK QP
          Lrow Lslot hZ hCk hCO hCH hX hK hP hIn hPow hRow
          hlog hPowUpper hQwidth hLambda0 hLambda1 hd hd1 hell0 hO hza hshift
          hNs heH heza heN hdelta hdeta hrowcap hslotcap hconst hbudget
          hXi hKcap hPcap hexp hFcap hscale hpool
          rows (tuples.image slotTupleProduct) (tuplePrimeFamily tuples hne hmax hgood)
          hrows hGN hGchar hrowcop hprod hScop hSN hSchar
        cases hglobal with
        | intro D hD =>
          refine Exists.intro D ?_
          intro theta r aw hqk hqp hKr hPr hr haw
          have heval := hD theta r (slotProductCoefficient tuples aw) hqk hqp hKr hPr hr
            (fun P hP=>slotProductCoefficient_norm tuples hinj aw haw P hP)
          convert heval using 1
          apply Finset.sum_congr rfl
          intro K hK
          congr 2
          exact (literalWholeRow_eq_member_tuples tuples hmax hgood G K.val
            (hrows K.val K.property) hne hinj (D K) s hc0 j W theta X r aw).symm

end PrimeFactorOscillations.GeneralLowGeometry
