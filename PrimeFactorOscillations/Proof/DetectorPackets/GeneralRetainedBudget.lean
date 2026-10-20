/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/


import PrimeFactorOscillations.Proof.DetectorPackets.GeneralSectorEnergy

/-!
# General retained low-energy budget

Exact component of the checked general low-energy statements and proofs.
All hypotheses and their original namespace are retained.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.GeneralLowGeometry
open OAI.SevenEighths.InverseTerminalWidths
open OAI.SevenEighths.ProbeLowReflected

open OAI OAI.SevenEighths
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
open InverseMoment InverseReflectedPhase
local notation "Eis" => ActualEisensteinCubic.O
variable {a c0 : Eis} {mode : Bool}

open CompletedDyadic
universe v
variable {Nlevel : Eis}

theorem original_low_sector_retained_budget_general
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
    (hdeltaL : 0<=delta+Lscale) (_hLpool : 0<=Lpool) :
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
        norm (tsum (fun u : Units Eis=>
          Finset.sum (retainedDyads (familyRawScale G s X QK QP) (16*Z^delta)) (fun i=>
            literalDyadicRow G K.val (hrows K.val K.property) S j Pset
              (E.completion K) s hc0 u i W theta X r aw)))^2)<=
        C*(1+norm theta)^degree*Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+200*eta+pi+kappa+rho*Lpool-O0/2)))) := by
  have hb := original_low_sector_retained_energy_general (Nlevel:=Nlevel)
    epsilon hepsilon lo hi hlo W hWs hW s hc0 hNlevel hbase hac rho hrho eta heta
  cases hb with
  | intro degree h0 =>
    cases h0 with
    | intro C h1 =>
      cases h1 with
      | intro Z0 he =>
        have hC : 0<C := he.1
        have hZ0 : 1<Z0 := he.2.1
        have hc := retained_count_budget kappa delta Lscale hkappa hdeltaL
        cases hc with
        | intro Cd hcd =>
          have hCd : 0<Cd := hcd.1
          refine Exists.intro degree (Exists.intro (C*Cd)
            (Exists.intro Z0 (And.intro (mul_pos hC hCd) (And.intro hZ0 ?_))))
          intro sigma _ J I F Q Q0 hJ hI hQ hpower hmask A
            Z O0 H za Nstar Lambda d ell0 shift pi Ck CO CH X QK QP
            Lrow Lslot hZ hCk hCO hCH hX hK hP hIn hPow hRow
            hlog hPowUpper hQwidth hLambda0 hLambda1 hd hd1 hell0 hO hza hshift
            hNs heH heza heN hdelta hdeta hrowcap hslotcap hconst hbudget
          dsimp only
          intro hscale hpool rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar
            theta r aw hqk hqp hKr hPr hr haw
          let G := (poolPrimeFamily J Q Q0).restrict A
          have hz : 1<Z := lt_of_lt_of_le hZ0 hZ
          have hzpos : 0<Z := lt_trans zero_lt_one hz
          have hs := he.2.2 J I F Q Q0 hJ hI hQ hpower hmask A
            Z O0 H za Nstar Lambda d ell0 shift delta pi Ck CO CH X QK QP
            Lscale Lrow Lslot hZ hCk hCO hCH hX hK hP hIn hPow hRow
            hlog hPowUpper hQwidth hLambda0 hLambda1 hd hd1 hell0 hO hza hshift
            hNs heH heza heN hdelta hdeta hrowcap hslotcap hconst hbudget hscale
            rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar
            theta r aw hqk hqp hKr hPr hr haw
          have hdc := hcd.2 Z (familyRawScale G s X QK QP) hz.le hscale
          have hp : (Ideal.absNorm (Finset.univ.prod fun b=>G.ideal b):Real)^rho<=Z^(Lpool*rho) := by
            rw [Real.rpow_mul hzpos.le]
            exact Real.rpow_le_rpow (Nat.cast_nonneg _) hpool hrho.le
          apply hs.trans
          calc
            _ <= C*(Cd*Z^kappa)*(1+norm theta)^degree*Z^(Lpool*rho)*
                Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+200*eta+pi-O0/2) := by gcongr
            _ = (C*Cd)*(1+norm theta)^degree*
                Z^(kappa+Lpool*rho+((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+200*eta+pi-O0/2)) := by
              rw [Real.rpow_add hzpos,Real.rpow_add hzpos]
              ring
            _ <= _ := mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le hz.le (by nlinarith)) (by positivity)

end PrimeFactorOscillations.GeneralLowGeometry
