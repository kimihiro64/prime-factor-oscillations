/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/


import PrimeFactorOscillations.Proof.DetectorPackets.GeneralSurvivingEnergy

/-!
# General literal and retained sector energy

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

theorem original_low_sector_literal_energy_general
    (epsilon : Real) (hepsilon : 0<epsilon)
    (lo hi : Real) (hlo : 0<lo) (W : Real->Complex)
    (hWs : Set.Subset (Function.support W) (Set.Icc lo hi))
    (hW : ContDiff Real ((Top.top : ENat) : WithTop ENat) W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c0 mode))
    (hc0 : Not (c0=0)) (hNlevel : Dvd.dvd ((9:Eis)*c0) Nlevel)
    (hbase : if mode then Dvd.dvd (ConcretePrimeRowBridge.goodLambda^2) (a-1)
      else Dvd.dvd (ConcretePrimeRowBridge.goodLambda^2) (c0-1))
    (hac : IsCoprime a c0) (rho : Real) (hrho : 0<rho)
    (eta : Real) (heta : 0<eta) :
    Exists (fun degree : Nat => Exists (fun C : Real => Exists (fun Z0 : Real =>
    0<C /\ 1<Z0 /\
    forall {sigma : Type v} [Fintype sigma],
    forall (J I F Q Q0 : Ideal Eis) (_hJ : Not (J=0))
      (_hI : Not (I=0)) (_hQ : Not (Q=0)),
      rowPowerfulPart J=rowPowerfulPart I ->
      rowMaskPart J Q=rowMaskPart I Q ->
    forall (A : Finset (FreeReflection.pool J Q Q0))
      (Z O0 H za Nstar Lambda d ell0 shift delta pi Ck CO CH X QK QP
        Lscale Lrow Lslot : Real) (i : Prod Nat (Prod Nat Nat)),
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
      Membership.mem (retainedDyads (familyRawScale G s X QK QP) (16*Z^delta)) i ->
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
    forall (u : Units Eis) (theta : Real) (r aw : Ideal Eis->Complex),
      1<=QK -> 2<=QP ->
      (forall K, Membership.mem rows K ->
        QK/2<=(Ideal.absNorm K:Real) /\ (Ideal.absNorm K:Real)<=QK) ->
      (forall P, Membership.mem Pset P ->
        CubicSieve.Admissible P /\ QP/2<=(Ideal.absNorm P:Real) /\
          (Ideal.absNorm P:Real)<=QP) ->
      (forall K, Membership.mem rows K -> norm (r K)<=1) ->
      (forall P, Membership.mem Pset P -> norm (aw P)<=1) ->
      (Finset.univ.sum fun K : rows=>
        norm (literalDyadicRow G K.val (hrows K.val K.property) S j Pset
          (E.completion K) s hc0 u i W theta X r aw)^2)<=
        C*(1+norm theta)^degree*
          (Ideal.absNorm (Finset.univ.prod fun b=>G.ideal b):Real)^rho*
          Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+200*eta+pi-O0/2)))) := by
  have hg := sector_normalized_literal_energy
    (N:=Nlevel) epsilon hepsilon lo hi hlo W hWs hW s hc0 eta heta
  cases hg with
  | intro degree hg0 =>
    cases hg0 with
    | intro C0 hg1 =>
      cases hg1 with
      | intro Cs hg2 =>
        cases hg2 with
        | intro Zs hg3 =>
          have hC0 : 0<=C0 := hg3.1
          have hCs : 0<Cs := hg3.2.1
          have hZs : 1<Zs := hg3.2.2.1
          have hbr := original_surviving_low_energy_sum_general s hc0 rho hrho 1 (1/2) eta
            (by norm_num) (by norm_num) heta
          cases hbr with
          | intro Zb hbr0 =>
            cases hbr0 with
            | intro Cb hbr1 =>
              have hZb : 1<Zb := hbr1.1
              have hCb : 0<Cb := hbr1.2.1
              let Kc := (Real.exp (Real.log 2/2+Real.log 2))^2*(6*Cs)
              have hKc : 0<Kc := by dsimp [Kc];positivity
              refine Exists.intro (degree*2) (Exists.intro (Kc*Cb*C0^2+1)
                (Exists.intro (max Zs Zb) (And.intro (by positivity)
                  (And.intro (lt_of_lt_of_le hZs (le_max_left _ _)) ?_))))
              intro sigma _ J I F Q Q0 hJ hI hQ hpower hmask A
                Z O0 H za Nstar Lambda d ell0 shift delta pi Ck CO CH X QK QP
                Lscale Lrow Lslot i hZ hCk hCO hCH hX hK hP hIn hPow hRow
                hlog hPowUpper hQwidth hLambda0 hLambda1 hd hd1 hell0 hO hza hshift
                hNs heH heza heN hdelta hdeta hrowcap hslotcap hconst hbudget
              dsimp only
              intro hscale hret rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar
                u theta r aw hqk hqp hKr hPr hr haw
              have hzpos : 0<Z := lt_trans zero_lt_one
                (lt_of_lt_of_le hZs ((le_max_left _ _).trans hZ))
              let G := (poolPrimeFamily J Q Q0).restrict A
              let j := fun b : A => completedLocalExponent J F b.val.val
              have hpair := (poolPrimeFamily J Q Q0).restrict_pairwise
                (poolPrimeFamily_pairwise J Q Q0) A
              have hj : forall b : A, j b<6 := by
                intro b
                exact Nat.mod_lt _ (by norm_num)
              have hs := hg3.2.2.2 Z ((le_max_left _ _).trans hZ) G j
                hNlevel hbase hac hpair hGN hGchar hj rows Pset S hrows E
                hrowcop hprod hScop hSN hSchar u i X theta QK QP r aw
                hX hqk hqp hKr hPr hr haw
              have hb := hbr1.2.2 J I F Q Q0 hJ hI hQ hpower hmask A
                (actualCuspColumn E.referenceArithmetic s hc0 u i.1)
                Z O0 H za Nstar Lambda d ell0 shift delta pi Ck CO CH X QK QP
                epsilon Lscale Lrow Lslot i ((le_max_right _ _).trans hZ)
                hCk hCO hCH hX hK hP hIn hPow hRow hlog hPowUpper hQwidth
                hLambda0 hLambda1 hd hd1 hell0 hO hza hshift hNs
                (by simpa only [one_mul] using heH)
                (by simpa only [one_div,mul_comm,mul_inv_rev,div_eq_mul_inv,one_mul] using heza)
                heN hdelta hdeta hepsilon.le
                (by simpa only [one_mul] using hrowcap)
                (by simpa only [one_div,mul_comm,mul_inv_rev,div_eq_mul_inv,one_mul] using hslotcap)
                hconst hbudget hscale hret
              dsimp only at hs hb
              rw [<-heH,<-heza,<-heN] at hs
              simp_rw [<-Finset.mul_sum] at hs
              let branches := survivingFrozenBranches G j
                (actualCuspColumn E.referenceArithmetic s hc0 u i.1)
                (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
              let Epow := fun e : A->Fin 3 =>
                OAI.SevenEighths.InverseTerminalWidths.reflectedExponent 0 H
                  (normWidth Z (frozenExtracted G j e 0))
                  (normWidth Z (frozenExtracted G j e 2)) za
                  (Real.logb Z (((2:Real)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1)))
                  (Real.logb Z (((2:Real)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2)))
                  (ramifiedWidth Z i.1) (terminalDualWidth Z H za Nstar G.ideal j e)+
                  epsilon*(H+
                    Real.logb Z (((2:Real)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1))+
                    Real.logb Z (((2:Real)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2))+za)+eta/2
              change _ <= ((branches.card:Real)*(Kc*Finset.sum branches (fun e=>Z^(Epow e))))*
                (C0*(1+norm theta)^degree)^2 at hs
              apply hs.trans
              calc
                _ = Kc*((branches.card:Real)*Finset.sum branches (fun e=>Z^(Epow e)))*
                    (C0*(1+norm theta)^degree)^2 := by
                  ring
                _ <= Kc*(Cb*(Ideal.absNorm (Finset.univ.prod fun b=>G.ideal b):Real)^rho*
                    Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+200*eta+pi-O0/2))*(C0*(1+norm theta)^degree)^2 := by
                  exact mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hb hKc.le) (sq_nonneg _)
                _ = (Kc*Cb*C0^2)*(1+norm theta)^(degree*2)*
                    (Ideal.absNorm (Finset.univ.prod fun b=>G.ideal b):Real)^rho*
                    Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+200*eta+pi-O0/2) := by
                  rw [mul_pow,<-pow_mul]
                  ring
                _ <= _ := by gcongr;linarith

theorem original_low_sector_retained_energy_general
    (epsilon : Real) (hepsilon : 0<epsilon)
    (lo hi : Real) (hlo : 0<lo) (W : Real->Complex)
    (hWs : Set.Subset (Function.support W) (Set.Icc lo hi))
    (hW : ContDiff Real ((Top.top : ENat) : WithTop ENat) W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c0 mode))
    (hc0 : Not (c0=0)) (hNlevel : Dvd.dvd ((9:Eis)*c0) Nlevel)
    (hbase : if mode then Dvd.dvd (ConcretePrimeRowBridge.goodLambda^2) (a-1)
      else Dvd.dvd (ConcretePrimeRowBridge.goodLambda^2) (c0-1))
    (hac : IsCoprime a c0) (rho : Real) (hrho : 0<rho)
    (eta : Real) (heta : 0<eta) :
    Exists (fun degree : Nat => Exists (fun C : Real => Exists (fun Z0 : Real =>
    0<C /\ 1<Z0 /\
    forall {sigma : Type v} [Fintype sigma],
    forall (J I F Q Q0 : Ideal Eis) (_hJ : Not (J=0))
      (_hI : Not (I=0)) (_hQ : Not (Q=0)),
      rowPowerfulPart J=rowPowerfulPart I ->
      rowMaskPart J Q=rowMaskPart I Q ->
    forall (A : Finset (FreeReflection.pool J Q Q0))
      (Z O0 H za Nstar Lambda d ell0 shift delta pi Ck CO CH X QK QP
        Lscale Lrow Lslot : Real),
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
        C*((retainedDyads (familyRawScale G s X QK QP) (16*Z^delta)).card:Real)^2*(1+norm theta)^degree*
          (Ideal.absNorm (Finset.univ.prod fun b=>G.ideal b):Real)^rho*
          Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+200*eta+pi-O0/2)))) := by
  have hb := original_low_sector_literal_energy_general (Nlevel:=Nlevel)
    epsilon hepsilon lo hi hlo W hWs hW s hc0 hNlevel hbase hac rho hrho eta heta
  cases hb with
  | intro degree h0 =>
    cases h0 with
    | intro C h1 =>
      cases h1 with
      | intro Z0 he =>
        have hC : 0<C := he.1
        have hZ0 : 1<Z0 := he.2.1
        refine Exists.intro degree (Exists.intro (36*C)
          (Exists.intro Z0 (And.intro (by positivity) (And.intro hZ0 ?_))))
        intro sigma _ J I F Q Q0 hJ hI hQ hpower hmask A
          Z O0 H za Nstar Lambda d ell0 shift delta pi Ck CO CH X QK QP
          Lscale Lrow Lslot hZ hCk hCO hCH hX hK hP hIn hPow hRow
          hlog hPowUpper hQwidth hLambda0 hLambda1 hd hd1 hell0 hO hza hshift
          hNs heH heza heN hdelta hdeta hrowcap hslotcap hconst hbudget
        dsimp only
        intro hscale rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar
          theta r aw hqk hqp hKr hPr hr haw
        let : Finite (Units Eis) := PrimaryIdealUnitReindex.finite_units
        let : Fintype (Units Eis) := Fintype.ofFinite _
        let G := (poolPrimeFamily J Q Q0).restrict A
        let j := fun b : A => completedLocalExponent J F b.val.val
        let Dset := retainedDyads (familyRawScale G s X QK QP) (16*Z^delta)
        let src := fun (ui : Prod (Units Eis) (Prod Nat (Prod Nat Nat))) (K : rows) =>
          literalDyadicRow G K.val (hrows K.val K.property) S j Pset
            (E.completion K) s hc0 ui.1 ui.2 W theta X r aw
        have hb (ui : Prod (Units Eis) (Prod Nat (Prod Nat Nat)))
            (hui : Membership.mem (SProd.sprod (Finset.univ : Finset (Units Eis)) Dset) ui) :=
          he.2.2 J I F Q Q0 hJ hI hQ hpower hmask A
            Z O0 H za Nstar Lambda d ell0 shift delta pi Ck CO CH X QK QP
            Lscale Lrow Lslot ui.2 hZ hCk hCO hCH hX hK hP hIn hPow hRow
            hlog hPowUpper hQwidth hLambda0 hLambda1 hd hd1 hell0 hO hza hshift
            hNs heH heza heN hdelta hdeta hrowcap hslotcap hconst hbudget hscale
            (Finset.mem_product.mp hui).2 rows Pset S hrows E hGN hGchar
            hrowcop hprod hScop hSN hSchar ui.1 theta r aw hqk hqp hKr hPr hr haw
        have hh := weighted_finite_row_energy_uniform
          (SProd.sprod (Finset.univ : Finset (Units Eis)) Dset) (Finset.univ : Finset rows)
          (fun _ => (1:Complex)) src _ hb
        have hcard : Fintype.card (Units Eis)=6 := by
          rw [<-Nat.card_eq_fintype_card]
          exact PrimaryIdealUnitReindex.card_units_eq_six
        simp only [src,one_mul,norm_one,Finset.sum_const,nsmul_eq_mul,mul_one,
          Finset.card_product,Finset.card_univ,hcard,Finset.sum_product,tsum_fintype] at hh
        simp only [tsum_fintype]
        apply hh.trans_eq
        push_cast
        ring

end PrimeFactorOscillations.GeneralLowGeometry
