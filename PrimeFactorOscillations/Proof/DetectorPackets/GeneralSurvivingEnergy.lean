/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/


import PrimeFactorOscillations.Proof.DetectorPackets.GeneralReflectedGeometry

/-!
# General surviving low-energy estimates

Exact component of the checked general low-energy statements and proofs.
All hypotheses and their original namespace are retained.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100

noncomputable section
namespace PrimeFactorOscillations.GeneralLowGeometry
open OAI.SevenEighths.InverseTerminalWidths
open OAI.SevenEighths.ProbeLowReflected

open OAI OAI.SevenEighths
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
open InverseMoment InverseReflectedPhase
local notation "Eis" => ActualEisensteinCubic.O
variable {a c0 : Eis} {mode : Bool}

theorem original_surviving_low_exponent_general
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c0 mode))
    (hc0 : Not (c0=0)) (kK kP eta : Real)
    (hkK : 0<kK) (hkP : 0<kP) (heta : 0<eta) :
    Exists (fun Z0 : Real => 1<Z0 /\
    forall (J I F Q Q0 : Ideal Eis) (_hJ : Not (J=0))
      (_hI : Not (I=0)) (_hQ : Not (Q=0)),
      rowPowerfulPart J=rowPowerfulPart I ->
      rowMaskPart J Q=rowMaskPart I Q ->
    forall (A : Finset (FreeReflection.pool J Q Q0)) (e : A->Fin 3)
      (column : Ideal Eis->Ideal Eis->Complex)
      (Z O0 H za Nstar Lambda d ell0 shift delta pi Ck CO CH X QK QP
        epsilon Lscale Lrow Lslot : Real) (i : Prod Nat (Prod Nat Nat)),
      Z0<=Z -> 0<Ck -> 0<CO -> 0<CH -> 0<X -> 0<QK -> 0<QP ->
      (Ideal.absNorm I:Real)<=Ck*Z^(1-Lambda-2*d) ->
      Z^O0/CO<=(Ideal.absNorm (rowPowerfulPart I):Real) ->
      Z^H/CH<=(Ideal.absNorm (rowResidualPart I Q):Real) ->
      Real.log (CH*Ck*CO)/Real.log Z<=eta ->
      normWidth Z (rowPowerfulPart I)<=O0+eta -> normWidth Z Q<=eta ->
      0<=Lambda -> Lambda<=1/5 -> 0<=d -> d<=Lambda ->
      ell0<=Lambda-d+eta -> 0<=O0 -> za<=ell0+eta -> abs shift<=eta ->
      Nstar=1+ell0+shift -> H=Real.logb Z (kK*QK) ->
      za=Real.logb Z (kP*QP) -> Nstar=Real.logb Z X ->
      0<=delta -> delta<=eta -> 0<=epsilon ->
      kK*QK<=Z^Lrow -> kP*QP<=Z^Lslot ->
      Real.logb Z 16<=eta ->
      epsilon*(Lrow+Lslot+2*(delta+Lscale+eta))+eta/2<=pi ->
      let G := (poolPrimeFamily J Q Q0).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      Inv.inv (familyRawScale G s X QK QP)<=Z^Lscale ->
      Membership.mem (retainedDyads (familyRawScale G s X QK QP) (16*Z^delta)) i ->
      Membership.mem (survivingFrozenBranches G j column
        (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)) e ->
      let v := Real.logb Z (((2:Real)^i.2.2)/
        Ideal.absNorm (frozenExtracted G j e 1))
      let ell := Real.logb Z (((2:Real)^i.2.1)/
        Ideal.absNorm (frozenExtracted G j e 2))
      OAI.SevenEighths.InverseTerminalWidths.reflectedExponent 0 H (normWidth Z (frozenExtracted G j e 0))
        (normWidth Z (frozenExtracted G j e 2)) za v ell (ramifiedWidth Z i.1)
        (terminalDualWidth Z H za Nstar G.ideal j e)+
        epsilon*(H+v+ell+za)+eta/2+O0/2<=
        (1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+200*eta+pi) := by
  have hbase := actual_surviving_retained_gates s hc0 kK kP eta hkK hkP heta
  let Z0 : Real := Classical.choose hbase
  have hZ0 : 1<Z0 := (Classical.choose_spec hbase).1
  refine Exists.intro Z0 (And.intro hZ0 ?_)
  intro J I F Q Q0 hJ hI hQ hpower hmask A e column
    Z O0 H za Nstar Lambda d ell0 shift delta pi Ck CO CH X QK QP
    epsilon Lscale Lrow Lslot i hZ hCk hCO hCH hX hK hP hIn hPow hRow
    hlog hPowUpper hQwidth hLambda0 hLambda1 hd hd1 hell0 hO hza hshift
    hNs heH heza heN hdelta hdeta hepsilon hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscale hret hsurv
  let G := (poolPrimeFamily J Q Q0).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  have hz : 1<Z := lt_of_lt_of_le hZ0 hZ
  have hpair := (poolPrimeFamily J Q Q0).restrict_pairwise
    (poolPrimeFamily_pairwise J Q Q0) A
  have hg := (Classical.choose_spec hbase).2
    G hpair j column e Z X QK QP delta i hZ hX hK hP hret hsurv
  have hv := hg.1
  have hell := hg.2.1
  have hel := hg.2.2.1
  have hwidth := hg.2.2.2
  rw [<-heH,<-heza,<-heN] at hwidth
  have hH := physical_residual_width I Q hI Z (1-Lambda-2*d) O0 H Ck CO CH
    hz hCk hCO hCH hIn hPow hRow
  have hA := original_optional_powerful_width J I Q Q0 hJ hI hQ hpower hmask A Z hz
  have hN0 := normWidth_nonneg Z hz _ (frozenExtracted_ne_zero G j e 1)
  have hS0 := normWidth_nonneg Z hz _ (frozenExtracted_ne_zero G j e 0)
  have hB0 := normWidth_nonneg Z hz _ (frozenExtracted_ne_zero G j e 2)
  have hNA := frozenExtracted_width_le G j e 1 Z hz
  have ht := compensated_reflected_exponent_general
    Lambda d ell0 O0 H (normWidth Z (Finset.univ.prod fun b=>G.ideal b))
    (normWidth Z (frozenExtracted G j e 1))
    (normWidth Z (frozenExtracted G j e 0))
    (normWidth Z (frozenExtracted G j e 2)) za
    (Real.logb Z (((2:Real)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1)))
    (Real.logb Z (((2:Real)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2)))
    (ramifiedWidth Z i.1) shift (5*eta)
    hd (by positivity) (by linarith) (by linarith) (by linarith)
    hN0 hNA hS0 hB0 (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith)
    (hshift.trans (by linarith)) ?_
  . have hb := retained_extracted_log_budget
      (familyRawScale G s X QK QP) Z delta Lscale Lrow Lslot eta
      (kK*QK) (kP*QP) (familyRawScale_pos G s hc0 X QK QP hX hK hP) hz
      (mul_pos hkK hK) (mul_pos hkP hP) hscale hconst hrowcap hslotcap i hret
      (frozenExtracted G j e 1) (frozenExtracted G j e 2)
      (frozenExtracted_ne_zero G j e 1) (frozenExtracted_ne_zero G j e 2)
    rw [<-heH,<-heza] at hb
    have hb' := mul_le_mul_of_nonneg_left hb hepsilon
    have hTd : terminalDualWidth Z H za Nstar G.ideal j e=
        2*H+2*normWidth Z (Finset.univ.prod fun b=>G.ideal b)+2*za-1-ell0-shift-
          normWidth Z (frozenExtracted G j e 1)-
          3*normWidth Z (frozenExtracted G j e 2) := by
      unfold terminalDualWidth
      rw [hNs,<-frozenExtracted_eq_ideal,<-frozenExtracted_eq_ideal]
      ring
    change OAI.SevenEighths.InverseTerminalWidths.reflectedExponent 0 H (normWidth Z (frozenExtracted G j e 0))
      (normWidth Z (frozenExtracted G j e 2)) za _ _ _ _+_+_+_<=_
    rw [hTd]
    unfold OAI.SevenEighths.InverseTerminalWidths.reflectedExponent at ht
    unfold OAI.SevenEighths.InverseTerminalWidths.reflectedExponent
    linarith
  . dsimp only [terminalDualWidth] at hwidth
    rw [hNs,<-frozenExtracted_eq_ideal,<-frozenExtracted_eq_ideal] at hwidth
    linarith


theorem original_surviving_low_energy_sum_general
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c0 mode))
    (hc0 : Not (c0=0)) (rho : Real) (hrho : 0<rho) (kK kP eta : Real)
    (hkK : 0<kK) (hkP : 0<kP) (heta : 0<eta) :
    Exists (fun Z0 : Real => Exists (fun C : Real => 1<Z0 /\ 0<C /\
    forall (J I F Q Q0 : Ideal Eis) (_hJ : Not (J=0))
      (_hI : Not (I=0)) (_hQ : Not (Q=0)),
      rowPowerfulPart J=rowPowerfulPart I ->
      rowMaskPart J Q=rowMaskPart I Q ->
    forall (A : Finset (FreeReflection.pool J Q Q0))
      (column : Ideal Eis->Ideal Eis->Complex)
      (Z O0 H za Nstar Lambda d ell0 shift delta pi Ck CO CH X QK QP
        epsilon Lscale Lrow Lslot : Real) (i : Prod Nat (Prod Nat Nat)),
      Z0<=Z -> 0<Ck -> 0<CO -> 0<CH -> 0<X -> 0<QK -> 0<QP ->
      (Ideal.absNorm I:Real)<=Ck*Z^(1-Lambda-2*d) ->
      Z^O0/CO<=(Ideal.absNorm (rowPowerfulPart I):Real) ->
      Z^H/CH<=(Ideal.absNorm (rowResidualPart I Q):Real) ->
      Real.log (CH*Ck*CO)/Real.log Z<=eta ->
      normWidth Z (rowPowerfulPart I)<=O0+eta -> normWidth Z Q<=eta ->
      0<=Lambda -> Lambda<=1/5 -> 0<=d -> d<=Lambda ->
      ell0<=Lambda-d+eta -> 0<=O0 -> za<=ell0+eta -> abs shift<=eta ->
      Nstar=1+ell0+shift -> H=Real.logb Z (kK*QK) ->
      za=Real.logb Z (kP*QP) -> Nstar=Real.logb Z X ->
      0<=delta -> delta<=eta -> 0<=epsilon ->
      kK*QK<=Z^Lrow -> kP*QP<=Z^Lslot ->
      Real.logb Z 16<=eta ->
      epsilon*(Lrow+Lslot+2*(delta+Lscale+eta))+eta/2<=pi ->
      let G := (poolPrimeFamily J Q Q0).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      Inv.inv (familyRawScale G s X QK QP)<=Z^Lscale ->
      Membership.mem (retainedDyads (familyRawScale G s X QK QP) (16*Z^delta)) i ->
      let branches := survivingFrozenBranches G j column
        (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
      ((branches.card:Real)*Finset.sum branches (fun e=>
        Z^(OAI.SevenEighths.InverseTerminalWidths.reflectedExponent 0 H
          (normWidth Z (frozenExtracted G j e 0))
          (normWidth Z (frozenExtracted G j e 2)) za
          (Real.logb Z (((2:Real)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1)))
          (Real.logb Z (((2:Real)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2)))
          (ramifiedWidth Z i.1) (terminalDualWidth Z H za Nstar G.ideal j e)+
          epsilon*(H+
            Real.logb Z (((2:Real)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1))+
            Real.logb Z (((2:Real)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2))+za)+eta/2)))<=
        C*(Ideal.absNorm (Finset.univ.prod fun b=>G.ideal b):Real)^rho*
          Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+200*eta+pi-O0/2))) := by
  have hbase := original_surviving_low_exponent_general s hc0 kK kP eta hkK hkP heta
  let Z0 : Real := Classical.choose hbase
  have hZ0 : 1<Z0 := (Classical.choose_spec hbase).1
  have hh := surviving_branch_count_small_power rho hrho
  let C : Real := Classical.choose hh
  have hC : 0<C := (Classical.choose_spec hh).1
  refine Exists.intro Z0 (Exists.intro C (And.intro hZ0 (And.intro hC ?_)))
  intro J I F Q Q0 hJ hI hQ hpower hmask A column
    Z O0 H za Nstar Lambda d ell0 shift delta pi Ck CO CH X QK QP
    epsilon Lscale Lrow Lslot i hZ hCk hCO hCH hX hK hP hIn hPow hRow
    hlog hPowUpper hQwidth hLambda0 hLambda1 hd hd1 hell0 hO hza hshift
    hNs heH heza heN hdelta hdeta hepsilon hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscale hret
  let G := (poolPrimeFamily J Q Q0).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  let branches := survivingFrozenBranches G j column
    (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
  have hpair := (poolPrimeFamily J Q Q0).restrict_pairwise
    (poolPrimeFamily_pairwise J Q Q0) A
  have hcbr := (Classical.choose_spec hh).2 G hpair j column
    (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
  have hz : 1<Z := lt_of_lt_of_le hZ0 hZ
  have hb (e : A->Fin 3) (he : Membership.mem branches e) :=
    (Classical.choose_spec hbase).2 J I F Q Q0 hJ hI hQ hpower hmask A e column
      Z O0 H za Nstar Lambda d ell0 shift delta pi Ck CO CH X QK QP
      epsilon Lscale Lrow Lslot i hZ hCk hCO hCH hX hK hP hIn hPow hRow
      hlog hPowUpper hQwidth hLambda0 hLambda1 hd hd1 hell0 hO hza hshift
      hNs heH heza heN hdelta hdeta hepsilon hrowcap hslotcap hconst hbudget
      hscale hret he
  calc
    _ <= (branches.card:Real)*Finset.sum branches (fun _e=>
        Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+200*eta+pi-O0/2)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro e he
      apply Real.rpow_le_rpow_of_exponent_le hz.le
      have ht := hb e he
      dsimp only at ht
      linarith
    _ = ((branches.card:Real)^2)*Z^((1-Lambda-2*d)+max 0 ((5*Lambda+d-1)/4)+200*eta+pi-O0/2) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      ring
    _ <= _ := mul_le_mul_of_nonneg_right hcbr (Real.rpow_nonneg (by positivity) _)

end PrimeFactorOscillations.GeneralLowGeometry
