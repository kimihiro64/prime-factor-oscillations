/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Energy.NaturalZeroStage
import PrimeFactorOscillations.Assembly.DetectorPackets.KappaHalfZeroGrowthPhysical

/-!
# KappaHalfNaturalZeroStage

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

Full high-source case split for the bounded kappa-half reflection chain.
All principal, diagonal, tail, conductor and profile terms are retained.
The actual PositiveLowAt input remains explicit.
-/

set_option maxHeartbeats 800000

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.KappaHalfNaturalZeroStage

open HeckeFamily HeckeDyadic ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyOriginalSource CenteredMomentEnergyPositiveHighSource
open CenteredMomentEnergyFixedRadialReduction CenteredMomentEnergyPhysicalEntry
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot

local notation "O" => HeckeFamily.O

variable {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
local instance : DecidableEq (Sum alpha (Fin 2)) := Classical.decEq _
variable (M : Ideal O) [NeZero M]
local instance : Finite (HasQuotient.Quotient O M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (Units (HasQuotient.Quotient O M)))
  (hH : RayOrthogonality.globalUnits M <= H)

open CenteredMomentEnergyPositiveHighParameters
open CenteredMomentEnergyBandMonotonicity CenteredMomentEnergyNaturalInputMatches

open CenteredMomentEnergyPositiveHighSourceBound
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyStageMargins CenteredMomentEnergyFirstSourceParameters
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyPositiveBalancedAdmission

open CenteredMomentEnergyStageMonotonicity

theorem actual_zero_stage
    (W:Real -> Complex)(aslot bslot Lslot lo hi kappa a b bPhi Bmask Lgoal Mparent Mchild
      Mschedule Bschedule eps rho:Real)(k:Nat)
    (haslot:0<aslot)(hWs:Function.support W <= Set.Icc aslot bslot)
    (hW:ContDiff Real ((Top.top : ENat) : WithTop ENat) W)(hLs:0 <= Lslot)(hKappa:(1/6:Real) <= kappa)
    (hbeta:(51/100:Real) <= HeckeZeroSupremum.beta)(hKappaBeta:2*HeckeZeroSupremum.beta-1 <= kappa)
    (ha:0<a)(hlo:a <= 1/4)(hhi:1 <= b)(hbPhi:2 <= bPhi)(hBmask:0 <= Bmask)(_hLgoal:0 <= Lgoal)
    (hMparent:0 <= Mparent)(hMchild:0 <= Mchild)(hMschedule:0 <= Mschedule)(hBschedule:0 <= Bschedule)
    (heps:0<eps)(hrho:0<rho)(hrhoChild:rho <= Mchild)
    (hdrop:Mparent-amplification eps/2 <= Mchild):
    exists d Lgrow Llow:Real,0<d  /\  d <= 1  /\  0<Lgrow  /\  Lgoal <= Lgrow  /\ 
      Lgrow=max Lgoal (Mparent+Bmask+2*d)+1  /\ 
      Llow=max Lgrow (Mparent+Bmask+rho/100)  /\ 
      Llow <= max Lgoal (Mparent+Bmask+rho/100+2)+1  /\ 
    forall Lchild:Real,0 <= Lchild -> max Mparent (2*Lgrow) <= Lchild -> 
      readyBudget (max Mparent (2*Lgrow)) Bmask <= Bschedule -> 
    forall degree degreeLow:Nat,forall S Slow:Finset (Prod Nat Nat),exists J:Nat,exists U:Finset (Prod Nat Nat),
    forall eta0:Character,forall Q:Ideal O,Q <= M -> Not (internalQ Q eta0 = 0) -> Not (internalQ Q eta0 = Top.top) -> 
      internalQ Q eta0 <= Ideal.span {(72:O)} -> 
    exists C:Real,0<C  /\  Filter.Eventually (fun Z : Real =>1<Z  /\ 
    forall epschild C0 C1 Clow:Real,epschild <= stageLoss Mschedule Bschedule eps k -> 
      0 <= C0 -> 0 <= C1 -> 0 <= Clow -> 
      ZeroAt (internalQ Q eta0) (a/max 1 b) b bPhi Bmask Lchild Mchild epschild Z degree S C0 -> 
      @PositiveAt alpha M inferInstance H hH W bslot (a/max 1 b) b bPhi Bmask Lchild Lslot lo hi
        Mchild epschild kappa Z eta0 Q degree S C1 -> 
      ZeroLowAt (internalQ Q eta0) a b bPhi Bmask Llow Mparent
        (physicalLoss Mschedule Bschedule eps k) Z degreeLow Slow Clow -> 
      ZeroAt (internalQ Q eta0) a b bPhi Bmask Lgoal Mparent
        (stageLoss Mschedule Bschedule eps (k+1)) Z J U (C*(Clow+C0+C1+1))) atTop := by
  classical
  let r:=reserve Mschedule Bschedule eps
  have hKappa0:0 <= kappa:=by linarith
  have hr:0<r:=(bounds Mschedule Bschedule kappa eps hMschedule hBschedule hKappa0 heps).2.2.2.1
  have hb:0 <= b:=by linarith
  have hrad:0<bPhi:=by linarith
  choose d Lgrow hd hd1 hLg hgoal hLexact hLupper hsharp using
    CenteredMomentEnergyZeroGrowthContourBounded.zero_from_growth_additional_loss_bounded
      a b bPhi r Mparent Bmask Lgoal ha hlo hhi hrad hr hMparent hBmask
  let Llow:=max Lgrow (Mparent+Bmask+rho/100)
  have hupperA : Lgrow <= max Lgoal (Mparent+Bmask+rho/100+2)+1 := by
    apply hLupper.trans
    exact add_le_add (max_le_max (le_refl Lgoal)
      (show Mparent+Bmask+2 <= Mparent+Bmask+rho/100+2 by linarith only [hrho]))
      (le_refl (1:Real))
  have hupperB : Mparent+Bmask+rho/100 <= max Lgoal (Mparent+Bmask+rho/100+2)+1 := by
    have hh := le_max_right Lgoal (Mparent+Bmask+rho/100+2)
    linarith
  refine Exists.intro d (Exists.intro Lgrow (Exists.intro Llow ?_))
  refine And.intro hd (And.intro hd1 (And.intro hLg (And.intro hgoal
    (And.intro hLexact (And.intro rfl (And.intro (max_le hupperA hupperB) ?_))))))
  intro Lchild hLc hcap hready degree degreeLow S Slow
  choose Psi hsPsi hnPsi hgrowth using
    CenteredMomentEnergyZeroGrowthSourceControlled.actual_growth_from_physical
      a b bPhi rho r Mparent Bmask (2*Lgrow) Lgrow (r/4) (r/4) (2*amplification eps+1)
      ha hlo hhi hrad hrho hr hMparent hBmask (by positivity) le_rfl (by positivity) (by positivity)
  choose Smass Jmass hphysical using
    @KappaHalfZeroGrowthPhysical.actual_growth_physical
      alpha inferInstance inferInstance M inferInstance H hH
      W aslot bslot Lslot lo hi kappa a b bPhi Bmask Lgrow Lchild Mparent Mchild Mschedule Bschedule eps
      haslot hWs hW hLs hKappa hbeta hKappaBeta ha hb hBmask hLg.le hLc hMparent hMchild
      hMschedule hBschedule heps hcap hready hdrop Psi degree S
  choose Jgrowth Ugrowth Cgrowth hCg hgrowth using hgrowth (degree+degreeLow) (Union.union S Slow) Jmass Smass
  choose J U Csharp hCs hsharp using hsharp Ugrowth
  refine Exists.intro J (Exists.intro U ?_)
  intro eta0 Q hQM hQ0 hQt hQ72
  choose Cmass hCm Zmass hZm hmass using hphysical eta0 Q hQM hQ0 hQt hQ72
  let C:=Csharp*(Cgrowth*(Cmass+2)+1)
  refine Exists.intro C (And.intro (by dsimp [C]; positivity) ?_)
  filter_upwards [eventually_ge_atTop Zmass,hgrowth,hsharp] with Z hZmZ hg hs
  have hZ:1<Z:=hZm.trans_le hZmZ
  refine And.intro hZ ?_
  intro epschild C0 C1 Clow hchild hC0 hC1 hClow hz hp hl
  have hmarg:=margins Mschedule Bschedule kappa eps hMschedule hBschedule hKappa0 heps k
  have hpLoss:0 <= physicalLoss Mschedule Bschedule eps k:=hmarg.1.le
  have hrLoss:0 <= reflectedLoss Mschedule Bschedule eps k:=hpLoss.trans hmarg.2.2.2.1
  have hlength:Lgrow <= Lchild:=by linarith [le_max_right Mparent (2*Lgrow)]
  have hap:a/max 1 b <= a:=div_le_self ha.le (le_max_left _ _)
  have hzero:=zeroAt_transport (internalQ Q eta0) _ _ _ _ _ _ _ Z _ _ 2 0 _ _ _
    degree degree S S C0 C0 hZ.le le_rfl le_rfl hbPhi hBmask le_rfl le_rfl le_rfl
    le_rfl (Finset.Subset.refl _) hC0 le_rfl hz
  have hpositive:=@positiveAt_transport alpha M inferInstance H hH W bslot _ _ _ _ _ _ _ _ _ _ kappa Z
    _ _ 2 0 _ _ _ eta0 Q degree degree S S C1 C1 hZ.le
    le_rfl le_rfl hbPhi hBmask le_rfl le_rfl le_rfl le_rfl (Finset.Subset.refl _) hC1 le_rfl hp
  have hmassNow:=hmass Z hZmZ k epschild C0 C1 rho hchild hC0 hC1 hzero hpositive
  have hprevious:=zeroAt_transport (internalQ Q eta0) _ _ _ _ _ _ _ Z a b bPhi Bmask Lgrow rho
    (reflectedLoss Mschedule Bschedule eps k) degree (degree+degreeLow) S (Union.union S Slow) C0 C0
    hZ.le hap le_rfl le_rfl le_rfl hlength hrhoChild
    (hchild.trans (hmarg.2.1.trans hmarg.2.2.2.1)) (Nat.le_add_right _ _)
    Finset.subset_union_left hC0 le_rfl hz
  have hlow:=zeroLowAt_transport (internalQ Q eta0) _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
    degreeLow (degree+degreeLow) Slow (Union.union S Slow) Clow Clow hZ.le
    le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl (Nat.le_add_left _ _)
    Finset.subset_union_right hClow le_rfl hl
  have hgrowthNow:=hg.2 (physicalLoss Mschedule Bschedule eps k)
    (physicalLoss Mschedule Bschedule eps k) (reflectedLoss Mschedule Bschedule eps k)
    (internalQ Q eta0) Clow (Cmass*(C0+C1+1)) C0 hpLoss hClow (by positivity) hC0
    (by unfold reflectedLoss;exact le_rfl) hmarg.2.2.2.1
    (hmarg.2.2.1.trans hmarg.2.2.2.1)
    (by have hh:= (bounds Mschedule Bschedule kappa eps hMschedule hBschedule hKappa0 heps).1
        linarith only [hrLoss,hh]) hprevious hlow hmassNow
  have hfinal:=hs.2 (reflectedLoss Mschedule Bschedule eps k) (internalQ Q eta0) Jgrowth
    (Cgrowth*(Clow+Cmass*(C0+C1+1)+C0+1)) hrLoss (by positivity) hgrowthNow
  rw [reflected_then_zero] at hfinal
  have hfront:Csharp*(Cgrowth*(Clow+Cmass*(C0+C1+1)+C0+1)+1) <= C*(Clow+C0+C1+1):=by
    have hinner:Clow+Cmass*(C0+C1+1)+C0+1 <= (Cmass+2)*(Clow+C0+C1+1):=by
      nlinarith [mul_nonneg hCm.le hClow]
    calc
      _ <= Csharp*(Cgrowth*((Cmass+2)*(Clow+C0+C1+1))+(Clow+C0+C1+1)):=by
        gcongr
        linarith
      _=_:=by dsimp [C];ring
  exact zeroAt_transport (internalQ Q eta0) _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
    J J U U _ _ hZ.le le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl
    le_rfl (Finset.Subset.refl _) (by positivity) hfront hfinal

end SevenEighths.KappaHalfNaturalZeroStage

end

end OAI

