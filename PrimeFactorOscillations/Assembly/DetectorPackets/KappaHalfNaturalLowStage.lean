/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Energy.NaturalLowStage
import PrimeFactorOscillations.Assembly.DetectorPackets.KappaHalfLowPhysical

/-!
# KappaHalfNaturalLowStage

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

namespace SevenEighths.KappaHalfNaturalLowStage

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

open CenteredMomentEnergyNaturalLowSourceBound CenteredMomentEnergyPositiveLowBandSource
open CenteredMomentEnergyNaturalSourceAdmission
open CenteredMomentAmplificationChildInput

theorem actual_low_from_bands
    (W:Real -> Complex)(hW:ContDiff Real ((Top.top : ENat) : WithTop ENat) W)(aslot bslot lo hi a b bPhi:Real)
    (haslot:0<aslot)(hWs:Function.support W <= Set.Icc aslot bslot)
    (hbslot:0 <= bslot)(ha:0<a)(hb:0 <= b)(hPhi:2 <= bPhi)
    (Mglobal A B Bmask Mparent Mchild Lgoal Lslot kappa eps:Real)(k:Nat)
    (hMg:0 <= Mglobal)(hA:0 <= A)(hB:0 <= B)(hBm:0 <= Bmask)
    (hMp:0 <= Mparent)(hMc:0 <= Mchild)(hL:0 <= Lgoal)(hLs:0 <= Lslot)
    (hMA:Mparent <= A)(hready:readyBudget A Bmask <= B)
    (hKappa:(1/6:Real) <= kappa)(hbeta:(51/100:Real) <= HeckeZeroSupremum.beta)
    (hKappaBeta:2*HeckeZeroSupremum.beta-1 <= kappa)(heps:0<eps)
    (hslot:Lslot <= mesh Mglobal B kappa eps)
    (hdrop:Mparent-amplification eps/2 <= Mchild)
    (degree:Nat)(S:Finset (Prod Nat Nat)):
    exists Uout:Finset (Prod Nat Nat),exists Jout:Nat,
    forall eta0:Character,forall Q:Ideal O,Q <= M -> Not (internalQ Q eta0 = 0) -> Not (internalQ Q eta0 = Top.top) -> 
      internalQ Q eta0 <= Ideal.span {(72:O)} -> 
    exists C:Real,0<C  /\  Filter.Eventually (fun Z : Real =>1<Z  /\ 
    forall epschild C0 C1:Real,epschild <= stageLoss Mglobal B eps k -> 0 <= C0 -> 0 <= C1 -> 
      ZeroAt (internalQ Q eta0) (a/max 1 b) b bPhi Bmask (2*max Lgoal Mparent+reserve Mglobal B eps/4)
        Mchild epschild Z degree S C0 -> 
      @PositiveAt alpha M inferInstance H hH W bslot (a/max 1 b) b bPhi Bmask (2*max Lgoal Mparent+reserve Mglobal B eps/4)
        Lslot lo hi Mchild epschild kappa Z eta0 Q degree S C1 -> 
      @PositiveLowAt alpha M inferInstance H hH W bslot a b bPhi Bmask Lgoal Lslot lo hi Mparent
        (physicalLoss Mglobal B eps k) kappa Z eta0 Q Jout Uout (C*(C0+C1+1))  /\ 
      ZeroLowAt (internalQ Q eta0) a b bPhi Bmask Lgoal Mparent
        (physicalLoss Mglobal B eps k) Z Jout Uout (C*(C0+C1+1))) atTop := by
  classical
  let r:=reserve Mglobal B eps
  have hKappa0:0 <= kappa:=by linarith
  have hr:0<r:=(bounds Mglobal B kappa eps hMg hB hKappa0 heps).2.2.2.1
  have hmarg:=margins Mglobal B kappa eps hMg hB hKappa0 heps k
  have hKappaSmall:(1/6:Real) <= kappa:=by linarith
  have hbPhi:0<bPhi:=by linarith
  choose Psi hPsis hPsin Cfixed hCfixed hentry using
    @CenteredMomentEnergyPositiveLowSourceControlled.actual_low_stages_from_physical
      alpha inferInstance inferInstance M inferInstance H hH W hW.continuous aslot bslot lo hi a b bPhi Mparent (r/4) (r/4)
      (2*amplification eps+1) haslot hWs hbslot ha hb hbPhi hMp (by positivity) (by positivity)
  choose U J hphysical using
    @KappaHalfLowPhysical.actual_natural_low_physical
      alpha inferInstance inferInstance M inferInstance H hH
      W hW aslot bslot lo hi a b bPhi haslot hWs hbslot ha hb
      Mglobal A B Bmask Mparent Mchild Lgoal Lslot Mchild kappa eps k
      hMg hA hB hBm hMp hMc hL hLs hMA hready hKappa hbeta hKappaBeta heps hslot hdrop Psi degree S
  let Umerge := Union.union S U
  let Jmerge:=degree+J
  have hS:S <= Umerge:=Finset.subset_union_left
  have hU:U <= Umerge:=Finset.subset_union_right
  have hdeg:degree <= Jmerge:=Nat.le_add_right _ _
  have hJ:J <= Jmerge:=Nat.le_add_left _ _
  have halower:a/max 1 b<=a := div_le_self ha.le (le_max_left _ _)
  have hlen:Lgoal <= 2*max Lgoal Mparent+r/4:=by
    have hh:=le_max_left Lgoal Mparent
    linarith
  refine Exists.intro (insert (0,0) Umerge) (Exists.intro Jmerge ?_)
  intro eta0 Q hQM hQ0 hQt hQ72
  choose Cp hCp hphys using hphysical eta0 Q hQM hQ0 hQt hQ72
  let Cout:=Cfixed*(Cp+1)+1
  have hCout:0<Cout:=by dsimp [Cout];positivity
  refine Exists.intro Cout (And.intro hCout ?_)
  filter_upwards [hentry,hphys] with Z he hp
  refine And.intro hp.1 ?_
  intro epschild C0 C1 hell hC0 hC1 hzero hpos
  have hzsmall:=zeroAt_transport (internalQ Q eta0)
    (a/max 1 b) b bPhi Bmask _ Mchild epschild Z
    (a/max 1 b) b 2 0 _ Mchild epschild degree degree S S C0 C0 hp.1.le
    le_rfl le_rfl hPhi hBm le_rfl le_rfl le_rfl le_rfl (Finset.Subset.refl _) hC0 le_rfl hzero
  have hpsmall:=@positiveAt_transport alpha M inferInstance H hH W bslot
    (a/max 1 b) b bPhi Bmask _ Lslot lo hi Mchild epschild kappa Z
    (a/max 1 b) b 2 0 _ Mchild epschild eta0 Q degree degree S S C1 C1 hp.1.le
    le_rfl le_rfl hPhi hBm le_rfl le_rfl le_rfl le_rfl (Finset.Subset.refl _) hC1 le_rfl hpos
  have hold:=@positiveAt_transport alpha M inferInstance H hH W bslot
    (a/max 1 b) b bPhi Bmask _ Lslot lo hi Mchild epschild kappa Z
    a b bPhi Bmask Lgoal Mchild (physicalLoss Mglobal B eps k) eta0 Q
    degree Jmerge S Umerge C1 C1 hp.1.le halower le_rfl le_rfl le_rfl hlen le_rfl
    (hell.trans hmarg.2.1) hdeg hS hC1 le_rfl hpos
  have hm:=hp.2 epschild C0 C1 hell hC0 hC1 hzsmall hpsmall
  have hm':@PhysicalLowAt alpha M inferInstance H hH W hW.continuous aslot bslot lo hi haslot hWs
      a b bPhi Bmask Lgoal Lslot Mchild Mparent kappa (r/4) (physicalLoss Mglobal B eps k)
      Z ha Psi eta0 Q Umerge Jmerge (Cp*(C0+C1+1)):=by
    intro T theta w sigma freq t height hw hwL hSigmaLo hSigmaHi hheight hfreq state hQ hrho hs
      p X1 X2 hX1 hX2 hc1 hc2 hcap hlow
    have hh:=hm T theta w sigma freq t height hw hwL hSigmaLo hSigmaHi hheight hfreq state hQ hrho hs
      p X1 X2 hX1 hX2 hc1 hc2 hcap hlow
    have hz:0 <= Z:=zero_le_one.trans hp.1.le
    have hcontrol:=profile_control_mono p hU
    have hc0:=p.control_nonneg U
    have hheight1:1 <= 1+abs t+height:=by linarith [abs_nonneg t]
    apply hh.trans
    gcongr
  have hsave:-(2*amplification eps+1) <= physicalLoss Mglobal B eps k:=by
    have hs:0<amplification eps:=(bounds Mglobal B kappa eps hMg hB hKappa0 heps).1
    linarith [hmarg.1]
  have hout:=he.2 Bmask Lgoal Lslot Mchild kappa (physicalLoss Mglobal B eps k) eta0 Q Umerge Jmerge
    (Cp*(C0+C1+1)) C1 hKappaSmall (by positivity) hC1 hmarg.2.2.1 hsave hold hm'
  have hC:Cfixed*(Cp*(C0+C1+1)+1)+C1 <= Cout*(C0+C1+1):=by
    dsimp [Cout]
    nlinarith [mul_nonneg hCfixed.le hC0,mul_nonneg hCfixed.le hC1]
  apply And.intro
  next =>
    exact @CenteredMomentEnergyStageMonotonicity.positiveLowAt_transport alpha M inferInstance H hH W bslot
      a b bPhi Bmask Lgoal Lslot lo hi Mparent (physicalLoss Mglobal B eps k) kappa Z
      a b bPhi Bmask Lgoal Mparent (physicalLoss Mglobal B eps k) eta0 Q Jmerge Jmerge
      (insert (0,0) Umerge) (insert (0,0) Umerge) _ _ hp.1.le
      le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl (Finset.Subset.refl _)
      (by positivity) hC hout.1
  next =>
    exact CenteredMomentEnergyStageMonotonicity.zeroLowAt_transport (internalQ Q eta0)
      a b bPhi Bmask Lgoal Mparent (physicalLoss Mglobal B eps k) Z
      a b bPhi Bmask Lgoal Mparent (physicalLoss Mglobal B eps k) Jmerge Jmerge
      (insert (0,0) Umerge) (insert (0,0) Umerge) _ _ hp.1.le
      le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl (Finset.Subset.refl _)
      (by positivity) hC hout.2

end SevenEighths.KappaHalfNaturalLowStage

end

end OAI

