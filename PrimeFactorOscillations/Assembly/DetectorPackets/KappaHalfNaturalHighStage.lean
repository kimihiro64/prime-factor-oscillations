/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Energy.NaturalHighStage
import PrimeFactorOscillations.Assembly.DetectorPackets.KappaHalfHighPhysical
import PrimeFactorOscillations.Assembly.DetectorPackets.KappaHalfHighStage

/-!
# KappaHalfNaturalHighStage

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

namespace SevenEighths.KappaHalfNaturalHighStage

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

theorem actual_high_stage
    (W:Real -> Complex)(hW:ContDiff Real ((Top.top : ENat) : WithTop ENat) W)(aslot bslot lo hi a b bPhi:Real)
    (haslot:0<aslot)(hWs:Function.support W <= Set.Icc aslot bslot)
    (hbslot:0 <= bslot)(ha:0<a)(hlo:a <= 1/4)(hhi:1 <= b)(hbPhi:0<bPhi)
    (Mglobal A B Bmask Mparent Mchild Lgoal Lslot rho kappa eps:Real)(k:Nat)
    (hrho:0<rho)(hMg:0 <= Mglobal)(hA:0 <= A)(hB:0 <= B)(hBm:0 <= Bmask)
    (hMp:0 <= Mparent)(hMc:0 <= Mchild)(hL:0 <= Lgoal)(hLs:0 <= Lslot)
    (hMA:Mparent <= A)(hready:readyBudget A Bmask <= B)
    (hKappa:(1/2:Real)<kappa)(hbeta:(51/100:Real) <= HeckeZeroSupremum.beta)
    (hKappaBeta:2*HeckeZeroSupremum.beta-1 <= kappa)(heps:0<eps)
    (hslot:Lslot <= mesh Mglobal B kappa eps)
    (hdrop:Mparent-amplification eps/2 <= Mchild)
    (degree:Nat)(S:Finset (Prod Nat Nat))(lowDegree:Nat)(Slow:Finset (Prod Nat Nat)):
    exists U:Finset (Prod Nat Nat),exists J:Nat,
    forall eta0:Character,forall Q:Ideal O,Q <= M -> Not (internalQ Q eta0 = 0) -> Not (internalQ Q eta0 = Top.top) -> 
      internalQ Q eta0 <= Ideal.span {(72:O)} -> 
    exists C:Real,0<C  /\  Filter.Eventually (fun Z : Real =>1<Z  /\ 
    forall epschild C0 C1 Clow:Real,epschild <= stageLoss Mglobal B eps k -> 0 <= C0 -> 0 <= C1 -> 0 <= Clow -> 
      ZeroAt (internalQ Q eta0) (a/max 1 b) b 2 0 (max Lgoal Mparent)
        Mchild epschild Z degree S C0 -> 
      @PositiveAt alpha M inferInstance H hH W bslot (a/max 1 b) b 2 0 (max Lgoal Mparent)
        Lslot lo hi Mchild epschild kappa Z eta0 Q degree S C1 -> 
      @CenteredMomentEnergyReferenceLowBands.PositiveLowAt alpha M inferInstance H hH W bslot a b bPhi Bmask
        (Mparent+Bmask+rho/100) Lslot lo hi Mparent (physicalLoss Mglobal B eps k) kappa Z eta0 Q
        lowDegree Slow Clow -> 
      @PositiveHighAt alpha M inferInstance H hH W bslot a b bPhi Bmask Lgoal Lslot lo hi rho Mparent
        (reflectedLoss Mglobal B eps k) kappa Z eta0 Q J U (C*(C0+C1+Clow+1))) atTop := by
  classical
  let r:=reserve Mglobal B eps
  have hKappa0:0 <= kappa:=by linarith
  have hb:0 <= b:=zero_le_one.trans hhi
  have hr:0<r:=(bounds Mglobal B kappa eps hMg hB hKappa0 heps).2.2.2.1
  have hr4:0<r/4:=by positivity
  have hs:0<amplification eps:=(bounds Mglobal B kappa eps hMg hB hKappa0 heps).1
  choose Psi hPsis hPsin hstage using
    @KappaHalfHighStage.actual_high_stage_from_physical
      alpha inferInstance inferInstance M inferInstance H hH
      W hW.continuous aslot bslot lo hi a b bPhi rho r Mparent Bmask (r/4) (r/4)
      (2*amplification eps+1) kappa
      haslot hWs hbslot ha hlo hhi hbPhi hrho hr hMp hBm hr4 hr4 hKappa
  choose Up Jp hphysical using
    @KappaHalfHighPhysical.actual_positive_high_physical
      alpha inferInstance inferInstance M inferInstance H hH
      W hW aslot bslot lo hi a b bPhi haslot hWs hbslot ha hb
      Mglobal A B Bmask Mparent Mchild Lgoal Lslot rho kappa eps k
      hMg hA hB hBm hMp hMc hL hLs hMA hready (by linarith)
      hbeta hKappaBeta heps hslot hdrop Psi degree S
  choose J U Cf hCf hstageZ using hstage lowDegree Slow Jp Up
  refine Exists.intro U (Exists.intro J ?_)
  intro eta0 Q hQM hQ0 hQt hQ72
  choose Cp hCp hphysZ using hphysical eta0 Q hQM hQ0 hQt hQ72
  refine Exists.intro (Cf*(Cp+1)) (And.intro (by positivity) ?_)
  filter_upwards [hstageZ,hphysZ] with Z hstageNow hphysicalNow
  refine And.intro hphysicalNow.1 ?_
  intro epschild C0 C1 Clow hchild hC0 hC1 hClow hzero hpos hlow
  have hp:=hphysicalNow.2 epschild C0 C1 hchild hC0 hC1 hzero hpos
  have hm:=margins Mglobal B kappa eps hMg hB hKappa0 heps k
  have hmass:0 <= Cp*(C0+C1+1):=by positivity
  have hh:=hstageNow.2 Lgoal Lslot kappa (physicalLoss Mglobal B eps k)
    (physicalLoss Mglobal B eps k) (reflectedLoss Mglobal B eps k) eta0 Q
    Clow (Cp*(C0+C1+1)) le_rfl hm.1.le hClow hmass
    (by exact le_rfl) hm.2.2.2.1 (hm.2.2.1.trans hm.2.2.2.1)
    (by have hpos:=hm.1.le.trans hm.2.2.2.1;linarith only [hpos,hs]) hlow hp
  have hconst:Cf*(Clow+Cp*(C0+C1+1)+1) <= (Cf*(Cp+1))*(C0+C1+Clow+1):=by
    have hh:0 <= Cp*Clow:=mul_nonneg hCp.le hClow
    nlinarith only [mul_nonneg hCf.le hh,mul_nonneg hCf.le hC0,mul_nonneg hCf.le hC1]
  intro T theta w sigma freq t height hw hwL hSigmaLo hSigmaHi hheight hfreq state hQ hslo hsupper
    p X1 X2 hX1 hX2 hXcap1 hXcap2 hcapacity hlarge
  apply (hh T theta w sigma freq t height hw hwL hSigmaLo hSigmaHi hheight hfreq state hQ hslo hsupper
    p X1 X2 hX1 hX2 hXcap1 hXcap2 hcapacity hlarge).trans
  have hd:=diagonalControl_nonneg state.radial.profile
  have hp0:=p.control_nonneg U
  have hz:0 <= Z:=zero_le_one.trans hphysicalNow.1.le
  gcongr

end SevenEighths.KappaHalfNaturalHighStage

end

end OAI

