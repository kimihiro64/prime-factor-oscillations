/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Energy.CappedLowStage
import PrimeFactorOscillations.Assembly.DetectorPackets.KappaHalfNaturalLowStage

/-!
# KappaHalfCappedLowStage

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

namespace SevenEighths.KappaHalfCappedLowStage

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

open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthInduction
open CenteredMomentEnergyWidthRanges CenteredMomentEnergyCappedRequests
open CenteredMomentEnergySourceCapSchedule

theorem actual_capped_low
    (W:Real -> Complex)(aslot bslot a b radial Bmask L lo hi Mcap kappa eps:Real)
    (hW:ContDiff Real ((Top.top : ENat) : WithTop ENat) W)(haslot:0<aslot)
    (hWs:Function.support W <= Set.Icc aslot bslot)(hbslot:0 <= bslot)
    (ha:0<a)(hb:0 <= b)(hrad:2 <= radial)(hmask:0 <= Bmask)(hMcap:0 <= Mcap)
    (hKappa:(1/6:Real) <= kappa)(heps:0<eps)(hbeta:(51/100:Real) <= HeckeZeroSupremum.beta)
    (hKappaBeta:2*HeckeZeroSupremum.beta-1 <= kappa)(k:Nat)(hk:k<count Mcap eps)
    (hold:@CenteredMomentEnergyCappedWidthInduction.CertifiedBand alpha M inferInstance H hH
      W bslot a b radial Bmask L lo hi Mcap kappa eps k):
    exists U:Finset (Prod Nat Nat),exists J:Nat,forall eta0:Character,forall Q:Ideal O,Q <= M -> 
      Not (internalQ Q eta0 = 0) -> Not (internalQ Q eta0 = Top.top) -> internalQ Q eta0 <= Ideal.span {(72:O)} -> 
      exists C:Real,0<C  /\  Filter.Eventually (fun Z : Real =>1<Z  /\ 
        @PositiveLowAt alpha M inferInstance H hH W bslot (lowerAt a b Mcap eps (k+1)) b radial Bmask
          (requestLength Mcap Bmask (lengthAt Mcap Bmask L eps (k+1)))
          (fineMesh Mcap Bmask L kappa eps) lo hi
          (bandWidth Mcap (finalSourceCap Mcap Bmask L eps) eps (k+1))
          (physicalLoss Mcap (finalSourceCap Mcap Bmask L eps) eps k) kappa Z eta0 Q J U C  /\ 
        ZeroLowAt (internalQ Q eta0) (lowerAt a b Mcap eps (k+1)) b radial Bmask
          (requestLength Mcap Bmask (lengthAt Mcap Bmask L eps (k+1)))
          (bandWidth Mcap (finalSourceCap Mcap Bmask L eps) eps (k+1))
          (physicalLoss Mcap (finalSourceCap Mcap Bmask L eps) eps k) Z J U C) atTop := by
  classical
  let Bs:=finalSourceCap Mcap Bmask L eps
  let Ag:=2*range Mcap Bmask L (count Mcap eps)+Mcap+1
  let Mp:=bandWidth Mcap Bs eps (k+1)
  let Mc:=bandWidth Mcap Bs eps k
  let Lreq:=requestLength Mcap Bmask (lengthAt Mcap Bmask L eps (k+1))
  have hBs:0 <= Bs:=sourceCap_nonneg Mcap Bmask L hMcap hmask _
  have hRange:=range_nonneg Mcap Bmask L hMcap hmask (count Mcap eps)
  have hAg:0 <= Ag:=by dsimp [Ag];positivity
  have hMp:0 <= Mp:=bandWidth_nonneg Mcap Bs eps hMcap hBs heps (k+1)
  have hMc:0 <= Mc:=bandWidth_nonneg Mcap Bs eps hMcap hBs heps k
  have hMpCap:Mp <= Mcap:=bandWidth_le Mcap Bs eps (k+1)
  have hMpAg:Mp <= Ag:=by dsimp [Ag];linarith
  have hLnext:0 <= lengthAt Mcap Bmask L eps (k+1):=
    range_nonneg Mcap Bmask L hMcap hmask _
  have hLreq:0 <= Lreq:=(request_bounds Mcap Bmask _ hMcap hmask hLnext).1
  have hKappa0:0 <= kappa:=by linarith
  have hbounds:=bounds Mcap Bs kappa eps hMcap hBs hKappa0 heps
  have hmesh:0 <= fineMesh Mcap Bmask L kappa eps:=hbounds.2.2.2.2.1.le
  have hr:0<reserve Mcap Bs eps:=hbounds.2.2.2.1
  have hr4:reserve Mcap Bs eps/4 <= 1:=by
    have hh:reserve Mcap Bs eps <= amplification eps/100:=min_le_left _ _
    have hs:=hbounds.2.1
    linarith
  have hready:CenteredMomentEnergyFirstLiveAdmission.readyBudget Ag Bmask <= Bs:=
    readyBudget_le_schedule Mcap Bmask L eps Ag Bmask hMcap hmask le_rfl le_rfl
  have hdrop:Mp-amplification eps/2 <= Mc:=parent_drop Mcap Bs eps heps k
  have hlength:2*max Lreq Mp+reserve Mcap Bs eps/4 <= lengthAt Mcap Bmask L eps k:=
    previous_admits Mcap Bmask L eps Mp (reserve Mcap Bs eps/4) hMcap hmask hMpCap hr4 k hk
  have hsupport:=child_support a b Mcap eps k hk
  choose degree S hold using hold
  choose U J hstage using
    @KappaHalfNaturalLowStage.actual_low_from_bands
      alpha inferInstance inferInstance M inferInstance H hH W hW aslot bslot lo hi (lowerAt a b Mcap eps (k+1)) b radial
    haslot hWs hbslot (lowerAt_pos a b Mcap eps ha (k+1)) hb hrad
    Mcap Ag Bs Bmask Mp Mc Lreq (fineMesh Mcap Bmask L kappa eps) kappa eps k
    hMcap hAg hBs hmask hMp hMc hLreq hmesh hMpAg hready hKappa hbeta hKappaBeta heps
    le_rfl hdrop degree S
  refine Exists.intro U (Exists.intro J ?_)
  intro eta0 Q hQM hQ0 hQt hQ72
  choose Cz Cp hCz hCp hold using hold eta0 Q hQM hQ0 hQt hQ72
  choose Cs hCs hstage using hstage eta0 Q hQM hQ0 hQt hQ72
  refine Exists.intro (Cs*(Cz+Cp+1)) (And.intro (by positivity) ?_)
  filter_upwards [hold,hstage] with Z hold hs
  have hz:=hold.2.1
  have hp:=hold.2.2
  rw [hsupport] at hz hp
  have hz':ZeroAt (internalQ Q eta0) (lowerAt a b Mcap eps (k+1)/max 1 b) b radial Bmask
      (2*max Lreq Mp+reserve Mcap Bs eps/4) Mc (stageLoss Mcap Bs eps k) Z degree S Cz:=
    zeroAt_transport (internalQ Q eta0) _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
      degree degree S S Cz Cz hold.1.le le_rfl le_rfl le_rfl le_rfl hlength le_rfl le_rfl
      le_rfl (Finset.Subset.refl _) hCz.le le_rfl hz
  have hp':@PositiveAt alpha M inferInstance H hH W bslot (lowerAt a b Mcap eps (k+1)/max 1 b) b radial Bmask
      (2*max Lreq Mp+reserve Mcap Bs eps/4) (fineMesh Mcap Bmask L kappa eps) lo hi Mc
      (stageLoss Mcap Bs eps k) kappa Z eta0 Q degree S Cp:=
    @positiveAt_transport alpha M inferInstance H hH W bslot _ _ _ _ _ _ _ _ _ _ kappa Z
      _ _ _ _ _ _ _ eta0 Q degree degree S S Cp Cp hold.1.le
      le_rfl le_rfl le_rfl le_rfl hlength le_rfl le_rfl le_rfl (Finset.Subset.refl _)
      hCp.le le_rfl hp
  exact And.intro hs.1 (hs.2 (stageLoss Mcap Bs eps k) Cz Cp le_rfl hCz.le hCp.le hz' hp')

end SevenEighths.KappaHalfCappedLowStage

end

end OAI

