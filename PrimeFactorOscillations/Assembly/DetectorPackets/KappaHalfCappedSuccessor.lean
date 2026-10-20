/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Energy.CappedAnalyticSuccessor
import PrimeFactorOscillations.Assembly.DetectorPackets.KappaHalfCappedLowStage
import PrimeFactorOscillations.Assembly.DetectorPackets.KappaHalfNaturalHighStage
import PrimeFactorOscillations.Assembly.DetectorPackets.KappaHalfNaturalZeroStage

/-!
# KappaHalfCappedSuccessor

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

namespace SevenEighths.KappaHalfCappedSuccessor

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

open CenteredMomentEnergyStageMonotonicity
open CenteredMomentEnergyWidthInduction (remaining lowerAt lengthAt lowerAt_pos child_support child_length)

theorem actual_successor
    (W:Real -> Complex)(aslot bslot a b radial Bmask L lo hi Mcap kappa eps:Real)
    (haslot:0<aslot)(hWs:Function.support W <= Set.Icc aslot bslot)(hW:ContDiff Real ((Top.top : ENat) : WithTop ENat) W)
    (hbslot:0 <= bslot)(ha:0<a)(hlo:a <= 1/4)(hhi:1 <= b)(hrad:2 <= radial)
    (hmask:0 <= Bmask)(hMcap:0<Mcap)(hKappa:(1/2:Real)<kappa)(heps:0<eps)
    (hbeta:(51/100:Real) <= HeckeZeroSupremum.beta)(hKappaBeta:2*HeckeZeroSupremum.beta-1 <= kappa)
    (k:Nat)(hk:k<count Mcap eps)
    (hold:@CenteredMomentEnergyCappedWidthInduction.CertifiedBand alpha M inferInstance H hH W bslot a b radial Bmask L lo hi Mcap kappa eps k):
    @CenteredMomentEnergyCappedWidthInduction.CertifiedBand alpha M inferInstance H hH W bslot a b radial Bmask L lo hi Mcap kappa eps (k+1):=by
  classical
  let Bs:=finalSourceCap Mcap Bmask L eps
  let Mp:=bandWidth Mcap Bs eps (k+1)
  let Mc:=bandWidth Mcap Bs eps k
  let ac:=lowerAt a b Mcap eps (k+1)
  let Lc:=lengthAt Mcap Bmask L eps (k+1)
  let Lp:=lengthAt Mcap Bmask L eps k
  let Lreq:=requestLength Mcap Bmask Lc
  let A:=2*range Mcap Bmask L (count Mcap eps)+Mcap+1
  let r:=reserve Mcap Bs eps
  have hBs:0 <= Bs:=sourceCap_nonneg Mcap Bmask L hMcap.le hmask _
  have hKappa0:0 <= kappa:=by linarith
  have hb:0 <= b:=zero_le_one.trans hhi
  have hr:0<r:=(bounds Mcap Bs kappa eps hMcap.le hBs hKappa0 heps).2.2.2.1
  have hr1:r/4 <= 1:=by
    have hh:=bounds Mcap Bs kappa eps hMcap.le hBs hKappa0 heps
    have hrs:r <= amplification eps/100:=min_le_left _ _
    linarith [hh.2.1]
  have hMp:0 <= Mp:=bandWidth_nonneg Mcap Bs eps hMcap.le hBs heps _
  have hMc:0<Mc:=band_positive Mcap Bs eps hMcap hBs heps k
  have hMpM:Mp <= Mcap:=bandWidth_le _ _ _ _
  have hMcM:Mc <= Mcap:=bandWidth_le _ _ _ _
  have hac:0<ac:=lowerAt_pos a b Mcap eps ha _
  have haca:ac <= a:=CenteredMomentEnergyProfiles.lower_antitone a b ha (Nat.zero_le _)
  have haclo:ac <= 1/4:=haca.trans hlo
  have hLc:0 <= Lc:=range_nonneg Mcap Bmask L hMcap.le hmask _
  have hLp:0 <= Lp:=range_nonneg Mcap Bmask L hMcap.le hmask _
  have hreq:=request_bounds Mcap Bmask Lc hMcap.le hmask hLc
  have hreqFinal:Lreq <= range Mcap Bmask L (count Mcap eps):=
    request_le_final Mcap Bmask L eps hMcap.le hmask k hk
  have hRange:=range_nonneg Mcap Bmask L hMcap.le hmask (count Mcap eps)
  have hA:0 <= A:=by dsimp [A];positivity
  have hMA:Mp <= A:=by dsimp [A];linarith [range_nonneg Mcap Bmask L hMcap.le hmask (count Mcap eps)]
  have hready:readyBudget A Bmask <= Bs:=
    readyBudget_le_schedule Mcap Bmask L eps A Bmask hMcap.le hmask le_rfl le_rfl
  have hdrop:Mp-amplification eps/2 <= Mc:=parent_drop Mcap Bs eps heps k
  have hmesh:0 <= fineMesh Mcap Bmask L kappa eps:=
    (fineMesh_pos Mcap Bmask L kappa eps hMcap.le hmask hKappa0 heps).le
  have hsupport:lowerAt a b Mcap eps k=ac/max 1 b:=child_support a b Mcap eps k hk
  have hrequest:2*max Lreq Mp+r/4 <= Lp:=previous_admits Mcap Bmask L eps Mp (r/4)
    hMcap.le hmask hMpM hr1 k hk
  have hhighL:max Lc Mp <= Lp:=by
    have hh:max Lc Mp <= Lreq:=max_le hreq.2.1 (hMpM.trans hreq.2.2)
    have hg:0 <= max Lreq Mp:=hreq.1.trans (le_max_left _ _)
    have hx:=le_max_left Lreq Mp
    linarith
  have href:Mp+Bmask+Mc/100 <= Lreq:=by
    have hh:=actual_contours Mcap Bmask Lc Mp Mc 0 hMcap.le hmask hMpM hMcM (by norm_num)
    exact (le_max_right _ _).trans hh
  choose Jold Sold hprev using hold
  choose Slow Jlow hlow using
    @KappaHalfCappedLowStage.actual_capped_low
      alpha inferInstance inferInstance M inferInstance H hH
    W aslot bslot a b radial Bmask L lo hi Mcap kappa eps hW haslot hWs hbslot ha hb hrad
    hmask hMcap.le (by linarith) heps hbeta hKappaBeta k hk
    (Exists.intro Jold (Exists.intro Sold hprev))
  choose Uhigh Jhigh hhigh using
    @KappaHalfNaturalHighStage.actual_high_stage
      alpha inferInstance inferInstance M inferInstance H hH
    W hW aslot bslot lo hi ac b radial haslot hWs hbslot hac haclo hhi (by linarith)
    Mcap A Bs Bmask Mp Mc Lc (fineMesh Mcap Bmask L kappa eps) Mc kappa eps k hMc hMcap.le hA hBs hmask
    hMp hMc.le hLc hmesh hMA hready hKappa hbeta hKappaBeta heps le_rfl hdrop Jold Sold Jlow Slow
  choose d Lgrow Llow hd hd1 hLg hgoal hLexact hLlow hLupper hzeroStage using
    @KappaHalfNaturalZeroStage.actual_zero_stage
      alpha inferInstance inferInstance M inferInstance H hH
      W aslot bslot (fineMesh Mcap Bmask L kappa eps) lo hi kappa ac b radial Bmask Lc Mp Mc Mcap Bs eps Mc k
      haslot hWs hW hmesh (by linarith) hbeta hKappaBeta hac haclo hhi hrad hmask hLc hMp hMc.le hMcap.le hBs
      heps hMc le_rfl hdrop
  have hLlowReq:Llow <= Lreq:=by
    rw [hLlow,hLexact]
    exact actual_contours Mcap Bmask Lc Mp Mc d hMcap.le hmask hMpM hMcM hd1
  have hLgrowLow:Lgrow <= Llow:=by rw [hLlow];exact le_max_left _ _
  have hLgrowReq:Lgrow <= Lreq:=hLgrowLow.trans hLlowReq
  have hzeroCap:max Mp (2*Lgrow) <= Lp:=by
    have hm:Mp <= Lreq:=hMpM.trans hreq.2.2
    have hh:=le_max_left Lreq Mp
    apply max_le <;> linarith
  have hzeroReady:readyBudget (max Mp (2*Lgrow)) Bmask <= Bs:=by
    have hc:max Mp (2*Lgrow) <= A:=max_le hMA (by dsimp [A]; linarith)
    apply le_trans _ hready
    unfold readyBudget
    linarith
  choose Jzero Uzero hzero using hzeroStage Lp hLp hzeroCap hzeroReady Jold Jlow Sold Slow
  have hmarg:=margins Mcap Bs kappa eps hMcap.le hBs hKappa0 heps k
  apply CenteredMomentEnergyCappedSuccessorPacking.certified_from_stages M H hH
    W bslot a b radial Bmask L lo hi Mcap kappa eps ha hmask hMcap.le hKappa0 heps k
    (stageLoss Mcap Bs eps (k+1)) (physicalLoss Mcap Bs eps k) (reflectedLoss Mcap Bs eps k)
    le_rfl (hmarg.2.2.2.1.trans hmarg.2.2.2.2) hmarg.2.2.2.2 (Exists.intro Jold (Exists.intro Sold hprev))
  next =>
    refine Exists.intro Jzero (Exists.intro Uzero ?_)
    intro eta0 Q hQM hQ0 hQt hQ72
    choose C0 C1 hC0 hC1 hprevZ using hprev eta0 Q hQM hQ0 hQt hQ72
    choose Clow hClow hlowZ using hlow eta0 Q hQM hQ0 hQt hQ72
    choose Cz hCz hzeroZ using hzero eta0 Q hQM hQ0 hQt hQ72
    refine Exists.intro (Cz*(Clow+C0+C1+1)) (And.intro (by positivity) ?_)
    filter_upwards [hprevZ,hlowZ,hzeroZ] with Z hp hl hz
    have hzz:=hp.2.1
    have hpp:=hp.2.2
    rw [hsupport] at hzz hpp
    have hlowRestricted:=zeroLowAt_transport (internalQ Q eta0)
      ac b radial Bmask Lreq Mp (physicalLoss Mcap Bs eps k) Z
      ac b radial Bmask Llow Mp (physicalLoss Mcap Bs eps k) Jlow Jlow Slow Slow Clow Clow
      hp.1.le le_rfl le_rfl le_rfl le_rfl hLlowReq le_rfl le_rfl le_rfl
      (Finset.Subset.refl _) hClow.le le_rfl hl.2.2
    exact hz.2 _ C0 C1 Clow le_rfl hC0.le hC1.le hClow.le hzz hpp hlowRestricted
  next =>
    refine Exists.intro Jlow (Exists.intro Slow ?_)
    intro eta0 Q hQM hQ0 hQt hQ72
    choose Clow hClow hlowZ using hlow eta0 Q hQM hQ0 hQt hQ72
    refine Exists.intro Clow (And.intro hClow ?_)
    filter_upwards [hlowZ] with Z hl
    exact @positiveLowAt_transport alpha M inferInstance H hH W bslot
      ac b radial Bmask Lreq (fineMesh Mcap Bmask L kappa eps) lo hi Mp (physicalLoss Mcap Bs eps k) kappa Z
      ac b radial Bmask Lc Mp (physicalLoss Mcap Bs eps k) eta0 Q Jlow Jlow Slow Slow Clow Clow
      hl.1.le le_rfl le_rfl le_rfl le_rfl hreq.2.1 le_rfl le_rfl le_rfl
      (Finset.Subset.refl _) hClow.le le_rfl hl.2.1
  next =>
    refine Exists.intro Jhigh (Exists.intro Uhigh ?_)
    intro eta0 Q hQM hQ0 hQt hQ72
    choose C0 C1 hC0 hC1 hprevZ using hprev eta0 Q hQM hQ0 hQt hQ72
    choose Clow hClow hlowZ using hlow eta0 Q hQM hQ0 hQt hQ72
    choose Ch hCh hhighZ using hhigh eta0 Q hQM hQ0 hQt hQ72
    refine Exists.intro (Ch*(C0+C1+Clow+1)) (And.intro (by positivity) ?_)
    filter_upwards [hprevZ,hlowZ,hhighZ] with Z hp hl hh
    have hzz:=hp.2.1
    have hpp:=hp.2.2
    rw [hsupport] at hzz hpp
    have hzSmall:=zeroAt_transport (internalQ Q eta0)
      (ac/max 1 b) b radial Bmask Lp Mc (stageLoss Mcap Bs eps k) Z
      (ac/max 1 b) b 2 0 (max Lc Mp) Mc (stageLoss Mcap Bs eps k)
      Jold Jold Sold Sold C0 C0 hp.1.le le_rfl le_rfl hrad hmask hhighL le_rfl le_rfl le_rfl
      (Finset.Subset.refl _) hC0.le le_rfl hzz
    have hpSmall:=@positiveAt_transport alpha M inferInstance H hH W bslot
      (ac/max 1 b) b radial Bmask Lp (fineMesh Mcap Bmask L kappa eps) lo hi Mc (stageLoss Mcap Bs eps k) kappa Z
      (ac/max 1 b) b 2 0 (max Lc Mp) Mc (stageLoss Mcap Bs eps k) eta0 Q
      Jold Jold Sold Sold C1 C1 hp.1.le le_rfl le_rfl hrad hmask hhighL le_rfl le_rfl le_rfl
      (Finset.Subset.refl _) hC1.le le_rfl hpp
    have hlRestricted:=@positiveLowAt_transport alpha M inferInstance H hH W bslot
      ac b radial Bmask Lreq (fineMesh Mcap Bmask L kappa eps) lo hi Mp (physicalLoss Mcap Bs eps k) kappa Z
      ac b radial Bmask (Mp+Bmask+Mc/100) Mp (physicalLoss Mcap Bs eps k) eta0 Q
      Jlow Jlow Slow Slow Clow Clow hp.1.le le_rfl le_rfl le_rfl le_rfl href le_rfl le_rfl le_rfl
      (Finset.Subset.refl _) hClow.le le_rfl hl.2.1
    exact hh.2 _ C0 C1 Clow le_rfl hC0.le hC1.le hClow.le hzSmall hpSmall hlRestricted

end SevenEighths.KappaHalfCappedSuccessor

end

end OAI

