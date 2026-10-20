/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Energy.ZeroGrowthPhysical
import PrimeFactorOscillations.Assembly.DetectorPackets.KappaHalfNaturalLowStage

/-!
# KappaHalfZeroGrowthPhysical

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

namespace SevenEighths.KappaHalfZeroGrowthPhysical

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

open CenteredMomentEnergyZeroGrowthPhysicalReindex CenteredMomentSourceInputReindex
open CenteredMomentEnergyZeroBalancedAdmission CenteredMomentEnergyZeroBalancedDictionary
open CenteredMomentEnergyCanonicalHighPhysical CenteredMomentEnergyZeroGrowthSource
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFirstAmplifiedFourCoefficients
open CenteredMomentSecondInputCapacitySource CenteredMomentFirstSourceReduction

theorem actual_growth_physical
    (Wslot:Real -> Complex)(aslot bslot Lslot lo hi kappa a b bPhi Bmask Lgoal Lchild Mparent Mchild
      Mschedule Bschedule eps:Real)
    (haslot:0<aslot)(hWs:Function.support Wslot <= Set.Icc aslot bslot)
    (hW:ContDiff Real ((Top.top : ENat) : WithTop ENat) Wslot)(hLs:0 <= Lslot)(hKappa:(1/6:Real) <= kappa)
    (hbeta:(51/100:Real) <= HeckeZeroSupremum.beta)(hKappaBeta:2*HeckeZeroSupremum.beta-1 <= kappa)
    (ha:0<a)(hb:0 <= b)(hBmask:0 <= Bmask)(hLgoal:0 <= Lgoal)(hLchild:0 <= Lchild)
    (hMparent:0 <= Mparent)(hMchild:0 <= Mchild)(hMschedule:0 <= Mschedule)(hBschedule:0 <= Bschedule)
    (heps:0<eps)(hcap: max Mparent (2*Lgoal) <= Lchild)
    (hready:readyBudget (max Mparent (2*Lgoal)) Bmask <= Bschedule)
    (hdrop:Mparent-amplification eps/2 <= Mchild)
    (Psi:SchwartzMap Real Complex)(degree:Nat)(S:Finset (Prod Nat Nat)):
    exists Uprofile:Finset (Prod Nat Nat),exists Jheight:Nat,
    forall eta0:Character,forall Q:Ideal O,Q <= M -> Not (internalQ Q eta0 = 0) -> Not (internalQ Q eta0 = Top.top) -> 
      internalQ Q eta0 <= Ideal.span {(72:O)} -> 
    exists C:Real,0<C  /\  exists Z0:Real,1<Z0  /\  forall Z:Real,Z0 <= Z -> 
    forall (k:Nat)(epschild C0 C1 rho:Real),epschild <= stageLoss Mschedule Bschedule eps k -> 
      0 <= C0 -> 0 <= C1 -> 
      ZeroAt (internalQ Q eta0) (a/max 1 b) b 2 0 Lchild Mchild epschild Z degree S C0 -> 
      @PositiveAt alpha M inferInstance H hH Wslot bslot (a/max 1 b) b 2 0 Lchild Lslot lo hi
        Mchild epschild kappa Z eta0 Q degree S C1 -> 
      PhysicalGrowthAt (internalQ Q eta0) a b bPhi Bmask Lgoal rho Mparent
        (reserve Mschedule Bschedule eps/4) (physicalLoss Mschedule Bschedule eps k)
        Z ha Psi Uprofile Jheight (C*(C0+C1+1)):=by
  classical
  let A:=max Mparent (2*Lgoal)
  let r:=reserve Mschedule Bschedule eps
  have hA:0 <= A:=hMparent.trans (le_max_left _ _)
  choose hsigma hsigma1 hr hxiSigma hxi1 hes hes1 hem hmesh hmeshEta heta0 heta hSaving hSeed using
    PrimeFactorOscillations.QRHSourceRange.parameter_gates_nonnegative
      Mschedule A Bschedule kappa eps hMschedule hA hBschedule (by linarith) heps
  have hKappaSmall:(1/6:Real) <= kappa:=by linarith
  have ha2:0<a^2:=sq_pos_of_pos ha
  choose U J hphysical using
    @CenteredMomentEnergyCanonicalHighPhysical.actual_high_physical
      alpha inferInstance inferInstance M inferInstance H hH
    Wslot aslot bslot Mchild Lslot (r/4) lo hi kappa a b 1
    (maskEpsilon Mschedule Bschedule eps) (by norm_num) hem ha hb
    Lchild hLchild degree S haslot hWs hW hMchild hLs hr hKappaSmall hbeta hKappaBeta
    0 1 1 (a^2) (r/4) (by norm_num) (by norm_num) ha2 hr
    (fun _=>1) (fun _=>1) (fun _=>by norm_num)
    (sourceEpsilon Mschedule A Bschedule eps) (r/4) (r/4) (A+1) (r/4)
    (2*amplification eps+1) hes hr hr hr
    (amplification eps) hsigma hxiSigma A Bmask (amplification eps/12) (r/4) (r/4)
    hA hBmask heta hr hsigma1 hxi1 hr hes1 le_rfl (fun _=>Psi) (r/4) (a*a)
    hr (mul_pos ha ha)
  have hfit := PrimeFactorOscillations.QRHSourceRange.eventually_actual_four_fit_nonnegative
    Mschedule A Bmask Bschedule kappa eps hMschedule hA hBschedule hready (by linarith) heps
  have hclip : Filter.Eventually (fun Z : Real =>
      1 < Z /\ Real.logb Z (max 1 b*max 1 b) <= 2*(r/4)) atTop := by
    filter_upwards [eventually_gt_atTop (1:Real),
      (Filter.tendsto_atTop.1 (tendsto_rpow_atTop (show 0<2*(r/4) by linarith)))
        (max 1 b*max 1 b)] with Z hZ hz
    refine And.intro hZ ?_
    exact (Real.logb_le_iff_le_rpow hZ (mul_pos
      (zero_lt_one.trans_le (le_max_left _ _))
      (zero_lt_one.trans_le (le_max_left _ _)))).mpr hz
  refine Exists.intro U (Exists.intro J ?_)
  intro eta0 Q hQM hQ0 hQt hQ72
  choose C hC Zbase hZbase hphysical using hphysical eta0 Q hQM hQ0 hQt hQ72
  choose Znum hZnum using Filter.eventually_atTop.mp (hfit.and hclip)
  refine Exists.intro C (And.intro hC (Exists.intro (max Zbase Znum)
    (And.intro (hZbase.trans_le (le_max_left _ _)) ?_)))
  intro Z hZZ k epschild C0 C1 rho hchild hC0 hC1 hzero hpos
  have hZbaseLe:Zbase <= Z:=(le_max_left _ _).trans hZZ
  have hn:=hZnum Z ((le_max_right _ _).trans hZZ)
  have hZ:1<Z:=hn.1.1
  intro s hQ hsLower hs p t X1 X2 hX1 hX2 hc1 hc2 hlarge
  dsimp only
  intro hfour
  let src:=emptyBalanced s p ha t X1 X2 hX1 hX2 alpha
  let theta : (Subtype fun i : alpha => Membership.mem (EmptyCollection.emptyCollection : Finset alpha) i) ->
      RayQuotient.Characters M H := fun i => isEmptyElim i
  have hmatch:CenteredMomentAllocatedRayDictionary.Matches M H hH src eta0 theta
      (fun _=>0) (fun _=>0) (fun _=>0) Wslot bslot Z:=by
    constructor <;> intro i <;> exact isEmptyElim i
  have hupper:=four_upper_scales s p ha t X1 X2 hX1 hX2 Mparent Lgoal hZ hLgoal hs hc1 hc2
  have hu:Z^A <= Z^Lchild:=Real.rpow_le_rpow_of_exponent_le hZ.le hcap
  have hgate:=declared_capacity s p ha t X1 X2 hX1 hX2 hZ
  have hdecl:=declared_capacity_upper s X1 X2 Mparent Lgoal hZ hLgoal hs hc1 hc2
  have hK:=CenteredMomentEnergyNaturalSourceAdmission.radial_admission s
  have hbound:=hphysical EmptyCollection.emptyCollection theta Z hZbaseLe epschild C0 C1 hC0 hC1 hzero hpos
    (fun _=>0) (fun _=>0) (fun _=>0) 0 (mesh Mschedule Bschedule kappa eps) hmesh.le
    (fun i=>isEmptyElim i)
    (fun i=>isEmptyElim i)
    (fun i=>isEmptyElim i)
    (fun i=>isEmptyElim i)
    (fun i=>isEmptyElim i)
    (fun i=>isEmptyElim i) (by norm_num)
    (fun i=>isEmptyElim i) src hmatch
    (fun i=>isEmptyElim i)
    (fun i=>isEmptyElim i)
    (fun i=>isEmptyElim i)
    (fun i=>isEmptyElim i) (by simp) le_rfl le_rfl
    hb hb (le_max_right _ _) (le_max_right _ _) (by simp)
    s.puncture 1 s.puncture_ne_zero s.puncture_bound squarefree_one one_ne_zero
    s.radial.scale hK.1 p rfl rfl
    (hupper.1.trans hu) (hupper.2.1.trans hu) (hupper.2.2.1.trans hu) (hupper.2.2.2.trans hu)
    (max s.width (length Z X1+length Z X2)) s.width (r/4)
    (columnLoss Mschedule Bschedule eps k) hr.le hdecl
    (by
      change length Z X1+length Z X2+6*kappa*(Finset.univ.sum
        (fun _ : (Subtype fun i : alpha => Membership.mem (EmptyCollection.emptyCollection : Finset alpha) i) =>
          (0 : Real))) <= _
      simpa only [Finset.sum_const_zero,mul_zero,add_zero] using
        le_max_right s.width (length Z X1+length Z X2))
    (hgate.2.1.trans (le_max_left _ _)) hgate.2.1 (by linarith)
    hn.2.2 (by simp [lowerFactor]) (le_max_left _ _)
    hfour.1 hfour.2.1 hfour.2.2.1 hfour.2.2.2 (hn.1.2 k epschild hchild)
  rw [show physicalMass src s.puncture 1 fixedBadMask 1 Psi s.radial.scale Z (r/4)=
      physicalMass (CenteredMomentEnergyZeroReferencePhysical.balancedInput s p ha t X1 X2 hX1 hX2)
        s.puncture 1 fixedBadMask 1 Psi s.radial.scale Z (r/4) from
        empty_balanced_mass s p ha t X1 X2 hX1 hX2 _ _ _ _ _ _ _ _] at hbound
  rw [show volume src=X1*X2 from empty_balanced_volume s p ha t X1 X2 hX1 hX2] at hbound
  have heq:max s.width (length Z X1+length Z X2)+columnLoss Mschedule Bschedule eps k+r/4=
      max s.width (length Z X1+length Z X2)+physicalLoss Mschedule Bschedule eps k:=by
    dsimp only [r]
    rw [add_assoc,columnLoss_physical]
  simpa only [map_one,Nat.cast_one,div_one,add_zero,
    show (src).t=t from rfl,heq] using hbound

end SevenEighths.KappaHalfZeroGrowthPhysical

end

end OAI

