/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Energy.NaturalLowPhysical
import PrimeFactorOscillations.Assembly.DetectorPackets.KappaHalfHighPhysical

/-!
# KappaHalfLowPhysical

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

namespace SevenEighths.KappaHalfLowPhysical

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

theorem actual_natural_low_physical
    (W:Real -> Complex)(hW:ContDiff Real ((Top.top : ENat) : WithTop ENat) W)(aslot bslot lo hi a b bPhi:Real)
    (haslot:0<aslot)(hWs:Function.support W <= Set.Icc aslot bslot)
    (hbslot:0 <= bslot)(ha:0<a)(hb:0 <= b)
    (Mglobal A B Bmask Mparent Mchild Lgoal Lslot rho kappa eps:Real)(k:Nat)
    (hMg:0 <= Mglobal)(hA:0 <= A)(hB:0 <= B)(hBm:0 <= Bmask)
    (_hMp:0 <= Mparent)(hMc:0 <= Mchild)(hL:0 <= Lgoal)(hLs:0 <= Lslot)
    (hMA:Mparent <= A)(hready:readyBudget A Bmask <= B)
    (hKappa:(1/6:Real) <= kappa)(hbeta:(51/100:Real) <= HeckeZeroSupremum.beta)
    (hKappaBeta:2*HeckeZeroSupremum.beta-1 <= kappa)(heps:0<eps)
    (hslot:Lslot <= mesh Mglobal B kappa eps)
    (hdrop:Mparent-amplification eps/2 <= Mchild)
    (Psi:(T:Finset alpha) -> SchwartzMap Real Complex)(degree:Nat)(S:Finset (Prod Nat Nat)):
    exists U:Finset (Prod Nat Nat),exists J:Nat,
    forall eta0:Character,forall Q:Ideal O,Q <= M -> Not (internalQ Q eta0 = 0) -> Not (internalQ Q eta0 = Top.top) -> 
      internalQ Q eta0 <= Ideal.span {(72:O)} -> 
    exists C:Real,0<C  /\  Filter.Eventually (fun Z : Real =>1<Z  /\ 
    forall epschild C0 C1:Real,epschild <= stageLoss Mglobal B eps k -> 0 <= C0 -> 0 <= C1 -> 
      ZeroAt (internalQ Q eta0) (a/max 1 b) b 2 0 (2*max Lgoal Mparent+reserve Mglobal B eps/4)
        Mchild epschild Z degree S C0 -> 
      @PositiveAt alpha M inferInstance H hH W bslot (a/max 1 b) b 2 0 (2*max Lgoal Mparent+reserve Mglobal B eps/4)
        Lslot lo hi Mchild epschild kappa Z eta0 Q degree S C1 -> 
      @PhysicalLowAt alpha M inferInstance H hH W hW.continuous aslot bslot lo hi haslot hWs
        a b bPhi Bmask Lgoal Lslot rho Mparent kappa (reserve Mglobal B eps/4)
        (physicalLoss Mglobal B eps k) Z ha Psi eta0 Q U J (C*(C0+C1+1))) atTop := by
  classical
  let r:=reserve Mglobal B eps
  let N:=Fintype.card alpha
  let Mslot:=profileBound W hW.continuous aslot bslot lo hi haslot hWs
  let a0:=CenteredMomentSecondInputCapacitySource.lowerFactor N aslot a
  let lp:=(min 1 aslot)^N*a*a
  have hMslot:1 <= Mslot:=profileBound_ge_one W hW.continuous aslot bslot lo hi haslot hWs
  have ha0:0<a0:=CenteredMomentSecondInputCapacitySource.lowerFactor_pos N aslot a haslot ha
  have hlp:0<lp:=by dsimp [lp];positivity
  choose hsigma hsigma1 hr hxi hxi1 hes hes1 hem hmesh hmesheta heta hetastrict htwosigma hAseed using
    PrimeFactorOscillations.QRHSourceRange.parameter_gates_nonnegative
      Mglobal A B kappa eps hMg hA hB (by linarith) heps
  have hrpos:0<r/4:=hr
  have hKappaSmall:(1/6:Real) <= kappa:=by linarith
  have hLbase:0 <= max Lgoal Mparent:=hL.trans (le_max_left _ _)
  have hLphys:0 <= 2*max Lgoal Mparent+r/4:=by positivity
  choose U J hphysical using
    @CenteredMomentEnergyCanonicalLowPhysical.actual_low_physical
      alpha inferInstance inferInstance M inferInstance H hH W aslot bslot Mchild Lslot (r/4) lo hi kappa a b Mslot (maskEpsilon Mglobal B eps)
    (zero_le_one.trans hMslot) hem ha hb (2*max Lgoal Mparent+r/4) hLphys degree S haslot hWs hW hMc hLs hr
    hKappaSmall hbeta hKappaBeta N aslot (max 1 bslot) a0 (r/4) haslot (le_max_left _ _) ha0 hr
    (fun _=>aslot) (fun _=>bslot) (fun _=>hbslot)
    (sourceEpsilon Mglobal A B eps) (r/4) (r/4) (A+1) (r/4) (2*amplification eps+1)
    hes hr hr hr (amplification eps) hsigma hxi A Bmask (amplification eps/12) (r/4) (r/4)
    hA hBm hetastrict hr hsigma1 hxi1 hr hes1 le_rfl Psi (r/4) lp hr hlp
  refine Exists.intro U (Exists.intro J ?_)
  intro eta0 Q hQM hQ0 hQt hQ72
  choose C hC Zzero hZzero hbound using hphysical eta0 Q hQM hQ0 hQt hQ72
  refine Exists.intro C (And.intro hC ?_)
  filter_upwards [eventually_ge_atTop Zzero,
    PrimeFactorOscillations.QRHSourceRange.eventually_actual_four_fit_nonnegative
      Mglobal A Bmask B kappa eps hMg hA hB hready (by linarith) heps,
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop (by linarith : 0<2*(r/4)))) (max 1 b*max 1 b),
    eventually_scale_admission b (max Lgoal Mparent) (r/4) hLbase hr]
    with Z hZZ hfit hclipPow hscale
  have hZ:1<Z:=hZzero.trans_le hZZ
  have hclip:Real.logb Z (max 1 b*max 1 b) <= 2*(r/4):=by
    have hh:=Real.logb_le_logb_of_le hZ (by positivity:0<max 1 b*max 1 b) hclipPow
    simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh
  refine And.intro hZ ?_
  intro epschild C0 C1 hell hC0 hC1 hzero hpos T theta w sigma freq t height hw hwL hSigmaLo hSigmaHi hheight hfreq state hQ hrho hstate
    p X1 X2 hX1 hX2 hc1 hc2 hcapacity hlow
  let inp:=zeroSourceInput M H hH eta0 theta W hW.continuous aslot bslot lo hi haslot hWs
    w sigma freq (fun i => And.intro (hSigmaLo i) (hSigmaHi i)) state p ha t X1 X2 hX1 hX2
  have hN:Fintype.card T <= N:=Fintype.card_le_of_injective (fun i:T=>i.val) Subtype.val_injective
  have hm:=(both_matches M H hH eta0 theta W hW.continuous aslot bslot lo hi haslot hWs
    w sigma freq (fun i => And.intro (hSigmaLo i) (hSigmaHi i)) state p ha t X1 X2 hX1 hX2).2
  have hu:=hscale.2 T M H hH eta0 theta W hW.continuous aslot bslot lo hi haslot hWs
    w sigma freq (fun i => And.intro (hSigmaLo i) (hSigmaHi i)) Bmask bPhi a state p ha t X1 X2 hX1 hX2 kappa
    hw hKappaSmall (hstate.trans (le_max_right _ _)) hcapacity
  have hg:max Lgoal Mparent <= 2*max Lgoal Mparent+r/4:=by linarith
  have hu1 :=
    hu.2.2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hg)
  have hu2 :=
    hu.2.2.2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hg)
  have hp:=lower_product_admission M H hH eta0 theta W hW.continuous aslot bslot lo hi haslot hWs
    w sigma freq (fun i => And.intro (hSigmaLo i) (hSigmaHi i)) state p ha t X1 X2 hX1 hX2 N hN
  have hlowV:Real.logb Z (volume inp) <= 5*state.width/6:=
    (low_admission M H hH eta0 theta W hW.continuous aslot bslot lo hi haslot hWs
      w sigma freq (fun i => And.intro (hSigmaLo i) (hSigmaHi i)) state p ha t X1 X2 hX1 hX2 hZ hlow).2
  have hr:=CenteredMomentEnergyNaturalSourceAdmission.radial_admission state
  have hwidth:=actual_width_le state hZ
  have hh:=hbound T theta Z hZZ epschild C0 C1 hC0 hC1 hzero hpos w sigma freq height (mesh Mglobal B kappa eps)
    hmesh.le hw (fun i=>(hwL i).trans hslot)
    (fun i=>((hwL i).trans hslot).trans hmesheta) hwL hSigmaLo hSigmaHi hheight hfreq
    inp hm (fun _=>le_rfl) (fun _=>le_rfl) (fun _=>rfl) (fun _=>rfl) hN le_rfl (le_max_right _ _)
    hb hb (le_max_right _ _) (le_max_right _ _) hp.2.2 state.puncture 1 state.puncture_ne_zero
    state.puncture_bound (by simp) (by simp) state.radial.scale hr.1 p rfl rfl
    hu1 hu2 hu.2.2.2.2.2.2.1 hu.2.2.2.2.2.2.2 state.width state.width (r/4) (columnLoss Mglobal B eps k)
    hrpos.le (hstate.trans hMA) hcapacity hwidth hwidth (by linarith only [hstate,hdrop])
    hclip le_rfl hlowV (hfit.2 k epschild hell)
  have hcost:state.width+columnLoss Mglobal B eps k+r/4=state.width+physicalLoss Mglobal B eps k:=by
    rw [add_assoc]
    exact congrArg (fun x => state.width+x) (columnLoss_physical Mglobal B eps k)
  rw [hcost] at hh
  have ht:inp.t=t:=rfl
  have hv0:volume inp = volume (sourceInput M H hH eta0 theta W hW.continuous aslot bslot lo hi haslot hWs
    w sigma freq (fun i => And.intro (hSigmaLo i) (hSigmaHi i)) state p ha t X1 X2 hX1 hX2):=rfl
  rw [ht,hv0] at hh
  simpa only [map_one,Nat.cast_one,div_one,mul_assoc] using hh

end SevenEighths.KappaHalfLowPhysical

end

end OAI

