/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Energy.PositiveHighSourceBound
import PrimeFactorOscillations.Assembly.DetectorPackets.KappaHalfHighBound

/-!
# KappaHalfHighStage

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

namespace SevenEighths.KappaHalfHighStage

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
open CenteredMomentEnergyPositiveHighAssembly (low_restrict)

theorem actual_high_stage_from_physical
    (W:Real -> Complex)(hW:Continuous W)(aslot bslot lo hi a b bPhi rho eps Mcap Bmask epsdiag Xi saving k0:Real)
    (haslot:0<aslot)(hWs:Function.support W <= Set.Icc aslot bslot)
    (hbslot:0 <= bslot)(ha:0<a)(hlo:a <= 1/4)(hhi:1 <= b)(hbPhi:0<bPhi)
    (hrho:0<rho)(heps:0<eps)(hMcap:0 <= Mcap)(hBmask:0 <= Bmask)(hepsdiag:0<epsdiag)(hXi:0<Xi)(hk0:1/2<k0):
    exists Psi:(T:Finset alpha) -> SchwartzMap Real Complex,
      (forall T,Function.support (Psi T:Real -> Complex) <= Set.Icc (-1) (bPhi+1))  /\ 
      (forall T x,0 <= (Psi T x).re)  /\ 
    forall degree:Nat,forall S:Finset (Prod Nat Nat),forall Jmass:Nat,forall Smass:Finset (Prod Nat Nat),
    exists Jout:Nat,exists U:Finset (Prod Nat Nat),exists Cfixed:Real,0<Cfixed  /\ 
    Filter.Eventually (fun Z : Real =>1<Z  /\ 
    forall (L Lslot k e emass efinal:Real)(eta0:Character)(Q:Ideal O)(K Cphysical:Real),
      k0 <= k -> 0 <= e -> 0 <= K -> 0 <= Cphysical -> e+eps <= efinal -> emass <= efinal -> epsdiag <= efinal -> -saving <= efinal -> 
      @PositiveLowAt alpha M inferInstance H hH W bslot a b bPhi Bmask (Mcap+Bmask+rho/100)
        Lslot lo hi Mcap e k Z eta0 Q degree S K -> 
      @PhysicalHighAt alpha M inferInstance H hH W hW aslot bslot lo hi haslot hWs
        a b bPhi Bmask L Lslot rho Mcap k Xi emass Z ha Psi eta0 Q Smass Jmass Cphysical -> 
      @PositiveHighAt alpha M inferInstance H hH W bslot a b bPhi Bmask L Lslot lo hi rho Mcap efinal k Z eta0 Q
        Jout U (Cfixed*(K+Cphysical+1))) atTop := by
  classical
  have hfixed (T : Finset alpha) :=
    @KappaHalfHighBound.actual_high_from_physical T inferInstance inferInstance
      M inferInstance H hH W aslot bslot lo hi haslot hWs hW
      a b bPhi rho eps Mcap Bmask epsdiag Xi saving k0
      ha hlo hhi hbPhi hrho heps hMcap hBmask hbslot hepsdiag hXi hk0
  choose Lj hLj hLjcap Psi hPsis hPsin hj using hfixed
  refine Exists.intro Psi (And.intro hPsis (And.intro hPsin ?_))
  intro degree S Jmass Smass
  have hall (T:Finset alpha):=hj T degree S Jmass Smass
  choose Jj Uj Cj hCj hbound using hall
  let Jout:Nat:=Finset.univ.sum Jj
  let U:Finset (Prod Nat Nat):=Finset.univ.biUnion Uj
  let Cfixed:Real:=1+Finset.univ.sum Cj
  have hCfixed:0<Cfixed:=by
    have hh:=Finset.sum_nonneg (fun T (_:Membership.mem (Finset.univ:Finset (Finset alpha)) T)=>(hCj T).le)
    dsimp [Cfixed];linarith
  have hCC (T:Finset alpha):Cj T <= Cfixed:=by
    have hh:=Finset.single_le_sum (fun T (_:Membership.mem (Finset.univ:Finset (Finset alpha)) T)=>(hCj T).le)
      (Finset.mem_univ T)
    dsimp [Cfixed];linarith
  have hJJ (T:Finset alpha):Jj T <= Jout:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ T)
  have hUU (T:Finset alpha):Uj T <= U:=by
    intro x hx
    exact Finset.mem_biUnion.mpr (Exists.intro T (And.intro (Finset.mem_univ T) hx))
  refine Exists.intro Jout (Exists.intro U (Exists.intro Cfixed (And.intro hCfixed ?_)))
  have hevent : Filter.Eventually (fun Z : Real => forall T : Finset alpha, _) atTop :=
    Filter.eventually_all.mpr hbound
  filter_upwards [hevent,eventually_gt_atTop (1:Real)] with Z hZ hZ1
  refine And.intro hZ1 ?_
  intro L Lslot k e emass efinal eta0 Q K Cphysical hk he hK hCphysical hefinal hmassFinal
    hdiagFinal htailFinal hlow hmass
    T theta w sigma freq t height hw hwL hSigmaLo hSigmaHi hheight hfreq state hQ hwidthLo hwidth
    p X1 X2 hX1 hX2 hcap1 hcap2 hcapacity hlarge
  have hlowT:=CenteredMomentEnergyLowBandSubtype.positiveLowAt_subtype M H hH T
    W bslot a b bPhi Bmask (Mcap+Bmask+rho/100) Lslot lo hi Mcap e k Z eta0 Q degree S K hlow
  have hlowLj:=low_restrict M H hH W bslot a b bPhi Bmask (Mcap+Bmask+rho/100)
    (Lj T) Lslot lo hi Mcap e e k Z eta0 Q degree S K hZ1.le (hLjcap T) le_rfl hK hlowT
  have hphys:=hmass T theta w sigma freq t height hw hwL hSigmaLo hSigmaHi hheight hfreq state hQ hwidthLo
    hwidth p X1 X2 hX1 hX2 hcap1 hcap2 hcapacity hlarge
  have hh:=(hZ T).2 e emass efinal Lslot k eta0 Q K Cphysical he hK hCphysical
    hefinal hmassFinal hdiagFinal htailFinal hlowLj theta w sigma freq t height hw hwL hSigmaLo hSigmaHi
    hheight hfreq hk state hQ hwidthLo hwidth p X1 X2 hX1 hX2 hlarge hcapacity hphys
  have hc:=hCC T
  have hp:=profile_control_mono p (hUU T)
  have hp0:=p.control_nonneg (Uj T)
  have hbase:1 <= 1+abs t+height:=by linarith [abs_nonneg t]
  have hJJt := hJJ T
  have hpow : (1+abs t+height)^(Jj T) <= (1+abs t+height)^Jout := by gcongr
  have hd:=diagonalControl_nonneg state.radial.profile
  have hz:0 <= Z:=zero_le_one.trans hZ1.le
  apply hh.trans
  gcongr

end SevenEighths.KappaHalfHighStage

end

end OAI

