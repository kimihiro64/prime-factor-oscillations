/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Energy.PositiveHighAssemblyBounded
import PrimeFactorOscillations.Assembly.DetectorPackets.KappaHalfPhysicalEntry
import PrimeFactorOscillations.Assembly.DetectorPackets.KappaHalfSymmetricBoundedPower

/-!
# KappaHalfHighAssembly

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

namespace SevenEighths.KappaHalfHighAssembly

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

theorem actual_high_source_split
    (Wslot:Real ->  Complex)(aslot bslot lo hi:Real)
    (haslot:0<aslot)(hsSlot:Function.support Wslot <= Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bPhi rho eps Mcap Bmask epsdiag Xi saving k0:Real)
    (ha:0<a)(hlo:a <= 1/4)(hhi:1 <= b)(hbPhi:0<bPhi)(hrho:0<rho)(heps:0<eps)
    (hM:0 <= Mcap)(hBmask:0 <= Bmask)(hbslot:0 <= bslot)(hepsdiag:0<epsdiag)(hXi:0<Xi)(hk0:1/2<k0):
    exists d L:Real,0<d  /\  0 <= L  /\  L <= Mcap+Bmask+rho/100  /\ 
    exists Psi:SchwartzMap Real Complex,Function.support (Psi:Real ->  Complex) <= Set.Icc (-1) (bPhi+1)  /\ 
      (forall x,0 <= (Psi x).re)  /\ 
    exists Sdiag Stail:Finset (Prod Nat Nat),exists Cdiag Ctail:Real,0<Cdiag  /\ 0<Ctail  /\ 
    forall degree:Nat,forall S:Finset (Prod Nat Nat),
    exists Ju Jr:Nat,exists Uu Ur:Finset (Prod Nat Nat),exists Cu Cr:Real,0<Cu  /\  0<Cr  /\ 
      Filter.Eventually (fun Z : Real =>1<Z  /\ 
      forall (e Lslot k:Real)(eta0:Character)(Q:Ideal O)(K:Real),0 <= e ->  0 <= K -> 
      @PositiveLowAt alpha M inferInstance H hH Wslot bslot a b bPhi Bmask L Lslot lo hi
        Mcap e k Z eta0 Q degree S K -> 
      forall (theta:alpha ->  RayQuotient.Characters M H)(w sigma freq:alpha ->  Real)(t height:Real),
      (forall i,0 <= w i) ->  (forall i,w i <= Lslot) ->  forall hSigmaLo:(forall i,lo <= sigma i),forall hSigmaHi:(forall i,sigma i <= hi),
      0 <= height ->  (forall i,abs (freq i) <= height) ->  k0 <= k -> 
      forall (s:NaturalState Z Bmask bPhi),s.fixedModulus=internalQ Q eta0 ->  rho <= s.width ->  s.width <= Mcap -> 
      forall (p:Profiles a b)(X1 X2:Real)(hX1:0<X1)(hX2:0<X2),
      5*s.width/6 <= length Z X1+length Z X2+Finset.univ.sum w -> 
      length Z X1+length Z X2+6*k*Finset.univ.sum w <= s.width -> 
      let inp:=balancedInput M H hH eta0 theta Wslot hcSlot aslot bslot lo hi haslot hsSlot
        w sigma freq (fun i => And.intro (hSigmaLo i) (hSigmaHi i)) s p ha t X1 X2 hX1 hX2;
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X1 X2 s.radial.keep s.radial.profile s.radial.scale <= 
        Cu*(K+1)*diagonalControl s.radial.profile*(sourceControl Uu (p.profile 0)*sourceControl Uu (p.profile 1))^2*
          (1+abs t+height)^Ju*Z^(s.width+e+eps)  \/ 
      (Z^(s.width/4) <= X1 /\ Z^(s.width/4) <= X2 /\
        Z^(s.width/4) <= comparisonFirst Z s.width /\
        Z^(s.width/4) <= comparisonSecond Z s.width X1 X2) /\
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X1 X2 s.radial.keep s.radial.profile s.radial.scale <= 
      2*diagonalControl s.radial.profile*(
        physicalMass inp s.puncture 1 fixedBadMask 1 Psi s.radial.scale Z Xi/
          CenteredMomentAmplificationChildInput.volume inp+
        Cdiag*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Sdiag.sup (schwartzSeminormFamily Real Real Complex) Psi*s.radial.scale*Z^epsdiag+
        Ctail*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Stail.sup (schwartzSeminormFamily Real Real Complex) Psi*s.radial.scale*Z^(-saving))+
      2*Cr*(K+1)*diagonalControl s.radial.profile*(sourceControl Ur (p.profile 0)*sourceControl Ur (p.profile 1))^2*
        (1+abs t+height)^Jr*Z^(s.width+e+eps)) atTop := by
  classical
  choose du xiu Lu hdu hxiu hxiuR hLu hLuUpper hustage using
    @KappaHalfSymmetricBoundedPower.original_unbalanced_from_low
      alpha inferInstance inferInstance M inferInstance H hH
      Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bPhi rho eps Mcap Bmask k0 ha hlo hhi hbPhi hrho heps hM hBmask hk0
  choose dr xir Lr hdr hxir hxirR hLr hLrUpper Psi hsPsi hnPsi
    Sdiag Stail Cdiag Ctail hCd hCt hrstage using
    @KappaHalfPhysicalEntry.actual_positive_source_entry
      alpha inferInstance inferInstance M inferInstance H hH
      Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bPhi rho eps Mcap Bmask epsdiag Xi saving k0
      ha hlo hhi hbPhi hrho heps hM hBmask hbslot hepsdiag hXi hk0
  have hLnonneg : 0 <= max Lu Lr :=
    (show 0 <= Lu by linarith).trans (le_max_left _ _)
  refine Exists.intro (min du dr) (Exists.intro (max Lu Lr) ?_)
  refine And.intro (lt_min hdu hdr) (And.intro hLnonneg
    (And.intro (max_le hLuUpper hLrUpper) ?_))
  refine Exists.intro Psi (And.intro hsPsi (And.intro hnPsi ?_))
  refine Exists.intro Sdiag (Exists.intro Stail
    (Exists.intro Cdiag (Exists.intro Ctail (And.intro hCd (And.intro hCt ?_)))))
  intro degree S
  choose Ju Uu Cu hCu hu using hustage degree S
  choose Jr Ur Cr hCr hr using hrstage degree S
  refine Exists.intro Ju (Exists.intro Jr (Exists.intro Uu (Exists.intro Ur
    (Exists.intro Cu (Exists.intro Cr (And.intro hCu (And.intro hCr ?_)))))))
  filter_upwards [hu, hr] with Z hzu hzr
  refine And.intro hzu.1 ?_
  intro e Lslot k eta0 Q K he hK hlow theta w sigma freq t height
    hw hwL hSigmaLo hSigmaHi hheight hfreq hk
    s hQ hsLower hs p X1 X2 hX1 hX2 hlarge hcap
  have hlu := @CenteredMomentEnergyPositiveHighAssembly.low_restrict
    alpha M inferInstance H hH
    Wslot bslot a b bPhi Bmask (max Lu Lr) Lu
    Lslot lo hi Mcap e e k Z eta0 Q degree S K
    hzu.1.le (le_max_left _ _) le_rfl hK hlow
  have hlr := @CenteredMomentEnergyPositiveHighAssembly.low_restrict
    alpha M inferInstance H hH
    Wslot bslot a b bPhi Bmask (max Lu Lr) Lr
    Lslot lo hi Mcap e e k Z eta0 Q degree S K
    hzu.1.le (le_max_right _ _) le_rfl hK hlow
  by_cases hshort : min (length Z X1) (length Z X2) <= s.width / 4
  next =>
    apply Or.inl
    exact hzu.2 e Lslot k eta0 Q K he hK hlu theta w sigma freq t height
      hw hwL hSigmaLo hSigmaHi hheight hfreq hk s hQ hsLower hs
      (p.profile 0) (p.profile 1) (p.support 0) (p.support 1)
      X1 X2 hX1 hX2 hshort hlarge hcap
  next =>
    have hfour := CenteredMomentEnergyOriginalHighReflectionSymmetric.balanced_four_scale_gates
      Z s.width X1 X2 hzu.1 (hrho.trans_le hsLower) hX1 hX2
      (le_of_lt (lt_of_not_ge hshort))
    have hz := hzr.2 e Lslot k eta0 Q K he hK hlr theta w sigma freq t height
      hw hwL hSigmaLo hSigmaHi hheight hfreq hk
      s hQ hsLower hs p X1 X2 hX1 hX2 hlarge hcap
    cases hz with
    | inl hzero =>
      apply Or.inl
      rw [hzero]
      have hd := diagonalControl_nonneg s.radial.profile
      have hZpos := zero_lt_one.trans hzu.1
      positivity
    | inr hsource =>
      exact Or.inr (And.intro
        (And.intro hfour.1 (And.intro hfour.2.1
          (And.intro hfour.2.2.1 hfour.2.2.2.1))) hsource)

end SevenEighths.KappaHalfHighAssembly

end

end OAI

