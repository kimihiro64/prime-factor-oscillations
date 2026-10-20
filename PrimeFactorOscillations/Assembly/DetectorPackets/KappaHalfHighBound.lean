/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Energy.PositiveHighBound
import PrimeFactorOscillations.Assembly.DetectorPackets.KappaHalfHighAssembly

/-!
# KappaHalfHighBound

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

namespace SevenEighths.KappaHalfHighBound

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

theorem actual_high_from_physical
    (Wslot:Real ->  Complex)(aslot bslot lo hi:Real)
    (haslot:0<aslot)(hsSlot:Function.support Wslot <= Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bPhi rho eps Mcap Bmask epsdiag Xi saving k0:Real)
    (ha:0<a)(hlo:a <= 1/4)(hhi:1 <= b)(hbPhi:0<bPhi)(hrho:0<rho)(heps:0<eps)
    (hM:0 <= Mcap)(hBmask:0 <= Bmask)(hbslot:0 <= bslot)(hepsdiag:0<epsdiag)(hXi:0<Xi)(hk0:1/2<k0):
    exists L:Real,0 <= L  /\  L <= Mcap+Bmask+rho/100  /\ 
    exists Psi:SchwartzMap Real Complex,Function.support (Psi:Real ->  Complex) <= Set.Icc (-1) (bPhi+1)  /\ 
      (forall x,0 <= (Psi x).re)  /\ 
    forall degree:Nat,forall S:Finset (Prod Nat Nat),forall Jmass:Nat,forall Smass:Finset (Prod Nat Nat),
    exists Jout:Nat,exists U:Finset (Prod Nat Nat),exists Cfixed:Real,0<Cfixed  /\ 
      Filter.Eventually (fun Z : Real =>1<Z  /\ 
      forall (e emass efinal Lslot k:Real)(eta0:Character)(Q:Ideal O)(K Cmass:Real),
        0 <= e -> 0 <= K -> 0 <= Cmass -> e+eps <= efinal -> emass <= efinal -> epsdiag <= efinal -> -saving <= efinal -> 
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
      ((Z^(s.width/4) <=  X1  /\  Z^(s.width/4) <=  X2  /\ 
        Z^(s.width/4) <=  comparisonFirst Z s.width  /\  Z^(s.width/4) <=  comparisonSecond Z s.width X1 X2)  -> 
        physicalMass inp s.puncture 1 fixedBadMask 1 Psi s.radial.scale Z Xi/
          CenteredMomentAmplificationChildInput.volume inp <= 
          Cmass*(p.control Smass)^2*(1+abs t+height)^Jmass*Z^(s.width+emass))  -> 
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X1 X2 s.radial.keep s.radial.profile s.radial.scale <= 
        Cfixed*(K+Cmass+1)*diagonalControl s.radial.profile*(p.control U)^2*
          (1+abs t+height)^Jout*Z^(s.width+efinal)) atTop := by
  classical
  choose d L hd hL hLupper Psi hsPsi hnPsi Sdiag Stail Cdiag Ctail hCd hCt hstage using
    @KappaHalfHighAssembly.actual_high_source_split
      alpha inferInstance inferInstance M inferInstance H hH
      Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bPhi rho eps Mcap Bmask epsdiag Xi saving k0
      ha hlo hhi hbPhi hrho heps hM hBmask hbslot hepsdiag hXi hk0
  refine Exists.intro L (And.intro hL (And.intro hLupper
    (Exists.intro Psi (And.intro hsPsi (And.intro hnPsi ?_)))))
  intro degree S Jmass Smass
  choose Ju Jr Uu Ur Cu Cr hCu hCr hbound using hstage degree S
  let U:Finset (Prod Nat Nat):=insert (0,0) (Union.union (Union.union Smass Uu) Ur)
  let Jout:Nat:=Jmass+Ju+Jr
  let P:Real:=(profileBound Wslot hcSlot aslot bslot lo hi haslot hsSlot)^(2*Fintype.card alpha)
  let D:Real:=Cdiag*P*Sdiag.sup (schwartzSeminormFamily Real Real Complex) Psi
  let T:Real:=Ctail*P*Stail.sup (schwartzSeminormFamily Real Real Complex) Psi
  have hP:0 <= P:=pow_nonneg (zero_le_one.trans
    (profileBound_ge_one Wslot hcSlot aslot bslot lo hi haslot hsSlot)) _
  have hD:0 <= D:=by dsimp [D];positivity
  have hT:0 <= T:=by dsimp [T];positivity
  let Cfixed:Real:=Cu+2*Cr+2*D+2*T+2
  have hCfixed:0<Cfixed:=by dsimp [Cfixed];positivity
  refine Exists.intro Jout (Exists.intro U (Exists.intro Cfixed (And.intro hCfixed ?_)))
  filter_upwards [hbound] with Z hZ
  refine And.intro hZ.1 ?_
  intro e emass efinal Lslot k eta0 Q K Cmass he hK hCmass hefinal hmassFinal hdiagFinal htailFinal
    hlow theta w sigma freq t height hw hwL hSigmaLo hSigmaHi hheight hfreq hk s hQ hwidthLo hwidth
    p X1 X2 hX1 hX2 hlarge hcap
  dsimp only
  intro hphysical
  let inp:=balancedInput M H hH eta0 theta Wslot hcSlot aslot bslot lo hi haslot hsSlot
    w sigma freq (fun i => And.intro (hSigmaLo i) (hSigmaHi i)) s p ha t X1 X2 hX1 hX2
  have hh:=hZ.2 e Lslot k eta0 Q K he hK hlow theta w sigma freq t height hw hwL hSigmaLo hSigmaHi
    hheight hfreq hk s hQ hwidthLo hwidth p X1 X2 hX1 hX2 hlarge hcap
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hscale:0 <= s.radial.scale:=s.radial.scale_pos.le
  have hdg:=diagonalControl_nonneg s.radial.profile
  have hbase : 1 <= 1+abs t+height := by linarith [abs_nonneg t]
  have hpowOne (n : Nat) : 1 <= (1+abs t+height)^n := by
    induction n with
    | zero => simp only [pow_zero]; exact le_rfl
    | succ n ih =>
      rw [pow_succ]
      nlinarith [mul_nonneg (sub_nonneg.mpr ih) (sub_nonneg.mpr hbase)]
  let F:Real:=(p.control U)^2*(1+abs t+height)^Jout*Z^(s.width+efinal)
  have hF:0 <= F:=by dsimp [F];positivity
  have henv (Sj:Finset (Prod Nat Nat))(jj:Nat)(ej:Real)(hSj:Sj <= U)(hjj:jj <= Jout)(hej:ej <= efinal):
      (p.control Sj)^2*(1+abs t+height)^jj*Z^(s.width+ej) <= F:=by
    have hp:=profile_control_mono p hSj
    have hp0:=p.control_nonneg Sj
    have hj : (1+abs t+height)^jj <= (1+abs t+height)^Jout := by gcongr
    have hex:=Real.rpow_le_rpow_of_exponent_le hZ.1.le (show s.width+ej <= s.width+efinal by linarith)
    dsimp [F]
    gcongr
  have hu:Uu <= U:=by intro x hx;simp only [U,Finset.mem_insert,Finset.mem_union];tauto
  have hr:Ur <= U:=by intro x hx;simp only [U,Finset.mem_insert,Finset.mem_union];tauto
  have hm:Smass <= U:=by intro x hx;simp only [U,Finset.mem_insert,Finset.mem_union];tauto
  have hju:Ju <= Jout:=by dsimp [Jout];omega
  have hjr:Jr <= Jout:=by dsimp [Jout];omega
  have hjm:Jmass <= Jout:=by dsimp [Jout];omega
  have huni:Cu*(K+1) <= Cfixed*(K+Cmass+1):=by
    dsimp [Cfixed]
    nlinarith only [hCr.le,hD,hT,hK,mul_nonneg hCr.le hK,mul_nonneg hD hK,mul_nonneg hT hK,
      mul_nonneg hCmass hCfixed.le]
  rcases hh with hunbalanced | hrest
  next =>
    change _ <= Cu*(K+1)*diagonalControl s.radial.profile*(p.control Uu)^2*
        (1+abs t+height)^Ju*Z^(s.width+e+eps) at hunbalanced
    have heq:=henv Uu Ju (e+eps) hu hju hefinal
    have hh':=mul_le_mul_of_nonneg_left heq (show 0 <= Cu*(K+1)*diagonalControl s.radial.profile by positivity)
    have hc:=mul_le_mul_of_nonneg_right huni (mul_nonneg hdg hF)
    apply hunbalanced.trans
    dsimp [F] at hh' hc
    rw [show s.width+e+eps=s.width+(e+eps) by ring]
    nlinarith only [hh',hc]
  next =>
    have hfour := hrest.1
    have hsource := hrest.2
    have hmass:=hphysical hfour
    have hmEnv:=henv Smass Jmass emass hm hjm hmassFinal
    have hmass':physicalMass inp s.puncture 1 fixedBadMask 1 Psi s.radial.scale Z Xi/
        CenteredMomentAmplificationChildInput.volume inp <= Cmass*F:=by
      apply hmass.trans
      convert mul_le_mul_of_nonneg_left hmEnv hCmass using 1 ; ring
    have hplain:(plainControl inp (p.profile 0) (p.profile 1))^2 <= P*(p.control U)^2:=by
      have hc:=balanced_control M H hH eta0 theta Wslot hcSlot aslot bslot lo hi haslot hsSlot
        w sigma freq (fun i => And.intro (hSigmaLo i) (hSigmaHi i)) s p ha t X1 X2 hX1 hX2
        (Fintype.card alpha) le_rfl U
      have h00:Membership.mem U (0,0):=Finset.mem_insert_self _ _
      simpa only [Finset.insert_eq_of_mem h00] using hc
    have hheight1 : 1 <= (1+abs t+height)^Jout := hpowOne Jout
    have hscalePower (x:Real)(hx:x <= efinal):s.radial.scale*Z^x <= Z^(s.width+efinal):=by
      rw [s.scale_eq,<-Real.rpow_add hz]
      exact Real.rpow_le_rpow_of_exponent_le hZ.1.le (by unfold NaturalState.width;linarith [s.character_nonneg])
    have hterm (c A x:Real)(hc:0 <= c)(hA:0 <= A)(hx:x <= efinal):
        c*(plainControl inp (p.profile 0) (p.profile 1))^2*A*s.radial.scale*Z^x <= c*P*A*F:=by
      calc
        _ <= c*(P*(p.control U)^2)*A*(s.radial.scale*Z^x):=by rw [<-mul_assoc];gcongr
        _ <= c*(P*(p.control U)^2)*A*Z^(s.width+efinal):=by gcongr;exact hscalePower x hx
        _ <= c*P*A*F:=by
          calc
            _ = (c*P*A*(p.control U)^2*Z^(s.width+efinal))*1 := by ring
            _  <=  (c*P*A*(p.control U)^2*Z^(s.width+efinal))*
                (1+abs t+height)^Jout := mul_le_mul_of_nonneg_left hheight1 (by positivity)
            _ = c*P*A*F := by dsimp [F]; ring
    have hdterm:=hterm Cdiag (Sdiag.sup (schwartzSeminormFamily Real Real Complex) Psi) epsdiag hCd.le (apply_nonneg _ _) hdiagFinal
    have htterm:=hterm Ctail (Stail.sup (schwartzSeminormFamily Real Real Complex) Psi) (-saving) hCt.le (apply_nonneg _ _) htailFinal
    have hrEnv:=henv Ur Jr (e+eps) hr hjr hefinal
    have href:=mul_le_mul_of_nonneg_left hrEnv (show 0 <= 2*Cr*(K+1)*diagonalControl s.radial.profile by positivity)
    have hsum:=mul_le_mul_of_nonneg_left (add_le_add (add_le_add hmass' hdterm) htterm)
      (show 0 <= 2*diagonalControl s.radial.profile by positivity)
    have hcoeff:2*Cmass+2*D+2*T+2*Cr*(K+1) <= Cfixed*(K+Cmass+1):=by
      dsimp [Cfixed]
      nlinarith only [hCu.le,hK,mul_nonneg hCu.le hK,mul_nonneg hCu.le hCmass,mul_nonneg hCr.le hCmass,
        mul_nonneg hD hK,mul_nonneg hD hCmass,mul_nonneg hT hK,mul_nonneg hT hCmass]
    have hfinish:=mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hdg hF)
    apply hsource.trans
    change _ <= Cfixed*(K+Cmass+1)*diagonalControl s.radial.profile*(p.control U)^2*
      (1+abs t+height)^Jout*Z^(s.width+efinal)
    dsimp [D,T,F] at hsum href hfinish
    change _ <= _ at hsum
    change 2*Cr*(K+1)*diagonalControl s.radial.profile*((p.control Ur)^2*
      (1+abs t+height)^Jr*Z^(s.width+(e+eps))) <= _ at href
    change 2*diagonalControl s.radial.profile*(_+_+_)+
      2*Cr*(K+1)*diagonalControl s.radial.profile*(p.control Ur)^2*
      (1+abs t+height)^Jr*Z^(s.width+e+eps) <= _
    have hex:s.width+e+eps=s.width+(e+eps):=by ring
    rw [hex]
    nlinarith only [hsum,href,hfinish]

end SevenEighths.KappaHalfHighBound

end

end OAI

