/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.KappaHalfOriginalPower

/-!
# KappaHalfLivePower

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

Actual clipped profile rows at every fixed kappa0 > 1/2.
The exact low-band energy input is retained.
-/


namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.KappaHalfLivePower

open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot

local notation "O" => HeckeFamily.O

variable {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
variable (M : Ideal O) [NeZero M]
local instance : Finite (HasQuotient.Quotient O M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (Units (HasQuotient.Quotient O M)))
  (hH : RayOrthogonality.globalUnits M <= H)

theorem original_reference_power_live
    (Wslot : Real -> Complex) (aslot bslot lo hi : Real)
    (haslot : 0 < aslot)
    (hsSlot : Function.support Wslot <= Set.Icc aslot bslot)
    (hcSlot : Continuous Wslot)
    (a b bPhi rho eps Mcap Bmask k0 : Real)
    (ha : 0 < a) (hlo : a <= 1 / 4) (hhi : 1 <= b)
    (hbPhi : 0 < bPhi) (hrho : 0 < rho) (heps : 0 < eps)
    (hM : 0 <= Mcap) (hBmask : 0 <= Bmask) (hk0 : 1 / 2 < k0) :
    exists d xi L : Real,
      0 < d /\ 0 < xi /\ xi <= rho / 100 /\ Mcap + Bmask + xi <= L /\
    forall degree : Nat, forall S : Finset (Prod Nat Nat),
    exists J : Nat, exists U : Finset (Prod Nat Nat), exists C : Real, 0 < C /\
      Filter.Eventually (fun Z : Real => 1 < Z /\
      forall (Lslot k : Real) (eta0 : Character) (Q : Ideal O) (K : Real), 0 <= K ->
      @PositiveLowAt alpha M inferInstance H hH Wslot bslot a b bPhi Bmask L Lslot lo hi
        Mcap d k Z eta0 Q degree S K ->
      forall (theta : alpha -> RayQuotient.Characters M H) (w sigma freq : alpha -> Real)
        (t height : Real),
      (forall i, 0 <= w i) -> (forall i, w i <= Lslot) ->
      (forall i, lo <= sigma i) -> (forall i, sigma i <= hi) ->
      0 <= height -> (forall i, abs (freq i) <= height) -> k0 <= k ->
      forall s : NaturalState Z Bmask bPhi,
      s.fixedModulus = internalQ Q eta0 -> rho <= s.width -> s.width <= Mcap ->
      forall p : Profiles a b,
      forall X1 X2 : Real, 0 < X1 -> 0 < X2 ->
      5 * s.width / 6 <= length Z X1 + length Z X2 + Finset.univ.sum w ->
      length Z X1 + length Z X2 + 6 * k * Finset.univ.sum w <= s.width ->
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i => primePool M H bslot (Z ^ (w i)))
        (fun i I => idealCoeff (relativeCharacter M H hH eta0 (theta i)) I *
          HeckePrimeAnnular.annularWeight Wslot (Z ^ (w i)) (sigma i) (freq i) I)
        (fun i => Z ^ (w i)) X1 X2
        s.radial.keep s.radial.profile s.radial.scale = 0 \/
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i => primePool M H bslot (Z ^ (w i)))
        (fun i I => idealCoeff (relativeCharacter M H hH eta0 (theta i)) I *
          HeckePrimeAnnular.annularWeight Wslot (Z ^ (w i)) (sigma i) (freq i) I)
        (fun i => Z ^ (w i)) (comparisonFirst Z s.width)
        (comparisonSecond Z s.width X1 X2)
        s.radial.keep s.radial.profile s.radial.scale <=
      C * (K + 1) * diagonalControl s.radial.profile *
        (sourceControl U (p.profile 0) * sourceControl U (p.profile 1)) ^ 2 *
        (1 + abs t + height) ^ J * Z ^ (s.width + eps)) atTop := by
  classical
  apply Exists.elim (@KappaHalfOriginalPower.original_reference_power
    alpha inferInstance inferInstance M inferInstance H hH
    Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bPhi rho eps Mcap Bmask k0 ha hlo hhi hbPhi hrho heps hM hBmask hk0)
  intro d h1
  apply Exists.elim h1
  intro xi h2
  apply Exists.elim h2
  intro L h3
  apply Exists.elim h3
  intro defect h4
  have hd := h4.1
  have hxi := h4.2.1
  have hdefect := h4.2.2.1
  have hxiRho := h4.2.2.2.1
  have hL := h4.2.2.2.2.2.1
  have hstage := h4.2.2.2.2.2.2
  apply Exists.elim (CenteredMomentEnergyLiveClippingDefect.endpoint_threshold b defect hdefect)
  intro Z0 hthreshold
  have hendpoint := hthreshold.2
  refine Exists.intro d (Exists.intro xi (Exists.intro L
    (And.intro hd (And.intro hxi (And.intro hxiRho (And.intro hL ?_))))))
  intro degree S
  apply Exists.elim (hstage degree S)
  intro J h5
  apply Exists.elim h5
  intro U h6
  apply Exists.elim h6
  intro C h7
  have hC := h7.1
  refine Exists.intro J (Exists.intro U (Exists.intro C (And.intro hC ?_)))
  filter_upwards [h7.2, eventually_ge_atTop Z0] with Z hZ hZZ
  refine And.intro hZ.1 ?_
  intro Lslot k eta0 Q K hK hlow theta w sigma freq t height
    hw hwL hslo hshi hheight hfreq hk s hQ hsLower hs p X1 X2 hX1 hX2 hlarge hcap
  have hsplit := CenteredMomentEnergyLiveClippingDefect.energy_zero_or_defect
    s.character s.mask 1 t p
    (fun i => primePool M H bslot (Z ^ (w i)))
    (fun i I => idealCoeff (relativeCharacter M H hH eta0 (theta i)) I *
      HeckePrimeAnnular.annularWeight Wslot (Z ^ (w i)) (sigma i) (freq i) I)
    (fun i => Z ^ (w i)) X1 X2 Z s.radial.keep s.radial.profile s.radial.scale
    hZ.1 hX1 hX2
  cases hsplit with
  | inl hz =>
    exact Or.inl hz
  | inr hdef =>
    apply Or.inr
    have hg := CenteredMomentEnergyLiveClippingDefect.raw_gates_of_defect
      Z s.width X1 X2 (Finset.univ.sum w) k defect hZ.1 hX1 hX2
      (hdef.2.trans (hendpoint Z hZZ)) hlarge hcap
    exact hZ.2 Lslot k eta0 Q K hK hlow theta w sigma freq t height
      hw hwL hslo hshi hheight hfreq hk s hQ hsLower hs
      (p.profile 0) (p.profile 1) (p.support 0) (p.support 1)
      X1 X2 hX1 hX2 hg.1 hg.2

end SevenEighths.KappaHalfLivePower

end

end OAI
