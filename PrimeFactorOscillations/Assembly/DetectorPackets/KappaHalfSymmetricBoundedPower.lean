/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Energy.OriginalHighReflectionSymmetric
import PrimeFactorOscillations.Assembly.DetectorPackets.KappaHalfUnbalancedBoundedPower

/-!
# KappaHalfSymmetricBoundedPower

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

Bounded separated power for the original short-input branch.
The child error exponent remains arbitrary and nonnegative. The checked
raw-energy owner supplies all scalar, conductor, deletion and profile
terms. PositiveLowAt remains an explicit input; no global exponent gain
is asserted by this module.
-/

set_option maxHeartbeats 800000

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.KappaHalfSymmetricBoundedPower

open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceScalarReserve CenteredMomentEnergyReferenceProfileBudget
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

theorem original_unbalanced_from_low
    (Wslot : Real -> Complex) (aslot bslot lo hi : Real)
    (haslot : 0 < aslot)
    (hsSlot : Function.support Wslot <= Set.Icc aslot bslot)
    (hcSlot : Continuous Wslot)
    (a b bPhi rho eps Mcap Bmask k0 : Real)
    (ha : 0 < a) (hlo : a <= 1 / 4) (hhi : 1 <= b)
    (hbPhi : 0 < bPhi) (hrho : 0 < rho) (heps : 0 < eps)
    (hM : 0 <= Mcap) (hBmask : 0 <= Bmask) (hk0 : 1 / 2 < k0) :
    exists d xi L : Real,
      0 < d /\ 0 < xi /\ xi <= rho / 100 /\
      Mcap + Bmask + xi <= L /\ L <= Mcap + Bmask + rho / 100 /\
    forall degree : Nat, forall S : Finset (Prod Nat Nat),
    exists J : Nat, exists U : Finset (Prod Nat Nat), exists C : Real, 0 < C /\
      Filter.Eventually (fun Z : Real => 1 < Z /\
      forall (e Lslot k : Real) (eta0 : Character) (Q : Ideal O) (K : Real),
      0 <= e -> 0 <= K ->
      @PositiveLowAt alpha M inferInstance H hH Wslot bslot a b bPhi Bmask L Lslot lo hi
        Mcap e k Z eta0 Q degree S K ->
      forall (theta : alpha -> RayQuotient.Characters M H) (w sigma freq : alpha -> Real)
        (t height : Real),
      (forall i, 0 <= w i) -> (forall i, w i <= Lslot) ->
      (forall i, lo <= sigma i) -> (forall i, sigma i <= hi) ->
      0 <= height -> (forall i, abs (freq i) <= height) -> k0 <= k ->
      forall s : NaturalState Z Bmask bPhi,
      s.fixedModulus = internalQ Q eta0 -> rho <= s.width -> s.width <= Mcap ->
      forall W1 W2 : SchwartzMap Real Complex,
      Function.support (W1 : Real -> Complex) <= Set.Icc a b ->
      Function.support (W2 : Real -> Complex) <= Set.Icc a b ->
      forall X1 X2 : Real, 0 < X1 -> 0 < X2 ->
      min (length Z X1) (length Z X2) <= s.width / 4 ->
      5 * s.width / 6 <= length Z X1 + length Z X2 + Finset.univ.sum w ->
      length Z X1 + length Z X2 + 6 * k * Finset.univ.sum w <= s.width ->
      energy s.character s.mask 1 t W1 W2
        (fun i => primePool M H bslot (Z ^ (w i)))
        (fun i I => idealCoeff (relativeCharacter M H hH eta0 (theta i)) I *
          HeckePrimeAnnular.annularWeight Wslot (Z ^ (w i)) (sigma i) (freq i) I)
        (fun i => Z ^ (w i)) X1 X2
        s.radial.keep s.radial.profile s.radial.scale <=
      C * (K + 1) * diagonalControl s.radial.profile *
        (sourceControl U W1 * sourceControl U W2) ^ 2 *
        (1 + abs t + height) ^ J * Z ^ (s.width + e + eps)) atTop := by
  classical
  choose d xi L hd hxi hxirho hL hLupper hstage using
    @KappaHalfUnbalancedBoundedPower.original_reference_power_unbalanced_bounded
      alpha inferInstance inferInstance M inferInstance H hH
      Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bPhi rho eps Mcap Bmask k0 ha hlo hhi hbPhi hrho heps hM hBmask hk0
  refine Exists.intro d (Exists.intro xi (Exists.intro L ?_))
  refine And.intro hd (And.intro hxi (And.intro hxirho
    (And.intro hL (And.intro hLupper ?_))))
  intro degree S
  choose J U C hC hbound using hstage degree S
  refine Exists.intro J (Exists.intro U (Exists.intro C (And.intro hC ?_)))
  filter_upwards [hbound] with Z hZ
  refine And.intro hZ.1 ?_
  intro e Lslot k eta0 Q K he hK hlow theta w sigma freq t height
    hw hwL hslo hshi hheight hfreq hk s hQ hsLower hs
    W1 W2 hsW1 hsW2 X1 X2 hX1 hX2 hshort hlarge hcap
  cases min_le_iff.mp hshort with
  | inl hshort =>
    exact hZ.2 e Lslot k eta0 Q K he hK hlow theta w sigma freq t height
      hw hwL hslo hshi hheight hfreq hk s hQ hsLower hs
      W1 W2 hsW1 hsW2 X1 X2 hX1 hX2 hshort hlarge hcap
  | inr hshort =>
    rw [CenteredMomentEnergyOriginalHighReflectionSymmetric.energy_swap]
    have hh := hZ.2 e Lslot k eta0 Q K he hK hlow theta w sigma freq t height
      hw hwL hslo hshi hheight hfreq hk s hQ hsLower hs
      W2 W1 hsW2 hsW1 X2 X1 hX2 hX1 hshort (by linarith) (by linarith)
    simpa only [mul_comm (sourceControl U W2) (sourceControl U W1)] using hh

end SevenEighths.KappaHalfSymmetricBoundedPower

end

end OAI

