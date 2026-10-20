/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Energy.ReferenceDeletionEnergy
import PrimeFactorOscillations.Assembly.DetectorPackets.KappaHalfUnbalancedDeletedEnergy

/-!
# KappaHalfUnbalancedOriginalEnergy

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

Weighted restoration for the original short input at every fixed kappa0 > 1/2.
The original-input lengths, low-band hypothesis and all errors remain explicit.
-/


namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.KappaHalfUnbalancedOriginalEnergy

open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceChild CenteredMomentNaturalFixedRaySource
open CenteredMomentNaturalRowSource CenteredMomentCommonMaskEnergy
open CenteredMomentCommonMaskExpansion CenteredMomentOriginalRadialComparison
open CenteredMomentAllocatedNaturalRadial CenteredMomentFiniteProfileExceptional
open QuadraticInitialBound CenteredMomentPrimeSlot
open CenteredMomentEnergyReferenceDeletionEnergy CenteredMomentInductionEnergy

local notation "O" => HeckeFamily.O

variable {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
variable (M : Ideal O) [NeZero M]
local instance : Finite (HasQuotient.Quotient O M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (Units (HasQuotient.Quotient O M)))
  (hH : RayOrthogonality.globalUnits M <= H)

theorem original_energy_unbalanced_from_low
    (epsilonDelete : Real) (hepsilonDelete : 0 < epsilonDelete)
    (Wslot : Real -> Complex) (aslot bslot lo hi : Real)
    (haslot : 0 < aslot)
    (hsSlot : Function.support Wslot <= Set.Icc aslot bslot)
    (hcSlot : Continuous Wslot)
    (a b bPhi epsilon xi saving Mcap Bmask L k0 : Real)
    (ha : 0 < a) (hlo : a <= 1 / 4) (hhi : 1 <= b)
    (hbPhi : 0 < bPhi) (hepsilon : 0 < epsilon) (hxi : 0 < xi)
    (hBmask : 0 <= Bmask)
    (hL : Mcap + Bmask + xi <= L) (hk0 : 1 / 2 < k0)
    (B : Nat) (hB : 2 <= B) (degree : Nat) (S : Finset (Prod Nat Nat)) :
    exists n : Nat, exists T : Finset (Prod Nat Nat), exists Dchild : Real, 0 < Dchild /\
    exists nlong : Nat, exists Slong : Finset (Prod Nat Nat), exists C D Cweight : Real,
      0 < C /\ 0 < D /\ 0 < Cweight /\
      Filter.Eventually (fun Z : Real => 1 < Z /\
      forall (Lslot eps k : Real) (eta0 : Character) (Q : Ideal O) (K : Real), 0 <= K ->
      @PositiveLowAt alpha M inferInstance H hH Wslot bslot a b bPhi Bmask L Lslot lo hi
        Mcap eps k Z eta0 Q degree S K ->
      forall (theta : alpha -> RayQuotient.Characters M H) (w sigma freq : alpha -> Real)
        (t height : Real),
      (forall i, 0 <= w i) -> (forall i, w i <= Lslot) ->
      (forall i, lo <= sigma i) -> (forall i, sigma i <= hi) ->
      0 <= height -> (forall i, abs (freq i) <= height) -> k0 <= k ->
      forall s : NaturalState Z Bmask bPhi,
      s.fixedModulus = internalQ Q eta0 -> s.width <= Mcap ->
      (6 * k0 - 1) * xi <= (6 * k0 - 3) * s.width / 6 ->
      forall W1 W2 : SchwartzMap Real Complex,
      forall hs1 : Function.support (W1 : Real -> Complex) <= Set.Icc a b,
      forall hs2 : Function.support (W2 : Real -> Complex) <= Set.Icc a b,
      forall X1 X2 : Real, 0 < X1 -> 0 < X2 ->
      length Z X1 <= s.width / 4 ->
      5 * s.width / 6 <= length Z X1 + length Z X2 + Finset.univ.sum w ->
      length Z X1 + length Z X2 + 6 * k * Finset.univ.sum w <= s.width ->
      energy s.character s.mask 1 t W1 W2
        (fun i => primePool M H bslot (Z ^ (w i)))
        (fun i I => idealCoeff (relativeCharacter M H hH eta0 (theta i)) I *
          HeckePrimeAnnular.annularWeight Wslot (Z ^ (w i)) (sigma i) (freq i) I)
        (fun i => Z ^ (w i)) X1 X2
        s.radial.keep s.radial.profile s.radial.scale <=
      Cweight * (s.puncture.radical.absNorm : Real) ^ epsilonDelete * (
        K * diagonalControl s.radial.profile *
          ((independentProfiles ha W1 W2 hs1 hs2 t t).control S) ^ 2 *
          (1 + abs t + height) ^ degree * Z ^ (s.width + eps) +
        (C * (max 1 ((fixedConductorFactor : Real) * bPhi * Z ^ s.width)) ^ epsilon *
          (sourceControl Slong W2) ^ 2 * (1 + norm t) ^ (2 * nlong) *
          (1 + 2 * (L * Real.log Z)) *
          (K * diagonalControl s.radial.profile * Dchild * (sourceControl T W1) ^ 2 *
            (1 + abs t + height) ^ (degree + 2 * n) * Z ^ (s.width + eps)) +
        D * (max 1 ((fixedConductorFactor : Real) * bPhi * Z ^ s.width)) ^ (2 * epsilon) *
          (sourceControl Slong W2) ^ 2 * (1 + norm t) ^ (2 * nlong) * Z ^ (-2 * saving) *
          ((schwartzSeminormFamily Real Real Complex (0, 0)) W1) ^ 2 *
          diagonalControl s.radial.profile * max 1 s.radial.scale * (Z ^ (s.width / 4)) *
          Finset.univ.prod (fun i => Z ^ (w i))))) atTop := by
  classical
  apply Exists.elim (CenteredMomentRayMaskedFloor.slot_coefficient_bounds
    Wslot aslot bslot lo hi haslot hsSlot hcSlot)
  intro Bslot hslotData
  have hBslot := hslotData.1
  have hslot := hslotData.2
  apply Exists.elim (original_energy_weighted_deletion
    (fun _ : alpha => bslot) (fun _ => Bslot) (fun _ => hBslot.le)
    epsilonDelete hepsilonDelete)
  intro Cweight hweightData
  have hCweight := hweightData.1
  have hweight := hweightData.2
  apply Exists.elim (@KappaHalfUnbalancedDeletedEnergy.deleted_energy_unbalanced_from_low
    alpha inferInstance inferInstance M inferInstance H hH
    Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bPhi epsilon xi saving Mcap Bmask L k0
    ha hlo hhi hbPhi hepsilon hxi hBmask hL hk0 B hB degree S)
  intro n h1
  apply Exists.elim h1
  intro T h2
  apply Exists.elim h2
  intro Dchild h3
  have hDc := h3.1
  apply Exists.elim h3.2
  intro nlong h4
  apply Exists.elim h4
  intro Slong h5
  apply Exists.elim h5
  intro C h6
  apply Exists.elim h6
  intro D h7
  have hC := h7.1
  have hD := h7.2.1
  refine Exists.intro n (Exists.intro T (Exists.intro Dchild
    (And.intro hDc (Exists.intro nlong (Exists.intro Slong
      (Exists.intro C (Exists.intro D (Exists.intro Cweight
        (And.intro hC (And.intro hD (And.intro hCweight ?_)))))))))))
  filter_upwards [h7.2.2] with Z hZ
  refine And.intro hZ.1 ?_
  intro Lslot eps k eta0 Q K hK hlow theta w sigma freq t height
    hw hwL hslo hshi hheight hfreq hk s hQ hs hres
    W1 W2 hs1 hs2 X1 X2 hX1 hX2 hshort hlarge hcap
  have hZpos : 0 < Z := zero_lt_one.trans hZ.1
  apply hweight Z Bmask bPhi a b s W1 W2 ha (by linarith) hs1 hs2
    (fun i => primePool M H bslot (Z ^ (w i)))
    (fun i I => idealCoeff (relativeCharacter M H hH eta0 (theta i)) I *
      HeckePrimeAnnular.annularWeight Wslot (Z ^ (w i)) (sigma i) (freq i) I)
    (fun i => Z ^ (w i)) t X1 X2 _ 0
  next =>
    intro i I hI
    exact (Finset.mem_filter.mp hI).2.1
  next =>
    intro i
    exact Real.rpow_pos_of_pos hZpos _
  next =>
    intro i I hI
    have hpI : Prime I := (Finset.mem_filter.mp hI).2.1
    have hh := (hslot (relativeCharacter M H hH eta0 (theta i)) (Z ^ (w i))
      (sigma i) (freq i) 0 (Real.rpow_pos_of_pos hZpos _) (hslo i) (hshi i)
      I hpI.ne_zero).1
    simpa only [heightCoefficient, Complex.ofReal_zero, mul_zero, Complex.cpow_zero, mul_one]
      using hh
  next =>
    intro i I hI hn
    have hpI : Prime I := (Finset.mem_filter.mp hI).2.1
    have hh := (hslot (relativeCharacter M H hH eta0 (theta i)) (Z ^ (w i))
      (sigma i) (freq i) 0 (Real.rpow_pos_of_pos hZpos _) (hslo i) (hshi i)
      I hpI.ne_zero).2
    apply hh
    simpa only [heightCoefficient, Complex.ofReal_zero, mul_zero, Complex.cpow_zero, mul_one]
      using hn
  next =>
    exact hX1
  next =>
    exact hX2
  next =>
    have hdiag : 0 <= diagonalControl s.radial.profile := by
      unfold diagonalControl
      positivity
    have hLpos : 0 <= L := by linarith [s.width_nonneg]
    have hlog : 0 <= Real.log Z := (Real.log_pos hZ.1).le
    positivity
  next =>
    norm_num
  next =>
    intro D1 hD1 D2 hD2 J hJ
    simpa only [Real.rpow_zero, mul_one] using hZ.2 Lslot eps k eta0 Q K hK hlow
      theta w sigma freq t height hw hwL hslo hshi hheight hfreq hk s hQ hs hres
      W1 W2 hs1 hs2 X1 X2 hX1 hX2 hshort hlarge hcap D1 hD1 D2 hD2 (Finset.univ \ J)

end SevenEighths.KappaHalfUnbalancedOriginalEnergy

end

end OAI

