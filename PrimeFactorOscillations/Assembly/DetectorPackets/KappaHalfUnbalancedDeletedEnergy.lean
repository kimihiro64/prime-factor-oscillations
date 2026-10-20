/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Energy.ReferenceRobustDeletedEnergy
import PrimeFactorOscillations.Assembly.DetectorPackets.KappaHalfUnbalancedGeometry

/-!
# KappaHalfUnbalancedDeletedEnergy

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

Deleted energy for the original short input at a fixed kappa0>1/2.
All reflection errors, principal energy terms, finite deletions and
character coefficients are retained.
-/


namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.KappaHalfUnbalancedDeletedEnergy

open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceLowReflectionError
open CenteredMomentEnergyReferenceLowDirect CenteredMomentEnergyReferenceChild
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot

local notation "O" => HeckeFamily.O

variable {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
variable (M : Ideal O) [NeZero M]
local instance : Finite (HasQuotient.Quotient O M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (Units (HasQuotient.Quotient O M)))
  (hH : RayOrthogonality.globalUnits M <= H)

theorem deleted_energy_unbalanced_from_low
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
    exists nlong : Nat, exists Slong : Finset (Prod Nat Nat), exists C D : Real,
      0 < C /\ 0 < D /\
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
      forall D1 : Finset (Ideal O),
      Membership.mem (CompletedGauss.primeSupport s.puncture).powerset D1 ->
      forall D2 : Finset (Ideal O),
      Membership.mem (CompletedGauss.primeSupport s.puncture).powerset D2 ->
      forall F : Finset alpha,
      let beta := fun i I => heightCoefficient
        (fun I => idealCoeff (relativeCharacter M H hH eta0 (theta i)) I *
          HeckePrimeAnnular.annularWeight Wslot (Z ^ (w i)) (sigma i) (freq i) I) t I;
      radialEnergy (fun z =>
        polynomial (naturalCharacter s.character z) false W1
          (X1 / ((D1.prod (fun I => I)).absNorm : Real)) 0 t *
        polynomial (naturalCharacter s.character z) false W2
          (X2 / ((D2.prod (fun I => I)).absNorm : Real)) 0 t *
        F.prod (fun i => naturalSlot (naturalCharacter s.character z)
          (primePool M H bslot (Z ^ (w i))) (beta i) (Z ^ (w i))))
        (effectiveState s).radial.keep s.radial.profile s.radial.scale <=
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
          Finset.univ.prod (fun i => Z ^ (w i)))) atTop := by
  classical
  let h := @CenteredMomentEnergyReferenceLowReflectionError.reference_from_low_with_error
    alpha inferInstance inferInstance M inferInstance H hH
    Finset.univ Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bPhi epsilon xi saving (Mcap + Bmask) ha hlo hhi hbPhi hepsilon hxi B hB degree S
  apply Exists.elim h
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
    (And.intro h3.1 (Exists.intro nlong (Exists.intro Slong
      (Exists.intro C (Exists.intro D (And.intro h7.1 (And.intro h7.2.1 ?_)))))))))
  filter_upwards [h7.2.2] with Z hZ
  refine And.intro hZ.1 ?_
  intro Lslot eps k eta0 Q K hK hlow theta w sigma freq t height
    hw hwL hslo hshi hheight hfreq hk s hQ hs hres
    W1 W2 hs1 hs2 X1 X2 hX1 hX2 hshort hlarge hcap D1 hD1 D2 hD2 F
  dsimp only
  let short := Real.logb Z (X1 / ((D1.prod (fun I => I)).absNorm : Real))
  let along := Real.logb Z (X2 / ((D2.prod (fun I => I)).absNorm : Real))
  have hsum : 0 <= F.sum w := Finset.sum_nonneg (fun i _ => hw i)
  have hsumle : F.sum w <= Finset.univ.sum w :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ F) (fun i _ _ => hw i)
  have hTotal : 0 <= Finset.univ.sum w := Finset.sum_nonneg (fun i _ => hw i)
  have hj := KappaHalfReflection.joint_slot_budget s.width
    (length Z X1 + length Z X2) (Finset.univ.sum w) k k0 xi 0 hk0 hk hTotal
    (by simpa only [sub_zero] using hlarge) hcap
    (by simpa only [mul_zero, add_zero] using hres)
  have hWidthPositive : 0 < s.width := by linarith
  have hg := KappaHalfUnbalancedGeometry.unbalanced_deleted_gates s hZ.1
    hWidthPositive hBmask Mcap L X1 X2 (Finset.univ.sum w) (F.sum w) k k0 xi hs hL
    hX1 hX2 hTotal hsum hsumle hk0 hk hxi.le hres hshort hlarge hcap D1 D2 hD1 hD2
  dsimp only at hg
  rw [<- hg.1, <- hg.2.1]
  have hZpos : 0 < Z := zero_lt_one.trans hZ.1
  have hdiag : 0 <= diagonalControl s.radial.profile := by
    unfold diagonalControl
    positivity
  have hlog : 0 <= Real.log Z := (Real.log_pos hZ.1).le
  have hLpos : 0 <= L := by linarith [s.width_nonneg]
  have hpower (G : Finset alpha) :
      G.prod (fun i => Z ^ (w i)) = Z ^ G.sum w := by
    induction G using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty, Real.rpow_zero]
    | @insert i G hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, Real.rpow_add hZpos]
  have hprod : F.prod (fun i => Z ^ (w i)) <= Finset.univ.prod (fun i => Z ^ (w i)) := by
    rw [hpower F, hpower Finset.univ]
    exact Real.rpow_le_rpow_of_exponent_le hZ.1.le hsumle
  cases hg.2.2.2.2.2.2.2 with
  | inl hd =>
    have hdirect := direct_child_from_low M H hH Wslot bslot a b bPhi Bmask L Lslot lo hi
      Mcap eps k Z eta0 Q degree S K hlow hBmask ha F theta w sigma freq t height
      hw hwL hslo hshi hheight hfreq s hQ hs W1 W2 hs1 hs2 (Z ^ short) (Z ^ along)
      (Real.rpow_pos_of_pos hZpos _) (Real.rpow_pos_of_pos hZpos _)
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hg.2.2.2.1)
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hg.2.2.2.2.1) hd.2 hd.1
    exact hdirect.trans (le_add_of_nonneg_right (by positivity))
  | inr hr =>
    have hh := hZ.2 Bmask L Lslot Mcap eps k eta0 Q K hK hlow hBmask F
      (Finset.subset_univ F) theta w sigma freq t height
      hw hwL hslo hshi hheight hfreq s hQ hs W2 W1 hs2 hs1 along short
      hg.2.2.2.2.2.1 hg.2.2.2.2.2.2.1 hg.2.2.2.1 hr.2 hr.1
    dsimp only at hh
    have hswap : (fun z =>
        polynomial (naturalCharacter s.character z) false W1 (Z ^ short) 0 t *
        polynomial (naturalCharacter s.character z) false W2 (Z ^ along) 0 t *
        F.prod (fun i => naturalSlot (naturalCharacter s.character z)
          (primePool M H bslot (Z ^ (w i)))
          (heightCoefficient (fun I => idealCoeff (relativeCharacter M H hH eta0 (theta i)) I *
            HeckePrimeAnnular.annularWeight Wslot (Z ^ (w i)) (sigma i) (freq i) I) t)
          (Z ^ (w i)))) =
      (fun z =>
        polynomial (naturalCharacter s.character z) false W2 (Z ^ along) 0 t *
        polynomial (naturalCharacter s.character z) false W1 (Z ^ short) 0 t *
        F.prod (fun i => naturalSlot (naturalCharacter s.character z)
          (primePool M H bslot (Z ^ (w i)))
          (heightCoefficient (fun I => idealCoeff (relativeCharacter M H hH eta0 (theta i)) I *
            HeckePrimeAnnular.annularWeight Wslot (Z ^ (w i)) (sigma i) (freq i) I) t)
          (Z ^ (w i)))) := by
      funext z
      ring
    rw [hswap]
    apply hh.trans
    apply le_trans _ (le_add_of_nonneg_left (by positivity))
    apply add_le_add
    next =>
      gcongr
      exact hg.2.2.2.2.2.2.1
    next =>
      gcongr
      next =>
        exact hZ.1.le
      next =>
        exact hg.2.2.1

end SevenEighths.KappaHalfUnbalancedDeletedEnergy

end

end OAI
