/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Energy.ReferenceProfileBudget
import OAI.NumberTheory.DirichletL.Energy.ReferenceScalarReserve
import PrimeFactorOscillations.Assembly.DetectorPackets.KappaHalfOriginalEnergy

/-!
# KappaHalfOriginalPower

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

All scalar, conductor, deletion and profile costs are absorbed at every
fixed kappa0 > 1/2. The actual PositiveLowAt estimate is still an input.
-/

set_option maxHeartbeats 800000

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.KappaHalfOriginalPower

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

theorem original_reference_power
    (Wslot : Real -> Complex) (aslot bslot lo hi : Real)
    (haslot : 0 < aslot)
    (hsSlot : Function.support Wslot <= Set.Icc aslot bslot)
    (hcSlot : Continuous Wslot)
    (a b bPhi rho eps Mcap Bmask k0 : Real)
    (ha : 0 < a) (hlo : a <= 1 / 4) (hhi : 1 <= b)
    (hbPhi : 0 < bPhi) (hrho : 0 < rho) (heps : 0 < eps)
    (hM : 0 <= Mcap) (hBmask : 0 <= Bmask) (hk0 : 1 / 2 < k0) :
    exists d xi L defect : Real,
      0 < d /\ 0 < xi /\ 0 < defect /\ xi <= rho / 100 /\ defect <= rho / 100 /\
      Mcap + Bmask + xi <= L /\
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
      forall W1 W2 : SchwartzMap Real Complex,
      Function.support (W1 : Real -> Complex) <= Set.Icc a b ->
      Function.support (W2 : Real -> Complex) <= Set.Icc a b ->
      forall X1 X2 : Real, 0 < X1 -> 0 < X2 ->
      5 * s.width / 6 - defect <= Real.logb Z (X1 * X2) + Finset.univ.sum w ->
      Real.logb Z (X1 * X2) + Finset.univ.sum w +
        (6 * k - 1) * Finset.univ.sum w <= s.width ->
      energy s.character s.mask 1 t W1 W2
        (fun i => primePool M H bslot (Z ^ (w i)))
        (fun i I => idealCoeff (relativeCharacter M H hH eta0 (theta i)) I *
          HeckePrimeAnnular.annularWeight Wslot (Z ^ (w i)) (sigma i) (freq i) I)
        (fun i => Z ^ (w i)) (comparisonFirst Z s.width)
        (comparisonSecond Z s.width X1 X2)
        s.radial.keep s.radial.profile s.radial.scale <=
      C * (K + 1) * diagonalControl s.radial.profile *
        (sourceControl U W1 * sourceControl U W2) ^ 2 *
        (1 + abs t + height) ^ J * Z ^ (s.width + eps)) atTop := by
  set_option maxRecDepth 100 in
    classical
    let rhoSmall : Real := (2 * k0 - 1) * rho / (4 * k0)
    have hkpos : 0 < k0 := by linarith
    have hrSmall : 0 < rhoSmall := by
      dsimp only [rhoSmall]
      exact div_pos (mul_pos (by linarith) hrho) (by linarith)
    have hrEq : 4 * k0 * rhoSmall = (2 * k0 - 1) * rho := by
      dsimp only [rhoSmall]
      field_simp
    have hrLe : rhoSmall <= rho := by
      nlinarith [mul_pos (by linarith : 0 < 2 * k0 + 1) hrho]
    let defect : Real := rhoSmall / 100
    have hdefect : 0 < defect := by dsimp only [defect]; positivity
    have hdefectLe : defect <= rho / 100 := by dsimp only [defect]; linarith
    apply Exists.elim (exists_reference_reserve rhoSmall eps Mcap Bmask bPhi
      hrSmall heps hM hBmask)
    intro d hs1
    apply Exists.elim hs1
    intro xi hs2
    apply Exists.elim hs2
    intro saving hs3
    apply Exists.elim hs3
    intro L hs4
    apply Exists.elim hs4
    intro Cscalar hs5
    have hd := hs5.1
    have hxi := hs5.2.1
    have hCs := hs5.2.2.2.1
    have hxiSmall := hs5.2.2.2.2.1
    have hL := hs5.2.2.2.2.2.1
    have hscalar := hs5.2.2.2.2.2.2
    have hxiRho : xi <= rho / 100 := by linarith
    refine Exists.intro d (Exists.intro xi (Exists.intro L (Exists.intro defect
      (And.intro hd (And.intro hxi (And.intro hdefect (And.intro hxiRho
        (And.intro hdefectLe (And.intro hL ?_)))))))))
    intro degree S
    apply Exists.elim (@KappaHalfOriginalEnergy.original_energy_from_low
      alpha inferInstance inferInstance M inferInstance H hH
      d hd Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bPhi d xi defect saving Mcap Bmask L k0 ha hlo hhi hbPhi hd hxi
      hdefect.le hBmask hL hk0 2 (by norm_num) degree S)
    intro n ho1
    apply Exists.elim ho1
    intro T ho2
    apply Exists.elim ho2
    intro Dchild ho3
    have hDc := ho3.1
    apply Exists.elim ho3.2
    intro nlong ho4
    apply Exists.elim ho4
    intro Slong ho5
    apply Exists.elim ho5
    intro Cref ho6
    apply Exists.elim ho6
    intro Dref ho7
    apply Exists.elim ho7
    intro Cweight ho8
    have hCr := ho8.1
    have hDr := ho8.2.1
    have hCw := ho8.2.2.1
    apply Exists.elim (reference_envelopes a b ha S T Slong degree n nlong
      Cref Dchild Dref hCr hDc hDr)
    intro J hp1
    apply Exists.elim hp1
    intro U hp2
    apply Exists.elim hp2
    intro Cprofile hp3
    have hCp := hp3.1
    have hprofile := hp3.2
    refine Exists.intro J (Exists.intro U (Exists.intro (Cweight * Cprofile * Cscalar)
      (And.intro (by positivity) ?_)))
    filter_upwards [ho8.2.2.2] with Z hZ
    refine And.intro hZ.1 ?_
    intro Lslot k eta0 Q K hK hlow theta w sigma freq t height
      hw hwL hslo hshi hheight hfreq hk s hQ hsLower hs
      W1 W2 hsW1 hsW2 X1 X2 hX1 hX2 hlarge hcap
    have hres1 : (6 * k0 - 1) * xi + (6 * k0 + 1) * defect <=
        12 * k0 * rhoSmall / 100 := by
      have hh := mul_le_mul_of_nonneg_left hxiSmall
        (by linarith : 0 <= 6 * k0 - 1)
      dsimp only [defect]
      nlinarith
    have hres2 : 12 * k0 * rhoSmall / 100 <= (6 * k0 - 3) * s.width / 6 := by
      have hh := mul_nonneg (by linarith : 0 <= 6 * k0 - 3)
        (sub_nonneg.mpr hsLower)
      nlinarith
    have hres := hres1.trans hres2
    have hh := hZ.2 Lslot d k eta0 Q K hK hlow theta w sigma freq t height
      hw hwL hslo hshi hheight hfreq hk s hQ hs hres
      W1 W2 hsW1 hsW2 X1 X2 hX1 hX2 hlarge hcap
    have hsum : 0 <= Finset.univ.sum w := Finset.sum_nonneg (fun i _ => hw i)
    have hj := KappaHalfReflection.joint_slot_budget s.width (Real.logb Z (X1 * X2))
      (Finset.univ.sum w) k k0 xi defect hk0 hk hsum hlarge
      (by nlinarith [hcap]) hres
    have hsumcap : Finset.univ.sum w <= Mcap := by linarith [s.width_nonneg]
    have hledger := hscalar Z hZ.1.le s hs alpha w hsumcap
    have hp := hprofile W1 W2 hsW1 hsW2 t height hheight
    dsimp only at hp
    let A := Cprofile * (sourceControl U W1 * sourceControl U W2) ^ 2 *
      (1 + abs t + height) ^ J
    let E := (K + 1) * diagonalControl s.radial.profile * A
    have hdiag : 0 <= diagonalControl s.radial.profile := by
      unfold diagonalControl
      positivity
    have hA : 0 <= A := by dsimp only [A]; positivity
    have hE : 0 <= E := by dsimp only [E]; positivity
    have hdir : K * diagonalControl s.radial.profile *
        ((CenteredMomentEnergyReferenceChild.independentProfiles ha W1 W2 hsW1 hsW2 t t).control S) ^ 2 *
        (1 + abs t + height) ^ degree <= E := by
      have ht := mul_le_mul_of_nonneg_left hp.1 (mul_nonneg hK hdiag)
      have hkE : K * diagonalControl s.radial.profile * A <= E :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hdiag) hA
      apply le_trans _ hkE
      convert ht using 1; ring
    have hmain : Cref * (sourceControl Slong W2) ^ 2 * (1 + norm t) ^ (2 * nlong) *
        (K * diagonalControl s.radial.profile * Dchild * (sourceControl T W1) ^ 2 *
          (1 + abs t + height) ^ (degree + 2 * n)) <= E := by
      have ht := mul_le_mul_of_nonneg_left hp.2.1 (mul_nonneg hK hdiag)
      have hkE : K * diagonalControl s.radial.profile * A <= E :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hdiag) hA
      apply le_trans _ hkE
      convert ht using 1; ring
    have herr : Dref * (sourceControl Slong W2) ^ 2 * (1 + norm t) ^ (2 * nlong) *
        ((schwartzSeminormFamily Real Real Complex (0, 0)) W1) ^ 2 *
        diagonalControl s.radial.profile <= E := by
      have ht := mul_le_mul_of_nonneg_left hp.2.2 hdiag
      have hkE : diagonalControl s.radial.profile * A <= E := by
        calc
          _ = (1 : Real) * diagonalControl s.radial.profile * A := by ring
          _ <= (K + 1) * diagonalControl s.radial.profile * A :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hK) hdiag) hA
      apply le_trans _ hkE
      convert ht using 1; ring
    have hz : 0 < Z := zero_lt_one.trans hZ.1
    have hlog : 0 <= Real.log Z := (Real.log_pos hZ.1).le
    have hLpos : 0 <= L := by linarith
    let P := Z ^ (s.width + d)
    let Qmain := (max 1 ((fixedConductorFactor : Real) * bPhi * Z ^ s.width)) ^ d *
      (1 + 2 * (L * Real.log Z)) * Z ^ (s.width + d)
    let Qerror := (max 1 ((fixedConductorFactor : Real) * bPhi * Z ^ s.width)) ^ (2 * d) *
      Z ^ (-2 * saving) * max 1 s.radial.scale * Z ^ (s.width / 4) *
      Finset.univ.prod (fun i => Z ^ (w i))
    have hP : 0 <= P := by dsimp only [P]; positivity
    have hQmain : 0 <= Qmain := by dsimp only [Qmain]; positivity
    have hQerror : 0 <= Qerror := by dsimp only [Qerror]; positivity
    have htotal := add_le_add (add_le_add (mul_le_mul_of_nonneg_right hdir hP)
      (mul_le_mul_of_nonneg_right hmain hQmain)) (mul_le_mul_of_nonneg_right herr hQerror)
    apply hh.trans
    have hfirst := mul_le_mul_of_nonneg_left htotal
      (show 0 <= Cweight * (s.puncture.radical.absNorm : Real) ^ d by positivity)
    have hlast := mul_le_mul_of_nonneg_left hledger (mul_nonneg hCw.le hE)
    refine le_trans ?_ (hlast.trans_eq ?_)
    next =>
      dsimp only [P, Qmain, Qerror] at hfirst
      convert hfirst using 1 <;> (try dsimp only [E, A]) <;> ring
    next =>
      dsimp only [E, A]
      ring
  
end SevenEighths.KappaHalfOriginalPower

end

end OAI
