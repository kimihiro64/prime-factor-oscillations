/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Energy.PositiveHighSourceBounded
import PrimeFactorOscillations.Assembly.DetectorPackets.KappaHalfBoundedLivePower

/-!
# KappaHalfPhysicalEntry

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

Physical-mass entry for the bounded kappa-half reflection chain.
All principal, diagonal, tail, conductor and profile terms are retained.
The actual PositiveLowAt input remains explicit.
-/

set_option maxHeartbeats 800000

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.KappaHalfPhysicalEntry

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

theorem actual_positive_source_entry
    (Wslot : Real -> Complex) (aslot bslot lo hi : Real)
    (haslot : 0 < aslot)
    (hsSlot : Function.support Wslot <= Set.Icc aslot bslot)
    (hcSlot : Continuous Wslot)
    (a b bPhi rho eps Mcap Bmask epsdiag Xi saving k0 : Real)
    (ha : 0 < a) (hlo : a <= 1 / 4) (hhi : 1 <= b)
    (hbPhi : 0 < bPhi) (hrho : 0 < rho) (heps : 0 < eps)
    (hM : 0 <= Mcap) (hBmask : 0 <= Bmask) (hbslot : 0 <= bslot)
    (hepsdiag : 0 < epsdiag) (hXi : 0 < Xi) (hk0 : 1 / 2 < k0) :
    exists d xi L : Real,
      0 < d /\ 0 < xi /\ xi <= rho / 100 /\
      Mcap + Bmask + xi <= L /\ L <= Mcap + Bmask + rho / 100 /\
    exists Psi : SchwartzMap Real Complex,
      Function.support (Psi : Real -> Complex) <= Set.Icc (-1) (bPhi + 1) /\
      (forall x, 0 <= (Psi x).re) /\
    exists Sdiag Stail : Finset (Prod Nat Nat), exists Cdiag Ctail : Real,
      0 < Cdiag /\ 0 < Ctail /\
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
      forall hSigmaLo : (forall i, lo <= sigma i),
      forall hSigmaHi : (forall i, sigma i <= hi),
      0 <= height -> (forall i, abs (freq i) <= height) -> k0 <= k ->
      forall s : NaturalState Z Bmask bPhi,
      s.fixedModulus = internalQ Q eta0 -> rho <= s.width -> s.width <= Mcap ->
      forall (p : Profiles a b) (X1 X2 : Real) (hX1 : 0 < X1) (hX2 : 0 < X2),
      5 * s.width / 6 <= length Z X1 + length Z X2 + Finset.univ.sum w ->
      length Z X1 + length Z X2 + 6 * k * Finset.univ.sum w <= s.width ->
      let inp := balancedInput M H hH eta0 theta Wslot hcSlot aslot bslot lo hi haslot hsSlot
        w sigma freq (fun i => And.intro (hSigmaLo i) (hSigmaHi i))
        s p ha t X1 X2 hX1 hX2;
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        inp.slots inp.toData.coefficient inp.P X1 X2
        s.radial.keep s.radial.profile s.radial.scale = 0 \/
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        inp.slots inp.toData.coefficient inp.P X1 X2
        s.radial.keep s.radial.profile s.radial.scale <=
      2 * diagonalControl s.radial.profile * (
        physicalMass inp s.puncture 1 fixedBadMask 1 Psi s.radial.scale Z Xi /
          CenteredMomentAmplificationChildInput.volume inp +
        Cdiag * (plainControl inp (p.profile 0) (p.profile 1)) ^ 2 *
          Sdiag.sup (schwartzSeminormFamily Real Real Complex) Psi *
            s.radial.scale * Z ^ epsdiag +
        Ctail * (plainControl inp (p.profile 0) (p.profile 1)) ^ 2 *
          Stail.sup (schwartzSeminormFamily Real Real Complex) Psi *
            s.radial.scale * Z ^ (-saving)) +
      2 * C * (K + 1) * diagonalControl s.radial.profile *
        (sourceControl U (p.profile 0) * sourceControl U (p.profile 1)) ^ 2 *
        (1 + abs t + height) ^ J * Z ^ (s.width + e + eps)) atTop := by
  classical
  choose d xi L hd hxi hxirho hL hLupper hstage using
    @KappaHalfBoundedLivePower.original_reference_power_live_bounded
      alpha inferInstance inferInstance M inferInstance H hH
      Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bPhi rho eps Mcap Bmask k0 ha hlo hhi hbPhi hrho heps hM hBmask hk0
  choose Psi hsPsi hnPsi Sdiag Stail Cdiag Ctail hCd hCt hred using
    actual_original_reduction bPhi hbPhi (fun _ : alpha => bslot)
      a b Mcap epsdiag Xi saving (fun _ : alpha => hbslot)
      ha (by linarith) hM hepsdiag hXi
  refine (Exists.intro d (Exists.intro xi (Exists.intro L (And.intro hd (And.intro hxi (And.intro hxirho (And.intro hL (And.intro hLupper (Exists.intro Psi (And.intro hsPsi (And.intro hnPsi (Exists.intro Sdiag (Exists.intro Stail (Exists.intro Cdiag (Exists.intro Ctail (And.intro hCd (And.intro hCt ?_)))))))))))))))))

  intro degree S
  choose J U C hC hbound using hstage degree S
  refine Exists.intro J (Exists.intro U (Exists.intro C (And.intro hC ?_)))
  filter_upwards [hbound, hred] with Z hz hr
  refine And.intro hz.1 ?_
  intro e Lslot k eta0 Q K he hK hlow theta w sigma freq t height
    hw hwL hSigmaLo hSigmaHi hheight hfreq hk s hQ hsLower hs p X1 X2 hX1 hX2
    hlarge hcap
  let inp := balancedInput M H hH eta0 theta Wslot hcSlot aslot bslot lo hi haslot hsSlot
    w sigma freq (fun i => And.intro (hSigmaLo i) (hSigmaHi i))
    s p ha t X1 X2 hX1 hX2
  have hsplit := hz.2 e Lslot k eta0 Q K he hK hlow
    theta w sigma freq t height hw hwL hSigmaLo hSigmaHi hheight hfreq hk
    s hQ hsLower hs p X1 X2 hX1 hX2 hlarge hcap
  cases hsplit with
  | inl hzero => exact Or.inl hzero
  | inr hreference =>
    apply Or.inr
    have hvolume : CenteredMomentAmplificationChildInput.volume inp <= Z ^ Mcap := by
      change X1 * X2 * (Finset.univ.prod fun i => Z ^ (w i)) <= Z ^ Mcap
      have hzpos : 0 < Z := zero_lt_one.trans hz.1
      have hw0 : 0 <= Finset.univ.sum w := Finset.sum_nonneg (fun i _ => hw i)
      have hslot : Finset.univ.sum w <= 6 * k * Finset.univ.sum w :=
        le_mul_of_one_le_left hw0 (by linarith)
      have hx (X : Real) : X <= Z ^ (length Z X) := by
        rw [length, Real.rpow_logb hzpos hz.1.ne'
          (lt_of_lt_of_le zero_lt_one (le_max_left _ _))]
        exact le_max_right _ _
      calc
        _ <= (Z ^ (length Z X1) * Z ^ (length Z X2)) *
            (Finset.univ.prod fun i => Z ^ (w i)) := by
          apply mul_le_mul_of_nonneg_right _
            (Finset.prod_nonneg (fun _ _ => Real.rpow_nonneg hzpos.le _))
          exact mul_le_mul (hx X1) (hx X2) hX2.le (Real.rpow_nonneg hzpos.le _)
        _ = Z ^ (length Z X1 + length Z X2 + Finset.univ.sum w) := by
          rw [<- Real.rpow_add hzpos, <- Real.rpow_sum_of_pos hzpos,
            <- Real.rpow_add hzpos]
        _ <= Z ^ Mcap := Real.rpow_le_rpow_of_exponent_le hz.1.le (by linarith)
    have hphysical := hr.2 inp (p.profile 0) (p.profile 1) rfl rfl
      (p.support 0) (p.support 1) (fun _ => le_rfl)
      s.puncture s.radial s.radial_support hvolume (natural_inverse_scale s Mcap hM)
    let Bterm : Real := 2 * diagonalControl s.radial.profile * (
      physicalMass inp s.puncture 1 fixedBadMask 1 Psi s.radial.scale Z Xi /
        CenteredMomentAmplificationChildInput.volume inp +
      Cdiag * (plainControl inp (p.profile 0) (p.profile 1)) ^ 2 *
        Sdiag.sup (schwartzSeminormFamily Real Real Complex) Psi *
          s.radial.scale * Z ^ epsdiag +
      Ctail * (plainControl inp (p.profile 0) (p.profile 1)) ^ 2 *
        Stail.sup (schwartzSeminormFamily Real Real Complex) Psi *
          s.radial.scale * Z ^ (-saving))
    have hRef := mul_le_mul_of_nonneg_left hreference (by norm_num : (0 : Real) <= 2)
    have hJoined := add_le_add (le_refl Bterm) hRef
    apply hphysical.trans
    convert hJoined using 1 <;> (try dsimp only [Bterm])
    all_goals first | rfl | ring

end SevenEighths.KappaHalfPhysicalEntry

end

end OAI
