/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelComplementaryAscent

/-!
# The actual fixed residue supports of complementary ascent masks

The original native kernel at every level at least sixteen is reduced through
the actual unit map to eight. This identifies its two zero-mask channels as
the fixed odd residue unions plus/minus one and plus/minus three.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelResidueAscent

open CarmichaelPrimePacket CarmichaelCorrelation CarmichaelCorrelationSpectrum
open CarmichaelTwoPowerConductor TwoPowerCharacterConductor
open CarmichaelComplementaryAscent

theorem kernel_eq_actual_eight_residues (r : Nat)
    (hd : Dvd.dvd 8 (2 ^ (r + 4))) (u : Units (ZMod (2 ^ (r + 4)))) :
    kernel (weight (2 ^ (r + 4)) labelTwo) u =
      if Or (Units.val (ZMod.unitsMap hd u) = 1)
        (Units.val (ZMod.unitsMap hd u) = -1) then 2 else 0 := by
  classical
  choose chi hChi hConductor hCoefficient using exists_large_conductor_eight_survivor r
  have hNonzero : Not (coefficient (weight (2 ^ (r + 4)) labelTwo) chi = 0) := by
    rw [hCoefficient]
    norm_num
  choose hd' psi hEquality using large_survivor_factorsThrough_eight r chi hNonzero
  have hValue (v : Units (ZMod (2 ^ (r + 4)))) :
      unitCharacter chi v = psi (Units.val (ZMod.unitsMap hd v)) := by
    change chi (Units.val v) = psi (Units.val (ZMod.unitsMap hd v))
    rw [hEquality, DirichletCharacter.changeLevel_eq_cast_of_dvd, ZMod.unitsMap_val]
  have hInverse : forall v : Units (ZMod 8), Inv.inv v = v := by decide
  have hKernel (v : Units (ZMod (2 ^ (r + 4)))) :
      (kernel (weight (2 ^ (r + 4)) labelTwo) v : Complex) =
        1 + psi (Units.val (ZMod.unitsMap hd v)) := by
    rw [large_kernel_two_modes r chi hChi hNonzero v, hValue, map_inv, hInverse]
  have hMinusMap : ZMod.unitsMap hd (-1 : Units (ZMod (2 ^ (r + 4)))) =
      (-1 : Units (ZMod 8)) := by
    apply Units.ext
    change ZMod.castHom hd (ZMod 8) (-1) = -1
    rw [map_neg, map_one]
  have hNativeEven : unitCharacter chi (-1 : Units (ZMod (2 ^ (r + 4)))) = 1 :=
    large_survivor_even r chi hNonzero
  have hPsiMinus : psi (-1 : ZMod 8) = 1 := by
    simpa only [hMinusMap, Units.val_neg, Units.val_one] using
      (hValue (-1)).symm.trans hNativeEven
  have hFiveMap : ZMod.unitsMap hd (fiveUnit (r + 1)) = fiveUnit 0 := by
    apply Units.ext
    change ZMod.castHom hd (ZMod 8) (Units.val (fiveUnit (r + 1))) =
      Units.val (fiveUnit 0)
    rw [fiveUnit_val, fiveUnit_val]
    exact map_natCast _ 5
  have hAtFive := hKernel (fiveUnit (r + 1))
  rw [five_kernel_zero, Complex.ofReal_zero, hFiveMap, fiveUnit_val] at hAtFive
  have hPsiFive : psi (5 : ZMod 8) = -1 := by
    calc
      _ = (1 + psi (5 : ZMod 8)) - 1 := by ring
      _ = 0 - 1 := congrArg (fun z : Complex => z - 1) hAtFive.symm
      _ = -1 := by ring
  have hPsiNegFive : psi (-5 : ZMod 8) = -1 := by
    rw [show (-5 : ZMod 8) = (-1) * 5 by ring, map_mul, hPsiMinus, hPsiFive]
    ring
  have hCases : forall v : Units (ZMod 8),
      Or (Units.val v = 1) (Or (Units.val v = -1)
        (Or (Units.val v = 5) (Units.val v = -5))) := by decide
  have hFiveNot : Not (Or ((5 : ZMod 8) = 1) ((5 : ZMod 8) = -1)) := by decide
  have hNegFiveNot : Not (Or ((-5 : ZMod 8) = 1) ((-5 : ZMod 8) = -1)) := by decide
  have hComplex :
      (kernel (weight (2 ^ (r + 4)) labelTwo) u : Complex) =
        ((if Or (Units.val (ZMod.unitsMap hd u) = 1)
          (Units.val (ZMod.unitsMap hd u) = -1) then 2 else 0 : Real) : Complex) := by
    rw [hKernel]
    rcases hCases (ZMod.unitsMap hd u) with h | h | h | h
    . norm_num [h]
    . norm_num [h, hPsiMinus]
    . rw [h, hPsiFive, ite_eq_right hFiveNot]
      norm_num
    . rw [h, hPsiNegFive, ite_eq_right hNegFiveNot]
      norm_num
  exact_mod_cast hComplex

theorem primeMask_false_eq_mod_eight (r p : Nat) (hp : Nat.Coprime p 2) :
    primeMask r false p = if Or (p % 8 = 1) (p % 8 = 7) then 2 else 0 := by
  classical
  have hPQ : Nat.Coprime p (2 ^ (r + 4)) := hp.pow_right _
  have hd : Dvd.dvd 8 (2 ^ (r + 4)) := by
    change Dvd.dvd (2 ^ 3) (2 ^ (r + 4))
    exact pow_dvd_pow 2 (by omega)
  simp only [primeMask, dite_eq_left hPQ, mask, Bool.false_eq_true, ite_false]
  rw [kernel_eq_actual_eight_residues r hd]
  have hResidue : Units.val (ZMod.unitsMap hd (ZMod.unitOfCoprime p hPQ)) =
      (p : ZMod 8) := by
    rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, ZMod.cast_natCast hd]
  rw [hResidue]
  have hValOne : (1 : ZMod 8).val = 1 := by decide
  have hValSeven : (7 : ZMod 8).val = 7 := by decide
  have hOne : (p : ZMod 8) = 1 <-> p % 8 = 1 := by
    constructor
    . intro h
      simpa only [ZMod.val_natCast, hValOne] using congrArg ZMod.val h
    . intro h
      apply ZMod.val_injective
      simpa only [ZMod.val_natCast, hValOne] using h
  have hSeven : (p : ZMod 8) = -1 <-> p % 8 = 7 := by
    rw [show (-1 : ZMod 8) = 7 by decide]
    constructor
    . intro h
      simpa only [ZMod.val_natCast, hValSeven] using congrArg ZMod.val h
    . intro h
      apply ZMod.val_injective
      simpa only [ZMod.val_natCast, hValSeven] using h
  simp only [hOne, hSeven]

theorem primeMask_true_eq_mod_eight (r p : Nat) (hp : Nat.Coprime p 2) :
    primeMask r true p = if Or (p % 8 = 3) (p % 8 = 5) then 2 else 0 := by
  have hNotTwo : Not (Dvd.dvd 2 p) :=
    Nat.prime_two.coprime_iff_not_dvd.mp hp.symm
  have hMod : Not (p % 2 = 0) := by
    intro h
    exact hNotTwo (Nat.dvd_of_mod_eq_zero h)
  have hResidue : Or (p % 8 = 1) (Or (p % 8 = 3)
      (Or (p % 8 = 5) (p % 8 = 7))) := by omega
  have hSum := primeMask_sum r p (hp.pow_right _)
  rw [primeMask_false_eq_mod_eight r p hp] at hSum
  rcases hResidue with h | h | h | h <;> norm_num [h] at hSum <;>
    norm_num [h] <;> linarith

def residueWeight (phase : Bool) (p : Nat) : Real :=
  if phase then if Or (p % 8 = 3) (p % 8 = 5) then 2 else 0
  else if Or (p % 8 = 1) (p % 8 = 7) then 2 else 0

def residueAscentExcess (H : Nat) (a : Nat -> Nat) (phase : Bool) (X : Nat) : Real :=
  residueWeight phase (PrimeFactorUnimodality.primeAt (a X)) *
    localAscentPairExcess H X (a X)

theorem primeMask_eq_residueWeight (r p : Nat) (phase : Bool)
    (hp : Nat.Coprime p 2) :
    primeMask r phase p = residueWeight phase p := by
  cases phase
  . exact primeMask_false_eq_mod_eight r p hp
  . exact primeMask_true_eq_mod_eight r p hp

theorem residueWeight_nonneg (phase : Bool) (p : Nat) :
    0 <= residueWeight phase p := by
  unfold residueWeight
  split_ifs <;> norm_num

theorem selected_prime_coprime_two_eventually
    (H : Nat) (a : Nat -> Nat) (hs : LocalAscentLocator H a) :
    Filter.Eventually (fun X : Nat =>
      Nat.Coprime (PrimeFactorUnimodality.primeAt (a X)) 2) Filter.atTop := by
  filter_upwards [selected_prime_coprime_eventually H a hs (fun _ => 0)] with X hX
  exact Nat.Coprime.of_dvd_right (by decide : Dvd.dvd 2 (2 ^ (0 + 4))) hX

theorem arbitrary_modulus_excess_eq_fixed_eventually
    (H : Nat) (a : Nat -> Nat) (hs : LocalAscentLocator H a) (r : Nat -> Nat) :
    Filter.Eventually (fun X : Nat => forall phase : Bool,
      primeAscentExcess H a r phase X = residueAscentExcess H a phase X) Filter.atTop := by
  filter_upwards [selected_prime_coprime_two_eventually H a hs] with X hX phase
  unfold primeAscentExcess channelExcess residueAscentExcess
  dsimp only
  rw [primeMask_eq_residueWeight _ _ phase hX]

theorem residue_cover_eventually
    (H : Nat) (a : Nat -> Nat) (hs : LocalAscentLocator H a) :
    Filter.Eventually (fun X : Nat =>
      residueWeight false (PrimeFactorUnimodality.primeAt (a X)) +
        residueWeight true (PrimeFactorUnimodality.primeAt (a X)) = 2) Filter.atTop := by
  filter_upwards [selected_prime_coprime_two_eventually H a hs] with X hX
  rw [<- primeMask_eq_residueWeight 0 _ false hX,
    <- primeMask_eq_residueWeight 0 _ true hX]
  exact primeMask_sum 0 _ (hX.pow_right _)

theorem riemannHypothesis_iff_fixed_residue_channels_bounded
    (H : Nat) (a : Nat -> Nat) (hs : LocalAscentLocator H a) :
    RiemannHypothesis <->
      forall phase : Bool, exists C : Real, Filter.Eventually (fun X : Nat =>
        residueAscentExcess H a phase X <= C) Filter.atTop := by
  exact riemannHypothesis_iff_joint_bounded H a hs
    (fun phase X => residueWeight phase (PrimeFactorUnimodality.primeAt (a X)))
    (Filter.Eventually.of_forall (fun X phase => residueWeight_nonneg phase _))
    (residue_cover_eventually H a hs)

theorem riemannHypothesis_iff_fixed_residue_channels_nonpos
    (H : Nat) (a : Nat -> Nat) (hs : LocalAscentLocator H a) :
    RiemannHypothesis <->
      Filter.Eventually (fun X : Nat => forall phase : Bool,
        residueAscentExcess H a phase X <= 0) Filter.atTop := by
  exact riemannHypothesis_iff_joint_nonpos H a hs
    (fun phase X => residueWeight phase (PrimeFactorUnimodality.primeAt (a X)))
    (Filter.Eventually.of_forall (fun X phase => residueWeight_nonneg phase _))
    (residue_cover_eventually H a hs)

theorem fixed_residue_channel_unbounded_of_not_RH
    (H : Nat) (a : Nat -> Nat) (hs : LocalAscentLocator H a)
    (hNotRH : Not RiemannHypothesis) :
    exists phase : Bool, forall C X0 : Real, exists n : Nat,
      X0 < (n : Real) /\ C < residueAscentExcess H a phase n := by
  exact fixed_channel_unbounded_of_not_RH H a hs
    (fun phase X => residueWeight phase (PrimeFactorUnimodality.primeAt (a X)))
    (Filter.Eventually.of_forall (fun X phase => residueWeight_nonneg phase _))
    (residue_cover_eventually H a hs) hNotRH

theorem not_canonical_eight_reduction (r : Nat)
    (hd : Dvd.dvd 8 (2 ^ (r + 4))) :
    Not (forall u : Units (ZMod (2 ^ (r + 4))),
      kernel (weight (2 ^ (r + 4)) labelTwo) u =
        kernel (weight 8 labelTwo) (ZMod.unitsMap hd u)) := by
  intro h
  have hOne := h 1
  rw [map_one, large_kernel_boolean, level_eight_kernel_positive] at hOne
  norm_num [CarmichaelCorrelationLocal.returnBit] at hOne

end PrimeFactorOscillations.CarmichaelResidueAscent
