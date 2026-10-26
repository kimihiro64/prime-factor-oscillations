/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelProfileProjection

/-!
# Uniform truncation of actual conditional return profiles

The retained law is the actual zero-padded marginal. Large auxiliary images
supply a prime reciprocal-square tail, uniformly over both old units.
The full principal vacancy keeps its positive finite-product multiplier.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelTailProjection

open CarmichaelFiberGeometry CarmichaelRedundantTail CarmichaelProfileProjection
open CarmichaelProfileKernel CarmichaelMaximalOrderLifts

/-- Keep every small or nonredundant label, including deterministic labels. -/
def retentionMask (m B : Nat) [NeZero B] (Y : Nat) (p : Nat.Primes) : Bool :=
  decide (Or ((p : Nat) <= Y)
    (PrimeOrderReturnLaw.returnIndex (G := Units (ZMod B))
      (Monoid.exponent (Units (ZMod (m * B)))) (p : Nat) < (p : Nat) ^ (2 : Nat)))

abbrev packetRate (m B : Nat) [NeZero B]
    (l : exponentPrimePacket (m * B)) : Real :=
  auxiliaryReturnRate m B (l.val : Nat)

abbrev packetGate (m B : Nat) (a : Units (ZMod m))
    (l : exponentPrimePacket (m * B)) : Bool :=
  returnGate m B a (l.val : Nat)

abbrev packetKeep (m B : Nat) [NeZero B] (Y : Nat)
    (l : exponentPrimePacket (m * B)) : Bool :=
  retentionMask m B Y l.val

/-- A pushforward of the actual fiber probability, on the original pattern space. -/
def retainedProfileProbability (m B : Nat) [NeZero B]
    (a : Units (ZMod m)) (Y : Nat) (bits : exponentPrimePacket (m * B) -> Bool) : Real := by
  classical
  exact Finset.univ.sum (fun pre : exponentPrimePacket (m * B) -> Bool =>
    if maskedGate (packetKeep m B Y) pre = bits
    then fiberProfileProbability m B a (exponentPrimePacket (m * B)) pre else 0)

theorem retained_profile_eq_gatedLaw (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)] (hCoprime : Nat.Coprime m B)
    (a : Units (ZMod m)) (Y : Nat) (bits : exponentPrimePacket (m * B) -> Bool) :
    retainedProfileProbability m B a Y bits =
      gatedLaw (packetRate m B) (maskedGate (packetKeep m B Y) (packetGate m B a)) bits := by
  unfold retainedProfileProbability
  simp_rw [fiber_profile_eq_gatedLaw m B hCoprime a]
  exact erasedLaw_eq_gatedLaw (packetRate m B) (packetKeep m B Y) (packetGate m B a) bits

theorem discarded_label_bounds (m B : Nat) [NeZero B] (Y : Nat) (p : Nat.Primes)
    (hDiscard : retentionMask m B Y p = false) :
    And (Y < (p : Nat)) (auxiliaryReturnRate m B (p : Nat) <=
      1 / (p : Real) ^ (2 : Nat)) := by
  have hNot : Not (Or ((p : Nat) <= Y)
      (PrimeOrderReturnLaw.returnIndex (G := Units (ZMod B))
        (Monoid.exponent (Units (ZMod (m * B)))) (p : Nat) <
          (p : Nat) ^ (2 : Nat))) := by
    simpa only [retentionMask, decide_eq_false_iff_not] using hDiscard
  have hY : Y < (p : Nat) := lt_of_not_ge (fun h => hNot (Or.inl h))
  have hIndex : (p : Nat) ^ (2 : Nat) <=
      PrimeOrderReturnLaw.returnIndex (G := Units (ZMod B))
        (Monoid.exponent (Units (ZMod (m * B)))) (p : Nat) :=
    le_of_not_gt (fun h => hNot (Or.inr h))
  have hIndexR : (p : Real) ^ (2 : Nat) <=
      (PrimeOrderReturnLaw.returnIndex (G := Units (ZMod B))
        (Monoid.exponent (Units (ZMod (m * B)))) (p : Nat) : Real) := by
    exact_mod_cast hIndex
  exact And.intro hY (one_div_le_one_div_of_le
    (sq_pos_of_pos (by exact_mod_cast p.property.pos)) hIndexR)

/-- The generic arithmetic adapter applies after masking, without old-gate agreement. -/
theorem removed_cost_le_prime_tail (S : Finset Nat.Primes) (Y : Nat)
    (r : Nat.Primes -> Real) (keep gate other : Nat.Primes -> Bool)
    (hDiscard : forall p, Membership.mem S p -> keep p = false ->
      And (Y < (p : Nat)) (r p <= 1 / (p : Real) ^ (2 : Nat))) :
    mismatchCost (fun l : S => r l.val)
      (fun l : S => removedGate keep gate l.val)
      (fun l : S => removedGate keep other l.val) <= primeReciprocalSquareTail Y := by
  classical
  let f : Nat.Primes -> Real := fun p =>
    if removedGate keep gate p = removedGate keep other p then 0 else r p
  let D : Finset Nat.Primes := S.filter (fun p : Nat.Primes =>
    Not (removedGate keep gate p = removedGate keep other p))
  have hKeep : forall p, Membership.mem D p -> keep p = false := by
    intro p hp
    have hDiff := (Finset.mem_filter.mp hp).2
    cases hk : keep p
    . rfl
    . exact False.elim (hDiff (by simp [removedGate, hk]))
  have hCost : mismatchCost (fun l : S => r l.val)
      (fun l : S => removedGate keep gate l.val)
      (fun l : S => removedGate keep other l.val) = D.sum r := by
    change S.attach.sum (fun l : S => f l.val) = _
    rw [Finset.sum_attach S f]
    dsimp only [D]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases h : removedGate keep gate p = removedGate keep other p <;> simp [f, h]
  rw [hCost]
  calc
    _ <= D.sum (fun p : Nat.Primes => 1 / (p : Real) ^ (2 : Nat)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact (hDiscard p (Finset.mem_filter.mp hp).1 (hKeep p hp)).2
    _ <= primeReciprocalSquareTail Y := finite_reciprocal_square_tail_le D Y
      (fun p hp => (hDiscard p (Finset.mem_filter.mp hp).1 (hKeep p hp)).1)

theorem removed_packet_cost_le_tail (m B : Nat) [NeZero B]
    (a b : Units (ZMod m)) (Y : Nat) :
    mismatchCost (packetRate m B)
      (removedGate (packetKeep m B Y) (packetGate m B a))
      (removedGate (packetKeep m B Y) (packetGate m B b)) <=
        primeReciprocalSquareTail Y :=
  removed_cost_le_prime_tail (exponentPrimePacket (m * B)) Y
    (fun p : Nat.Primes => auxiliaryReturnRate m B (p : Nat))
    (retentionMask m B Y) (fun p : Nat.Primes => returnGate m B a (p : Nat))
    (fun p : Nat.Primes => returnGate m B b (p : Nat))
    (fun p _ hp => discarded_label_bounds m B Y p hp)

def retainedTotalVariation (m B : Nat) [NeZero B]
    (a b : Units (ZMod m)) (Y : Nat) : Real := by
  classical
  exact (1 / 2 : Real) * Finset.univ.sum
    (fun bits : exponentPrimePacket (m * B) -> Bool =>
      abs (retainedProfileProbability m B a Y bits -
        retainedProfileProbability m B b Y bits))

def retainedHellingerEnergy (m B : Nat) [NeZero B]
    (a b : Units (ZMod m)) (Y : Nat) : Real := by
  classical
  exact Finset.univ.sum (fun bits : exponentPrimePacket (m * B) -> Bool =>
    (Real.sqrt (retainedProfileProbability m B a Y bits) -
      Real.sqrt (retainedProfileProbability m B b Y bits)) ^ 2)

/-- Uniform distortion for arbitrary actual fibers; no low-gate agreement is assumed. -/
theorem fiber_projection_distortion (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)] (hCoprime : Nat.Coprime m B)
    (a b : Units (ZMod m)) (Y : Nat) :
    And (And (0 <= fiberTotalVariation m B a b - retainedTotalVariation m B a b Y)
      (fiberTotalVariation m B a b - retainedTotalVariation m B a b Y <=
        primeReciprocalSquareTail Y))
      (And (0 <= fiberHellingerEnergy m B a b - retainedHellingerEnergy m B a b Y)
        (fiberHellingerEnergy m B a b - retainedHellingerEnergy m B a b Y <=
          redundantEnergyTail Y)) := by
  classical
  let r := packetRate m B
  let keep := packetKeep m B Y
  let ga := packetGate m B a
  let gb := packetGate m B b
  have hr : forall l, And (0 <= r l) (r l <= 1) :=
    fun l => auxiliaryReturnRate_bounds m B (l.val : Nat)
  have hTV := variation_projection_bounds r hr keep ga gb
  have hE := energy_projection_bounds r hr keep ga gb
  have hCost := removed_packet_cost_le_tail m B a b Y
  have hTVTail := gated_variation_le_mismatch_cost r hr
    (removedGate keep ga) (removedGate keep gb)
  have hETail := gated_energy_le_mismatch_cost r hr
    (removedGate keep ga) (removedGate keep gb)
  have hRoot := Real.sqrt_le_sqrt (sub_le_sub_left hCost 1)
  have hTVBound : gatedTotalVariation r ga gb -
      gatedTotalVariation r (maskedGate keep ga) (maskedGate keep gb) <=
        primeReciprocalSquareTail Y := hTV.2.2.trans (hTVTail.trans hCost)
  have hEBound : gatedHellingerEnergy r ga gb -
      gatedHellingerEnergy r (maskedGate keep ga) (maskedGate keep gb) <=
        redundantEnergyTail Y := by
    dsimp only [redundantEnergyTail]
    exact hE.2.trans (hETail.trans (by linarith))
  unfold fiberTotalVariation retainedTotalVariation fiberHellingerEnergy retainedHellingerEnergy
  simp_rw [fiber_profile_eq_gatedLaw m B hCoprime a,
    fiber_profile_eq_gatedLaw m B hCoprime b,
    retained_profile_eq_gatedLaw m B hCoprime a,
    retained_profile_eq_gatedLaw m B hCoprime b]
  exact And.intro (And.intro hTV.1 hTVBound) (And.intro hE.1 hEBound)

def erasedVacancyFactor (m B : Nat) [NeZero B] (a : Units (ZMod m)) (Y : Nat) : Real :=
  projectionTailFactor (packetRate m B) (packetKeep m B Y) (packetGate m B a)

/-- Principal mass is retained as an exact product, including its zero branch. -/
theorem vacancy_projection_identity (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)] (hCoprime : Nat.Coprime m B)
    (a : Units (ZMod m)) (Y : Nat) :
    maximalOrderLiftProbability m B a =
      retainedProfileProbability m B a Y (fun _ => false) *
        erasedVacancyFactor m B a Y := by
  rw [maximalOrderLiftProbability_eq_profile,
    fiber_profile_eq_gatedLaw m B hCoprime a,
    retained_profile_eq_gatedLaw m B hCoprime a]
  exact vacancy_projection_factor (packetRate m B) (packetKeep m B Y) (packetGate m B a)

theorem erased_vacancy_factor_bounds (m B : Nat) [NeZero B]
    (a : Units (ZMod m)) (Y : Nat) :
    And (1 - primeReciprocalSquareTail Y <= erasedVacancyFactor m B a Y)
      (erasedVacancyFactor m B a Y <= 1) := by
  let r := packetRate m B
  let keep := packetKeep m B Y
  let ga := packetGate m B a
  have hr : forall l, And (0 <= r l) (r l <= 1) :=
    fun l => auxiliaryReturnRate_bounds m B (l.val : Nat)
  have hCost : mismatchCost r ga (maskedGate keep ga) <= primeReciprocalSquareTail Y := by
    rw [projection_cost_eq_removed]
    have hZero : removedGate keep (fun _ : exponentPrimePacket (m * B) => false) =
        (fun _ : exponentPrimePacket (m * B) => false) := by
      funext l
      simp only [removedGate, Bool.and_false]
    rw [<- hZero]
    exact removed_cost_le_prime_tail (exponentPrimePacket (m * B)) Y
      (fun p : Nat.Primes => auxiliaryReturnRate m B (p : Nat))
      (retentionMask m B Y) (fun p : Nat.Primes => returnGate m B a (p : Nat))
      (fun _ : Nat.Primes => false)
      (fun p _ hp => discarded_label_bounds m B Y p hp)
  have hTV := gated_variation_le_mismatch_cost r hr ga (maskedGate keep ga)
  rw [projection_variation_eq r hr keep ga] at hTV
  exact And.intro (by change 1 - primeReciprocalSquareTail Y <= projectionTailFactor r keep ga; linarith)
    (overlapMass_le_one r hr ga (maskedGate keep ga))

theorem erased_vacancy_uniform_floor (m B : Nat) [NeZero B]
    (a : Units (ZMod m)) (Y : Nat) (hY : 3 <= Y) :
    And (0 < 1 - 2 / (Y : Real))
      (1 - 2 / (Y : Real) <= erasedVacancyFactor m B a Y) := by
  have hTail := (reciprocal_tail_bounds Y (by omega)).2
  have hFactor := (erased_vacancy_factor_bounds m B a Y).1
  have hYR : (2 : Real) < Y := by exact_mod_cast (show 2 < Y by omega)
  have hFrac : 2 / (Y : Real) < 1 := (div_lt_one (by linarith)).mpr hYR
  exact And.intro (by linarith) (by linarith)

/-- Every erased factor is positive, even before the tail majorant becomes small. -/
theorem erased_vacancy_factor_pos (m B : Nat) [NeZero B]
    (a : Units (ZMod m)) (Y : Nat) : 0 < erasedVacancyFactor m B a Y := by
  classical
  unfold erasedVacancyFactor projectionTailFactor overlapMass
  apply Finset.prod_pos
  intro l _
  by_cases hk : packetKeep m B Y l = true
  . cases hg : packetGate m B a l <;> simp [overlapFactor, maskedGate, hk, hg]
  . have hkFalse : retentionMask m B Y l.val = false := by
      cases h : packetKeep m B Y l <;> simp_all [packetKeep]
    have hNot : Not (Or ((l.val : Nat) <= Y)
        (PrimeOrderReturnLaw.returnIndex (G := Units (ZMod B))
          (Monoid.exponent (Units (ZMod (m * B)))) (l.val : Nat) <
            (l.val : Nat) ^ (2 : Nat))) := by
      simpa only [retentionMask, decide_eq_false_iff_not] using hkFalse
    have hIndex : (l.val : Nat) ^ (2 : Nat) <=
        PrimeOrderReturnLaw.returnIndex (G := Units (ZMod B))
          (Monoid.exponent (Units (ZMod (m * B)))) (l.val : Nat) :=
      le_of_not_gt (fun h => hNot (Or.inr h))
    have hp := l.val.property.two_le
    have hOne : (1 : Real) <
        (PrimeOrderReturnLaw.returnIndex (G := Units (ZMod B))
          (Monoid.exponent (Units (ZMod (m * B)))) (l.val : Nat) : Real) := by
      exact_mod_cast (show 1 <
        PrimeOrderReturnLaw.returnIndex (G := Units (ZMod B))
          (Monoid.exponent (Units (ZMod (m * B)))) (l.val : Nat) by nlinarith)
    have hr : packetRate m B l < 1 := by
      exact (div_lt_one (zero_lt_one.trans hOne)).mpr hOne
    cases hg : packetGate m B a l <;>
      simp [overlapFactor, maskedGate, hkFalse, packetKeep, hg, sub_pos.mpr hr]

theorem retained_vacancy_zero_iff (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)] (hCoprime : Nat.Coprime m B)
    (a : Units (ZMod m)) (Y : Nat) :
    maximalOrderLiftProbability m B a = 0 <->
      retainedProfileProbability m B a Y (fun _ => false) = 0 := by
  rw [vacancy_projection_identity m B hCoprime a Y, mul_eq_zero]
  exact or_iff_left (ne_of_gt (erased_vacancy_factor_pos m B a Y))

theorem retained_vacancy_pos_iff (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)] (hCoprime : Nat.Coprime m B)
    (a : Units (ZMod m)) (Y : Nat) :
    0 < maximalOrderLiftProbability m B a <->
      0 < retainedProfileProbability m B a Y (fun _ => false) := by
  rw [vacancy_projection_identity m B hCoprime a Y]
  exact mul_pos_iff_of_pos_right (erased_vacancy_factor_pos m B a Y)

/-- In squarefree auxiliary moduli, erasure removes exactly the large rank-at-least-two labels. -/
theorem squarefree_retention_iff (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)] (hSqB : Squarefree B)
    (hCoprime : Nat.Coprime m B) (Y : Nat) (l : exponentPrimePacket (m * B)) :
    packetKeep m B Y l = true <->
      Or ((l.val : Nat) <= Y) (CarmichaelConditionalRigidity.auxiliaryRank m B l.val <= 1) := by
  have hl := (exponentPrimePacket_mem (m * B) l.val).mp l.property
  have hIndex := CarmichaelConditionalRigidity.auxiliary_index_prime_pow
    m B hSqB hCoprime l.val hl
  have hp := l.val.property.two_le
  have hRank :
      PrimeOrderReturnLaw.returnIndex (G := Units (ZMod B))
        (Monoid.exponent (Units (ZMod (m * B)))) (l.val : Nat) <
          (l.val : Nat) ^ (2 : Nat) <->
        CarmichaelConditionalRigidity.auxiliaryRank m B l.val <= 1 := by
    constructor
    . intro hSmall
      by_contra hNot
      have hTwo : 2 <= CarmichaelConditionalRigidity.auxiliaryRank m B l.val := by omega
      have hLarge := CarmichaelConditionalRigidity.auxiliary_power_le_index
        m B hSqB hCoprime l.val hl 2 hTwo
      omega
    . intro hOne
      have hCases : Or (CarmichaelConditionalRigidity.auxiliaryRank m B l.val = 0)
          (CarmichaelConditionalRigidity.auxiliaryRank m B l.val = 1) := by omega
      cases hCases with
      | inl h => rw [hIndex, h, pow_zero]; nlinarith
      | inr h => rw [hIndex, h, pow_one]; nlinarith
  simp only [packetKeep, retentionMask, decide_eq_true_eq, hRank]

end PrimeFactorOscillations.CarmichaelTailProjection
