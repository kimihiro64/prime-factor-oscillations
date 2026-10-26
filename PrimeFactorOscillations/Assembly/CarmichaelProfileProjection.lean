/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelRedundantTail

/-!
# Exact projection of complete conditional return profiles

Erasure is the zero-padded pushforward of the actual pattern law.
Both directed overlaps split exactly into retained and discarded factors.
The vacancy factor and the joint distance correction remain explicit.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelProfileProjection

open CarmichaelFiberGeometry CarmichaelRedundantTail

variable {I : Type*} [Fintype I]

def maskedGate (keep gate : I -> Bool) : I -> Bool :=
  fun i => keep i && gate i

def removedGate (keep gate : I -> Bool) : I -> Bool :=
  fun i => !keep i && gate i

/-- The discrete pushforward under zero-padding the erased coordinates. -/
def erasedLaw [DecidableEq I] (r : I -> Real) (keep gate bits : I -> Bool) : Real := by
  classical
  exact Finset.univ.sum (fun pre : I -> Bool =>
    if maskedGate keep pre = bits then gatedLaw r gate pre else 0)

/-- Zero-padding an actual product law changes exactly its observation gates. -/
theorem erasedLaw_eq_gatedLaw [DecidableEq I]
    (r : I -> Real) (keep gate bits : I -> Bool) :
    erasedLaw r keep gate bits = gatedLaw r (maskedGate keep gate) bits := by
  classical
  have hPoint (pre : I -> Bool) :
      (if maskedGate keep pre = bits then gatedLaw r gate pre else 0) =
        Finset.univ.prod (fun i =>
          if (keep i && pre i) = bits i then gatedFactor (r i) (gate i) (pre i) else 0) := by
    by_cases h : maskedGate keep pre = bits
    { rw [ite_eq_left h]
      apply Finset.prod_congr rfl
      intro i _
      have hi : (keep i && pre i) = bits i := congrFun h i
      rw [ite_eq_left hi] }
    { have hWitness : Exists (fun i => Not ((keep i && pre i) = bits i)) := by
        by_contra hNo
        apply h
        funext i
        change (keep i && pre i) = bits i
        by_contra hDiff
        exact hNo (Exists.intro i hDiff)
      choose i hi using hWitness
      rw [ite_eq_right h]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [ite_eq_right hi] }
  unfold erasedLaw
  simp_rw [hPoint]
  calc
    _ = Finset.univ.prod (fun i : I => Finset.univ.sum (fun pre : Bool =>
        if (keep i && pre) = bits i then gatedFactor (r i) (gate i) pre else 0)) :=
      (Fintype.prod_sum (fun (i : I) (pre : Bool) =>
        if (keep i && pre) = bits i then gatedFactor (r i) (gate i) pre else 0)).symm
    _ = gatedLaw r (maskedGate keep gate) bits := by
      unfold gatedLaw
      apply Finset.prod_congr rfl
      intro i _
      cases hk : keep i <;> cases hg : gate i <;> cases bits i <;>
        simp [maskedGate, gatedFactor, hk, hg]

theorem overlapMass_split (r : I -> Real) (keep gate other : I -> Bool) :
    overlapMass r gate other =
      overlapMass r (maskedGate keep gate) (maskedGate keep other) *
        overlapMass r (removedGate keep gate) (removedGate keep other) := by
  unfold overlapMass
  rw [<- Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases hk : keep i <;> cases hg : gate i <;> cases ho : other i <;>
    simp [maskedGate, removedGate, overlapFactor, hk, hg, ho]

theorem reverse_projection_overlap_one (r : I -> Real) (keep gate : I -> Bool) :
    overlapMass r (maskedGate keep gate) gate = 1 := by
  apply Finset.prod_eq_one
  intro i _
  cases hk : keep i <;> cases hg : gate i <;>
    simp [maskedGate, overlapFactor, hk, hg]

def projectionTailFactor (r : I -> Real) (keep gate : I -> Bool) : Real :=
  overlapMass r gate (maskedGate keep gate)

/-- The principal vacancy retains its exact discarded-coordinate multiplier. -/
theorem vacancy_projection_factor (r : I -> Real) (keep gate : I -> Bool) :
    gatedLaw r gate (fun _ => false) =
      gatedLaw r (maskedGate keep gate) (fun _ => false) *
        projectionTailFactor r keep gate := by
  have hPoint (i : I) :
      gatedFactor (r i) (gate i) false =
        gatedFactor (r i) (maskedGate keep gate i) false *
          overlapFactor (r i) (gate i) (maskedGate keep gate i) := by
    cases hk : keep i <;> cases hg : gate i <;>
      simp [maskedGate, gatedFactor, overlapFactor, hk, hg]
  unfold gatedLaw projectionTailFactor overlapMass
  simp_rw [hPoint]
  rw [Finset.prod_mul_distrib]

theorem projection_variation_eq [DecidableEq I] (r : I -> Real)
    (hr : forall i, And (0 <= r i) (r i <= 1)) (keep gate : I -> Bool) :
    gatedTotalVariation r gate (maskedGate keep gate) =
      1 - projectionTailFactor r keep gate := by
  rw [gatedTotalVariation_eq r hr gate (maskedGate keep gate),
    reverse_projection_overlap_one,
    min_eq_left (overlapMass_le_one r hr gate (maskedGate keep gate))]
  rfl

theorem projection_energy_eq [DecidableEq I] (r : I -> Real)
    (hr : forall i, And (0 <= r i) (r i <= 1)) (keep gate : I -> Bool) :
    gatedHellingerEnergy r gate (maskedGate keep gate) =
      2 * (1 - Real.sqrt (projectionTailFactor r keep gate)) := by
  rw [gatedHellingerEnergy_eq r hr gate (maskedGate keep gate),
    reverse_projection_overlap_one, mul_one]
  rfl

/-- One-packet erasure charges exactly the removed open-coordinate cost. -/
theorem projection_cost_eq_removed (r : I -> Real) (keep gate : I -> Bool) :
    mismatchCost r gate (maskedGate keep gate) =
      mismatchCost r (removedGate keep gate) (fun _ => false) := by
  unfold mismatchCost
  apply Finset.sum_congr rfl
  intro i _
  cases hk : keep i <;> cases hg : gate i <;>
    simp [maskedGate, removedGate, mismatchRate, hk, hg]

/-- The comparison retains the entire product of the two directed tail factors. -/
theorem variation_projection_bounds [DecidableEq I] (r : I -> Real)
    (hr : forall i, And (0 <= r i) (r i <= 1)) (keep gate other : I -> Bool) :
    And (0 <= gatedTotalVariation r gate other -
      gatedTotalVariation r (maskedGate keep gate) (maskedGate keep other))
      (And (gatedTotalVariation r gate other -
        gatedTotalVariation r (maskedGate keep gate) (maskedGate keep other) <=
          (1 - gatedTotalVariation r (maskedGate keep gate) (maskedGate keep other)) *
            gatedTotalVariation r (removedGate keep gate) (removedGate keep other))
        (gatedTotalVariation r gate other -
          gatedTotalVariation r (maskedGate keep gate) (maskedGate keep other) <=
            gatedTotalVariation r (removedGate keep gate) (removedGate keep other))) := by
  let A := overlapMass r (maskedGate keep gate) (maskedGate keep other)
  let B := overlapMass r (maskedGate keep other) (maskedGate keep gate)
  let C := overlapMass r (removedGate keep gate) (removedGate keep other)
  let D := overlapMass r (removedGate keep other) (removedGate keep gate)
  have hA0 : 0 <= A := overlapMass_nonneg r hr _ _
  have hB0 : 0 <= B := overlapMass_nonneg r hr _ _
  have hC0 : 0 <= C := overlapMass_nonneg r hr _ _
  have hD0 : 0 <= D := overlapMass_nonneg r hr _ _
  have hA1 : A <= 1 := overlapMass_le_one r hr _ _
  have hC1 : C <= 1 := overlapMass_le_one r hr _ _
  have hD1 : D <= 1 := overlapMass_le_one r hr _ _
  have hAC : A * C <= A := by nlinarith [mul_nonneg hA0 (sub_nonneg.mpr hC1)]
  have hBD : B * D <= B := by nlinarith [mul_nonneg hB0 (sub_nonneg.mpr hD1)]
  have hUpper : min (A * C) (B * D) <= min A B :=
    le_min ((min_le_left _ _).trans hAC) ((min_le_right _ _).trans hBD)
  have hLower : min A B * min C D <= min (A * C) (B * D) :=
    le_min
      (mul_le_mul (min_le_left _ _) (min_le_left _ _) (le_min hC0 hD0) hA0)
      (mul_le_mul (min_le_right _ _) (min_le_right _ _) (le_min hC0 hD0) hB0)
  have hMinAB : min A B <= 1 := (min_le_left A B).trans hA1
  have hMinCD : min C D <= 1 := (min_le_left C D).trans hC1
  have hAllowance :=
    mul_nonneg (sub_nonneg.mpr hMinAB) (sub_nonneg.mpr hMinCD)
  have hFull : gatedTotalVariation r gate other = 1 - min (A * C) (B * D) := by
    rw [gatedTotalVariation_eq r hr gate other,
      overlapMass_split r keep gate other, overlapMass_split r keep other gate]
  have hRet : gatedTotalVariation r (maskedGate keep gate) (maskedGate keep other) =
      1 - min A B := gatedTotalVariation_eq r hr _ _
  have hTail : gatedTotalVariation r (removedGate keep gate) (removedGate keep other) =
      1 - min C D := gatedTotalVariation_eq r hr _ _
  rw [hFull, hRet, hTail]
  exact And.intro (by linarith) (And.intro (by nlinarith) (by nlinarith))

/-- The Hellinger chain identity keeps its exact negative compensation term. -/
theorem energy_projection_chain [DecidableEq I] (r : I -> Real)
    (hr : forall i, And (0 <= r i) (r i <= 1)) (keep gate other : I -> Bool) :
    gatedHellingerEnergy r gate other =
      gatedHellingerEnergy r (maskedGate keep gate) (maskedGate keep other) +
        gatedHellingerEnergy r (removedGate keep gate) (removedGate keep other) -
          gatedHellingerEnergy r (maskedGate keep gate) (maskedGate keep other) *
            gatedHellingerEnergy r (removedGate keep gate) (removedGate keep other) / 2 := by
  let A := overlapMass r (maskedGate keep gate) (maskedGate keep other)
  let B := overlapMass r (maskedGate keep other) (maskedGate keep gate)
  let C := overlapMass r (removedGate keep gate) (removedGate keep other)
  let D := overlapMass r (removedGate keep other) (removedGate keep gate)
  have hAB : 0 <= A * B :=
    mul_nonneg (overlapMass_nonneg r hr _ _) (overlapMass_nonneg r hr _ _)
  have hReorder : (A * C) * (B * D) = (A * B) * (C * D) := by ring
  have hFull : gatedHellingerEnergy r gate other =
      2 * (1 - Real.sqrt ((A * B) * (C * D))) := by
    rw [gatedHellingerEnergy_eq r hr gate other,
      overlapMass_split r keep gate other, overlapMass_split r keep other gate]
    change 2 * (1 - Real.sqrt ((A * C) * (B * D))) = _
    rw [hReorder]
  have hRet : gatedHellingerEnergy r (maskedGate keep gate) (maskedGate keep other) =
      2 * (1 - Real.sqrt (A * B)) := gatedHellingerEnergy_eq r hr _ _
  have hTail : gatedHellingerEnergy r (removedGate keep gate) (removedGate keep other) =
      2 * (1 - Real.sqrt (C * D)) := gatedHellingerEnergy_eq r hr _ _
  rw [hFull, hRet, hTail, Real.sqrt_mul hAB]
  ring

theorem energy_nonneg [DecidableEq I] (r : I -> Real) (gate other : I -> Bool) :
    0 <= gatedHellingerEnergy r gate other :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem energy_le_two [DecidableEq I] (r : I -> Real)
    (hr : forall i, And (0 <= r i) (r i <= 1)) (gate other : I -> Bool) :
    gatedHellingerEnergy r gate other <= 2 := by
  rw [gatedHellingerEnergy_eq r hr gate other]
  have h := Real.sqrt_nonneg (overlapMass r gate other * overlapMass r other gate)
  linarith

theorem energy_projection_bounds [DecidableEq I] (r : I -> Real)
    (hr : forall i, And (0 <= r i) (r i <= 1)) (keep gate other : I -> Bool) :
    And (0 <= gatedHellingerEnergy r gate other -
      gatedHellingerEnergy r (maskedGate keep gate) (maskedGate keep other))
      (gatedHellingerEnergy r gate other -
        gatedHellingerEnergy r (maskedGate keep gate) (maskedGate keep other) <=
          gatedHellingerEnergy r (removedGate keep gate) (removedGate keep other)) := by
  have hChain := energy_projection_chain r hr keep gate other
  have hRet0 := energy_nonneg r (maskedGate keep gate) (maskedGate keep other)
  have hRet2 := energy_le_two r hr (maskedGate keep gate) (maskedGate keep other)
  have hTail0 := energy_nonneg r (removedGate keep gate) (removedGate keep other)
  exact And.intro
    (by nlinarith [mul_nonneg (sub_nonneg.mpr hRet2) hTail0])
    (by nlinarith [mul_nonneg hRet0 hTail0])

end PrimeFactorOscillations.CarmichaelProfileProjection
