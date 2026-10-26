/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelConditionalStability

/-!
# Exact geometry of gated conditional return profiles

Two old units have the same auxiliary image probabilities. Only their
gate disagreements distinguish the conditional laws. Their common
part has two explicit masses; its smaller mass is the exact overlap.
No feasibility or positive-vacancy normalization is needed.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelFiberGeometry

open CarmichaelProfileKernel CarmichaelMaximalOrderLifts PrimeOrderReturnLaw

def gatedFactor (r : Real) (gate bit : Bool) : Real :=
  if gate then if bit then r else 1 - r else if bit then 0 else 1

def overlapFactor (r : Real) (gate other : Bool) : Real :=
  if gate then if other then 1 else 1 - r else 1

def commonFactor (r : Real) (gate other bit : Bool) : Real :=
  if gate = other then gatedFactor r gate bit else if bit then 0 else 1

variable {I : Type*} [Fintype I] [DecidableEq I]

def gatedLaw (r : I -> Real) (gate : I -> Bool) (bits : I -> Bool) : Real :=
  Finset.univ.prod (fun i => gatedFactor (r i) (gate i) (bits i))

def overlapMass (r : I -> Real) (gate other : I -> Bool) : Real :=
  Finset.univ.prod (fun i => overlapFactor (r i) (gate i) (other i))

def commonLaw (r : I -> Real) (gate other : I -> Bool) (bits : I -> Bool) : Real :=
  Finset.univ.prod (fun i => commonFactor (r i) (gate i) (other i) (bits i))

theorem gatedFactor_nonneg (r : Real) (hr0 : 0 <= r) (hr1 : r <= 1)
    (gate bit : Bool) : 0 <= gatedFactor r gate bit := by
  cases gate <;> cases bit <;> simp [gatedFactor, hr0, sub_nonneg.mpr hr1]

omit [DecidableEq I] in
theorem gatedLaw_nonneg (r : I -> Real)
    (hr : forall i, And (0 <= r i) (r i <= 1)) (gate bits : I -> Bool) :
    0 <= gatedLaw r gate bits := by
  exact Finset.prod_nonneg (fun i _ => gatedFactor_nonneg _ (hr i).1 (hr i).2 _ _)

omit [DecidableEq I] in
theorem commonLaw_nonneg (r : I -> Real)
    (hr : forall i, And (0 <= r i) (r i <= 1)) (gate other bits : I -> Bool) :
    0 <= commonLaw r gate other bits := by
  apply Finset.prod_nonneg
  intro i _
  unfold commonFactor
  split_ifs
  { exact gatedFactor_nonneg _ (hr i).1 (hr i).2 _ _ }
  { exact le_rfl }
  { exact zero_le_one }

theorem gatedLaw_sum_one (r : I -> Real) (gate : I -> Bool) :
    Finset.univ.sum (gatedLaw r gate) = 1 := by
  classical
  unfold gatedLaw
  calc
    _ = Finset.univ.prod (fun i => Finset.univ.sum
        (fun bit : Bool => gatedFactor (r i) (gate i) bit)) :=
      (Fintype.prod_sum (fun (i : I) (bit : Bool) =>
        gatedFactor (r i) (gate i) bit)).symm
    _ = 1 := by
      apply Finset.prod_eq_one
      intro i _
      cases gate i <;> simp [gatedFactor]

theorem commonLaw_sum_one (r : I -> Real) (gate other : I -> Bool) :
    Finset.univ.sum (commonLaw r gate other) = 1 := by
  classical
  unfold commonLaw
  calc
    _ = Finset.univ.prod (fun i => Finset.univ.sum
        (fun bit : Bool => commonFactor (r i) (gate i) (other i) bit)) :=
      (Fintype.prod_sum (fun (i : I) (bit : Bool) =>
        commonFactor (r i) (gate i) (other i) bit)).symm
    _ = 1 := by
      apply Finset.prod_eq_one
      intro i _
      cases gate i <;> cases other i <;> simp [commonFactor, gatedFactor]

omit [DecidableEq I] in
theorem gatedLaw_eq_common_on_quiet (r : I -> Real) (gate other bits : I -> Bool)
    (hQuiet : forall i, bits i = true -> gate i = other i) :
    gatedLaw r gate bits = overlapMass r gate other * commonLaw r gate other bits := by
  have hLocal (i : I) :
      gatedFactor (r i) (gate i) (bits i) =
        overlapFactor (r i) (gate i) (other i) *
          commonFactor (r i) (gate i) (other i) (bits i) := by
    have h := hQuiet i
    cases hg : gate i <;> cases ho : other i <;> cases hb : bits i <;>
      simp_all [gatedFactor, overlapFactor, commonFactor]
  unfold gatedLaw overlapMass commonLaw
  simp_rw [hLocal]
  rw [Finset.prod_mul_distrib]

omit [DecidableEq I] in
theorem commonLaw_symm (r : I -> Real) (gate other bits : I -> Bool) :
    commonLaw r gate other bits = commonLaw r other gate bits := by
  apply Finset.prod_congr rfl
  intro i _
  cases gate i <;> cases other i <;> simp [commonFactor]

omit [DecidableEq I] in
/-- The entire common part has one scalar mass in each conditional law. -/
theorem gatedLaw_min_eq_common (r : I -> Real)
    (hr : forall i, And (0 <= r i) (r i <= 1)) (gate other bits : I -> Bool) :
    min (gatedLaw r gate bits) (gatedLaw r other bits) =
      min (overlapMass r gate other) (overlapMass r other gate) *
        commonLaw r gate other bits := by
  classical
  by_cases hQuiet : forall i, bits i = true -> gate i = other i
  { have hReverse : forall i, bits i = true -> other i = gate i := by
      intro i hi
      exact (hQuiet i hi).symm
    rw [gatedLaw_eq_common_on_quiet r gate other bits hQuiet,
      gatedLaw_eq_common_on_quiet r other gate bits hReverse,
      <- commonLaw_symm r gate other bits]
    have hC := commonLaw_nonneg r hr gate other bits
    by_cases h : overlapMass r gate other <= overlapMass r other gate
    { rw [min_eq_left h, min_eq_left (mul_le_mul_of_nonneg_right h hC)] }
    { have h := (not_le.mp h).le
      rw [min_eq_right h, min_eq_right (mul_le_mul_of_nonneg_right h hC)] } }
  { have hWitness : Exists (fun i => And (bits i = true) (Not (gate i = other i))) := by
      by_contra hNo
      apply hQuiet
      intro i hi
      by_contra hDiff
      exact hNo (Exists.intro i (And.intro hi hDiff))
    choose i hi using hWitness
    have hCommon : commonLaw r gate other bits = 0 := by
      unfold commonLaw
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [commonFactor, hi.1, hi.2]
    have hZero : Or (gatedLaw r gate bits = 0) (gatedLaw r other bits = 0) := by
      cases hg : gate i
      { apply Or.inl
        unfold gatedLaw
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [gatedFactor, hg, hi.1] }
      { apply Or.inr
        have ho : other i = false := by
          cases ho : other i
          { rfl }
          { exact False.elim (hi.2 (hg.trans ho.symm)) }
        unfold gatedLaw
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [gatedFactor, ho, hi.1] }
    rw [hCommon, mul_zero]
    cases hZero with
    | inl h =>
      rw [h, min_eq_left (gatedLaw_nonneg r hr other bits)]
    | inr h =>
      rw [h, min_eq_right (gatedLaw_nonneg r hr gate bits)] }

theorem gatedLaw_overlap_sum (r : I -> Real)
    (hr : forall i, And (0 <= r i) (r i <= 1)) (gate other : I -> Bool) :
    Finset.univ.sum (fun bits : I -> Bool =>
      min (gatedLaw r gate bits) (gatedLaw r other bits)) =
      min (overlapMass r gate other) (overlapMass r other gate) := by
  simp_rw [gatedLaw_min_eq_common r hr gate other]
  rw [<- Finset.mul_sum, commonLaw_sum_one, mul_one]

def gatedTotalVariation (r : I -> Real) (gate other : I -> Bool) : Real :=
  (1 / 2 : Real) * Finset.univ.sum (fun bits : I -> Bool =>
    abs (gatedLaw r gate bits - gatedLaw r other bits))

/-- Exact variation retains both directions of gate mismatch and every product term. -/
theorem gatedTotalVariation_eq (r : I -> Real)
    (hr : forall i, And (0 <= r i) (r i <= 1)) (gate other : I -> Bool) :
    gatedTotalVariation r gate other =
      1 - min (overlapMass r gate other) (overlapMass r other gate) := by
  have hAbs (x y : Real) : abs (x - y) = x + y - 2 * min x y := by
    by_cases h : x <= y
    { rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
      ring }
    { have h := (not_le.mp h).le
      rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
      ring }
  unfold gatedTotalVariation
  simp_rw [hAbs]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, <- Finset.mul_sum,
    gatedLaw_sum_one, gatedLaw_sum_one, gatedLaw_overlap_sum r hr gate other]
  ring

omit [DecidableEq I] in
theorem overlapMass_nonneg (r : I -> Real)
    (hr : forall i, And (0 <= r i) (r i <= 1)) (gate other : I -> Bool) :
    0 <= overlapMass r gate other := by
  apply Finset.prod_nonneg
  intro i _
  cases gate i <;> cases other i <;> simp [overlapFactor, sub_nonneg.mpr (hr i).2]

omit [DecidableEq I] in
theorem gatedLaw_product_eq (r : I -> Real) (gate other bits : I -> Bool) :
    gatedLaw r gate bits * gatedLaw r other bits =
      (overlapMass r gate other * overlapMass r other gate) *
        commonLaw r gate other bits ^ 2 := by
  have hLocal (i : I) :
      gatedFactor (r i) (gate i) (bits i) * gatedFactor (r i) (other i) (bits i) =
        (overlapFactor (r i) (gate i) (other i) *
          overlapFactor (r i) (other i) (gate i)) *
            commonFactor (r i) (gate i) (other i) (bits i) ^ 2 := by
    cases gate i <;> cases other i <;> cases bits i <;>
      simp [gatedFactor, overlapFactor, commonFactor, pow_two]
  unfold gatedLaw overlapMass commonLaw
  rw [<- Finset.prod_mul_distrib]
  simp_rw [hLocal]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow]

theorem gatedLaw_affinity_eq (r : I -> Real)
    (hr : forall i, And (0 <= r i) (r i <= 1)) (gate other : I -> Bool) :
    Finset.univ.sum (fun bits : I -> Bool =>
      Real.sqrt (gatedLaw r gate bits) * Real.sqrt (gatedLaw r other bits)) =
      Real.sqrt (overlapMass r gate other * overlapMass r other gate) := by
  have hPoint (bits : I -> Bool) :
      Real.sqrt (gatedLaw r gate bits) * Real.sqrt (gatedLaw r other bits) =
        Real.sqrt (overlapMass r gate other * overlapMass r other gate) *
          commonLaw r gate other bits := by
    calc
      _ = Real.sqrt (gatedLaw r gate bits * gatedLaw r other bits) :=
        (Real.sqrt_mul (gatedLaw_nonneg r hr gate bits) _).symm
      _ = _ := by
        rw [gatedLaw_product_eq,
          Real.sqrt_mul (mul_nonneg (overlapMass_nonneg r hr gate other)
            (overlapMass_nonneg r hr other gate)),
          Real.sqrt_sq (commonLaw_nonneg r hr gate other bits)]
  simp_rw [hPoint]
  rw [<- Finset.mul_sum, commonLaw_sum_one, mul_one]

def gatedHellingerEnergy (r : I -> Real) (gate other : I -> Bool) : Real :=
  Finset.univ.sum (fun bits : I -> Bool =>
    (Real.sqrt (gatedLaw r gate bits) - Real.sqrt (gatedLaw r other bits)) ^ 2)

/-- Exact affinity, including disjoint-support and deterministic-return cases. -/
theorem gatedHellingerEnergy_eq (r : I -> Real)
    (hr : forall i, And (0 <= r i) (r i <= 1)) (gate other : I -> Bool) :
    gatedHellingerEnergy r gate other =
      2 * (1 - Real.sqrt (overlapMass r gate other * overlapMass r other gate)) := by
  have hPoint (bits : I -> Bool) :
      (Real.sqrt (gatedLaw r gate bits) - Real.sqrt (gatedLaw r other bits)) ^ 2 =
        gatedLaw r gate bits + gatedLaw r other bits -
          2 * (Real.sqrt (gatedLaw r gate bits) * Real.sqrt (gatedLaw r other bits)) := by
    nlinarith [Real.sq_sqrt (gatedLaw_nonneg r hr gate bits),
      Real.sq_sqrt (gatedLaw_nonneg r hr other bits)]
  unfold gatedHellingerEnergy
  simp_rw [hPoint]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, <- Finset.mul_sum,
    gatedLaw_sum_one, gatedLaw_sum_one, gatedLaw_affinity_eq r hr gate other]
  ring

local instance imageFintype {G : Type*} [CommGroup G] [Fintype G] (L l : Nat) :
    Fintype (returnImage (G := G) L l) :=
  PrimeOrderReturnLaw.imageFintype L l

def auxiliaryReturnRate (m B : Nat) [NeZero B] (l : Nat) : Real :=
  1 / (returnIndex (G := Units (ZMod B))
    (Monoid.exponent (Units (ZMod (m * B)))) l : Real)

theorem auxiliaryReturnRate_bounds (m B : Nat) [NeZero B] (l : Nat) :
    And (0 <= auxiliaryReturnRate m B l) (auxiliaryReturnRate m B l <= 1) := by
  have hPos : 0 < returnIndex (G := Units (ZMod B))
      (Monoid.exponent (Units (ZMod (m * B)))) l :=
    Fintype.card_pos_iff.mpr (Nonempty.intro 1)
  have hReal : (0 : Real) < (returnIndex (G := Units (ZMod B))
      (Monoid.exponent (Units (ZMod (m * B)))) l : Real) := by exact_mod_cast hPos
  have hOne : (1 : Real) <= (returnIndex (G := Units (ZMod B))
      (Monoid.exponent (Units (ZMod (m * B)))) l : Real) := by
    exact_mod_cast (Nat.succ_le_of_lt hPos)
  exact And.intro (one_div_pos.mpr hReal).le ((div_le_one hReal).mpr hOne)

theorem fiber_profile_eq_gatedLaw (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)] (hCoprime : Nat.Coprime m B)
    (a : Units (ZMod m)) (bits : exponentPrimePacket (m * B) -> Bool) :
    fiberProfileProbability m B a (exponentPrimePacket (m * B)) bits =
      gatedLaw (fun l : exponentPrimePacket (m * B) =>
        auxiliaryReturnRate m B (l.val : Nat))
        (fun l => returnGate m B a (l.val : Nat)) bits := by
  rw [fiberProfileProbability_eq_product m B hCoprime a _
    (fun l => (exponentPrimePacket_mem (m * B) l.val).mp l.property) bits]
  rfl

def fiberOverlapMass (m B : Nat) [NeZero B] (a b : Units (ZMod m)) : Real :=
  overlapMass (fun l : exponentPrimePacket (m * B) =>
    auxiliaryReturnRate m B (l.val : Nat))
    (fun l => returnGate m B a (l.val : Nat))
    (fun l => returnGate m B b (l.val : Nat))

def fiberTotalVariation (m B : Nat) (a b : Units (ZMod m)) : Real :=
  (1 / 2 : Real) * Finset.univ.sum (fun bits : exponentPrimePacket (m * B) -> Bool =>
    abs (fiberProfileProbability m B a (exponentPrimePacket (m * B)) bits -
      fiberProfileProbability m B b (exponentPrimePacket (m * B)) bits))

def fiberHellingerEnergy (m B : Nat) (a b : Units (ZMod m)) : Real :=
  Finset.univ.sum (fun bits : exponentPrimePacket (m * B) -> Bool =>
    (Real.sqrt (fiberProfileProbability m B a (exponentPrimePacket (m * B)) bits) -
      Real.sqrt (fiberProfileProbability m B b (exponentPrimePacket (m * B)) bits)) ^ 2)

/-- Exact distance of two actual fibers, with neither vacancy divided out. -/
theorem fiberTotalVariation_eq (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)] (hCoprime : Nat.Coprime m B)
    (a b : Units (ZMod m)) :
    fiberTotalVariation m B a b =
      1 - min (fiberOverlapMass m B a b) (fiberOverlapMass m B b a) := by
  unfold fiberTotalVariation fiberOverlapMass
  simp_rw [fiber_profile_eq_gatedLaw m B hCoprime a,
    fiber_profile_eq_gatedLaw m B hCoprime b]
  exact gatedTotalVariation_eq (fun l : exponentPrimePacket (m * B) => auxiliaryReturnRate m B (l.val : Nat))
    (fun l : exponentPrimePacket (m * B) => auxiliaryReturnRate_bounds m B (l.val : Nat))
    (fun l : exponentPrimePacket (m * B) => returnGate m B a (l.val : Nat))
    (fun l : exponentPrimePacket (m * B) => returnGate m B b (l.val : Nat))

theorem fiberHellingerEnergy_eq (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)] (hCoprime : Nat.Coprime m B)
    (a b : Units (ZMod m)) :
    fiberHellingerEnergy m B a b =
      2 * (1 - Real.sqrt (fiberOverlapMass m B a b * fiberOverlapMass m B b a)) := by
  unfold fiberHellingerEnergy fiberOverlapMass
  simp_rw [fiber_profile_eq_gatedLaw m B hCoprime a,
    fiber_profile_eq_gatedLaw m B hCoprime b]
  exact gatedHellingerEnergy_eq (fun l : exponentPrimePacket (m * B) => auxiliaryReturnRate m B (l.val : Nat))
    (fun l : exponentPrimePacket (m * B) => auxiliaryReturnRate_bounds m B (l.val : Nat))
    (fun l : exponentPrimePacket (m * B) => returnGate m B a (l.val : Nat))
    (fun l : exponentPrimePacket (m * B) => returnGate m B b (l.val : Nat))

theorem fiberOverlapMass_nonneg (m B : Nat) [NeZero B] (a b : Units (ZMod m)) :
    0 <= fiberOverlapMass m B a b :=
  overlapMass_nonneg (fun l : exponentPrimePacket (m * B) => auxiliaryReturnRate m B (l.val : Nat))
    (fun l : exponentPrimePacket (m * B) => auxiliaryReturnRate_bounds m B (l.val : Nat))
    (fun l : exponentPrimePacket (m * B) => returnGate m B a (l.val : Nat))
    (fun l : exponentPrimePacket (m * B) => returnGate m B b (l.val : Nat))

/-- A deterministic auxiliary return at a mismatched gate makes the overlap zero. -/
theorem fiberOverlapMass_zero_of_frozen_gate (m B : Nat) [NeZero B]
    (a b : Units (ZMod m)) (l : exponentPrimePacket (m * B))
    (ha : returnGate m B a (l.val : Nat) = true)
    (hb : returnGate m B b (l.val : Nat) = false)
    (hIndex : returnIndex (G := Units (ZMod B))
      (Monoid.exponent (Units (ZMod (m * B)))) (l.val : Nat) = 1) :
    fiberOverlapMass m B a b = 0 := by
  unfold fiberOverlapMass overlapMass
  apply Finset.prod_eq_zero (Finset.mem_univ l)
  simp [overlapFactor, auxiliaryReturnRate, ha, hb, hIndex]

/-- The singular branch has maximal variation and Hellinger energy exactly. -/
theorem fiber_distances_of_frozen_gate (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)] (hCoprime : Nat.Coprime m B)
    (a b : Units (ZMod m)) (l : exponentPrimePacket (m * B))
    (ha : returnGate m B a (l.val : Nat) = true)
    (hb : returnGate m B b (l.val : Nat) = false)
    (hIndex : returnIndex (G := Units (ZMod B))
      (Monoid.exponent (Units (ZMod (m * B)))) (l.val : Nat) = 1) :
    And (fiberTotalVariation m B a b = 1) (fiberHellingerEnergy m B a b = 2) := by
  have hZero := fiberOverlapMass_zero_of_frozen_gate m B a b l ha hb hIndex
  rw [fiberTotalVariation_eq m B hCoprime a b,
    fiberHellingerEnergy_eq m B hCoprime a b, hZero]
  simp [min_eq_left (fiberOverlapMass_nonneg m B b a)]

end PrimeFactorOscillations.CarmichaelFiberGeometry
