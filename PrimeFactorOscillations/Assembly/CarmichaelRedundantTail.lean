/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelFiberGeometry
import PrimeFactorOscillations.Helpers.PrimeReciprocalSquareTail
import PrimeFactorOscillations.Mathlib.Algebra.Order.BigOperators.Ring.ProductError

/-!
# Information carried by redundant large return labels

The exact two-fiber geometry is consumed before estimating its product.
The existing quadratic product-error theorem retains every cross term.
The existing prime reciprocal-square tail supplies a uniform arithmetic
majorant, rather than a new integer-tail approximation.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelRedundantTail

open CarmichaelFiberGeometry CarmichaelProfileKernel CarmichaelMaximalOrderLifts

variable {I : Type*} [Fintype I]

def mismatchRate (r : I -> Real) (gate other : I -> Bool) (i : I) : Real :=
  if gate i = other i then 0 else r i

def mismatchCost (r : I -> Real) (gate other : I -> Bool) : Real :=
  Finset.univ.sum (mismatchRate r gate other)

omit [Fintype I] in
theorem mismatchRate_bounds (r : I -> Real)
    (hr : forall i, And (0 <= r i) (r i <= 1)) (gate other : I -> Bool) (i : I) :
    And (0 <= mismatchRate r gate other i) (mismatchRate r gate other i <= 1) := by
  unfold mismatchRate
  split_ifs
  { exact And.intro le_rfl zero_le_one }
  { exact hr i }

theorem overlapMass_le_one (r : I -> Real)
    (hr : forall i, And (0 <= r i) (r i <= 1)) (gate other : I -> Bool) :
    overlapMass r gate other <= 1 := by
  classical
  let f : I -> Real := fun i => overlapFactor (r i) (gate i) (other i)
  have hf : forall i, And (0 <= f i) (f i <= 1) := by
    intro i
    cases hg : gate i <;> cases ho : other i <;>
      simp [f, overlapFactor, hg, ho]
    all_goals constructor <;> linarith [(hr i).1, (hr i).2]
  have hProduct : forall s : Finset I, s.prod f <= 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      simpa only [one_mul] using mul_le_mul (hf i).2 ih
        (Finset.prod_nonneg (fun j _ => (hf j).1)) (zero_le_one : (0 : Real) <= 1)
  exact hProduct Finset.univ

theorem combined_overlap_eq_product (r : I -> Real) (gate other : I -> Bool) :
    overlapMass r gate other * overlapMass r other gate =
      Finset.univ.prod (fun i => 1 - mismatchRate r gate other i) := by
  unfold overlapMass
  rw [<- Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases hg : gate i <;> cases ho : other i <;>
    simp [overlapFactor, mismatchRate, hg, ho]

/-- The existing product-error provider is applied to the complete coupled overlap. -/
theorem combined_overlap_error_bounds (r : I -> Real)
    (hr : forall i, And (0 <= r i) (r i <= 1)) (gate other : I -> Bool) :
    And (0 <= overlapMass r gate other * overlapMass r other gate - 1 +
      mismatchCost r gate other)
      (overlapMass r gate other * overlapMass r other gate - 1 +
        mismatchCost r gate other <= mismatchCost r gate other ^ 2 / 2) := by
  rw [combined_overlap_eq_product]
  exact Finset.prod_one_sub_linear_error_bounds Finset.univ
    (mismatchRate r gate other) (fun i _ => mismatchRate_bounds r hr gate other i)

/-- Total variation is controlled by the full reciprocal cost of gate disagreements. -/
theorem gated_variation_le_mismatch_cost [DecidableEq I] (r : I -> Real)
    (hr : forall i, And (0 <= r i) (r i <= 1)) (gate other : I -> Bool) :
    gatedTotalVariation r gate other <= mismatchCost r gate other := by
  have ha0 := overlapMass_nonneg r hr gate other
  have hb0 := overlapMass_nonneg r hr other gate
  have ha1 := overlapMass_le_one r hr gate other
  have hb1 := overlapMass_le_one r hr other gate
  have hCombined : overlapMass r gate other * overlapMass r other gate <=
      min (overlapMass r gate other) (overlapMass r other gate) := by
    apply le_min
    { nlinarith [mul_nonneg ha0 (sub_nonneg.mpr hb1)] }
    { nlinarith [mul_nonneg hb0 (sub_nonneg.mpr ha1)] }
  have hError := (combined_overlap_error_bounds r hr gate other).1
  rw [gatedTotalVariation_eq r hr gate other]
  linarith

theorem gated_energy_le_mismatch_cost [DecidableEq I] (r : I -> Real)
    (hr : forall i, And (0 <= r i) (r i <= 1)) (gate other : I -> Bool) :
    gatedHellingerEnergy r gate other <=
      2 * (1 - Real.sqrt (1 - mismatchCost r gate other)) := by
  have hError := (combined_overlap_error_bounds r hr gate other).1
  have hRoot := Real.sqrt_le_sqrt
    (show 1 - mismatchCost r gate other <=
      overlapMass r gate other * overlapMass r other gate by linarith)
  rw [gatedHellingerEnergy_eq r hr gate other]
  linarith

/-- Finite prime tails are bounded by the already proved infinite prime tail. -/
theorem finite_reciprocal_square_tail_le (S : Finset Nat.Primes) (Y : Nat)
    (hY : forall p, Membership.mem S p -> Y < (p : Nat)) :
    S.sum (fun p => 1 / (p : Real) ^ (2 : Nat)) <= primeReciprocalSquareTail Y := by
  classical
  let T := {p : Nat.Primes // Y < (p : Nat)}
  let e : S -> T := fun p => Subtype.mk p.val (hY p.val p.property)
  have he : Function.Injective e := by
    intro p q h
    have hVal : (e p).val = (e q).val := congrArg (fun z : T => z.val) h
    change p.val = q.val at hVal
    exact Subtype.ext hVal
  let t : Finset T := S.attach.image e
  have hSum : t.sum (fun p => 1 / (p.val : Real) ^ (2 : Nat)) =
      S.sum (fun p => 1 / (p : Real) ^ (2 : Nat)) := by
    rw [Finset.sum_image (fun p _ q _ h => he h)]
    change S.attach.sum (fun p => 1 / (p.val : Real) ^ (2 : Nat)) = _
    exact Finset.sum_attach S (fun p : Nat.Primes => 1 / (p : Real) ^ (2 : Nat))
  rw [<- hSum]
  exact Summable.sum_le_tsum t
    (fun p _ => div_nonneg zero_le_one (sq_nonneg _))
    (summable_prime_reciprocal_sq.subtype (fun p => Y < (p : Nat)))

/-- Hellinger energy has the exact reciprocal-cost main term with a quadratic error. -/
theorem gated_energy_linear_error [DecidableEq I] (r : I -> Real)
    (hr : forall i, And (0 <= r i) (r i <= 1)) (gate other : I -> Bool) :
    And (-(mismatchCost r gate other ^ 2) / 2 <=
      gatedHellingerEnergy r gate other - mismatchCost r gate other)
      (gatedHellingerEnergy r gate other - mismatchCost r gate other <=
        mismatchCost r gate other ^ 2) := by
  let P := overlapMass r gate other * overlapMass r other gate
  let C := mismatchCost r gate other
  let H := 2 * (1 - Real.sqrt P)
  have hP0 : 0 <= P :=
    mul_nonneg (overlapMass_nonneg r hr gate other) (overlapMass_nonneg r hr other gate)
  have hP1 : P <= 1 := by
    calc
      _ <= (1 : Real) * 1 := mul_le_mul (overlapMass_le_one r hr gate other)
        (overlapMass_le_one r hr other gate) (overlapMass_nonneg r hr other gate)
        zero_le_one
      _ = 1 := by norm_num
  have hC : 0 <= C :=
    Finset.sum_nonneg (fun i _ => (mismatchRate_bounds r hr gate other i).1)
  have hError := combined_overlap_error_bounds r hr gate other
  change And (0 <= P - 1 + C) (P - 1 + C <= C ^ 2 / 2) at hError
  have hSquare := Real.sq_sqrt hP0
  have hRoot0 := Real.sqrt_nonneg P
  have hRoot1 : Real.sqrt P <= 1 := by nlinarith
  have hRootP : P <= Real.sqrt P := by
    nlinarith [mul_nonneg hRoot0 (sub_nonneg.mpr hRoot1)]
  have hH0 : 0 <= H := by dsimp [H]; linarith
  have hHC : H <= 2 * C := by dsimp [H]; linarith [hError.1]
  have hIdentity : H - (1 - P) = H ^ 2 / 4 := by
    dsimp [H]
    nlinarith
  have hHSquare : H ^ 2 <= 4 * C ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hHC)
      (add_nonneg (mul_nonneg (by norm_num : (0 : Real) <= 2) hC) hH0)]
  rw [gatedHellingerEnergy_eq r hr gate other]
  change And (-(C ^ 2) / 2 <= H - C) (H - C <= C ^ 2)
  constructor
  { nlinarith [sq_nonneg H, hError.2] }
  { nlinarith [hError.1] }

def fiberMismatchCost (m B : Nat) [NeZero B] (a b : Units (ZMod m)) : Real :=
  mismatchCost (fun l : exponentPrimePacket (m * B) =>
    auxiliaryReturnRate m B (l.val : Nat))
    (fun l => returnGate m B a (l.val : Nat))
    (fun l => returnGate m B b (l.val : Nat))

/-- Only the actually mismatched labels enter the arithmetic tail. -/
theorem fiber_mismatch_cost_le_tail (m B : Nat) [NeZero B]
    (a b : Units (ZMod m)) (Y : Nat)
    (hAgree : forall l : exponentPrimePacket (m * B), (l.val : Nat) <= Y ->
      returnGate m B a (l.val : Nat) = returnGate m B b (l.val : Nat))
    (hRepeated : forall l : exponentPrimePacket (m * B),
      Not (returnGate m B a (l.val : Nat) = returnGate m B b (l.val : Nat)) ->
      (l.val : Nat) ^ (2 : Nat) <= PrimeOrderReturnLaw.returnIndex (G := Units (ZMod B))
        (Monoid.exponent (Units (ZMod (m * B)))) (l.val : Nat)) :
    fiberMismatchCost m B a b <= primeReciprocalSquareTail Y := by
  classical
  let S := exponentPrimePacket (m * B)
  let f : Nat.Primes -> Real := fun p =>
    if returnGate m B a (p : Nat) = returnGate m B b (p : Nat)
    then 0 else auxiliaryReturnRate m B (p : Nat)
  let D : Finset Nat.Primes := S.filter (fun p : Nat.Primes =>
    Not (returnGate m B a (p : Nat) = returnGate m B b (p : Nat)))
  have hCost : fiberMismatchCost m B a b =
      D.sum (fun p : Nat.Primes => auxiliaryReturnRate m B (p : Nat)) := by
    change S.attach.sum (fun l : S => f l.val) = _
    rw [Finset.sum_attach S f]
    dsimp only [D]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases h : returnGate m B a (p : Nat) = returnGate m B b (p : Nat) <;> simp [f, h]
  have hDY : forall p, Membership.mem D p -> Y < (p : Nat) := by
    intro p hp
    have h := Finset.mem_filter.mp hp
    by_contra hNot
    exact h.2 (hAgree (Subtype.mk p h.1) (Nat.le_of_not_gt hNot))
  calc
    _ = D.sum (fun p : Nat.Primes => auxiliaryReturnRate m B (p : Nat)) := hCost
    _ <= D.sum (fun p : Nat.Primes => 1 / (p : Real) ^ (2 : Nat)) := by
      apply Finset.sum_le_sum
      intro p hp
      have h := Finset.mem_filter.mp hp
      have hd := hRepeated (Subtype.mk p h.1) h.2
      have hdReal : (p : Real) ^ (2 : Nat) <=
          (PrimeOrderReturnLaw.returnIndex (G := Units (ZMod B))
            (Monoid.exponent (Units (ZMod (m * B)))) (p : Nat) : Real) := by
        exact_mod_cast hd
      exact one_div_le_one_div_of_le
        (sq_pos_of_pos (by exact_mod_cast p.property.pos)) hdReal
    _ <= primeReciprocalSquareTail Y := finite_reciprocal_square_tail_le D Y hDY

theorem fiber_variation_le_cost (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)] (hCoprime : Nat.Coprime m B)
    (a b : Units (ZMod m)) :
    fiberTotalVariation m B a b <= fiberMismatchCost m B a b := by
  unfold fiberTotalVariation fiberMismatchCost
  simp_rw [fiber_profile_eq_gatedLaw m B hCoprime a,
    fiber_profile_eq_gatedLaw m B hCoprime b]
  exact gated_variation_le_mismatch_cost
    (fun l : exponentPrimePacket (m * B) => auxiliaryReturnRate m B (l.val : Nat))
    (fun l : exponentPrimePacket (m * B) => auxiliaryReturnRate_bounds m B (l.val : Nat))
    (fun l : exponentPrimePacket (m * B) => returnGate m B a (l.val : Nat))
    (fun l : exponentPrimePacket (m * B) => returnGate m B b (l.val : Nat))

theorem fiber_energy_le_cost (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)] (hCoprime : Nat.Coprime m B)
    (a b : Units (ZMod m)) :
    fiberHellingerEnergy m B a b <=
      2 * (1 - Real.sqrt (1 - fiberMismatchCost m B a b)) := by
  unfold fiberHellingerEnergy fiberMismatchCost
  simp_rw [fiber_profile_eq_gatedLaw m B hCoprime a,
    fiber_profile_eq_gatedLaw m B hCoprime b]
  exact gated_energy_le_mismatch_cost
    (fun l : exponentPrimePacket (m * B) => auxiliaryReturnRate m B (l.val : Nat))
    (fun l : exponentPrimePacket (m * B) => auxiliaryReturnRate_bounds m B (l.val : Nat))
    (fun l : exponentPrimePacket (m * B) => returnGate m B a (l.val : Nat))
    (fun l : exponentPrimePacket (m * B) => returnGate m B b (l.val : Nat))

theorem fiber_energy_linear_error (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)] (hCoprime : Nat.Coprime m B)
    (a b : Units (ZMod m)) :
    And (-(fiberMismatchCost m B a b ^ 2) / 2 <=
      fiberHellingerEnergy m B a b - fiberMismatchCost m B a b)
      (fiberHellingerEnergy m B a b - fiberMismatchCost m B a b <=
        fiberMismatchCost m B a b ^ 2) := by
  unfold fiberHellingerEnergy fiberMismatchCost
  simp_rw [fiber_profile_eq_gatedLaw m B hCoprime a,
    fiber_profile_eq_gatedLaw m B hCoprime b]
  exact gated_energy_linear_error
    (fun l : exponentPrimePacket (m * B) => auxiliaryReturnRate m B (l.val : Nat))
    (fun l : exponentPrimePacket (m * B) => auxiliaryReturnRate_bounds m B (l.val : Nat))
    (fun l : exponentPrimePacket (m * B) => returnGate m B a (l.val : Nat))
    (fun l : exponentPrimePacket (m * B) => returnGate m B b (l.val : Nat))

/-- Uniform in both moduli, both old units, and the entire finite prime packet. -/
theorem fiber_distances_le_prime_tail (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)] (hCoprime : Nat.Coprime m B)
    (a b : Units (ZMod m)) (Y : Nat)
    (hAgree : forall l : exponentPrimePacket (m * B), (l.val : Nat) <= Y ->
      returnGate m B a (l.val : Nat) = returnGate m B b (l.val : Nat))
    (hRepeated : forall l : exponentPrimePacket (m * B),
      Not (returnGate m B a (l.val : Nat) = returnGate m B b (l.val : Nat)) ->
      (l.val : Nat) ^ (2 : Nat) <= PrimeOrderReturnLaw.returnIndex (G := Units (ZMod B))
        (Monoid.exponent (Units (ZMod (m * B)))) (l.val : Nat)) :
    And (fiberTotalVariation m B a b <= primeReciprocalSquareTail Y)
      (fiberHellingerEnergy m B a b <=
        2 * (1 - Real.sqrt (1 - primeReciprocalSquareTail Y))) := by
  have hCost := fiber_mismatch_cost_le_tail m B a b Y hAgree hRepeated
  apply And.intro ((fiber_variation_le_cost m B hCoprime a b).trans hCost)
  have hEnergy := fiber_energy_le_cost m B hCoprime a b
  have hRoot := Real.sqrt_le_sqrt (show
    1 - primeReciprocalSquareTail Y <= 1 - fiberMismatchCost m B a b by linarith)
  linarith

theorem reciprocal_tail_bounds (Y : Nat) (hY : 1 <= Y) :
    And (0 <= primeReciprocalSquareTail Y)
      (primeReciprocalSquareTail Y <= 2 / (Y : Real)) := by
  have hShift := primeProfileQuadraticTail_shift_bound Y hY
  have hQuad := primeProfileQuadraticTail_bounds Y hY
  apply And.intro
  { exact tsum_nonneg (fun p => div_nonneg zero_le_one (sq_nonneg _)) }
  { linarith [hShift.1, hQuad.2] }

open Filter

theorem tendsto_reciprocal_tail_zero :
    Tendsto primeReciprocalSquareTail atTop (nhds (0 : Real)) := by
  have hInv : Tendsto (fun Y : Nat => Inv.inv (Y : Real)) atTop (nhds (0 : Real)) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun Y : Nat => (Y : Real)) atTop atTop)
  have hUpper : Tendsto (fun Y : Nat => 2 / (Y : Real)) atTop (nhds (0 : Real)) := by
    simpa only [div_eq_mul_inv, mul_zero] using hInv.const_mul (2 : Real)
  apply squeeze_zero_norm' (a := fun Y : Nat => 2 / (Y : Real)) ?_ hUpper
  filter_upwards [eventually_ge_atTop (1 : Nat)] with Y hY
  rw [Real.norm_eq_abs, abs_of_nonneg (reciprocal_tail_bounds Y hY).1]
  exact (reciprocal_tail_bounds Y hY).2

def redundantEnergyTail (Y : Nat) : Real :=
  2 * (1 - Real.sqrt (1 - primeReciprocalSquareTail Y))

theorem redundantEnergyTail_eq_rational (Y : Nat) (hY : 2 <= Y) :
    redundantEnergyTail Y =
      2 * primeReciprocalSquareTail Y /
        (1 + Real.sqrt (1 - primeReciprocalSquareTail Y)) := by
  have hYR : (2 : Real) <= Y := by exact_mod_cast hY
  have hYPos : (0 : Real) < Y := by linarith
  have hT : primeReciprocalSquareTail Y <= 1 :=
    (reciprocal_tail_bounds Y (by omega)).2.trans ((div_le_one hYPos).mpr hYR)
  have hDen : 0 < 1 + Real.sqrt (1 - primeReciprocalSquareTail Y) := by
    have h := Real.sqrt_nonneg (1 - primeReciprocalSquareTail Y)
    linarith
  unfold redundantEnergyTail
  apply (eq_div_iff (ne_of_gt hDen)).mpr
  nlinarith [Real.sq_sqrt (sub_nonneg.mpr hT)]

/-- The energy majorant has leading constant one at the prime-tail scale. -/
theorem tendsto_redundantEnergyTail_scaled :
    Tendsto (fun Y : Nat => redundantEnergyTail Y *
      ((Y : Real) * Real.log (Y : Real))) atTop (nhds (1 : Real)) := by
  have hDiff : Tendsto (fun Y : Nat => 1 - primeReciprocalSquareTail Y)
      atTop (nhds (1 : Real)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub tendsto_reciprocal_tail_zero
  have hRoot : Tendsto (fun Y : Nat => Real.sqrt (1 - primeReciprocalSquareTail Y))
      atTop (nhds (1 : Real)) := by
    simpa only [Real.sqrt_one] using hDiff.sqrt
  have hDen : Tendsto (fun Y : Nat => 1 + Real.sqrt (1 - primeReciprocalSquareTail Y))
      atTop (nhds (2 : Real)) := by
    simpa only [show (1 : Real) + 1 = 2 by norm_num] using
      (show Tendsto (fun _ : Nat => (1 : Real)) atTop (nhds (1 : Real)) from
        tendsto_const_nhds).add hRoot
  have hRatio := (tendsto_primeReciprocalSquareTail_scaled.const_mul (2 : Real)).div
    hDen (by norm_num : Not ((2 : Real) = 0))
  have hRatio' : Tendsto
      ((fun Y : Nat => 2 * (primeReciprocalSquareTail Y * ((Y : Real) * Real.log (Y : Real)))) /
        (fun Y : Nat => 1 + Real.sqrt (1 - primeReciprocalSquareTail Y)))
      atTop (nhds (1 : Real)) := by
    simpa only [mul_one, div_self (by norm_num : Not ((2 : Real) = 0))] using hRatio
  apply hRatio'.congr'
  filter_upwards [eventually_ge_atTop (2 : Nat)] with Y hY
  simp only [Pi.div_apply]
  rw [redundantEnergyTail_eq_rational Y hY]
  ring

/-- For squarefree auxiliary moduli, two actual carriers per disagreement suffice. -/
theorem squarefree_fiber_distances_le_prime_tail (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)] (hSqB : Squarefree B)
    (hCoprime : Nat.Coprime m B) (a b : Units (ZMod m)) (Y : Nat)
    (hAgree : forall l : exponentPrimePacket (m * B), (l.val : Nat) <= Y ->
      returnGate m B a (l.val : Nat) = returnGate m B b (l.val : Nat))
    (hRepeated : forall l : exponentPrimePacket (m * B),
      Not (returnGate m B a (l.val : Nat) = returnGate m B b (l.val : Nat)) ->
      2 <= CarmichaelConditionalRigidity.auxiliaryRank m B l.val) :
    And (fiberTotalVariation m B a b <= primeReciprocalSquareTail Y)
      (fiberHellingerEnergy m B a b <= redundantEnergyTail Y) := by
  apply fiber_distances_le_prime_tail m B hCoprime a b Y hAgree
  intro l hDiff
  exact CarmichaelConditionalRigidity.auxiliary_power_le_index m B hSqB hCoprime l.val
    ((exponentPrimePacket_mem (m * B) l.val).mp l.property) 2 (hRepeated l hDiff)

end PrimeFactorOscillations.CarmichaelRedundantTail
