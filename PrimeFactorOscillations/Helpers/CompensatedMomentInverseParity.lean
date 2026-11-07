/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThreeLineEffectiveParityThreshold

/-! # Quantitative inverse geometry of the compensated parity cost -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def compensatedQuadraticRadius (a b z : Real) : Real :=
  (2 * z) / (b + Real.sqrt (b ^ 2 + 4 * a * z))

def compensatedParityInverseRadius (mass slack : Real) : Real :=
  compensatedQuadraticRadius (momentRoundThreshold - 1 / 4)
    (momentRoundThreshold * mass) (mass * slack)

def compensatedParityJointRadius (mass slack coefficient : Real) : Real :=
  min (compensatedParityInverseRadius mass slack) (slack / coefficient)

theorem compensatedQuadraticRadius_denominator_pos (a b z : Real) (hb : 0 < b) :
    0 < b + Real.sqrt (b ^ 2 + 4 * a * z) := by
  linarith [Real.sqrt_nonneg (b ^ 2 + 4 * a * z)]

theorem compensatedQuadraticRadius_nonneg (a b z : Real) (hb : 0 < b) (hz : 0 <= z) :
    0 <= compensatedQuadraticRadius a b z := by
  unfold compensatedQuadraticRadius
  exact div_nonneg (by linarith) (le_of_lt (compensatedQuadraticRadius_denominator_pos a b z hb))

theorem compensatedQuadraticRadius_equation (a b z : Real)
    (ha : 0 <= a) (hb : 0 < b) (hz : 0 <= z) :
    a * (compensatedQuadraticRadius a b z) ^ 2 +
      b * compensatedQuadraticRadius a b z = z := by
  have hDisc : 0 <= b ^ 2 + 4 * a * z := by
    have hMul := mul_nonneg ha hz
    nlinarith [sq_nonneg b]
  have hSquare := Real.sq_sqrt hDisc
  have hScaled := congrArg (fun v : Real => z * v) hSquare
  have hDen := compensatedQuadraticRadius_denominator_pos a b z hb
  have hDenComm : Not (Real.sqrt (b ^ 2 + 4 * a * z) + b = 0) := by
    linarith [Real.sqrt_nonneg (b ^ 2 + 4 * a * z)]
  unfold compensatedQuadraticRadius
  have hArgument : b ^ 2 + a * z * 4 = b ^ 2 + 4 * a * z := by ring
  field_simp [hDen.ne', hDenComm]
  rw [hArgument]
  nlinarith only [hScaled]

theorem compensatedQuadraticCost_order (a b x y : Real)
    (ha : 0 <= a) (hb : 0 < b) (hx : 0 <= x) (hy : 0 <= y) :
    (a * x ^ 2 + b * x <= a * y ^ 2 + b * y) <-> x <= y := by
  have hPositive : 0 < a * (x + y) + b := by
    have hMul := mul_nonneg ha (add_nonneg hx hy)
    linarith
  constructor
  case mp =>
    intro hCost
    by_contra hNot
    have hProduct := mul_pos (sub_pos.mpr (lt_of_not_ge hNot)) hPositive
    nlinarith only [hCost, hProduct]
  case mpr =>
    intro hOrder
    have hProduct := mul_nonneg (sub_nonneg.mpr hOrder) (le_of_lt hPositive)
    nlinarith only [hProduct]

theorem compensatedQuadraticCost_strict_order (a b x y : Real)
    (ha : 0 <= a) (hb : 0 < b) (hx : 0 <= x) (hy : 0 <= y) :
    (a * x ^ 2 + b * x < a * y ^ 2 + b * y) <-> x < y := by
  constructor
  case mp =>
    intro hCost
    by_contra hNot
    have hOrder := (compensatedQuadraticCost_order a b y x ha hb hy hx).mpr (le_of_not_gt hNot)
    exact (not_lt_of_ge hOrder) hCost
  case mpr =>
    intro hOrder
    by_contra hNot
    have hReverse := (compensatedQuadraticCost_order a b y x ha hb hy hx).mp (le_of_not_gt hNot)
    exact (not_lt_of_ge hReverse) hOrder

theorem compensatedQuadraticRadius_bound_iff (a b z x : Real)
    (ha : 0 <= a) (hb : 0 < b) (hz : 0 <= z) (hx : 0 <= x) :
    (a * x ^ 2 + b * x <= z) <-> x <= compensatedQuadraticRadius a b z := by
  have hOrder := compensatedQuadraticCost_order a b x (compensatedQuadraticRadius a b z)
    ha hb hx (compensatedQuadraticRadius_nonneg a b z hb hz)
  rw [compensatedQuadraticRadius_equation a b z ha hb hz] at hOrder
  exact hOrder

theorem compensatedQuadraticRadius_lt_iff (a b z r : Real)
    (ha : 0 <= a) (hb : 0 < b) (hz : 0 <= z) (hr : 0 <= r) :
    (compensatedQuadraticRadius a b z < r) <-> z < a * r ^ 2 + b * r := by
  have hOrder := compensatedQuadraticCost_strict_order a b
    (compensatedQuadraticRadius a b z) r ha hb
    (compensatedQuadraticRadius_nonneg a b z hb hz) hr
  rw [compensatedQuadraticRadius_equation a b z ha hb hz] at hOrder
  exact hOrder.symm

theorem compensatedQuadraticRadius_zero (a b : Real) :
    compensatedQuadraticRadius a b 0 = 0 := by
  simp [compensatedQuadraticRadius]

theorem compensatedParityInverseRadius_nonneg (mass slack : Real)
    (hMass : 0 < mass) (hSlack : 0 <= slack) :
    0 <= compensatedParityInverseRadius mass slack := by
  exact compensatedQuadraticRadius_nonneg _ _ _
    (mul_pos momentRoundThreshold_bounds.1 hMass) (mul_nonneg (le_of_lt hMass) hSlack)

theorem compensatedParityInverseRadius_bound (mass discrepancy slack : Real)
    (hMass : 0 < mass) (hSlack : 0 <= slack)
    (hCost : compensatedParityStabilityCost mass discrepancy <= slack) :
    abs discrepancy <= compensatedParityInverseRadius mass slack := by
  rw [compensatedParityStabilityCost_formula] at hCost
  have hScaled := _root_.mul_le_mul_of_nonneg_right hCost (le_of_lt hMass)
  have hCancel : ((momentRoundThreshold - 1 / 4) * discrepancy ^ 2 / mass) * mass =
      (momentRoundThreshold - 1 / 4) * discrepancy ^ 2 := by field_simp [hMass.ne']
  have hQuad : (momentRoundThreshold - 1 / 4) * (abs discrepancy) ^ 2 +
      (momentRoundThreshold * mass) * abs discrepancy <= mass * slack := by
    rw [sq_abs]
    nlinarith only [hScaled, hCancel]
  exact (compensatedQuadraticRadius_bound_iff _ _ _ _
    (le_of_lt (sub_pos.mpr momentRoundThreshold_gt_quarter))
    (mul_pos momentRoundThreshold_bounds.1 hMass)
    (mul_nonneg (le_of_lt hMass) hSlack) (abs_nonneg discrepancy)).mp hQuad

theorem compensatedParityInverseRadius_lt_one_iff (mass slack : Real)
    (hMass : 0 < mass) (hSlack : 0 <= slack) :
    (compensatedParityInverseRadius mass slack < 1) <->
      slack < momentRoundThreshold + (momentRoundThreshold - 1 / 4) / mass := by
  have hOrder := compensatedQuadraticRadius_lt_iff (momentRoundThreshold - 1 / 4)
    (momentRoundThreshold * mass) (mass * slack) 1
    (le_of_lt (sub_pos.mpr momentRoundThreshold_gt_quarter))
    (mul_pos momentRoundThreshold_bounds.1 hMass)
    (mul_nonneg (le_of_lt hMass) hSlack) (show (0 : Real) <= 1 by norm_num)
  have hCancel : ((momentRoundThreshold - 1 / 4) / mass) * mass =
      momentRoundThreshold - 1 / 4 := by field_simp [hMass.ne']
  constructor
  case mp =>
    intro hRadius
    have hCost := hOrder.mp hRadius
    norm_num only [one_pow, mul_one] at hCost
    by_contra hNot
    have hScaled := _root_.mul_le_mul_of_nonneg_right (le_of_not_gt hNot) (le_of_lt hMass)
    nlinarith only [hCost, hCancel, hScaled]
  case mpr =>
    intro hSlackSmall
    apply hOrder.mpr
    norm_num only [one_pow, mul_one]
    have hScaled := _root_.mul_lt_mul_of_pos_right hSlackSmall hMass
    nlinarith only [hScaled, hCancel]

theorem compensatedParityInverseRadius_crossover (mass slack coefficient : Real)
    (hMass : 0 < mass) (hSlack : 0 < slack) (hCoefficient : 0 < coefficient) :
    (compensatedParityInverseRadius mass slack < slack / coefficient) <->
      mass * coefficient * (coefficient - momentRoundThreshold) <
        (momentRoundThreshold - 1 / 4) * slack := by
  have hOrder := compensatedQuadraticRadius_lt_iff (momentRoundThreshold - 1 / 4)
    (momentRoundThreshold * mass) (mass * slack) (slack / coefficient)
    (le_of_lt (sub_pos.mpr momentRoundThreshold_gt_quarter))
    (mul_pos momentRoundThreshold_bounds.1 hMass)
    (mul_nonneg (le_of_lt hMass) (le_of_lt hSlack))
    (div_nonneg (le_of_lt hSlack) (le_of_lt hCoefficient))
  have hFactor : 0 < slack / coefficient ^ 2 := div_pos hSlack (sq_pos_of_pos hCoefficient)
  have hIdentity :
      (momentRoundThreshold - 1 / 4) * (slack / coefficient) ^ 2 +
        (momentRoundThreshold * mass) * (slack / coefficient) - mass * slack =
      (slack / coefficient ^ 2) *
        ((momentRoundThreshold - 1 / 4) * slack -
          mass * coefficient * (coefficient - momentRoundThreshold)) := by
    field_simp [hCoefficient.ne']
    ring
  constructor
  case mp =>
    intro hRadius
    have hCost := hOrder.mp hRadius
    by_contra hNot
    have hDifference :
        (momentRoundThreshold - 1 / 4) * slack -
          mass * coefficient * (coefficient - momentRoundThreshold) <= 0 := by
      linarith only [le_of_not_gt hNot]
    have hProduct := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hFactor) hDifference
    nlinarith only [hIdentity, hProduct, hCost]
  case mpr =>
    intro hComparison
    apply hOrder.mpr
    have hProduct := mul_pos hFactor (sub_pos.mpr hComparison)
    nlinarith only [hIdentity, hProduct]

theorem compensatedParityJointRadius_lt_one (mass slack coefficient : Real)
    (hMass : 0 < mass) (hSlack : 0 <= slack) (hCoefficient : 0 < coefficient)
    (hThreshold : slack < max coefficient
      (momentRoundThreshold + (momentRoundThreshold - 1 / 4) / mass)) :
    compensatedParityJointRadius mass slack coefficient < 1 := by
  unfold compensatedParityJointRadius
  by_cases hCompare : coefficient <= momentRoundThreshold + (momentRoundThreshold - 1 / 4) / mass
  case pos =>
    rw [max_eq_right hCompare] at hThreshold
    exact lt_of_le_of_lt (min_le_left _ _)
      ((compensatedParityInverseRadius_lt_one_iff mass slack hMass hSlack).mpr hThreshold)
  case neg =>
    rw [max_eq_left (le_of_not_ge hCompare)] at hThreshold
    have hCancel : (slack / coefficient) * coefficient = slack := by field_simp [hCoefficient.ne']
    have hSmall : slack / coefficient < 1 := by
      by_contra hNot
      have hScaled := _root_.mul_le_mul_of_nonneg_right (le_of_not_gt hNot) (le_of_lt hCoefficient)
      nlinarith only [hCancel, hScaled, hThreshold]
    exact lt_of_le_of_lt (min_le_right _ _) hSmall

theorem evenNatural_unique_abs_lt_one (x : Real) (a b : Nat)
    (ha : Even a) (hb : Even b)
    (hA : abs (x - (a : Real)) < 1) (hB : abs (x - (b : Real)) < 1) :
    a = b := by
  choose k hk using ha
  choose l hl using hb
  have hCastA : (a : Real) = 2 * (k : Real) := by
    exact_mod_cast (show a = 2 * k by omega)
  have hCastB : (b : Real) = 2 * (l : Real) := by
    exact_mod_cast (show b = 2 * l by omega)
  have hALower := (abs_lt.mp hA).1
  have hAUpper := (abs_lt.mp hA).2
  have hBLower := (abs_lt.mp hB).1
  have hBUpper := (abs_lt.mp hB).2
  have hKL : (k : Real) < (l : Real) + 1 := by linarith
  have hLK : (l : Real) < (k : Real) + 1 := by linarith
  have hNatKL : k < l + 1 := by exact_mod_cast hKL
  have hNatLK : l < k + 1 := by exact_mod_cast hLK
  have hEqual : k = l := by omega
  omega

theorem evenNatural_unique_in_radius (x radius : Real) (k : Nat)
    (hk : Even k) (hBound : abs (x - (k : Real)) <= radius) (hRadius : radius < 1) :
    ExistsUnique (fun j : Nat => And (Even j) (abs (x - (j : Real)) <= radius)) := by
  apply ExistsUnique.intro k (And.intro hk hBound)
  intro j hj
  exact evenNatural_unique_abs_lt_one x j k hj.1 hk
    (lt_of_le_of_lt hj.2 hRadius) (lt_of_le_of_lt hBound hRadius)

theorem evenNatural_closed_unit_not_unique :
    Not (forall x : Real, forall a b : Nat, Even a -> Even b ->
      abs (x - (a : Real)) <= 1 -> abs (x - (b : Real)) <= 1 -> a = b) := by
  intro hAll
  have hBad := hAll 3 2 4 (by decide) (by decide) (by norm_num) (by norm_num)
  omega

end PrimeFactorOscillations
