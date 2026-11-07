/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.CompensatedMomentInverseParity
import PrimeFactorOscillations.Helpers.DirectionalParityRigidity

/-! # Optimally shifted even-order recovery from directional parity -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

def parityBranchCost (mass coefficient u : Real) : Real :=
  coefficient / mass * u ^ 2 + momentRoundThreshold * u

def shiftedParityWidth (mass : Real) : Real :=
  compensatedQuadraticRadius (positiveParityCoefficient - sharpParityCoefficient)
    (2 * momentRoundThreshold * mass + 4 * sharpParityCoefficient)
    (2 * momentRoundThreshold * mass + 4 * sharpParityCoefficient)

def shiftedParityAllowance (mass : Real) : Real :=
  parityBranchCost mass positiveParityCoefficient (shiftedParityWidth mass)

def shiftedParityCenter (mass : Real) : Real :=
  mass + 1 - shiftedParityWidth mass

theorem parityBranchCost_order (mass coefficient x y : Real)
    (hMass : 0 < mass) (hCoefficient : 0 <= coefficient) (hx : 0 <= x) (hy : 0 <= y) :
    (parityBranchCost mass coefficient x <= parityBranchCost mass coefficient y) <-> x <= y :=
  compensatedQuadraticCost_order (coefficient / mass) momentRoundThreshold x y
    (div_nonneg hCoefficient hMass.le) momentRoundThreshold_bounds.1 hx hy

theorem parityBranchCost_strict_order (mass coefficient x y : Real)
    (hMass : 0 < mass) (hCoefficient : 0 <= coefficient) (hx : 0 <= x) (hy : 0 <= y) :
    (parityBranchCost mass coefficient x < parityBranchCost mass coefficient y) <-> x < y :=
  compensatedQuadraticCost_strict_order (coefficient / mass) momentRoundThreshold x y
    (div_nonneg hCoefficient hMass.le) momentRoundThreshold_bounds.1 hx hy

theorem shiftedParityWidth_equation (mass : Real) (hMass : 0 < mass) :
    (positiveParityCoefficient - sharpParityCoefficient) * shiftedParityWidth mass ^ 2 +
      (2 * momentRoundThreshold * mass + 4 * sharpParityCoefficient) *
        shiftedParityWidth mass = 2 * momentRoundThreshold * mass + 4 * sharpParityCoefficient := by
  have hb : 0 < 2 * momentRoundThreshold * mass + 4 * sharpParityCoefficient := by
    have hd := momentRoundThreshold_bounds.1
    have hg := sharpParityCoefficient_pos
    positivity
  exact compensatedQuadraticRadius_equation _ _ _
    (sub_pos.mpr positiveParityCoefficient_gt_sharp).le hb hb.le

theorem shiftedParityWidth_bounds (mass : Real) (hMass : 0 < mass) :
    And (0 < shiftedParityWidth mass) (shiftedParityWidth mass < 1) := by
  let a := positiveParityCoefficient - sharpParityCoefficient
  let b := 2 * momentRoundThreshold * mass + 4 * sharpParityCoefficient
  have ha : 0 < a := sub_pos.mpr positiveParityCoefficient_gt_sharp
  have hb : 0 < b := by
    dsimp only [b]
    have hd := momentRoundThreshold_bounds.1
    have hg := sharpParityCoefficient_pos
    positivity
  have hPos : 0 < compensatedQuadraticRadius a b b := by
    unfold compensatedQuadraticRadius
    exact div_pos (by linarith) (compensatedQuadraticRadius_denominator_pos a b b hb)
  have hLess : compensatedQuadraticRadius a b b < 1 := by
    apply (compensatedQuadraticRadius_lt_iff a b b 1 ha.le hb hb.le (by norm_num)).mpr
    norm_num only [one_pow, mul_one]
    linarith only [ha]
  exact And.intro hPos hLess

theorem shiftedParityAllowance_matching (mass : Real) (hMass : 0 < mass) :
    shiftedParityAllowance mass =
      parityBranchCost mass sharpParityCoefficient (2 - shiftedParityWidth mass) := by
  have hRoot := shiftedParityWidth_equation mass hMass
  have hIdentity : mass * (shiftedParityAllowance mass -
      parityBranchCost mass sharpParityCoefficient (2 - shiftedParityWidth mass)) =
      (positiveParityCoefficient - sharpParityCoefficient) * shiftedParityWidth mass ^ 2 +
        (2 * momentRoundThreshold * mass + 4 * sharpParityCoefficient) *
          shiftedParityWidth mass - (2 * momentRoundThreshold * mass + 4 * sharpParityCoefficient) := by
    unfold shiftedParityAllowance parityBranchCost
    field_simp [hMass.ne']
    ring
  have hZero : mass * (shiftedParityAllowance mass -
      parityBranchCost mass sharpParityCoefficient (2 - shiftedParityWidth mass)) = 0 := by
    nlinarith only [hIdentity, hRoot]
  have hh := (mul_eq_zero.mp hZero).resolve_left hMass.ne'
  linarith only [hh]

theorem shiftedParityAllowance_pos (mass : Real) (hMass : 0 < mass) :
    0 < shiftedParityAllowance mass := by
  have hx := (shiftedParityWidth_bounds mass hMass).1
  have hd := momentRoundThreshold_bounds.1
  have hp := positiveParityCoefficient_pos
  unfold shiftedParityAllowance parityBranchCost
  positivity

theorem shiftedParityAllowance_strict_gain (mass : Real) (hMass : 0 < mass) :
    momentRoundThreshold + sharpParityCoefficient / mass < shiftedParityAllowance mass := by
  have hx := shiftedParityWidth_bounds mass hMass
  have hCost := (parityBranchCost_strict_order mass sharpParityCoefficient 1
    (2 - shiftedParityWidth mass) hMass sharpParityCoefficient_pos.le
    (by norm_num) (by linarith only [hx.2])).mpr (by linarith only [hx.2])
  rw [<- shiftedParityAllowance_matching mass hMass] at hCost
  simpa only [parityBranchCost, one_pow, mul_one, add_comm] using hCost

theorem shiftedParityAllowance_maximal (mass r : Real) (hMass : 0 < mass)
    (hr : And (0 <= r) (r <= 2)) :
    min (parityBranchCost mass positiveParityCoefficient r)
      (parityBranchCost mass sharpParityCoefficient (2 - r)) <= shiftedParityAllowance mass := by
  have hx := shiftedParityWidth_bounds mass hMass
  by_cases hSide : r <= shiftedParityWidth mass
  case pos =>
    have hOrder := (parityBranchCost_order mass positiveParityCoefficient r
      (shiftedParityWidth mass) hMass positiveParityCoefficient_pos.le hr.1 hx.1.le).mpr hSide
    exact le_trans (min_le_left _ _) hOrder
  case neg =>
    have hOrder := (parityBranchCost_order mass sharpParityCoefficient (2 - r)
      (2 - shiftedParityWidth mass) hMass sharpParityCoefficient_pos.le
      (by linarith only [hr.2]) (by linarith only [hx.2])).mpr
        (by linarith only [lt_of_not_ge hSide])
    rw [<- shiftedParityAllowance_matching mass hMass] at hOrder
    exact le_trans (min_le_right _ _) hOrder

theorem shiftedParityAllowance_unique_maximum (mass r : Real) (hMass : 0 < mass)
    (hr : And (0 <= r) (r <= 2)) :
    (min (parityBranchCost mass positiveParityCoefficient r)
      (parityBranchCost mass sharpParityCoefficient (2 - r)) = shiftedParityAllowance mass) <->
        r = shiftedParityWidth mass := by
  have hx := shiftedParityWidth_bounds mass hMass
  constructor
  case mp =>
    intro hEq
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt | hgt
    case inl =>
      have hCost := (parityBranchCost_strict_order mass positiveParityCoefficient r
        (shiftedParityWidth mass) hMass positiveParityCoefficient_pos.le hr.1 hx.1.le).mpr hlt
      have hm := min_le_left (parityBranchCost mass positiveParityCoefficient r)
        (parityBranchCost mass sharpParityCoefficient (2 - r))
      change parityBranchCost mass positiveParityCoefficient r < shiftedParityAllowance mass at hCost
      linarith only [hEq, hCost, hm]
    case inr =>
      have hCost := (parityBranchCost_strict_order mass sharpParityCoefficient (2 - r)
        (2 - shiftedParityWidth mass) hMass sharpParityCoefficient_pos.le
        (by linarith only [hr.2]) (by linarith only [hx.2])).mpr (by linarith only [hgt])
      rw [<- shiftedParityAllowance_matching mass hMass] at hCost
      have hm := min_le_right (parityBranchCost mass positiveParityCoefficient r)
        (parityBranchCost mass sharpParityCoefficient (2 - r))
      linarith only [hEq, hCost, hm]
  case mpr =>
    intro hEq
    subst r
    change min (shiftedParityAllowance mass)
      (parityBranchCost mass sharpParityCoefficient (2 - shiftedParityWidth mass)) = _
    rw [<- shiftedParityAllowance_matching mass hMass, min_self]

theorem directionalParity_shifted_unit_bound (mass D : Real) (hMass : 0 < mass)
    (hCost : Not (D = 0) -> directionalParityStabilityCost mass D < shiftedParityAllowance mass) :
    abs (D + 1 - shiftedParityWidth mass) < 1 := by
  have hx := shiftedParityWidth_bounds mass hMass
  have hUpper : D < shiftedParityWidth mass := by
    by_contra hn
    have hOrder : shiftedParityWidth mass <= D := le_of_not_gt hn
    have hD : 0 < D := lt_of_lt_of_le hx.1 hOrder
    have hStrong := hCost hD.ne'
    have hFloor := (parityBranchCost_order mass positiveParityCoefficient
      (shiftedParityWidth mass) D hMass positiveParityCoefficient_pos.le hx.1.le hD.le).mpr hOrder
    have hSame : directionalParityStabilityCost mass D =
        parityBranchCost mass positiveParityCoefficient D := by
      rw [directionalParityStabilityCost, if_pos hD.le, abs_of_nonneg hD.le]
      unfold parityBranchCost
      ring
    rw [hSame] at hStrong
    change shiftedParityAllowance mass <= parityBranchCost mass positiveParityCoefficient D at hFloor
    linarith only [hStrong, hFloor]
  have hLower : shiftedParityWidth mass - 2 < D := by
    by_contra hn
    have hOrder : D <= shiftedParityWidth mass - 2 := le_of_not_gt hn
    have hD : D < 0 := by linarith only [hOrder, hx.2]
    have hStrong := hCost hD.ne
    have hFloor := (parityBranchCost_order mass sharpParityCoefficient
      (2 - shiftedParityWidth mass) (-D) hMass sharpParityCoefficient_pos.le
      (by linarith only [hx.2]) (by linarith only [hD])).mpr (by linarith only [hOrder])
    rw [<- shiftedParityAllowance_matching mass hMass] at hFloor
    have hSame : directionalParityStabilityCost mass D =
        parityBranchCost mass sharpParityCoefficient (-D) := by
      rw [directionalParityStabilityCost, if_neg (not_le.mpr hD), abs_of_neg hD]
      unfold parityBranchCost
      ring
    rw [hSame] at hStrong
    linarith only [hStrong, hFloor]
  apply abs_lt.mpr
  exact And.intro (by linarith only [hLower]) (by linarith only [hUpper])

end PrimeFactorOscillations
