/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianSpectralProductAverage

/-! # Central spectral jets with explicit energy dependence

The first three determinant jets are bounded from the existing logarithmic
budgets. These bounds control the actual affine product remainder and its
Gamma tail, rather than estimating the signed main correction separately.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*}

theorem spectralFactors_central_jet_bounds (S : Finset Iota) (lam : Iota -> Real)
    (delta a : Real) (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (ha : 1 <= a)
    (hLam0 : forall i, Membership.mem S i -> 0 <= lam i)
    (hLam1 : forall i, Membership.mem S i -> lam i <= (1 - delta) ^ 2)
    (hMass : Finset.sum S lam <= a) :
    And (delta * abs (spectralFactorJet1 S lam 1) <=
      2 * spectralFactors S lam 1 * a)
      (And (delta ^ 2 * abs (spectralFactorJet2 S lam 1) <=
        13 * spectralFactors S lam 1 * a ^ 2)
        (delta ^ 3 * abs (spectralFactorJet3 S lam 1) <=
          138 * spectralFactors S lam 1 * a ^ 3)) := by
  let L1 := Finset.sum S (fun i => spectralCoordinate1 (lam i) 1)
  let L2 := Finset.sum S (fun i => spectralCoordinate2 (lam i) 1)
  let L3 := Finset.sum S (fun i => spectralCoordinate3 (lam i) 1)
  let x := delta * L1
  let y := delta ^ 2 * L2
  let z := delta ^ 3 * L3
  let D := spectralFactors S lam 1
  have hD : 0 < D := Real.exp_pos _
  have hA : 0 <= a := le_trans (by norm_num) ha
  have hBudget := spectralFactors_strip_budget S lam delta 0 1 hDelta0 hDelta1
    (by norm_num) (by linarith only [hDelta0]) hLam0 hLam1 (by norm_num)
  have hL1 : 0 <= L1 := hBudget.nonnegative_one
  have hL2 : 0 <= L2 := hBudget.nonnegative_two
  have hL3 : 0 <= L3 := hBudget.nonnegative_three
  have hx0 : 0 <= x := mul_nonneg hDelta0.le hL1
  have hy0 : 0 <= y := mul_nonneg (sq_nonneg delta) hL2
  have hx : x <= 2 * a := by
    have h := hBudget.bound_one
    change x <= 2 * Finset.sum S lam at h
    linarith only [h, hMass]
  have hy : y <= 9 * a := by
    have h := hBudget.bound_two
    change y <= 9 * Finset.sum S lam at h
    linarith only [h, hMass]
  have hz : z <= 76 * a := by
    have h := hBudget.bound_three
    change z <= 76 * Finset.sum S lam at h
    linarith only [h, hMass]
  have hx2 : x ^ 2 <= 4 * a ^ 2 := by
    have h := mul_le_mul hx hx hx0 (by positivity)
    nlinarith only [h]
  have hx3 : x ^ 3 <= 8 * a ^ 3 := by
    have h := mul_le_mul hx2 hx hx0 (by positivity)
    nlinarith only [h]
  have hxy : x * y <= 18 * a ^ 2 := by
    have h := mul_le_mul hx hy hy0 (by positivity)
    nlinarith only [h]
  have ha2 : a <= a ^ 2 := by nlinarith only [ha]
  have ha3 : a ^ 2 <= a ^ 3 := by
    have h := mul_le_mul_of_nonneg_right ha2 hA
    nlinarith only [h]
  have hSecond : x ^ 2 + y <= 13 * a ^ 2 := by
    linarith only [hx2, hy, ha2]
  have hThird : x ^ 3 + 3 * x * y + z <= 138 * a ^ 3 := by
    linarith only [hx3, hxy, hz, ha2, ha3]
  have hJ1 : 0 <= spectralFactorJet1 S lam 1 := by
    change 0 <= D * L1
    exact mul_nonneg hD.le hL1
  have hJ2 : 0 <= spectralFactorJet2 S lam 1 := by
    change 0 <= D * (L1 ^ 2 + L2)
    positivity
  have hJ3 : 0 <= spectralFactorJet3 S lam 1 := by
    change 0 <= D * (L1 ^ 3 + 3 * L1 * L2 + L3)
    positivity
  rw [abs_of_nonneg hJ1, abs_of_nonneg hJ2, abs_of_nonneg hJ3]
  constructor
  next =>
    have h := mul_le_mul_of_nonneg_left hx hD.le
    change delta * (D * L1) <= 2 * D * a
    dsimp only [x] at h
    nlinarith only [h]
  next =>
    constructor
    next =>
      have h := mul_le_mul_of_nonneg_left hSecond hD.le
      change delta ^ 2 * (D * (L1 ^ 2 + L2)) <= 13 * D * a ^ 2
      dsimp only [x, y] at h
      nlinarith only [h]
    next =>
      have h := mul_le_mul_of_nonneg_left hThird hD.le
      change delta ^ 3 * (D * (L1 ^ 3 + 3 * L1 * L2 + L3)) <= 138 * D * a ^ 3
      dsimp only [x, y, z] at h
      nlinarith only [h]

end PrimeFactorOscillations
