/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Calculus.MeanValue
import PrimeFactorOscillations.Helpers.HamiltonianSpectralFactorDerivatives

/-! # The full fourth spectral derivative and its dimension-free bound

All terms in the fourth derivative of the exponential are retained.
The actual successive derivative functions are identified, and the
rational-coordinate budget gives the constant 2049 without a dimension
factor. The remaining local Taylor consumer also needs the spectral
factor ratio between the current point and the central point.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*}

def spectralFactorJet1 (S : Finset Iota) (lam : Iota -> Real) (s : Real) : Real :=
  spectralFactors S lam s * Finset.sum S (fun i => spectralCoordinate1 (lam i) s)

def spectralFactorJet2 (S : Finset Iota) (lam : Iota -> Real) (s : Real) : Real :=
  spectralFactors S lam s *
    ((Finset.sum S (fun i => spectralCoordinate1 (lam i) s)) ^ 2 +
      Finset.sum S (fun i => spectralCoordinate2 (lam i) s))

def spectralFactorJet3 (S : Finset Iota) (lam : Iota -> Real) (s : Real) : Real :=
  spectralFactors S lam s *
    ((Finset.sum S (fun i => spectralCoordinate1 (lam i) s)) ^ 3 +
      3 * (Finset.sum S (fun i => spectralCoordinate1 (lam i) s)) *
        (Finset.sum S (fun i => spectralCoordinate2 (lam i) s)) +
      Finset.sum S (fun i => spectralCoordinate3 (lam i) s))

def spectralFourthBell (L1 L2 L3 L4 : Real) : Real :=
  L1 ^ 4 + 6 * L1 ^ 2 * L2 + 3 * L2 ^ 2 + 4 * L1 * L3 + L4

def spectralFactorJet4 (S : Finset Iota) (lam : Iota -> Real) (s : Real) : Real :=
  spectralFactors S lam s * spectralFourthBell
    (Finset.sum S (fun i => spectralCoordinate1 (lam i) s))
    (Finset.sum S (fun i => spectralCoordinate2 (lam i) s))
    (Finset.sum S (fun i => spectralCoordinate3 (lam i) s))
    (Finset.sum S (fun i => spectralCoordinate4 (lam i) s))

theorem spectralFactorJet1_hasDerivAt (S : Finset Iota) (lam : Iota -> Real)
    (s : Real) (hDen : forall i, Membership.mem S i -> Not (1 - s ^ 2 * lam i = 0)) :
    HasDerivAt (spectralFactorJet1 S lam) (spectralFactorJet2 S lam s) s := by
  have h := (spectralFactors_hasDerivAt S lam s hDen).fun_mul
    (spectralFirstSum_hasDerivAt S lam s hDen)
  unfold spectralFactorJet1 spectralFactorJet2
  convert h using 1
  ring

theorem spectralFactorJet2_hasDerivAt (S : Finset Iota) (lam : Iota -> Real)
    (s : Real) (hDen : forall i, Membership.mem S i -> Not (1 - s ^ 2 * lam i = 0)) :
    HasDerivAt (spectralFactorJet2 S lam) (spectralFactorJet3 S lam s) s := by
  have h1 := spectralFirstSum_hasDerivAt S lam s hDen
  have h2 := spectralSecondSum_hasDerivAt S lam s hDen
  have hSq := h1.fun_pow' 2
  norm_num [Finset.sum_range_succ] at hSq
  have h := (spectralFactors_hasDerivAt S lam s hDen).fun_mul (hSq.fun_add h2)
  unfold spectralFactorJet2 spectralFactorJet3
  convert h using 1
  ring

theorem spectralFactorJet3_hasDerivAt (S : Finset Iota) (lam : Iota -> Real)
    (s : Real) (hDen : forall i, Membership.mem S i -> Not (1 - s ^ 2 * lam i = 0)) :
    HasDerivAt (spectralFactorJet3 S lam) (spectralFactorJet4 S lam s) s := by
  have h1 := spectralFirstSum_hasDerivAt S lam s hDen
  have h2 := spectralSecondSum_hasDerivAt S lam s hDen
  have h3 := spectralThirdSum_hasDerivAt S lam s hDen
  have hCube := h1.fun_pow' 3
  norm_num [Finset.sum_range_succ] at hCube
  have hG := (hCube.fun_add ((h1.fun_mul h2).const_mul 3)).fun_add h3
  have h := (spectralFactors_hasDerivAt S lam s hDen).fun_mul hG
  unfold spectralFactorJet3 spectralFactorJet4 spectralFourthBell
  convert h using 1
  all_goals first
  | (funext x; ring)
  | ring

theorem spectralLogBudget_fourth_bound (tau mass L1 L2 L3 L4 : Real)
    (hTau : 0 <= tau) (hBudget : SpectralLogBudget tau mass L1 L2 L3 L4) :
    tau ^ 4 * spectralFourthBell L1 L2 L3 L4 <= 2049 * (1 + mass) ^ 4 := by
  let x : Real := tau * L1
  let y : Real := tau ^ 2 * L2
  let z : Real := tau ^ 3 * L3
  let w : Real := tau ^ 4 * L4
  have hMass := hBudget.nonnegative_mass
  have hx0 : 0 <= x := mul_nonneg hTau hBudget.nonnegative_one
  have hy0 : 0 <= y := mul_nonneg (sq_nonneg tau) hBudget.nonnegative_two
  have hz0 : 0 <= z := mul_nonneg (pow_nonneg hTau 3) hBudget.nonnegative_three
  have hx : x <= 2 * mass := hBudget.bound_one
  have hy : y <= 9 * mass := hBudget.bound_two
  have hz : z <= 76 * mass := hBudget.bound_three
  have hw : w <= 966 * mass := hBudget.bound_four
  have hX2 : x ^ 2 <= (2 * mass) ^ 2 := by
    have h := mul_le_mul hx hx hx0 (by positivity)
    nlinarith only [h]
  have hX4 : x ^ 4 <= 16 * mass ^ 4 := by
    have h := mul_le_mul hX2 hX2 (sq_nonneg x) (sq_nonneg (2 * mass))
    nlinarith only [h]
  have hY2 : y ^ 2 <= 81 * mass ^ 2 := by
    have h := mul_le_mul hy hy hy0 (by positivity)
    nlinarith only [h]
  have hX2Y := mul_le_mul hX2 hy hy0 (sq_nonneg (2 * mass))
  have hXZ := mul_le_mul hx hz hz0 (by positivity)
  have hIdentity : tau ^ 4 * spectralFourthBell L1 L2 L3 L4 =
      x ^ 4 + 6 * x ^ 2 * y + 3 * y ^ 2 + 4 * x * z + w := by
    dsimp [x, y, z, w, spectralFourthBell]
    ring
  rw [hIdentity]
  have hIntermediate : x ^ 4 + 6 * x ^ 2 * y + 3 * y ^ 2 + 4 * x * z + w <=
      16 * mass ^ 4 + 216 * mass ^ 3 + 851 * mass ^ 2 + 966 * mass := by
    nlinarith only [hX4, hX2Y, hY2, hXZ, hw]
  apply le_trans hIntermediate
  nlinarith only [hMass, sq_nonneg mass, pow_nonneg hMass 3, pow_nonneg hMass 4]

theorem spectralFactorJet4_strip_bound (S : Finset Iota) (lam : Iota -> Real)
    (delta eps s : Real) (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hEps0 : 0 <= eps) (hEps1 : eps <= delta / 4)
    (hLam0 : forall i, Membership.mem S i -> 0 <= lam i)
    (hLam1 : forall i, Membership.mem S i -> lam i <= (1 - delta) ^ 2)
    (hs : abs (s - 1) <= eps) :
    delta ^ 4 * abs (spectralFactorJet4 S lam s) <=
      2049 * spectralFactors S lam s * (1 + Finset.sum S lam) ^ 4 := by
  have hBudget := spectralFactors_strip_budget S lam delta eps s
    hDelta0 hDelta1 hEps0 hEps1 hLam0 hLam1 hs
  have hB := spectralLogBudget_fourth_bound delta (Finset.sum S lam)
    _ _ _ _ (le_of_lt hDelta0) hBudget
  have hN1 := hBudget.nonnegative_one
  have hN2 := hBudget.nonnegative_two
  have hN3 := hBudget.nonnegative_three
  have hN4 := hBudget.nonnegative_four
  have hPos : 0 < spectralFactors S lam s := Real.exp_pos _
  have hBell : 0 <= spectralFourthBell
      (Finset.sum S (fun i => spectralCoordinate1 (lam i) s))
      (Finset.sum S (fun i => spectralCoordinate2 (lam i) s))
      (Finset.sum S (fun i => spectralCoordinate3 (lam i) s))
      (Finset.sum S (fun i => spectralCoordinate4 (lam i) s)) := by
    unfold spectralFourthBell
    positivity
  unfold spectralFactorJet4
  rw [abs_mul, abs_of_pos hPos, abs_of_nonneg hBell]
  have h := mul_le_mul_of_nonneg_left hB (le_of_lt hPos)
  nlinarith only [h]

theorem spectralFactors_central_ratio (S : Finset Iota) (lam : Iota -> Real)
    (delta eps s : Real) (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hEps0 : 0 <= eps) (hEps1 : eps <= delta / 4)
    (hLam0 : forall i, Membership.mem S i -> 0 <= lam i)
    (hLam1 : forall i, Membership.mem S i -> lam i <= (1 - delta) ^ 2)
    (hSmall : 2 * (Finset.sum S lam) * eps <= delta)
    (hs : abs (s - 1) <= eps) :
    spectralFactors S lam s <= Real.exp 1 * spectralFactors S lam 1 := by
  let I : Set Real := Set.Icc (1 - eps) (1 + eps)
  have hWindow : forall x : Real, Membership.mem I x -> abs (x - 1) <= eps := by
    intro x hx
    apply abs_le.mpr
    exact And.intro (by linarith only [hx.1]) (by linarith only [hx.2])
  have hOne : Membership.mem I (1 : Real) :=
    And.intro (by linarith only [hEps0]) (by linarith only [hEps0])
  have hS : Membership.mem I s := by
    have hr := abs_le.mp hs
    exact And.intro (by linarith only [hr.1]) (by linarith only [hr.2])
  have hDeriv : forall x : Real, Membership.mem I x ->
      HasDerivAt (fun y : Real => delta * spectralLogFactors S lam y)
        (delta * Finset.sum S (fun i => spectralCoordinate1 (lam i) x)) x := by
    intro x hx
    apply (spectralLogFactors_hasDerivAt S lam x _).const_mul delta
    intro i hi
    have hStrip := spectralFactor_strip delta eps (lam i) x hDelta0 hDelta1
      hEps0 hEps1 (hLam0 i hi) (hLam1 i hi) (hWindow x hx)
    exact ne_of_gt (lt_of_lt_of_le hDelta0 hStrip.2.2.2)
  have hBound : forall x : Real, Membership.mem I x ->
      norm (delta * Finset.sum S (fun i => spectralCoordinate1 (lam i) x)) <=
        2 * Finset.sum S lam := by
    intro x hx
    have hBudget := spectralFactors_strip_budget S lam delta eps x
      hDelta0 hDelta1 hEps0 hEps1 hLam0 hLam1 (hWindow x hx)
    have hNonneg := mul_nonneg (le_of_lt hDelta0) hBudget.nonnegative_one
    rw [Real.norm_eq_abs, abs_of_nonneg hNonneg]
    exact hBudget.bound_one
  have hMVT := _root_.Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun y : Real => delta * spectralLogFactors S lam y)
    (f' := fun x : Real => delta * Finset.sum S (fun i => spectralCoordinate1 (lam i) x))
    (C := 2 * Finset.sum S lam)
    (fun x hx => (hDeriv x hx).hasDerivWithinAt) hBound
    (_root_.convex_Icc (1 - eps) (1 + eps)) hOne hS
  have hScalar : abs (delta * spectralLogFactors S lam s -
      delta * spectralLogFactors S lam 1) <=
      2 * (Finset.sum S lam) * abs (s - 1) := by
    simpa only [Real.norm_eq_abs] using hMVT
  have hMass : 0 <= Finset.sum S lam := Finset.sum_nonneg (fun i hi => hLam0 i hi)
  have hScaled : delta * (spectralLogFactors S lam s - spectralLogFactors S lam 1) <=
      delta := by
    calc
      _ <= abs (delta * spectralLogFactors S lam s -
          delta * spectralLogFactors S lam 1) := by
        have h := le_abs_self (delta * spectralLogFactors S lam s -
          delta * spectralLogFactors S lam 1)
        nlinarith only [h]
      _ <= 2 * (Finset.sum S lam) * abs (s - 1) := hScalar
      _ <= 2 * (Finset.sum S lam) * eps :=
        mul_le_mul_of_nonneg_left hs (by linarith only [hMass])
      _ <= delta := hSmall
  have hLog : spectralLogFactors S lam s - spectralLogFactors S lam 1 <= 1 := by
    by_contra hNot
    have hStrict := mul_lt_mul_of_pos_left (lt_of_not_ge hNot) hDelta0
    rw [mul_one] at hStrict
    exact (not_lt_of_ge hScaled) hStrict
  unfold spectralFactors
  calc
    _ <= Real.exp (spectralLogFactors S lam 1 + 1) :=
      Real.exp_le_exp.mpr (by linarith only [hLog])
    _ = _ := by rw [Real.exp_add]; ring

theorem spectralFactorJet4_central_bound (S : Finset Iota) (lam : Iota -> Real)
    (delta eps s : Real) (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hEps0 : 0 <= eps) (hEps1 : eps <= delta / 4)
    (hLam0 : forall i, Membership.mem S i -> 0 <= lam i)
    (hLam1 : forall i, Membership.mem S i -> lam i <= (1 - delta) ^ 2)
    (hSmall : 2 * (Finset.sum S lam) * eps <= delta)
    (hs : abs (s - 1) <= eps) :
    abs (spectralFactorJet4 S lam s) <=
      (2049 * Real.exp 1 * spectralFactors S lam 1 *
        (1 + Finset.sum S lam) ^ 4) / delta ^ 4 := by
  have hCross := spectralFactorJet4_strip_bound S lam delta eps s
    hDelta0 hDelta1 hEps0 hEps1 hLam0 hLam1 hs
  have hRatio := spectralFactors_central_ratio S lam delta eps s
    hDelta0 hDelta1 hEps0 hEps1 hLam0 hLam1 hSmall hs
  have hMass : 0 <= Finset.sum S lam := Finset.sum_nonneg (fun i hi => hLam0 i hi)
  have hScaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hRatio (by norm_num : (0 : Real) <= 2049))
    (pow_nonneg (show (0 : Real) <= 1 + Finset.sum S lam by linarith only [hMass]) 4)
  have hCombined : delta ^ 4 * abs (spectralFactorJet4 S lam s) <=
      2049 * Real.exp 1 * spectralFactors S lam 1 *
        (1 + Finset.sum S lam) ^ 4 := by
    nlinarith only [hCross, hScaled]
  have hDenPos : 0 < delta ^ 4 := pow_pos hDelta0 4
  have hClear : delta ^ 4 *
      ((2049 * Real.exp 1 * spectralFactors S lam 1 *
        (1 + Finset.sum S lam) ^ 4) / delta ^ 4) =
      2049 * Real.exp 1 * spectralFactors S lam 1 *
        (1 + Finset.sum S lam) ^ 4 := by
    field_simp [ne_of_gt hDenPos]
  by_contra hNot
  have hStrict := mul_lt_mul_of_pos_left (lt_of_not_ge hNot) hDenPos
  rw [hClear] at hStrict
  exact (not_lt_of_ge hCombined) hStrict

end PrimeFactorOscillations
