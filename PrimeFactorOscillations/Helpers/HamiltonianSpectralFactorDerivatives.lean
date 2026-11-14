/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Quantitative derivatives of the actual spectral factor

The coordinates are the successive derivatives of
-(1/2) log(1-s^2*lambda). The finite product is represented by the
exponential of their sum. These are actual differentiation statements,
with every singular denominator retained. Their quantitative consumer is
the fourth-order local inverse-Gamma average in HamiltonianGammaTaylor.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

def spectralCoordinate0 (lam s : Real) : Real :=
  -(1 / 2 : Real) * Real.log (1 - s ^ 2 * lam)

def spectralCoordinate1 (lam s : Real) : Real :=
  s * lam / (1 - s ^ 2 * lam)

def spectralCoordinate2 (lam s : Real) : Real :=
  lam / (1 - s ^ 2 * lam) +
    2 * s ^ 2 * lam ^ 2 / (1 - s ^ 2 * lam) ^ 2

def spectralCoordinate3 (lam s : Real) : Real :=
  6 * s * lam ^ 2 / (1 - s ^ 2 * lam) ^ 2 +
    8 * s ^ 3 * lam ^ 3 / (1 - s ^ 2 * lam) ^ 3

def spectralCoordinate4 (lam s : Real) : Real :=
  6 * lam ^ 2 / (1 - s ^ 2 * lam) ^ 2 +
    48 * s ^ 2 * lam ^ 3 / (1 - s ^ 2 * lam) ^ 3 +
      48 * s ^ 4 * lam ^ 4 / (1 - s ^ 2 * lam) ^ 4

private theorem spectralDenominator_hasDerivAt (lam s : Real) :
    HasDerivAt (fun x : Real => 1 - x ^ 2 * lam) (-2 * s * lam) s := by
  convert (hasDerivAt_const s (1 : Real)).sub
    (((hasDerivAt_id s).pow 2).mul_const lam) using 1
  case e'_8 =>
    funext x
    simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
  case e'_9 =>
    simp only [id_eq]
    ring

theorem spectralCoordinate0_hasDerivAt (lam s : Real)
    (hDen : Not (1 - s ^ 2 * lam = 0)) :
    HasDerivAt (spectralCoordinate0 lam) (spectralCoordinate1 lam s) s := by
  have h := ((spectralDenominator_hasDerivAt lam s).log hDen).const_mul
    (-(1 / 2 : Real))
  unfold spectralCoordinate0 spectralCoordinate1
  convert h using 1
  ring

theorem spectralCoordinate1_hasDerivAt (lam s : Real)
    (hDen : Not (1 - s ^ 2 * lam = 0)) :
    HasDerivAt (spectralCoordinate1 lam) (spectralCoordinate2 lam s) s := by
  have h := ((hasDerivAt_id s).mul_const lam).div
    (spectralDenominator_hasDerivAt lam s) hDen
  unfold spectralCoordinate1 spectralCoordinate2
  convert h using 1
  case e'_8 =>
    funext x
    simp only [Pi.div_apply, id_eq]
  case e'_9 =>
    simp only [id_eq]
    field_simp [hDen]
    ring

theorem spectralCoordinate2_hasDerivAt (lam s : Real)
    (hDen : Not (1 - s ^ 2 * lam = 0)) :
    HasDerivAt (spectralCoordinate2 lam) (spectralCoordinate3 lam s) s := by
  have hQ := spectralDenominator_hasDerivAt lam s
  have hA := (hasDerivAt_const s lam).div hQ hDen
  have hB := (((hasDerivAt_id s).pow 2).const_mul (2 * lam ^ 2)).div
    (hQ.pow 2) (pow_ne_zero 2 hDen)
  have h := hA.add hB
  unfold spectralCoordinate2 spectralCoordinate3
  convert h using 1
  all_goals first
  | (funext x; dsimp; ring)
  | (dsimp; field_simp [hDen]; ring)

theorem spectralCoordinate3_hasDerivAt (lam s : Real)
    (hDen : Not (1 - s ^ 2 * lam = 0)) :
    HasDerivAt (spectralCoordinate3 lam) (spectralCoordinate4 lam s) s := by
  have hQ := spectralDenominator_hasDerivAt lam s
  have hA := ((hasDerivAt_id s).const_mul (6 * lam ^ 2)).div
    (hQ.pow 2) (pow_ne_zero 2 hDen)
  have hB := (((hasDerivAt_id s).pow 3).const_mul (8 * lam ^ 3)).div
    (hQ.pow 3) (pow_ne_zero 3 hDen)
  have h := hA.add hB
  unfold spectralCoordinate3 spectralCoordinate4
  convert h using 1
  all_goals first
  | (funext x; dsimp; ring)
  | (dsimp; field_simp [hDen]; ring)

variable {Iota : Type*}

def spectralLogFactors (S : Finset Iota) (lam : Iota -> Real) (s : Real) : Real :=
  Finset.sum S (fun i => spectralCoordinate0 (lam i) s)

def spectralFactors (S : Finset Iota) (lam : Iota -> Real) (s : Real) : Real :=
  Real.exp (spectralLogFactors S lam s)

theorem spectralLogFactors_hasDerivAt (S : Finset Iota) (lam : Iota -> Real)
    (s : Real) (hDen : forall i, Membership.mem S i -> Not (1 - s ^ 2 * lam i = 0)) :
    HasDerivAt (spectralLogFactors S lam)
      (Finset.sum S (fun i => spectralCoordinate1 (lam i) s)) s := by
  exact HasDerivAt.fun_sum (fun i hi => spectralCoordinate0_hasDerivAt (lam i) s (hDen i hi))

theorem spectralFirstSum_hasDerivAt (S : Finset Iota) (lam : Iota -> Real)
    (s : Real) (hDen : forall i, Membership.mem S i -> Not (1 - s ^ 2 * lam i = 0)) :
    HasDerivAt (fun x : Real => Finset.sum S (fun i => spectralCoordinate1 (lam i) x))
      (Finset.sum S (fun i => spectralCoordinate2 (lam i) s)) s := by
  exact HasDerivAt.fun_sum (fun i hi => spectralCoordinate1_hasDerivAt (lam i) s (hDen i hi))

theorem spectralSecondSum_hasDerivAt (S : Finset Iota) (lam : Iota -> Real)
    (s : Real) (hDen : forall i, Membership.mem S i -> Not (1 - s ^ 2 * lam i = 0)) :
    HasDerivAt (fun x : Real => Finset.sum S (fun i => spectralCoordinate2 (lam i) x))
      (Finset.sum S (fun i => spectralCoordinate3 (lam i) s)) s := by
  exact HasDerivAt.fun_sum (fun i hi => spectralCoordinate2_hasDerivAt (lam i) s (hDen i hi))

theorem spectralThirdSum_hasDerivAt (S : Finset Iota) (lam : Iota -> Real)
    (s : Real) (hDen : forall i, Membership.mem S i -> Not (1 - s ^ 2 * lam i = 0)) :
    HasDerivAt (fun x : Real => Finset.sum S (fun i => spectralCoordinate3 (lam i) x))
      (Finset.sum S (fun i => spectralCoordinate4 (lam i) s)) s := by
  exact HasDerivAt.fun_sum (fun i hi => spectralCoordinate3_hasDerivAt (lam i) s (hDen i hi))

theorem spectralFactors_hasDerivAt (S : Finset Iota) (lam : Iota -> Real)
    (s : Real) (hDen : forall i, Membership.mem S i -> Not (1 - s ^ 2 * lam i = 0)) :
    HasDerivAt (spectralFactors S lam)
      (spectralFactors S lam s * Finset.sum S (fun i => spectralCoordinate1 (lam i) s)) s := by
  exact (spectralLogFactors_hasDerivAt S lam s hDen).exp

theorem spectralFactor_strip (delta eps lam s : Real)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (_hEps0 : 0 <= eps) (hEps1 : eps <= delta / 4)
    (hLam0 : 0 <= lam) (hLam1 : lam <= (1 - delta) ^ 2)
    (hs : abs (s - 1) <= eps) :
    And (0 <= s) (And (s <= 2) (And (lam <= 1) (delta <= 1 - s ^ 2 * lam))) := by
  have hRange := abs_le.mp hs
  have hs0 : 0 <= s := by linarith only [hRange.1, hEps1, hDelta1]
  have hs2 : s <= 2 := by linarith only [hRange.2, hEps1, hDelta1]
  have hsUpper : s <= 1 + delta / 4 := by linarith only [hRange.2, hEps1]
  have hSquare : s ^ 2 <= (1 + delta / 4) ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hsUpper)
      (show 0 <= 1 + delta / 4 + s by linarith only [hDelta0, hs0])]
  have hLamBound : lam <= 1 := by
    nlinarith only [hLam1, hDelta0, hDelta1,
      mul_nonneg (le_of_lt hDelta0) (sub_nonneg.mpr hDelta1)]
  have hMul1 := mul_le_mul_of_nonneg_right hSquare hLam0
  have hMul2 := mul_le_mul_of_nonneg_left hLam1 (sq_nonneg (1 + delta / 4))
  have hPoly : 0 <= delta * (1 - delta) * (delta ^ 2 + 7 * delta + 8) :=
    mul_nonneg (mul_nonneg (le_of_lt hDelta0) (sub_nonneg.mpr hDelta1))
      (by nlinarith only [sq_nonneg delta, hDelta0])
  have hIdentity : 1 - (1 + delta / 4) ^ 2 * (1 - delta) ^ 2 - delta =
      delta * (1 - delta) * (delta ^ 2 + 7 * delta + 8) / 16 := by ring
  have hDen : delta <= 1 - s ^ 2 * lam := by
    nlinarith only [hMul1, hMul2, hPoly, hIdentity]
  exact And.intro hs0 (And.intro hs2 (And.intro hLamBound hDen))

private theorem spectral_power_mono (a b : Real) (ha : 0 <= a)
    (hab : a <= b) (j : Nat) : a ^ j <= b ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, pow_succ]
    exact mul_le_mul ih hab ha (pow_nonneg (le_trans ha hab) j)

private theorem spectral_monomial_cap (s lam q : Real)
    (hs0 : 0 <= s) (hs2 : s <= 2) (hLam0 : 0 <= lam) (hLam1 : lam <= 1)
    (hq0 : 0 <= q) (hq1 : q <= 1) (p k r : Nat) :
    s ^ p * lam ^ (k + 1) * q ^ r <= (2 : Real) ^ p * lam := by
  have hS := spectral_power_mono s 2 hs0 hs2 p
  have hL : lam ^ k <= 1 := by
    simpa only [one_pow] using spectral_power_mono lam 1 hLam0 hLam1 k
  have hQ : q ^ r <= 1 := by
    simpa only [one_pow] using spectral_power_mono q 1 hq0 hq1 r
  have hNext : lam ^ (k + 1) <= lam := by
    rw [pow_succ]
    have h := mul_le_mul_of_nonneg_right hL hLam0
    simpa only [one_mul] using h
  have hPair : s ^ p * lam ^ (k + 1) <= (2 : Real) ^ p * lam :=
    mul_le_mul hS hNext (pow_nonneg hLam0 (k + 1)) (by positivity)
  have hAll := mul_le_mul hPair hQ (pow_nonneg hq0 r)
    (mul_nonneg (by positivity) hLam0)
  simpa only [mul_one] using hAll

structure SpectralLogBudget (tau mass L1 L2 L3 L4 : Real) : Prop where
  nonnegative_mass : 0 <= mass
  nonnegative_one : 0 <= L1
  nonnegative_two : 0 <= L2
  nonnegative_three : 0 <= L3
  nonnegative_four : 0 <= L4
  bound_one : tau * L1 <= 2 * mass
  bound_two : tau ^ 2 * L2 <= 9 * mass
  bound_three : tau ^ 3 * L3 <= 76 * mass
  bound_four : tau ^ 4 * L4 <= 966 * mass

theorem spectralCoordinate_budget (tau lam s : Real) (hTau : 0 < tau)
    (hs0 : 0 <= s) (hs2 : s <= 2) (hLam0 : 0 <= lam) (hLam1 : lam <= 1)
    (hDen : tau <= 1 - s ^ 2 * lam) :
    SpectralLogBudget tau lam
      (spectralCoordinate1 lam s) (spectralCoordinate2 lam s)
      (spectralCoordinate3 lam s) (spectralCoordinate4 lam s) := by
  let q : Real := 1 - s ^ 2 * lam
  have hqPos : 0 < q := lt_of_lt_of_le hTau hDen
  have hq0 : 0 <= q := le_of_lt hqPos
  have hq1 : q <= 1 := by
    dsimp [q]
    nlinarith only [mul_nonneg (sq_nonneg s) hLam0]
  have hDenNe : Not (1 - s ^ 2 * lam = 0) := ne_of_gt hqPos
  have hN1 : 0 <= spectralCoordinate1 lam s := by
    unfold spectralCoordinate1
    positivity
  have hN2 : 0 <= spectralCoordinate2 lam s := by
    unfold spectralCoordinate2
    positivity
  have hN3 : 0 <= spectralCoordinate3 lam s := by
    unfold spectralCoordinate3
    positivity
  have hN4 : 0 <= spectralCoordinate4 lam s := by
    unfold spectralCoordinate4
    positivity
  have hClear1 : q * spectralCoordinate1 lam s = s * lam := by
    dsimp [q, spectralCoordinate1]
    field_simp [hDenNe] <;> ring
  have hClear2 : q ^ 2 * spectralCoordinate2 lam s =
      lam * q + 2 * s ^ 2 * lam ^ 2 := by
    dsimp [q, spectralCoordinate2]
    field_simp [hDenNe] <;> ring
  have hClear3 : q ^ 3 * spectralCoordinate3 lam s =
      6 * s * lam ^ 2 * q + 8 * s ^ 3 * lam ^ 3 := by
    dsimp [q, spectralCoordinate3]
    field_simp [hDenNe] <;> ring
  have hClear4 : q ^ 4 * spectralCoordinate4 lam s =
      6 * lam ^ 2 * q ^ 2 + 48 * s ^ 2 * lam ^ 3 * q +
        48 * s ^ 4 * lam ^ 4 := by
    dsimp [q, spectralCoordinate4]
    field_simp [hDenNe] <;> ring
  have hM10 := spectral_monomial_cap s lam q hs0 hs2 hLam0 hLam1 hq0 hq1 1 0 0
  have hM01 := spectral_monomial_cap s lam q hs0 hs2 hLam0 hLam1 hq0 hq1 0 0 1
  have hM20 := spectral_monomial_cap s lam q hs0 hs2 hLam0 hLam1 hq0 hq1 2 1 0
  have hM31 := spectral_monomial_cap s lam q hs0 hs2 hLam0 hLam1 hq0 hq1 1 1 1
  have hM32 := spectral_monomial_cap s lam q hs0 hs2 hLam0 hLam1 hq0 hq1 3 2 0
  have hM41 := spectral_monomial_cap s lam q hs0 hs2 hLam0 hLam1 hq0 hq1 0 1 2
  have hM42 := spectral_monomial_cap s lam q hs0 hs2 hLam0 hLam1 hq0 hq1 2 2 1
  have hM43 := spectral_monomial_cap s lam q hs0 hs2 hLam0 hLam1 hq0 hq1 4 3 0
  norm_num at hM10 hM01 hM20 hM31 hM32 hM41 hM42 hM43
  have hB1 : q * spectralCoordinate1 lam s <= 2 * lam := by
    rw [hClear1]
    exact hM10
  have hB2 : q ^ 2 * spectralCoordinate2 lam s <= 9 * lam := by
    rw [hClear2]
    nlinarith only [hM01, hM20]
  have hB3 : q ^ 3 * spectralCoordinate3 lam s <= 76 * lam := by
    rw [hClear3]
    nlinarith only [hM31, hM32]
  have hB4 : q ^ 4 * spectralCoordinate4 lam s <= 966 * lam := by
    rw [hClear4]
    nlinarith only [hM41, hM42, hM43]
  refine {
    nonnegative_mass := hLam0
    nonnegative_one := hN1
    nonnegative_two := hN2
    nonnegative_three := hN3
    nonnegative_four := hN4
    bound_one := le_trans (mul_le_mul_of_nonneg_right hDen hN1) hB1
    bound_two := ?_
    bound_three := ?_
    bound_four := ?_ }
  case refine_1 =>
    exact le_trans
      (mul_le_mul_of_nonneg_right
        (spectral_power_mono tau q (le_of_lt hTau) hDen 2) hN2) hB2
  case refine_2 =>
    exact le_trans
      (mul_le_mul_of_nonneg_right
        (spectral_power_mono tau q (le_of_lt hTau) hDen 3) hN3) hB3
  case refine_3 =>
    exact le_trans
      (mul_le_mul_of_nonneg_right
        (spectral_power_mono tau q (le_of_lt hTau) hDen 4) hN4) hB4

theorem spectralLogBudget_sum (S : Finset Iota) (lam : Iota -> Real) (tau s : Real)
    (hBudget : forall i, Membership.mem S i ->
      SpectralLogBudget tau (lam i)
        (spectralCoordinate1 (lam i) s) (spectralCoordinate2 (lam i) s)
        (spectralCoordinate3 (lam i) s) (spectralCoordinate4 (lam i) s)) :
    SpectralLogBudget tau (Finset.sum S lam)
      (Finset.sum S (fun i => spectralCoordinate1 (lam i) s))
      (Finset.sum S (fun i => spectralCoordinate2 (lam i) s))
      (Finset.sum S (fun i => spectralCoordinate3 (lam i) s))
      (Finset.sum S (fun i => spectralCoordinate4 (lam i) s)) := by
  refine {
    nonnegative_mass := Finset.sum_nonneg (fun i hi => (hBudget i hi).nonnegative_mass)
    nonnegative_one := Finset.sum_nonneg (fun i hi => (hBudget i hi).nonnegative_one)
    nonnegative_two := Finset.sum_nonneg (fun i hi => (hBudget i hi).nonnegative_two)
    nonnegative_three := Finset.sum_nonneg (fun i hi => (hBudget i hi).nonnegative_three)
    nonnegative_four := Finset.sum_nonneg (fun i hi => (hBudget i hi).nonnegative_four)
    bound_one := ?_
    bound_two := ?_
    bound_three := ?_
    bound_four := ?_ }
  case refine_1 =>
    simpa only [Finset.mul_sum] using
      Finset.sum_le_sum (fun i hi => (hBudget i hi).bound_one)
  case refine_2 =>
    simpa only [Finset.mul_sum] using
      Finset.sum_le_sum (fun i hi => (hBudget i hi).bound_two)
  case refine_3 =>
    simpa only [Finset.mul_sum] using
      Finset.sum_le_sum (fun i hi => (hBudget i hi).bound_three)
  case refine_4 =>
    simpa only [Finset.mul_sum] using
      Finset.sum_le_sum (fun i hi => (hBudget i hi).bound_four)

theorem spectralFactors_strip_budget (S : Finset Iota) (lam : Iota -> Real)
    (delta eps s : Real) (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (hEps0 : 0 <= eps) (hEps1 : eps <= delta / 4)
    (hLam0 : forall i, Membership.mem S i -> 0 <= lam i)
    (hLam1 : forall i, Membership.mem S i -> lam i <= (1 - delta) ^ 2)
    (hs : abs (s - 1) <= eps) :
    SpectralLogBudget delta (Finset.sum S lam)
      (Finset.sum S (fun i => spectralCoordinate1 (lam i) s))
      (Finset.sum S (fun i => spectralCoordinate2 (lam i) s))
      (Finset.sum S (fun i => spectralCoordinate3 (lam i) s))
      (Finset.sum S (fun i => spectralCoordinate4 (lam i) s)) := by
  apply spectralLogBudget_sum
  intro i hi
  have hStrip := spectralFactor_strip delta eps (lam i) s hDelta0 hDelta1
    hEps0 hEps1 (hLam0 i hi) (hLam1 i hi) hs
  exact spectralCoordinate_budget delta (lam i) s hDelta0
    hStrip.1 hStrip.2.1 (hLam0 i hi) hStrip.2.2.1 hStrip.2.2.2

end PrimeFactorOscillations
