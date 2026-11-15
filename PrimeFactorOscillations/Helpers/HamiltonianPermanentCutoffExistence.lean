/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPermanentCutoffChoice

/-! # Feasible scalar cutoff for the signed physical-window remainder

The cutoff is proportional to sqrt N. Its cube-root parameter retains the
N^-2 moderate- and high-diagram budget rather than weakening its exponent.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianPermanentCutoff (delta a x : Real) : Nat :=
  Nat.ceil (1000 * (1 + a) ^ 3 * Real.sqrt x / delta ^ 2)

def hamiltonianPermanentCutoffUpper (delta a : Real) : Real :=
  1001 * (1 + a) ^ 3 / delta ^ 2

def hamiltonianPermanentCutoffThreshold (delta a : Real) : Real :=
  1001 * (192 * Real.exp 1) ^ 3 * (1 + a) ^ 6 / delta ^ 5

theorem hamiltonian_cube_le_inverse (x y : Real)
    (hx : 0 <= x) (hy : 0 <= y) (hCube : x ^ 3 <= y ^ 3) : x <= y := by
  by_contra h
  have hLess : y < x := lt_of_not_ge h
  have hxPos : 0 < x := lt_of_le_of_lt hy hLess
  have hFactor : 0 < x ^ 2 + x * y + y ^ 2 :=
    add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg (pow_pos hxPos 2) (mul_nonneg hx hy)) (sq_nonneg y)
  have hProduct := mul_pos (sub_pos.mpr hLess) hFactor
  nlinarith only [hCube, hProduct]

theorem hamiltonian_cube_root_exact (x : Real) (hx : 0 <= x) :
    (x ^ (1 / 3 : Real)) ^ 3 = x := by
  calc
    _ = (x ^ (1 / 3 : Real)) ^ (3 : Real) :=
      (Real.rpow_natCast _ 3).symm
    _ = x ^ ((1 / 3 : Real) * 3) := (Real.rpow_mul hx _ _).symm
    _ = x := by norm_num

theorem hamiltonian_permanent_cutoff_bounds (delta a x : Real)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (ha : 1 <= a) (hx : 1 <= x) :
    And (1000 * (1 + a) ^ 3 * Real.sqrt x / delta ^ 2 <=
          (hamiltonianPermanentCutoff delta a x : Real))
      ((hamiltonianPermanentCutoff delta a x : Real) <=
        hamiltonianPermanentCutoffUpper delta a * Real.sqrt x) := by
  let q := (1 + a) ^ 3 * Real.sqrt x / delta ^ 2
  have hD2 : 0 < delta ^ 2 := pow_pos hDelta0 2
  have hD2Upper : delta ^ 2 <= 1 := by nlinarith
  have hRoot : 1 <= Real.sqrt x := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hx
  have hAPow : 1 <= (1 + a) ^ 3 := by nlinarith [sq_nonneg a]
  have hNum : 1 <= (1 + a) ^ 3 * Real.sqrt x :=
    calc
      _ = (1 : Real) * 1 := by norm_num
      _ <= _ := mul_le_mul hAPow hRoot (by norm_num) (by positivity)
  have hQ : 1 <= q := by
    calc
      _ <= (1 + a) ^ 3 * Real.sqrt x := hNum
      _ = ((1 + a) ^ 3 * Real.sqrt x) / 1 := by rw [div_one]
      _ <= q := div_le_div_of_nonneg_left (by positivity) hD2 hD2Upper
  have hCeil := Nat.le_ceil (1000 * (1 + a) ^ 3 * Real.sqrt x / delta ^ 2)
  have hCeilUpper := Nat.ceil_lt_add_one
    (show 0 <= 1000 * (1 + a) ^ 3 * Real.sqrt x / delta ^ 2 by positivity)
  constructor
  next =>
    exact hCeil
  next =>
    have hU : (hamiltonianPermanentCutoff delta a x : Real) <= 1001 * q := by
      change (Nat.ceil (1000 * (1 + a) ^ 3 * Real.sqrt x / delta ^ 2) : Real) <= _
      have hId : 1000 * (1 + a) ^ 3 * Real.sqrt x / delta ^ 2 = 1000 * q := by
        dsimp [q]
        ring
      rw [hId] at hCeilUpper
      rw [hId]
      linarith
    calc
      _ <= 1001 * q := hU
      _ = _ := by dsimp [hamiltonianPermanentCutoffUpper, q]; ring

theorem hamiltonian_permanent_cutoff_at_least_eleven (delta a x : Real)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (ha : 1 <= a) (hx : 1 <= x) :
    11 <= hamiltonianPermanentCutoff delta a x := by
  have hBounds := hamiltonian_permanent_cutoff_bounds delta a x hDelta0 hDelta1 ha hx
  have hRoot : 1 <= Real.sqrt x := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hx
  have hAPow : 1 <= (1 + a) ^ 3 := by nlinarith [sq_nonneg a]
  have hProd : 1 <= (1 + a) ^ 3 * Real.sqrt x := by
    calc
      _ = (1 : Real) * 1 := by norm_num
      _ <= _ := mul_le_mul hAPow hRoot (by norm_num) (by positivity)
  have hD2 : 0 < delta ^ 2 := pow_pos hDelta0 2
  have hD2Upper : delta ^ 2 <= 1 := by nlinarith
  have hLarge : (1000 : Real) <= 1000 * (1 + a) ^ 3 * Real.sqrt x / delta ^ 2 := by
    calc
      _ <= 1000 * (1 + a) ^ 3 * Real.sqrt x := by nlinarith only [hProd]
      _ = (1000 * (1 + a) ^ 3 * Real.sqrt x) / 1 := by rw [div_one]
      _ <= _ := div_le_div_of_nonneg_left (by positivity) hD2 hD2Upper
  exact_mod_cast (show (11 : Real) <=
      (hamiltonianPermanentCutoff delta a x : Real) by linarith)

theorem hamiltonian_permanent_cutoff_square_bound (delta a x : Real)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (ha : 1 <= a) (hx : 1 <= x) :
    (hamiltonianPermanentCutoff delta a x : Real) ^ 2 <=
      hamiltonianPermanentCutoffUpper delta a ^ 2 * x := by
  have hBounds := hamiltonian_permanent_cutoff_bounds delta a x hDelta0 hDelta1 ha hx
  have h := wick_nonnegative_power_le
    (hamiltonianPermanentCutoff delta a x : Real)
    (hamiltonianPermanentCutoffUpper delta a * Real.sqrt x)
    (Nat.cast_nonneg _) hBounds.2 2
  simpa only [mul_pow, Real.sq_sqrt (le_trans (by norm_num) hx)] using h

theorem hamiltonian_permanent_cutoff_cubic_budget (delta a x kappa : Real)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (ha : 1 <= a) (hx : 1 <= x) (hKappa0 : 0 <= kappa)
    (hKappa : kappa <= 6 * a / delta)
    (hSize : hamiltonianPermanentCutoffThreshold delta a <= Real.sqrt x) :
    (hamiltonianPermanentCutoff delta a x : Real) *
      (32 * Real.exp 1 * kappa) ^ 3 <= x := by
  have ha0 : 0 <= a := le_trans (by norm_num) ha
  have hB0 : 0 <= hamiltonianPermanentCutoffUpper delta a := by
    unfold hamiltonianPermanentCutoffUpper
    positivity
  have hBound := (hamiltonian_permanent_cutoff_bounds delta a x hDelta0 hDelta1 ha hx).2
  have hPow := wick_nonnegative_power_le kappa (6 * a / delta) hKappa0 hKappa 3
  have hAPow := wick_nonnegative_power_le a (1 + a) ha0 (by linarith) 3
  have hMain :
      hamiltonianPermanentCutoffUpper delta a * (32 * Real.exp 1 * kappa) ^ 3 <=
        hamiltonianPermanentCutoffThreshold delta a := by
    calc
      _ <= hamiltonianPermanentCutoffUpper delta a *
          ((32 * Real.exp 1) ^ 3 * (6 * a / delta) ^ 3) := by
        simpa only [mul_pow, mul_assoc] using
          mul_le_mul_of_nonneg_left hPow
            (mul_nonneg hB0 (pow_nonneg (by positivity : (0 : Real) <= 32 * Real.exp 1) 3))
      _ = (1001 * (192 * Real.exp 1) ^ 3 / delta ^ 5) *
          ((1 + a) ^ 3 * a ^ 3) := by
        unfold hamiltonianPermanentCutoffUpper
        field_simp [ne_of_gt hDelta0]
        ring
      _ <= (1001 * (192 * Real.exp 1) ^ 3 / delta ^ 5) *
          ((1 + a) ^ 3 * (1 + a) ^ 3) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hAPow (pow_nonneg (by linarith : (0 : Real) <= 1 + a) 3))
          (by positivity)
      _ = _ := by unfold hamiltonianPermanentCutoffThreshold; ring
  calc
    _ <= (hamiltonianPermanentCutoffUpper delta a * Real.sqrt x) *
        (32 * Real.exp 1 * kappa) ^ 3 :=
      mul_le_mul_of_nonneg_right hBound (by positivity)
    _ = Real.sqrt x *
        (hamiltonianPermanentCutoffUpper delta a * (32 * Real.exp 1 * kappa) ^ 3) := by ring
    _ <= Real.sqrt x * Real.sqrt x :=
      mul_le_mul_of_nonneg_left (le_trans hMain hSize) (Real.sqrt_nonneg x)
    _ = x := Real.mul_self_sqrt (le_trans (by norm_num) hx)

theorem hamiltonian_permanent_threshold_dominates_upper (delta a : Real)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1) (ha : 1 <= a) :
    hamiltonianPermanentCutoffUpper delta a <=
      hamiltonianPermanentCutoffThreshold delta a := by
  have hD3 := wick_nonnegative_power_le delta 1 hDelta0.le hDelta1 3
  have hD3Upper : delta ^ 3 <= 1 := by simpa only [one_pow] using hD3
  have hExp := Real.add_one_le_exp (1 : Real)
  have hE : 1 <= (192 * Real.exp 1) ^ 3 := by
    have h := wick_nonnegative_power_le (1 : Real) (192 * Real.exp 1)
      (by norm_num) (by linarith) 3
    simpa only [one_pow] using h
  have hA : 1 <= (1 + a) ^ 3 := by
    have h := wick_nonnegative_power_le (1 : Real) (1 + a)
      (by norm_num) (by linarith) 3
    simpa only [one_pow] using h
  have hNumerator : 1 <= (192 * Real.exp 1) ^ 3 * (1 + a) ^ 3 := by
    simpa only [one_mul] using mul_le_mul hE hA (by norm_num) (by positivity)
  have hFactor : 1 <= (192 * Real.exp 1) ^ 3 * (1 + a) ^ 3 / delta ^ 3 := by
    calc
      _ <= (192 * Real.exp 1) ^ 3 * (1 + a) ^ 3 := hNumerator
      _ = ((192 * Real.exp 1) ^ 3 * (1 + a) ^ 3) / 1 := by rw [div_one]
      _ <= _ := div_le_div_of_nonneg_left (by positivity) (pow_pos hDelta0 3) hD3Upper
  calc
    _ = hamiltonianPermanentCutoffUpper delta a * 1 := by rw [mul_one]
    _ <= hamiltonianPermanentCutoffUpper delta a *
        ((192 * Real.exp 1) ^ 3 * (1 + a) ^ 3 / delta ^ 3) :=
      mul_le_mul_of_nonneg_left hFactor (by unfold hamiltonianPermanentCutoffUpper; positivity)
    _ = _ := by
      unfold hamiltonianPermanentCutoffUpper hamiltonianPermanentCutoffThreshold
      field_simp [ne_of_gt hDelta0] <;> ring

theorem hamiltonian_permanent_cutoff_le_size (delta a x : Real)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (ha : 1 <= a) (hx : 1 <= x)
    (hSize : hamiltonianPermanentCutoffThreshold delta a <= Real.sqrt x) :
    (hamiltonianPermanentCutoff delta a x : Real) <= x := by
  have hUpper := le_trans
    (hamiltonian_permanent_threshold_dominates_upper delta a hDelta0 hDelta1 ha) hSize
  calc
    _ <= hamiltonianPermanentCutoffUpper delta a * Real.sqrt x :=
      (hamiltonian_permanent_cutoff_bounds delta a x hDelta0 hDelta1 ha hx).2
    _ <= Real.sqrt x * Real.sqrt x :=
      mul_le_mul_of_nonneg_right hUpper (Real.sqrt_nonneg x)
    _ = x := Real.mul_self_sqrt (le_trans (by norm_num) hx)

def hamiltonianPermanentCutoffRoot (delta a x : Real) : Real :=
  ((hamiltonianPermanentCutoff delta a x : Real) / x) ^ (1 / 3 : Real)

theorem hamiltonian_permanent_cutoff_root_bounds (delta a x : Real)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (ha : 1 <= a) (hx : 1 <= x)
    (hSize : hamiltonianPermanentCutoffThreshold delta a <= Real.sqrt x) :
    And (0 <= hamiltonianPermanentCutoffRoot delta a x)
      (And (hamiltonianPermanentCutoffRoot delta a x <= 1)
        (hamiltonianPermanentCutoffRoot delta a x ^ 3 =
          (hamiltonianPermanentCutoff delta a x : Real) / x)) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hRatio0 : 0 <= (hamiltonianPermanentCutoff delta a x : Real) / x :=
    div_nonneg (Nat.cast_nonneg _) hx0.le
  have hRoot0 : 0 <= hamiltonianPermanentCutoffRoot delta a x :=
    Real.rpow_nonneg hRatio0 _
  have hCube : hamiltonianPermanentCutoffRoot delta a x ^ 3 =
      (hamiltonianPermanentCutoff delta a x : Real) / x :=
    hamiltonian_cube_root_exact _ hRatio0
  have hRatio1 : (hamiltonianPermanentCutoff delta a x : Real) / x <= 1 := by
    simpa only [div_self (ne_of_gt hx0)] using div_le_div_of_nonneg_right
      (hamiltonian_permanent_cutoff_le_size delta a x hDelta0 hDelta1 ha hx hSize) hx0.le
  refine And.intro hRoot0 (And.intro ?_ hCube)
  apply hamiltonian_cube_le_inverse _ 1 hRoot0 (by norm_num)
  simpa only [hCube, one_pow] using hRatio1

theorem hamiltonian_permanent_cutoff_root_small (delta a x kappa : Real)
    (hDelta0 : 0 < delta) (hDelta1 : delta <= 1)
    (ha : 1 <= a) (hx : 1 <= x) (hKappa0 : 0 <= kappa)
    (hKappa : kappa <= 6 * a / delta)
    (hSize : hamiltonianPermanentCutoffThreshold delta a <= Real.sqrt x) :
    16 * Real.exp 1 * kappa * hamiltonianPermanentCutoffRoot delta a x <= 1 / 2 := by
  have hRoot := hamiltonian_permanent_cutoff_root_bounds delta a x hDelta0 hDelta1 ha hx hSize
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hBudget := hamiltonian_permanent_cutoff_cubic_budget
    delta a x kappa hDelta0 hDelta1 ha hx hKappa0 hKappa hSize
  have hBudgetDiv :
      ((hamiltonianPermanentCutoff delta a x : Real) * (32 * Real.exp 1 * kappa) ^ 3) /
        x <= 1 := by
    simpa only [div_self (ne_of_gt hx0)] using
      div_le_div_of_nonneg_right hBudget hx0.le
  have hIdentity :
      (16 * Real.exp 1 * kappa * hamiltonianPermanentCutoffRoot delta a x) ^ 3 =
        (((hamiltonianPermanentCutoff delta a x : Real) *
          (32 * Real.exp 1 * kappa) ^ 3) / x) / 8 := by
    rw [mul_pow, hRoot.2.2]
    ring
  apply hamiltonian_cube_le_inverse _ (1 / 2)
    (mul_nonneg (mul_nonneg (by positivity) hKappa0) hRoot.1) (by norm_num)
  rw [hIdentity]
  nlinarith only [hBudgetDiv]

end PrimeFactorOscillations
