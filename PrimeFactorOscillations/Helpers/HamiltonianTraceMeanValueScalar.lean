/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Full scalar secant pairing for the signed trace moment consumer

Every term of the geometric difference quotient is paired with its
reflected exponent. The even-power bound is uniform over both real
signs and every moment order, with no finite numerical truncation.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

theorem hamiltonian_nonnegative_power_pair
    (x y : Real) (r s : Nat) (hx : 0 <= x) (hy : 0 <= y) :
    x ^ r * y ^ s + x ^ s * y ^ r <= x ^ (r + s) + y ^ (r + s) := by
  rw [pow_add, pow_add]
  by_cases hxy : x <= y
  case pos =>
    have hr : x ^ r <= y ^ r := by gcongr
    have hs : x ^ s <= y ^ s := by gcongr
    have h := mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hs)
    nlinarith only [h]
  case neg =>
    have hyx : y <= x := by linarith only [hxy]
    have hr : y ^ r <= x ^ r := by gcongr
    have hs : y ^ s <= x ^ s := by gcongr
    have h := mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hs)
    nlinarith only [h]

theorem hamiltonian_even_power_pair
    (x y : Real) (r s : Nat) (hEven : Even (r + s)) :
    x ^ r * y ^ s + x ^ s * y ^ r <= x ^ (r + s) + y ^ (r + s) := by
  let t := hEven.choose
  have hRS : r + s = t + t := hEven.choose_spec
  have hx0 : 0 <= x ^ (r + s) := by
    rw [hRS, pow_add]
    exact mul_self_nonneg (x ^ t)
  have hy0 : 0 <= y ^ (r + s) := by
    rw [hRS, pow_add]
    exact mul_self_nonneg (y ^ t)
  have hAbsX : abs x ^ (r + s) = x ^ (r + s) := by
    rw [<- abs_pow, abs_of_nonneg hx0]
  have hAbsY : abs y ^ (r + s) = y ^ (r + s) := by
    rw [<- abs_pow, abs_of_nonneg hy0]
  have hFirst : x ^ r * y ^ s <= abs x ^ r * abs y ^ s := by
    simpa only [abs_mul, abs_pow] using le_abs_self (x ^ r * y ^ s)
  have hSecond : x ^ s * y ^ r <= abs x ^ s * abs y ^ r := by
    simpa only [abs_mul, abs_pow] using le_abs_self (x ^ s * y ^ r)
  have hPair := hamiltonian_nonnegative_power_pair (abs x) (abs y) r s
    (abs_nonneg x) (abs_nonneg y)
  rw [hAbsX, hAbsY] at hPair
  linarith only [hFirst, hSecond, hPair]

def hamiltonianPowerSecantSum (x y : Real) (q : Nat) : Real :=
  (Finset.range (q + 1)).sum (fun r => x ^ r * y ^ (q - r))

theorem hamiltonian_power_secant_successor (x y : Real) (q : Nat) :
    hamiltonianPowerSecantSum x y (q + 1) =
      y * hamiltonianPowerSecantSum x y q + x ^ (q + 1) := by
  have hTerms :
      (Finset.range (q + 1)).sum (fun r => x ^ r * y ^ (q + 1 - r)) =
        y * (Finset.range (q + 1)).sum (fun r => x ^ r * y ^ (q - r)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    have hrq : r <= q := by have h := Finset.mem_range.mp hr; omega
    have hSub : q + 1 - r = (q - r) + 1 := by omega
    rw [hSub, pow_succ]
    ring
  unfold hamiltonianPowerSecantSum
  rw [Finset.sum_range_succ (n := q + 1)]
  simp only [Nat.sub_self, pow_zero, mul_one]
  rw [hTerms]

theorem hamiltonian_power_secant_factorization (x y : Real) (q : Nat) :
    (x - y) * hamiltonianPowerSecantSum x y q =
      x ^ (q + 1) - y ^ (q + 1) := by
  induction q with
  | zero => simp [hamiltonianPowerSecantSum]
  | succ q ih =>
      rw [hamiltonian_power_secant_successor]
      calc
        _ = y * ((x - y) * hamiltonianPowerSecantSum x y q) +
            (x - y) * x ^ (q + 1) := by ring
        _ = y * (x ^ (q + 1) - y ^ (q + 1)) +
            (x - y) * x ^ (q + 1) := by rw [ih]
        _ = _ := by simp only [pow_succ]; ring

theorem hamiltonian_even_power_secant_sum_bound
    (x y : Real) (q : Nat) (hEven : Even q) :
    2 * hamiltonianPowerSecantSum x y q <=
      ((q + 1 : Nat) : Real) * (x ^ q + y ^ q) := by
  have hPoint (r : Nat) (hr : Membership.mem (Finset.range (q + 1)) r) :
      x ^ r * y ^ (q - r) + x ^ (q - r) * y ^ (q - (q - r)) <=
        x ^ q + y ^ q := by
    have hrq : r <= q := by have h := Finset.mem_range.mp hr; omega
    have hRS : r + (q - r) = q := by omega
    have hBack : q - (q - r) = r := by omega
    have hEvenRS : Even (r + (q - r)) := by rw [hRS]; exact hEven
    have h := hamiltonian_even_power_pair x y r (q - r) hEvenRS
    rw [hRS] at h
    simpa only [hBack] using h
  have hReflect :
      (Finset.range (q + 1)).sum (fun r => x ^ (q - r) * y ^ (q - (q - r))) =
        (Finset.range (q + 1)).sum (fun r => x ^ r * y ^ (q - r)) := by
    simpa only [Nat.add_sub_cancel] using
      Finset.sum_range_reflect (fun r => x ^ r * y ^ (q - r)) (q + 1)
  have hSum := Finset.sum_le_sum (s := Finset.range (q + 1)) hPoint
  rw [Finset.sum_add_distrib, hReflect, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at hSum
  unfold hamiltonianPowerSecantSum
  linarith only [hSum]

theorem hamiltonian_trace_mean_value_scalar
    (x y : Real) (q : Nat) (hEven : Even q) :
    (x - y) * (x ^ (q + 1) - y ^ (q + 1)) <=
      (((q + 1 : Nat) : Real) / 2) * (x - y) ^ 2 * (x ^ q + y ^ q) := by
  have hBound := hamiltonian_even_power_secant_sum_bound x y q hEven
  have hProduct := mul_le_mul_of_nonneg_left hBound (sq_nonneg (x - y))
  have hIdentity : (x - y) * (x ^ (q + 1) - y ^ (q + 1)) =
      (x - y) ^ 2 * hamiltonianPowerSecantSum x y q := by
    rw [<- hamiltonian_power_secant_factorization]
    ring
  rw [hIdentity]
  nlinarith only [hProduct]

theorem hamiltonian_trace_mean_value_scalar_odd_power
    (x y : Real) (k : Nat) (hk : 1 <= k) :
    (x - y) * (x ^ (2 * k - 1) - y ^ (2 * k - 1)) <=
      ((2 * (k : Real) - 1) / 2) * (x - y) ^ 2 *
        (x ^ (2 * k - 2) + y ^ (2 * k - 2)) := by
  let q := 2 * k - 2
  have hEven : Even q := Exists.intro (k - 1) (by dsimp only [q]; omega)
  have hSucc : q + 1 = 2 * k - 1 := by dsimp only [q]; omega
  have hAdd : ((2 * k - 1 : Nat) : Real) + 1 = 2 * (k : Real) := by
    exact_mod_cast Nat.sub_add_cancel (show 1 <= 2 * k by omega)
  have hCoeff : ((2 * k - 1 : Nat) : Real) = 2 * (k : Real) - 1 := by
    linarith only [hAdd]
  have h := hamiltonian_trace_mean_value_scalar x y q hEven
  rw [hSucc, hCoeff] at h
  exact h

end PrimeFactorOscillations
