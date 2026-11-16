/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCoprimeEulerCoefficients

/-! # Uniform arithmetic bounds for the complete coprime constant

The full signed Euler coefficients are consumed before any positive
majorant. A finite telescoping bound controls all odd prime factors
uniformly; the actual constant retains its proved prime-product series.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_coprime_constant_prime_factors
    (n m : Nat) [NeZero n] [NeZero m] (hn : 1 < n) (hm : 1 < m)
    (hOddN : Odd n) (hOddM : Odd m) (hFactors : n.primeFactors = m.primeFactors) :
    hamiltonianCoprimeArithmeticConstant n = hamiltonianCoprimeArithmeticConstant m := by
  have hN := hamiltonian_coprime_odd_constant_prime_product_series n hOddN hn
  have hM := hamiltonian_coprime_odd_constant_prime_product_series m hOddM hm
  rw [hFactors] at hN
  have hLog := hN.unique hM
  have h := congrArg Real.exp hLog
  simpa only [Real.exp_log (hamiltonian_coprime_odd_constant_positive hOddN),
    Real.exp_log (hamiltonian_coprime_odd_constant_positive hOddM)] using h

theorem hamiltonian_reciprocal_square_step (x : Real) (hx : 1 <= x) :
    1 / x ^ 2 <= 2 * (1 / x - 1 / (x + 1)) := by
  have hX : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hX1 : 0 < x + 1 := by linarith only [hX]
  have hXNe : Not (x = 0) := ne_of_gt hX
  have hX1Ne : Not (x + 1 = 0) := ne_of_gt hX1
  have hDen : 0 < x ^ 2 * (x + 1) := mul_pos (pow_pos hX _) hX1
  have hL : (1 / x ^ 2) * (x ^ 2 * (x + 1)) = x + 1 := by field_simp
  have hR : (2 * (1 / x - 1 / (x + 1))) * (x ^ 2 * (x + 1)) = 2 * x := by
    field_simp
    <;> ring
  apply (mul_le_mul_iff_of_pos_right hDen).mp
  rw [hL, hR]
  linarith only [hx]

theorem hamiltonian_reciprocal_square_finite_tail (L : Nat) :
    (Finset.range L).sum (fun k => 1 / ((k + 1 : Nat) : Real) ^ 2) <=
      2 * (1 - 1 / ((L + 1 : Nat) : Real)) := by
  induction L with
  | zero => norm_num
  | succ L ih =>
    rw [Finset.sum_range_succ]
    have hOne : (1 : Real) <= ((L + 1 : Nat) : Real) := by
      exact_mod_cast (show 1 <= L + 1 by omega)
    have hStep := hamiltonian_reciprocal_square_step ((L + 1 : Nat) : Real) hOne
    have hCast : ((L + 1 : Nat) : Real) + 1 = ((L + 1 + 1 : Nat) : Real) := by push_cast; ring
    rw [hCast] at hStep
    nlinarith only [ih, hStep]

theorem hamiltonian_reciprocal_square_finite_bound (L : Nat) :
    (Finset.range L).sum (fun k => 1 / ((k + 1 : Nat) : Real) ^ 2) <= 2 := by
  have h := hamiltonian_reciprocal_square_finite_tail L
  have hInv : 0 <= 1 / ((L + 1 : Nat) : Real) := by positivity
  linarith only [h, hInv]


theorem hamiltonian_one_le_power (x : Real) (hx : 1 <= x) (a : Nat) :
    1 <= x ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ]
    have hX0 : 0 <= x := le_trans (by norm_num) hx
    have h := mul_le_mul_of_nonneg_right ih hX0
    rw [one_mul] at h
    exact hx.trans h

theorem hamiltonian_square_le_even_power (x : Real) (hx : 1 <= x)
    (j : Nat) (hj : 0 < j) : x ^ 2 <= x ^ (2 * j) := by
  rw [show 2 * j = 2 + 2 * (j - 1) by omega, pow_add]
  have h := mul_le_mul_of_nonneg_left
    (hamiltonian_one_le_power x hx (2 * (j - 1))) (sq_nonneg x)
  simpa only [mul_one] using h

theorem hamiltonian_odd_reciprocal_power_budget (p j : Nat)
    (hOdd : Odd p) (hp3 : 3 <= p) (hj : 0 < j) :
    1 / ((p : Real) - 1) ^ (2 * j) <=
      (1 / 4 : Real) ^ j / ((((p - 3) / 2 + 1 : Nat) : Real) ^ 2) := by
  let ell : Nat := (p - 3) / 2 + 1
  choose k hk using hOdd
  have hRel : p = 2 * ell + 1 := by dsimp only [ell]; omega
  have hEll : (1 : Real) <= (ell : Real) := by
    exact_mod_cast (show 1 <= ell by dsimp only [ell]; omega)
  have hEllPos : 0 < (ell : Real) := lt_of_lt_of_le (by norm_num) hEll
  have hPminus : (p : Real) - 1 = 2 * (ell : Real) := by
    have h : (p : Real) = 2 * (ell : Real) + 1 := by exact_mod_cast hRel
    linarith only [h]
  have hDen : ((p : Real) - 1) ^ (2 * j) =
      (4 : Real) ^ j * (ell : Real) ^ (2 * j) := by
    rw [hPminus, mul_pow, pow_mul]
    norm_num
  have hFour : (0 : Real) < (4 : Real) ^ j := pow_pos (by norm_num) _
  have hInv := one_div_le_one_div_of_le (mul_pos hFour (pow_pos hEllPos 2))
    (mul_le_mul_of_nonneg_left (hamiltonian_square_le_even_power _ hEll j hj) hFour.le)
  have hFourNe : Not ((4 : Real) ^ j = 0) := ne_of_gt hFour
  have hEllNe : Not ((ell : Real) = 0) := ne_of_gt hEllPos
  change 1 / ((p : Real) - 1) ^ (2 * j) <= (1 / 4 : Real) ^ j / (ell : Real) ^ 2
  calc
    _ = 1 / ((4 : Real) ^ j * (ell : Real) ^ (2 * j)) := by rw [hDen]
    _ <= 1 / ((4 : Real) ^ j * (ell : Real) ^ 2) := hInv
    _ = _ := by rw [one_div_pow]; field_simp

theorem hamiltonian_odd_prime_factor_data (n p : Nat) [NeZero n]
    (hOdd : Odd n) (hp : Membership.mem n.primeFactors p) :
    Odd p /\ 3 <= p /\ p <= n := by
  have hData := Nat.mem_primeFactors.mp hp
  have hNotTwo : Not (p = 2) := by
    intro hTwo
    have hDiv := hData.2.1
    rw [hTwo] at hDiv
    choose k hk using hDiv
    have hEven : Even n := Exists.intro k (by omega)
    exact (Nat.not_even_iff_odd.mpr hOdd) hEven
  exact And.intro (hData.1.odd_of_ne_two hNotTwo) (And.intro (by have h := hData.1.two_le; omega)
    (Nat.le_of_dvd (NeZero.pos n) hData.2.1))

theorem hamiltonian_odd_prime_reciprocal_budget (n j : Nat) [NeZero n]
    (hOdd : Odd n) (hj : 0 < j) :
    n.primeFactors.sum (fun p => 1 / ((p : Real) - 1) ^ (2 * j)) <=
      2 * (1 / 4 : Real) ^ j := by
  let g := fun p : Nat => (p - 3) / 2
  have hRel (p : Nat) (hp : Membership.mem n.primeFactors p) :
      p = 2 * g p + 3 := by
    have hData := hamiltonian_odd_prime_factor_data n p hOdd hp
    choose k hk using hData.1
    dsimp only [g]
    omega
  have hInj : Set.InjOn g (n.primeFactors : Set Nat) := by
    intro p hp q hq hEq
    have hP := hRel p hp
    have hQ := hRel q hq
    omega
  have hSubset : n.primeFactors.image g <= Finset.range n := by
    intro k hk
    choose p hp hEq using Finset.mem_image.mp hk
    have hData := hamiltonian_odd_prime_factor_data n p hOdd hp
    have hP := hRel p hp
    apply Finset.mem_range.mpr
    omega
  have hMapped :
      n.primeFactors.sum (fun p => 1 / ((g p + 1 : Nat) : Real) ^ 2) =
        (n.primeFactors.image g).sum (fun k => 1 / ((k + 1 : Nat) : Real) ^ 2) :=
    (Finset.sum_image (f := fun k : Nat => 1 / ((k + 1 : Nat) : Real) ^ 2) hInj).symm
  have hSubsetSum :=
    Finset.sum_le_sum_of_subset_of_nonneg hSubset
      (fun k hk hNot => show (0 : Real) <= 1 / ((k + 1 : Nat) : Real) ^ 2 by positivity)
  have hSumBound :
      n.primeFactors.sum (fun p => 1 / ((g p + 1 : Nat) : Real) ^ 2) <= 2 := by
    rw [hMapped]
    exact hSubsetSum.trans (hamiltonian_reciprocal_square_finite_bound n)
  calc
    _ <= n.primeFactors.sum (fun p =>
        (1 / 4 : Real) ^ j / ((g p + 1 : Nat) : Real) ^ 2) := by
      apply Finset.sum_le_sum
      intro p hp
      have hData := hamiltonian_odd_prime_factor_data n p hOdd hp
      exact hamiltonian_odd_reciprocal_power_budget p j hData.1 hData.2.1 hj
    _ = (1 / 4 : Real) ^ j *
        n.primeFactors.sum (fun p => 1 / ((g p + 1 : Nat) : Real) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ <= (1 / 4 : Real) ^ j * 2 :=
      mul_le_mul_of_nonneg_left hSumBound (pow_nonneg (by norm_num) j)
    _ = _ := by ring


theorem hamiltonian_product_unit_interval {Iota : Type*} [DecidableEq Iota]
    (S : Finset Iota) (f : Iota -> Real)
    (hf : forall i, Membership.mem S i -> 0 <= f i /\ f i <= 1) :
    0 <= S.prod f /\ S.prod f <= 1 := by
  revert hf
  induction S using Finset.induction_on with
  | empty =>
    intro hf
    simp
  | @insert i S hi ih =>
    intro hf
    have hI := hf i (Finset.mem_insert_self i S)
    have hS := ih (fun k hk => hf k (Finset.mem_insert_of_mem hk))
    rw [Finset.prod_insert hi]
    refine And.intro (mul_nonneg hI.1 hS.1) ?_
    have h := mul_le_mul_of_nonneg_left hS.2 hI.1
    rw [mul_one] at h
    exact h.trans hI.2

def hamiltonianCoprimeLogCoefficient (n j : Nat) : Real :=
  if j = 0 then 1 else
    (1 - n.primeFactors.prod (fun p =>
      1 - 1 / ((p : Real) - 1) ^ (2 * j))) / ((2 * j + 1 : Nat) : Real)

theorem hamiltonian_coprime_euler_deficit_bounds (n j : Nat) [NeZero n]
    (hOdd : Odd n) (hj : 0 < j) :
    0 <= 1 - n.primeFactors.prod (fun p => 1 - 1 / ((p : Real) - 1) ^ (2 * j)) /\
      1 - n.primeFactors.prod (fun p => 1 - 1 / ((p : Real) - 1) ^ (2 * j)) <=
        2 * (1 / 4 : Real) ^ j := by
  let u := fun p : Nat => 1 / ((p : Real) - 1) ^ (2 * j)
  have hU : forall p, Membership.mem n.primeFactors p -> 0 <= u p /\ u p <= 1 := by
    intro p hp
    have hData := hamiltonian_odd_prime_factor_data n p hOdd hp
    have hpR : (3 : Real) <= (p : Real) := by exact_mod_cast hData.2.1
    have hBase : 1 <= (p : Real) - 1 := by linarith only [hpR]
    have hPower := hamiltonian_one_le_power ((p : Real) - 1) hBase (2 * j)
    have hInv := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1) hPower
    constructor
    case left =>
      dsimp only [u]
      positivity
    case right => simpa only [one_div_one] using hInv
  have hProduct := hamiltonian_product_unit_interval n.primeFactors (fun p => 1 - u p)
    (fun p hp => And.intro (sub_nonneg.mpr (hU p hp).2)
      (by linarith only [(hU p hp).1]))
  have hLower := (Finset.prod_one_sub_linear_error_bounds n.primeFactors u hU).1
  have hBudget := hamiltonian_odd_prime_reciprocal_budget n j hOdd hj
  change 0 <= 1 - n.primeFactors.prod (fun p => 1 - u p) /\
    1 - n.primeFactors.prod (fun p => 1 - u p) <= 2 * (1 / 4 : Real) ^ j
  refine And.intro (sub_nonneg.mpr hProduct.2) ?_
  have hDeficit : 1 - n.primeFactors.prod (fun p => 1 - u p) <= n.primeFactors.sum u := by
    linarith only [hLower]
  exact hDeficit.trans hBudget

theorem hamiltonian_coprime_log_coefficient_bounds (n j : Nat) [NeZero n]
    (hOdd : Odd n) (hj : 0 < j) :
    0 <= hamiltonianCoprimeLogCoefficient n j /\
      hamiltonianCoprimeLogCoefficient n j <= (2 / 3 : Real) * (1 / 4 : Real) ^ j := by
  have hZero : Not (j = 0) := ne_of_gt hj
  have hData := hamiltonian_coprime_euler_deficit_bounds n j hOdd hj
  have hDen3 : (3 : Real) <= ((2 * j + 1 : Nat) : Real) := by
    exact_mod_cast (show 3 <= 2 * j + 1 by omega)
  have hDen : 0 < ((2 * j + 1 : Nat) : Real) := lt_of_lt_of_le (by norm_num) hDen3
  rw [hamiltonianCoprimeLogCoefficient, if_neg hZero]
  refine And.intro (div_nonneg hData.1 hDen.le) ?_
  calc
    _ <= (2 * (1 / 4 : Real) ^ j) / ((2 * j + 1 : Nat) : Real) :=
      div_le_div_of_nonneg_right hData.2 hDen.le
    _ <= (2 * (1 / 4 : Real) ^ j) / 3 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hDen3
    _ = _ := by ring

end PrimeFactorOscillations
