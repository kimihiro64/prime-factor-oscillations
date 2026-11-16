/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCoprimeUnorientedCount
import PrimeFactorOscillations.Helpers.HamiltonianStirlingNormalization

/-! # Final Stirling normalization of the actual odd coprime-circle count

The factorial reference is identified exactly with the displayed arithmetic
reference times its Stirling ratio. Both relative errors are retained.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianCoprimeOddStirlingReference (n : Nat) : Real :=
  hamiltonianCoprimeArithmeticConstant n * Real.sqrt (Real.pi / (2 * (n : Real))) *
    ((n.totient : Real) / Real.exp 1) ^ n

theorem hamiltonian_stirling_linear_relative (n : Nat) (hn : 1 <= n) :
    1 <= Stirling.stirlingSeq n / Real.sqrt Real.pi /\
      Stirling.stirlingSeq n / Real.sqrt Real.pi - 1 <= 1 / (3 * (n : Real)) := by
  have hPi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hLower := Stirling.sqrt_pi_le_stirlingSeq (by omega : Not (n = 0))
  have hs : 1 <= Stirling.stirlingSeq n / Real.sqrt Real.pi :=
    by
      have h := div_le_div_of_nonneg_right hLower hPi.le
      simpa only [div_self (ne_of_gt hPi)] using h
  have hSquare : (Stirling.stirlingSeq n / Real.sqrt Real.pi) ^ 2 =
      Stirling.stirlingSeq n ^ 2 / Real.pi := by
    rw [div_pow, Real.sq_sqrt Real.pi_pos.le]
  have hErr := hamiltonian_stirling_square_relative n hn
  have hUpper := (le_abs_self (Stirling.stirlingSeq n ^ 2 / Real.pi - 1)).trans hErr
  rw [<- hSquare] at hUpper
  exact And.intro hs (by nlinarith only [hs, hUpper])

theorem hamiltonian_stirling_ratio_upper (n : Nat) (hn : 1 <= n) :
    Stirling.stirlingSeq n / Real.sqrt Real.pi <= (4 / 3 : Real) := by
  have h := (hamiltonian_stirling_linear_relative n hn).2
  have hnR : (1 : Real) <= n := by exact_mod_cast hn
  have hInv : 1 / (3 * (n : Real)) <= (1 / 3 : Real) :=
    one_div_le_one_div_of_le (by norm_num) (by nlinarith only [hnR])
  linarith only [h, hInv]

theorem hamiltonian_coprime_odd_stirling_reference_identity (n : Nat) (hn : 1 <= n) :
    hamiltonianCoprimeUnorientedReference n =
      (Stirling.stirlingSeq n / Real.sqrt Real.pi) *
        hamiltonianCoprimeOddStirlingReference n := by
  have hnR : 0 < (n : Real) := Nat.cast_pos.mpr (by omega)
  have hPi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hSqrt : 0 < Real.sqrt (2 * (n : Real)) := Real.sqrt_pos.mpr (by positivity)
  have hSq : Real.sqrt (2 * (n : Real)) ^ 2 = 2 * (n : Real) :=
    Real.sq_sqrt (by positivity)
  have hFact : (n.factorial : Real) = (n : Real) * ((n - 1).factorial : Real) := by
    have h := Nat.factorial_succ (n - 1)
    have hnSub : n - 1 + 1 = n := by omega
    rw [hnSub] at h
    exact_mod_cast h
  unfold hamiltonianCoprimeUnorientedReference hamiltonianCoprimeOddStirlingReference
  rw [Stirling.stirlingSeq, Real.sqrt_div Real.pi_pos.le, div_pow, div_pow, hFact]
  field_simp [ne_of_gt hnR, ne_of_gt hPi, ne_of_gt hSqrt, ne_of_gt (Real.exp_pos 1)]
  rw [hSq]
  ring

theorem hamiltonian_reciprocal_le_tenth_power (n : Nat) (hn : 1 <= n) :
    1 / (n : Real) <= (n : Real) ^ (-(1 : Real) / 10) := by
  have hnR : (1 : Real) <= n := by exact_mod_cast hn
  have h := Real.rpow_le_rpow_of_exponent_le hnR
    (by norm_num : (-1 : Real) <= -(1 : Real) / 10)
  simpa only [Real.rpow_neg_one, one_div] using h

theorem hamiltonian_coprime_odd_stirling_count_uniform :
    exists N0 : Nat, 256 <= N0 /\
      forall (n : Nat) [NeZero n], N0 <= n -> Odd n ->
        0 < hamiltonianCoprimeOddStirlingReference n /\
        abs ((hamiltonianGraphUnorientedCount (hamiltonianCoprimeRelation (n := n)) : Real) /
          hamiltonianCoprimeOddStirlingReference n - 1) <=
            23 * (n : Real) ^ (-(1 : Real) / 10) := by
  choose N0 hN0 hCount using hamiltonian_coprime_odd_unoriented_count_uniform
  refine Exists.intro N0 (And.intro hN0 ?_)
  intro n inst hn hOdd
  have hn1 : 1 <= n := by omega
  have hRaw := hCount n hn hOdd
  let s := Stirling.stirlingSeq n / Real.sqrt Real.pi
  have hStirling := hamiltonian_stirling_linear_relative n hn1
  have hs : 1 <= s := hStirling.1
  have hsPos : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hsUpper : s <= (4 / 3 : Real) := hamiltonian_stirling_ratio_upper n hn1
  have hId : hamiltonianCoprimeUnorientedReference n =
      s * hamiltonianCoprimeOddStirlingReference n :=
    hamiltonian_coprime_odd_stirling_reference_identity n hn1
  have hRef : 0 < hamiltonianCoprimeOddStirlingReference n := by
    have h := hRaw.1
    rw [hId] at h
    exact (mul_pos_iff_of_pos_left hsPos).mp h
  refine And.intro hRef ?_
  let a := (hamiltonianGraphUnorientedCount (hamiltonianCoprimeRelation (n := n)) : Real) /
    hamiltonianCoprimeUnorientedReference n
  let t := (n : Real) ^ (-(1 : Real) / 10)
  have ht : 0 <= t := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hRatio :
      (hamiltonianGraphUnorientedCount (hamiltonianCoprimeRelation (n := n)) : Real) /
        hamiltonianCoprimeOddStirlingReference n = a * s := by
    dsimp only [a]
    rw [hId]
    field_simp [ne_of_gt hsPos, ne_of_gt hRef]
  rw [hRatio]
  have hA : abs (a - 1) <= 17 * t := hRaw.2
  have hS : abs (s - 1) <= 1 / (3 * (n : Real)) := by
    rw [abs_of_nonneg (sub_nonneg.mpr hs)]
    exact hStirling.2
  have hInv : 1 / (3 * (n : Real)) <= t / 3 := by
    have h := div_le_div_of_nonneg_right (hamiltonian_reciprocal_le_tenth_power n hn1)
      (by norm_num : (0 : Real) <= 3)
    convert h using 1 <;> ring
  calc
    abs (a * s - 1) = abs ((a - 1) * s + (s - 1)) := by congr 1; ring
    _ <= abs ((a - 1) * s) + abs (s - 1) := abs_add_le _ _
    _ = abs (a - 1) * s + abs (s - 1) := by
      rw [abs_mul, abs_of_nonneg hsPos.le]
    _ <= (17 * t) * s + 1 / (3 * (n : Real)) :=
      add_le_add (mul_le_mul_of_nonneg_right hA hsPos.le) hS
    _ <= (17 * t) * (4 / 3 : Real) + t / 3 :=
      add_le_add (mul_le_mul_of_nonneg_left hsUpper (by positivity)) hInv
    _ = 23 * t := by ring

end PrimeFactorOscillations
