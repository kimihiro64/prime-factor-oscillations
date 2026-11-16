/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCoprimeEvenCount
import PrimeFactorOscillations.Helpers.HamiltonianCoprimeStirlingCount

/-! # The full parity-dependent relative count through every modulus

The actual odd and even unoriented counts are combined under one absolute
threshold. The common rate retains the exact parity-dependent references.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_half_size_half_power_le_tenth (m : Nat) (hm : 1 <= m) :
    (m : Real) ^ (-1 / 2 : Real) <=
      2 * ((2 * m : Nat) : Real) ^ (-1 / 10 : Real) := by
  have hmR : (1 : Real) <= m := by exact_mod_cast hm
  have hBase : (1 : Real) <= 2 * (m : Real) := by linarith only [hmR]
  have hScale : (m : Real) ^ (-1 / 2 : Real) =
      (2 : Real) ^ (1 / 2 : Real) * (2 * (m : Real)) ^ (-1 / 2 : Real) := by
    rw [Real.mul_rpow (by norm_num : (0 : Real) <= 2) (Nat.cast_nonneg m),
      <- mul_assoc, <- Real.rpow_add (by norm_num : (0 : Real) < 2)]
    norm_num
  have hTwo : (2 : Real) ^ (1 / 2 : Real) <= 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) <= 2)
      (by norm_num : (1 / 2 : Real) <= 1)
    simpa only [Real.rpow_one] using h
  have hPower := Real.rpow_le_rpow_of_exponent_le hBase
    (by norm_num : (-1 / 2 : Real) <= -1 / 10)
  rw [Nat.cast_mul, Nat.cast_ofNat]
  calc
    _ = _ := hScale
    _ <= (2 : Real) ^ (1 / 2 : Real) * (2 * (m : Real)) ^ (-1 / 10 : Real) :=
      mul_le_mul_of_nonneg_left hPower (Real.rpow_nonneg (by norm_num) _)
    _ <= _ := mul_le_mul_of_nonneg_right hTwo (Real.rpow_nonneg (by positivity) _)

theorem hamiltonian_coprime_even_unoriented_count_uniform :
    exists N0 : Nat, 512 <= N0 /\
      forall (n : Nat) [NeZero n], N0 <= n -> Dvd.dvd 2 n ->
        0 < hamiltonianCoprimeEvenReference n /\
        abs ((hamiltonianGraphUnorientedCount (hamiltonianCoprimeRelation (n := n)) : Real) /
          hamiltonianCoprimeEvenReference n - 1) <=
            4 * (n : Real) ^ (-1 / 10 : Real) := by
  choose M0 hM0 hCount using hamiltonian_coprime_even_unoriented_half_size_count
  let N0 := 2 * M0
  refine Exists.intro N0 (And.intro (by dsimp only [N0]; omega) ?_)
  intro n inst hn hEven
  let m := n / 2
  have hSize : 2 * m = n := by
    dsimp only [m]
    simpa only [Nat.mul_comm] using Nat.div_mul_cancel hEven
  have hm : M0 <= m := by dsimp only [N0] at hn; omega
  have hm1 : 1 <= m := by omega
  letI : NeZero m := NeZero.mk (by omega)
  have hRaw := hCount m hm
  have hPower := mul_le_mul_of_nonneg_left (hamiltonian_half_size_half_power_le_tenth m hm1)
    (by norm_num : (0 : Real) <= 2)
  have hBound :
      abs ((hamiltonianGraphUnorientedCount (hamiltonianCoprimeRelation (n := 2 * m)) : Real) /
        hamiltonianCoprimeEvenReference (2 * m) - 1) <=
          4 * ((2 * m : Nat) : Real) ^ (-1 / 10 : Real) :=
    hRaw.2.trans (by linarith only [hPower])
  let P : Nat -> Prop := fun q => forall [NeZero q],
    0 < hamiltonianCoprimeEvenReference q /\
      abs ((hamiltonianGraphUnorientedCount (hamiltonianCoprimeRelation (n := q)) : Real) /
        hamiltonianCoprimeEvenReference q - 1) <=
          4 * (q : Real) ^ (-1 / 10 : Real)
  have hmP : P (2 * m) := by
    intro instQ
    exact And.intro hRaw.1 hBound
  have hnP : P n := @Eq.mp (P (2 * m)) (P n) (congrArg P hSize) (@hmP)
  exact hnP

def hamiltonianCoprimeRelativeReference (n : Nat) : Real :=
  if Odd n then hamiltonianCoprimeOddStirlingReference n else hamiltonianCoprimeEvenReference n

theorem hamiltonian_coprime_relative_count_uniform :
    exists N0 : Nat, 512 <= N0 /\
      forall (n : Nat) [NeZero n], N0 <= n ->
        0 < hamiltonianCoprimeRelativeReference n /\
        abs ((hamiltonianGraphUnorientedCount (hamiltonianCoprimeRelation (n := n)) : Real) /
          hamiltonianCoprimeRelativeReference n - 1) <=
            23 * (n : Real) ^ (-1 / 10 : Real) := by
  choose O hO hOddCount using hamiltonian_coprime_odd_stirling_count_uniform
  choose E hE hEvenCount using hamiltonian_coprime_even_unoriented_count_uniform
  let N0 := max O E
  refine Exists.intro N0 (And.intro (hE.trans (le_max_right _ _)) ?_)
  intro n inst hn
  have hnO : O <= n := (le_max_left _ _).trans hn
  have hnE : E <= n := (le_max_right _ _).trans hn
  by_cases hOdd : Odd n
  case pos =>
    simpa only [hamiltonianCoprimeRelativeReference, if_pos hOdd, neg_div] using
      hOddCount n hnO hOdd
  case neg =>
    have hEven : Even n := by
      apply Classical.byContradiction
      intro hNotEven
      exact hOdd (Nat.not_even_iff_odd.mp hNotEven)
    have hDiv : Dvd.dvd 2 n := Exists.intro hEven.choose (by
      have h := hEven.choose_spec
      omega)
    have hRaw := hEvenCount n hnE hDiv
    rw [hamiltonianCoprimeRelativeReference, if_neg hOdd]
    refine And.intro hRaw.1 (hRaw.2.trans ?_)
    have ht : 0 <= (n : Real) ^ (-1 / 10 : Real) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    linarith only [ht]

end PrimeFactorOscillations
