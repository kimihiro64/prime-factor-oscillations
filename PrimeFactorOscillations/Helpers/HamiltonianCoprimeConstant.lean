/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCoprimeDeterminant
import PrimeFactorOscillations.Helpers.HamiltonianSymmetricDeterminantRatio

/-! # The positive arithmetic constant in the odd coprime count

The actual determinant quotient is identified with the full divisor
product, using positive real powers. Positivity is proved on every
supported divisor before division or square roots are used.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianCoprimeArithmeticRatio (t : Nat) : Real :=
  if t = 1 then 1 else
    ((t.totient : Real) - (ArithmeticFunction.moebius t : Real)) /
      ((t.totient : Real) + (ArithmeticFunction.moebius t : Real))

def hamiltonianCoprimeArithmeticConstant (n : Nat) : Real :=
  n.divisors.prod (fun t =>
    hamiltonianCoprimeArithmeticRatio t ^ ((t.totient : Real) / 2))

variable {n : Nat} [NeZero n]

theorem hamiltonian_coprime_odd_divisor_signs (hOdd : Odd n) (t : Nat)
    (ht : Membership.mem n.divisors t) (hNotOne : Not (t = 1)) :
    0 < (t.totient : Real) - (ArithmeticFunction.moebius t : Real) /\
    0 < (t.totient : Real) + (ArithmeticFunction.moebius t : Real) /\
    0 < (t.totient : Real) := by
  have hDiv := (Nat.mem_divisors.mp ht).1
  have htPos : 0 < t := Nat.pos_of_dvd_of_pos hDiv (NeZero.pos n)
  have hNotTwo : Not (t = 2) := by
    intro hTwo
    rw [hTwo] at hDiv
    choose k hk using hDiv
    have hEven : Even n := Exists.intro k (by omega)
    exact (Nat.not_even_iff_odd.mpr hOdd) hEven
  have hPhiPos := Nat.totient_pos.mpr htPos
  have hPhi : 2 <= t.totient := by
    by_contra h
    have hOne : t.totient = 1 := by omega
    have hCases := Nat.totient_eq_one_iff.mp hOne
    omega
  have hPhiR : (2 : Real) <= (t.totient : Real) := by exact_mod_cast hPhi
  have hMu : abs (ArithmeticFunction.moebius t : Real) <= 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := t)
  have hMuRange := abs_le.mp hMu
  refine And.intro ?_ (And.intro ?_ ?_) <;> linarith only [hPhiR, hMuRange.1, hMuRange.2]

theorem hamiltonian_coprime_odd_arithmetic_ratio_positive (hOdd : Odd n) (t : Nat)
    (ht : Membership.mem n.divisors t) :
    0 < hamiltonianCoprimeArithmeticRatio t := by
  by_cases hOne : t = 1
  case pos => simp [hamiltonianCoprimeArithmeticRatio, hOne]
  case neg =>
    have hSigns := hamiltonian_coprime_odd_divisor_signs hOdd t ht hOne
    exact (show 0 < hamiltonianCoprimeArithmeticRatio t from by
      rw [hamiltonianCoprimeArithmeticRatio, if_neg hOne]
      exact div_pos hSigns.1 hSigns.2.1)

theorem hamiltonian_coprime_odd_factor_ratio (hOdd : Odd n) (t : Nat)
    (ht : Membership.mem n.divisors t) :
    hamiltonianCoprimeDeterminantFactor 1 t /
        hamiltonianCoprimeDeterminantFactor (-1) t =
      hamiltonianCoprimeArithmeticRatio t := by
  by_cases hOne : t = 1
  case pos => simp [hamiltonianCoprimeDeterminantFactor, hamiltonianCoprimeArithmeticRatio, hOne]
  case neg =>
    have hSigns := hamiltonian_coprime_odd_divisor_signs hOdd t ht hOne
    have hPhi : Not ((t.totient : Real) = 0) := ne_of_gt hSigns.2.2
    have hPlus : Not ((t.totient : Real) + (ArithmeticFunction.moebius t : Real) = 0) :=
      ne_of_gt hSigns.2.1
    simp only [hamiltonianCoprimeDeterminantFactor, hamiltonianCoprimeArithmeticRatio,
      hOne, ite_false, one_mul, neg_one_mul, sub_neg_eq_add]
    field_simp
    <;> ring

theorem hamiltonian_coprime_odd_constant_positive (hOdd : Odd n) :
    0 < hamiltonianCoprimeArithmeticConstant n := by
  apply Finset.prod_pos
  intro t ht
  exact Real.rpow_pos_of_pos (hamiltonian_coprime_odd_arithmetic_ratio_positive hOdd t ht) _

theorem hamiltonian_positive_rpow_half_square (x : Real) (hx : 0 < x) (m : Nat) :
    (x ^ ((m : Real) / 2)) ^ 2 = x ^ m := by
  have hNat : x ^ m = Real.exp (Real.log x * (m : Real)) := by
    rw [<- Real.rpow_natCast x m, Real.rpow_def_of_pos hx]
  rw [Real.rpow_def_of_pos hx, pow_two, <- Real.exp_add, hNat]
  congr 1
  ring

theorem hamiltonian_coprime_odd_constant_square (hOdd : Odd n) :
    (hamiltonianCoprimeArithmeticConstant n) ^ 2 =
      Matrix.det ((1 : Matrix (ZMod n) (ZMod n) Real) -
        centeredKernel (hamiltonianCoprimeKernel (n := n)) (1 / (n : Real))) /
      Matrix.det ((1 : Matrix (ZMod n) (ZMod n) Real) +
        centeredKernel (hamiltonianCoprimeKernel (n := n)) (1 / (n : Real))) := by
  have hMinus := hamiltonian_coprime_determinant_divisor_product (n := n) 1
  have hPlus := hamiltonian_coprime_determinant_divisor_product (n := n) (-1)
  simp only [one_smul] at hMinus
  simp only [neg_one_smul, sub_neg_eq_add] at hPlus
  rw [hMinus, hPlus, <- Finset.prod_div_distrib]
  calc
    _ = n.divisors.prod (fun t => hamiltonianCoprimeArithmeticRatio t ^ t.totient) := by
      unfold hamiltonianCoprimeArithmeticConstant
      rw [<- Finset.prod_pow]
      apply Finset.prod_congr rfl
      intro t ht
      exact hamiltonian_positive_rpow_half_square _
        (hamiltonian_coprime_odd_arithmetic_ratio_positive hOdd t ht) _
    _ = _ := by
      apply Finset.prod_congr rfl
      intro t ht
      rw [<- div_pow, hamiltonian_coprime_odd_factor_ratio hOdd t ht]

theorem hamiltonian_coprime_odd_constant_sqrt (hOdd : Odd n) :
    Real.sqrt
      (Matrix.det ((1 : Matrix (ZMod n) (ZMod n) Real) -
        centeredKernel (hamiltonianCoprimeKernel (n := n)) (1 / (n : Real))) /
      Matrix.det ((1 : Matrix (ZMod n) (ZMod n) Real) +
        centeredKernel (hamiltonianCoprimeKernel (n := n)) (1 / (n : Real)))) =
      hamiltonianCoprimeArithmeticConstant n := by
  rw [<- hamiltonian_coprime_odd_constant_square hOdd,
    Real.sqrt_sq_eq_abs, abs_of_pos (hamiltonian_coprime_odd_constant_positive hOdd)]

theorem hamiltonian_coprime_odd_gram_factor_constant (hOdd : Odd n) :
    Matrix.det ((1 : Matrix (ZMod n) (ZMod n) Real) -
        centeredKernel (hamiltonianCoprimeKernel (n := n)) (1 / (n : Real))) *
      realGramDeterminantFactor
        (centeredKernel (hamiltonianCoprimeKernel (n := n)) (1 / (n : Real))) 1 =
      hamiltonianCoprimeArithmeticConstant n := by
  have hSym :
      (centeredKernel (hamiltonianCoprimeKernel (n := n)) (1 / (n : Real))).transpose =
        centeredKernel (hamiltonianCoprimeKernel (n := n)) (1 / (n : Real)) := by
    unfold centeredKernel
    rw [Matrix.transpose_sub, hamiltonian_coprime_kernel_symmetric,
      averagingKernel_transpose]
  rw [hamiltonian_symmetric_gram_factor_quotient _ hSym (1 / 2) (by norm_num)
    (hamiltonian_coprime_odd_physical_gap hOdd), hamiltonian_coprime_odd_constant_sqrt hOdd]


theorem hamiltonian_coprime_odd_constant_divisor_product (hOdd : Odd n) :
    hamiltonianCoprimeArithmeticConstant n =
      (n.divisors.filter (fun t => 1 < t)).prod (fun t =>
        (((t.totient : Real) - (ArithmeticFunction.moebius t : Real)) /
          ((t.totient : Real) + (ArithmeticFunction.moebius t : Real))) ^
            ((t.totient : Real) / 2)) := by
  unfold hamiltonianCoprimeArithmeticConstant
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro t ht
  have htPos : 0 < t := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp ht).1 (NeZero.pos n)
  by_cases hHigh : 1 < t
  case pos =>
    have hNotOne : Not (t = 1) := by omega
    simp only [hHigh, ite_true, hamiltonianCoprimeArithmeticRatio, hNotOne, ite_false]
  case neg =>
    have hOne : t = 1 := by omega
    simp [hOne, hamiltonianCoprimeArithmeticRatio]

end PrimeFactorOscillations
