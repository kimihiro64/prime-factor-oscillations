/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Actual inverse-Gamma averages and their signed moments

These are Lebesgue integrals with the normalized Euler--Gamma density.
The raw inverse moments and their integrability are proved, not assumed.
The finite polynomial identity retains every binomial sign and is the input
to central truncation and Taylor averaging in the permanent expansion.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

def gammaHalfLine : MeasureTheory.Measure Real :=
  MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi (0 : Real))

def gammaInverseAverage (n : Nat) (f : Real -> Real) : Real :=
  (Inv.inv (n.factorial : Real)) *
    MeasureTheory.integral gammaHalfLine
      (fun t => Real.exp (-t) * t ^ n * f ((n : Real) / t))

theorem gammaKernel_integrable (n : Nat) :
    MeasureTheory.Integrable (fun t : Real => Real.exp (-t) * t ^ n) gammaHalfLine := by
  have hPos : 0 < (n : Real) + 1 :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one
  simpa only [gammaHalfLine, MeasureTheory.IntegrableOn, add_sub_cancel_right,
    Real.rpow_natCast] using Real.GammaIntegral_convergent hPos

theorem gammaKernel_integral (n : Nat) :
    MeasureTheory.integral gammaHalfLine
      (fun t : Real => Real.exp (-t) * t ^ n) = (n.factorial : Real) := by
  have hPos : 0 < (n : Real) + 1 :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one
  simpa only [gammaHalfLine, add_sub_cancel_right, Real.rpow_natCast,
    Real.Gamma_nat_eq_factorial] using (Real.Gamma_eq_integral hPos).symm

theorem gammaInverseIntegrand_eq (n j : Nat) (hj : j <= n) (t : Real) (ht : 0 < t) :
    Real.exp (-t) * t ^ n * ((n : Real) / t) ^ j =
      (n : Real) ^ j * (Real.exp (-t) * t ^ (n - j)) := by
  have hPow : t ^ n = t ^ (n - j) * t ^ j := by
    rw [<- pow_add, Nat.sub_add_cancel hj]
  rw [div_pow, hPow]
  field_simp [ne_of_gt ht]

theorem gammaInversePower_integrable (n j : Nat) (hj : j <= n) :
    MeasureTheory.Integrable
      (fun t : Real => Real.exp (-t) * t ^ n * ((n : Real) / t) ^ j)
      gammaHalfLine := by
  have hInt := (gammaKernel_integrable (n - j)).const_mul ((n : Real) ^ j)
  apply hInt.congr
  exact (MeasureTheory.ae_restrict_mem measurableSet_Ioi).mono
    (fun t ht => (gammaInverseIntegrand_eq n j hj t ht).symm)

theorem gammaInverseAverage_pow (n j : Nat) (hj : j <= n) :
    gammaInverseAverage n (fun s => s ^ j) =
      (n : Real) ^ j * ((n - j).factorial : Real) / (n.factorial : Real) := by
  have hIntegral :
      MeasureTheory.integral gammaHalfLine
        (fun t : Real => Real.exp (-t) * t ^ n * ((n : Real) / t) ^ j) =
        (n : Real) ^ j * ((n - j).factorial : Real) := by
    calc
      _ = MeasureTheory.integral gammaHalfLine
          (fun t : Real => (n : Real) ^ j * (Real.exp (-t) * t ^ (n - j))) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        exact gammaInverseIntegrand_eq n j hj t ht
      _ = _ := by
        rw [MeasureTheory.integral_const_mul, gammaKernel_integral]
  unfold gammaInverseAverage
  rw [hIntegral]
  ring

theorem gammaInverseAverage_pow_zero (n : Nat) :
    gammaInverseAverage n (fun s => s ^ 0) = 1 := by
  rw [gammaInverseAverage_pow n 0 (Nat.zero_le n)]
  have hFact : Not ((n.factorial : Real) = 0) :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  simp [hFact]

theorem gammaInverseAverage_pow_one (n : Nat) (hn : 1 <= n) :
    gammaInverseAverage n (fun s => s ^ 1) = 1 := by
  have hNat : n.factorial = n * (n - 1).factorial := by
    calc
      _ = ((n - 1) + 1).factorial :=
        congrArg Nat.factorial (Nat.sub_add_cancel hn).symm
      _ = ((n - 1) + 1) * (n - 1).factorial := Nat.factorial_succ (n - 1)
      _ = n * (n - 1).factorial := by rw [Nat.sub_add_cancel hn]
  have hFact : (n.factorial : Real) = (n : Real) * ((n - 1).factorial : Real) := by
    exact_mod_cast hNat
  have hNonzero : Not ((n.factorial : Real) = 0) :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [gammaInverseAverage_pow n 1 hn, pow_one, <- hFact, div_self hNonzero]

theorem gammaInverseAverage_finsetPolynomial (n : Nat) (S : Finset Nat)
    (c : Nat -> Real) (hDegree : forall j, Membership.mem S j -> j <= n) :
    gammaInverseAverage n (fun s => Finset.sum S (fun j => c j * s ^ j)) =
      Finset.sum S (fun j => c j * gammaInverseAverage n (fun s => s ^ j)) := by
  have hFun :
      (fun t : Real => Real.exp (-t) * t ^ n *
        Finset.sum S (fun j => c j * ((n : Real) / t) ^ j)) =
      (fun t : Real => Finset.sum S
        (fun j => c j * (Real.exp (-t) * t ^ n * ((n : Real) / t) ^ j))) := by
    funext t
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hTerm : forall j, Membership.mem S j ->
      MeasureTheory.Integrable
        (fun t : Real => c j * (Real.exp (-t) * t ^ n * ((n : Real) / t) ^ j))
        gammaHalfLine := by
    intro j hj
    exact (gammaInversePower_integrable n j (hDegree j hj)).const_mul (c j)
  unfold gammaInverseAverage
  rw [hFun, MeasureTheory.integral_finsetSum S (fun j hj => hTerm j hj),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [MeasureTheory.integral_const_mul]
  ring

theorem gammaInverseAverage_centered_binomial (n k : Nat) (hk : k <= n) :
    gammaInverseAverage n (fun s => (s - 1) ^ k) =
      Finset.sum (Finset.range (k + 1)) (fun j =>
        ((Nat.choose k j : Nat) : Real) * (-1 : Real) ^ (k - j) *
          ((n : Real) ^ j * ((n - j).factorial : Real) / (n.factorial : Real))) := by
  have hDegree : forall j, Membership.mem (Finset.range (k + 1)) j -> j <= n := by
    intro j hj
    exact le_trans (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hk
  have hFun : (fun s : Real => (s - 1) ^ k) =
      (fun s : Real => Finset.sum (Finset.range (k + 1)) (fun j =>
        (((Nat.choose k j : Nat) : Real) * (-1 : Real) ^ (k - j)) * s ^ j)) := by
    funext s
    rw [sub_eq_add_neg, add_pow]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hFun, gammaInverseAverage_finsetPolynomial n (Finset.range (k + 1))
    (fun j => ((Nat.choose k j : Nat) : Real) * (-1 : Real) ^ (k - j)) hDegree]
  apply Finset.sum_congr rfl
  intro j hj
  rw [gammaInverseAverage_pow n j (hDegree j hj)]

theorem gammaInverseAverage_centered_first (n : Nat) (hn : 1 <= n) :
    gammaInverseAverage n (fun s => s - 1) = 0 := by
  have hMean := gammaInverseAverage_pow_one n hn
  have hMass := gammaInverseAverage_pow_zero n
  have hFun :
      (fun t : Real => Real.exp (-t) * t ^ n * ((n : Real) / t - 1)) =
      (fun t : Real =>
        Real.exp (-t) * t ^ n * ((n : Real) / t) ^ 1 -
          Real.exp (-t) * t ^ n * ((n : Real) / t) ^ 0) := by
    funext t
    simp only [pow_one, pow_zero, mul_one]
    ring
  unfold gammaInverseAverage at hMean hMass
  unfold gammaInverseAverage
  rw [hFun, MeasureTheory.integral_sub (gammaInversePower_integrable n 1 hn)
    (gammaInversePower_integrable n 0 (Nat.zero_le n))]
  nlinarith only [hMean, hMass]

end PrimeFactorOscillations
