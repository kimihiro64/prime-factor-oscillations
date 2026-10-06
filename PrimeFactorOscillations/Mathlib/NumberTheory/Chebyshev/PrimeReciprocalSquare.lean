/-
Copyright (c) 2025 Alastair Irving. All rights reserved.
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alastair Irving, Terry Tao, Ruben Van de Velde,
  Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.Chebyshev.PrimeReciprocal

/-!
# Reciprocal-square primes and the theta integral

An inverse-square specialization of the existing finite Abel summation
argument. The inclusive prime cutoff and lower integration endpoint two
are exact. This identity will be used to obtain the quadratic Euler tail
from PNT; it contains no asymptotic or RH assumption.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open MeasureTheory
namespace Chebyshev

private theorem hasDerivAt_inv_sq_mul_log_kernel {t : Real} (ht : 1 < t) :
    HasDerivAt (fun u : Real => 1 / (u ^ 2 * Real.log u))
      (-(1 + 2 * Real.log t) / (t ^ 3 * Real.log t ^ 2)) t := by
  have ht0 : Not (t = 0) := (lt_trans Real.zero_lt_one ht).ne'
  have hl0 : Not (Real.log t = 0) := (Real.log_pos ht).ne'
  have hd := (((hasDerivAt_id t).pow 2).mul (Real.hasDerivAt_log ht0)).inv
    (mul_ne_zero (pow_ne_zero 2 ht0) hl0)
  convert hd using 1
  . simp only [one_div]
    rfl
  . norm_num
    field_simp
    ring

theorem sum_prime_reciprocal_sq_eq_theta_div_add_integral
    {x : Real} (hx : 2 <= x) :
    ((Finset.Icc 0 (Nat.floor x)).filter Nat.Prime).sum
        (fun p => 1 / (p : Real) ^ 2) =
      theta x / (x ^ 2 * Real.log x) +
        intervalIntegral (fun t : Real =>
          theta t * (1 + 2 * Real.log t) / (t ^ 3 * Real.log t ^ 2)) 2 x volume := by
  classical
  let c : Nat -> Real := fun n => if Nat.Prime n then Real.log n else 0
  have htheta (t : Real) :
      (Finset.Icc 0 (Nat.floor t)).sum c = theta t := by
    simp only [c, theta_eq_sum_Icc, Finset.sum_filter]
  have hderivInt :
      IntegrableOn (deriv (fun t : Real => 1 / (t ^ 2 * Real.log t))) (Set.Icc 2 x) := by
    have hcont : ContinuousOn
        (fun t : Real => -(1 + 2 * Real.log t) / (t ^ 3 * Real.log t ^ 2))
        (Set.Icc 2 x) := by
      intro t ht
      have ht0 : Not (t = 0) := by linarith [ht.1]
      have hl0 : Not (Real.log t = 0) := (Real.log_pos (by linarith [ht.1])).ne'
      have hden : Not (t ^ 3 * Real.log t ^ 2 = 0) :=
        mul_ne_zero (pow_ne_zero 3 ht0) (pow_ne_zero 2 hl0)
      exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption))
    apply IntegrableOn.congr_fun hcont.integrableOn_Icc
      (fun t ht => (hasDerivAt_inv_sq_mul_log_kernel (by linarith [ht.1])).deriv.symm)
      measurableSet_Icc
  have hAbel :
      (Finset.Icc 0 (Nat.floor x)).sum
          (fun n => (1 / ((n : Real) ^ 2 * Real.log n)) * c n) =
        (1 / (x ^ 2 * Real.log x)) * (Finset.Icc 0 (Nat.floor x)).sum c -
          integral (volume.restrict (Set.Ioc 2 x))
            (fun t : Real =>
              deriv (fun u : Real => 1 / (u ^ 2 * Real.log u)) t *
                (Finset.Icc 0 (Nat.floor t)).sum c) := by
    run_tac
      let declaration := Lean.Name.mkSimple
        ("sum_mul_eq_sub_integral_mul" ++ String.singleton (Char.ofNat 8321))
      let coefficient := Lean.mkIdent (Lean.Name.mkSimple "c")
      let endpoint := Lean.mkIdent (Lean.Name.mkSimple "x")
      let proofSyntax <- `(tactic|
        refine ($(Lean.mkIdent declaration) $coefficient
          (f := fun t : Real => 1 / (t ^ 2 * Real.log t)) ?_ ?_ $endpoint ?_ ?_))
      Lean.Elab.Tactic.evalTactic proofSyntax
    . simp [c]
    . simp [c]
    . intro t ht
      exact (hasDerivAt_inv_sq_mul_log_kernel (by linarith [ht.1])).differentiableAt
    . exact hderivInt
  simp only [htheta] at hAbel
  have hIntegral :
      integral (volume.restrict (Set.Ioc 2 x))
          (fun t : Real => deriv (fun u : Real => 1 / (u ^ 2 * Real.log u)) t * theta t) =
        -intervalIntegral (fun t : Real =>
          theta t * (1 + 2 * Real.log t) / (t ^ 3 * Real.log t ^ 2)) 2 x volume := by
    rw [<- intervalIntegral.integral_of_le hx, <- intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht1 : 1 < t := by
      rw [Set.uIcc_of_le hx] at ht
      linarith [ht.1]
    dsimp only
    rw [(hasDerivAt_inv_sq_mul_log_kernel ht1).deriv]
    ring
  calc
    _ = (Finset.Icc 0 (Nat.floor x)).sum
        (fun n => (1 / ((n : Real) ^ 2 * Real.log n)) * c n) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hp : Nat.Prime n
      . have hn0 : Not ((n : Real) = 0) := Nat.cast_ne_zero.mpr hp.ne_zero
        have hl0 : Not (Real.log (n : Real) = 0) :=
          (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
        simp only [c, hp, ite_true]
        field_simp
      . simp [c, hp]
    _ = _ := by
      rw [hAbel, hIntegral]
      ring

end Chebyshev

