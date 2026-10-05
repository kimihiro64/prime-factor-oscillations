/-
Copyright (c) 2025 Alastair Irving. All rights reserved.
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alastair Irving, Terry Tao, Ruben Van de Velde,
  Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Reciprocal primes and the theta integral

The proof specializes Mathlib's Abel summation theorem in the same way as
Chebyshev.primeCounting_eq_theta_div_log_add_integral, using the weight
1 / (t * log t). This is the finite part of Rosser--Schoenfeld equation
(4.19); no Rosser module, Mertens copy, or prime-distribution assumption
is imported. The endpoint 2 is retained.

Source: Mathlib commit 5ed2965256430c3649e86755f9576b54eca72435,
Chebyshev source blob 0c70e9d4de7e8d454df1a5840334ef3e0dcbf777.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

open MeasureTheory

namespace Chebyshev

private theorem hasDerivAt_inv_mul_log_kernel {t : Real} (ht : 1 < t) :
    HasDerivAt (fun u : Real => 1 / (u * Real.log u))
      (-(1 + Real.log t) / (t ^ 2 * Real.log t ^ 2)) t := by
  have ht0 : Not (t = 0) := (lt_trans Real.zero_lt_one ht).ne'
  have hl0 : Not (Real.log t = 0) := (Real.log_pos ht).ne'
  convert (Real.hasDerivAt_mul_log ht0).inv (mul_ne_zero ht0 hl0) using 1 <;>
    simp only [one_div, mul_pow, add_comm]
  rfl

theorem sum_prime_reciprocal_eq_theta_div_add_integral
    {x : Real} (hx : 2 <= x) :
    ((Finset.Icc 0 (Nat.floor x)).filter Nat.Prime).sum
        (fun p => 1 / (p : Real)) =
      theta x / (x * Real.log x) +
        intervalIntegral (fun t : Real =>
          theta t * (1 + Real.log t) / (t ^ 2 * Real.log t ^ 2)) 2 x volume := by
  classical
  let c : Nat -> Real := fun n => if Nat.Prime n then Real.log n else 0
  have htheta (t : Real) :
      (Finset.Icc 0 (Nat.floor t)).sum c = theta t := by
    simp only [c, theta_eq_sum_Icc, Finset.sum_filter]
  have hderivInt :
      IntegrableOn (deriv (fun t : Real => 1 / (t * Real.log t))) (Set.Icc 2 x) := by
    have hcont : ContinuousOn
        (fun t : Real => -(1 + Real.log t) / (t ^ 2 * Real.log t ^ 2))
        (Set.Icc 2 x) := by
      intro t ht
      have ht0 : Not (t = 0) := by linarith [ht.1]
      have hl0 : Not (Real.log t = 0) := (Real.log_pos (by linarith [ht.1])).ne'
      have hden : Not (t ^ 2 * Real.log t ^ 2 = 0) :=
        mul_ne_zero (pow_ne_zero 2 ht0) (pow_ne_zero 2 hl0)
      exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption))
    apply IntegrableOn.congr_fun hcont.integrableOn_Icc
      (fun t ht => (hasDerivAt_inv_mul_log_kernel (by linarith [ht.1])).deriv.symm)
      measurableSet_Icc
  have hAbel :
      (Finset.Icc 0 (Nat.floor x)).sum
          (fun n => (1 / ((n : Real) * Real.log n)) * c n) =
        (1 / (x * Real.log x)) * (Finset.Icc 0 (Nat.floor x)).sum c -
          integral (volume.restrict (Set.Ioc 2 x))
            (fun t : Real =>
              deriv (fun u : Real => 1 / (u * Real.log u)) t *
                (Finset.Icc 0 (Nat.floor t)).sum c) := by
    run_tac
      let declaration := Lean.Name.mkSimple
        ("sum_mul_eq_sub_integral_mul" ++ String.singleton (Char.ofNat 8321))
      let coefficient := Lean.mkIdent (Lean.Name.mkSimple "c")
      let endpoint := Lean.mkIdent (Lean.Name.mkSimple "x")
      let proofSyntax <- `(tactic|
        refine ($(Lean.mkIdent declaration) $coefficient
          (f := fun t : Real => 1 / (t * Real.log t)) ?_ ?_ $endpoint ?_ ?_))
      Lean.Elab.Tactic.evalTactic proofSyntax
    . simp [c]
    . simp [c]
    . intro t ht
      exact (hasDerivAt_inv_mul_log_kernel (by linarith [ht.1])).differentiableAt
    . exact hderivInt
  simp only [htheta] at hAbel
  have hIntegral :
      integral (volume.restrict (Set.Ioc 2 x))
          (fun t : Real => deriv (fun u : Real => 1 / (u * Real.log u)) t * theta t) =
        -intervalIntegral (fun t : Real =>
          theta t * (1 + Real.log t) / (t ^ 2 * Real.log t ^ 2)) 2 x volume := by
    rw [<- intervalIntegral.integral_of_le hx, <- intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht1 : 1 < t := by
      rw [Set.uIcc_of_le hx] at ht
      linarith [ht.1]
    dsimp only
    rw [(hasDerivAt_inv_mul_log_kernel ht1).deriv]
    ring
  calc
    _ = (Finset.Icc 0 (Nat.floor x)).sum
        (fun n => (1 / ((n : Real) * Real.log n)) * c n) := by
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
