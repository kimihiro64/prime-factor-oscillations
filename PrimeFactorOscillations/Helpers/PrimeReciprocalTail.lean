/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Helpers.ThetaErrorIntegrability
import PrimeFactorOscillations.Mathlib.NumberTheory.Chebyshev.PrimeReciprocal
import VendorPrimeNumberTheoremAnd.Mertens

/-!
# Reciprocal primes and the canonical Mertens theta-error tail

The finite Abel identity, the proved absolute theta-error tail integrability,
and the existing cached Mertens second theorem identify the integration
constant exactly. No second Mertens definition or unproved Rosser input is used.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

open Filter MeasureTheory Real
open scoped Topology

namespace PrimeFactorOscillations

private theorem primeFilter_Icc_eq_Ioc (N : Nat) :
    (Finset.Icc 0 N).filter Nat.Prime = (Finset.Ioc 0 N).filter Nat.Prime := by
  apply Finset.ext
  intro p
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  constructor
  . intro hp
    exact And.intro (And.intro hp.2.pos hp.1.2) hp.2
  . intro hp
    exact And.intro (And.intro (Nat.zero_le p) hp.1.2) hp.2

private theorem integral_nicolas_main_kernel {x : Real} (hx : 2 <= x) :
    intervalIntegral (fun t : Real =>
        t * (1 + log t) / (t ^ 2 * log t ^ 2)) 2 x volume =
      (log (log x) - 1 / log x) - (log (log 2) - 1 / log 2) := by
  have hi : IntervalIntegrable (fun t : Real =>
      t * (1 + log t) / (t ^ 2 * log t ^ 2)) volume 2 x := by
    apply ContinuousOn.intervalIntegrable_of_Icc hx
    intro t ht
    have ht0 : Not (t = 0) := by linarith [ht.1]
    have hl0 : Not (log t = 0) := (log_pos (by linarith [ht.1])).ne'
    have hden : Not (t ^ 2 * log t ^ 2 = 0) :=
      mul_ne_zero (pow_ne_zero 2 ht0) (pow_ne_zero 2 hl0)
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption))
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : Real => log (log t) - 1 / log t) ?_ hi
  intro t ht
  rw [Set.uIcc_of_le hx] at ht
  have ht0 : Not (t = 0) := by linarith [ht.1]
  have hl0 : Not (log t = 0) := (log_pos (by linarith [ht.1])).ne'
  have hd := ((hasDerivAt_log hl0).comp t (hasDerivAt_log ht0)).sub
    ((hasDerivAt_log ht0).inv hl0)
  convert hd using 1
  . simp only [one_div, Function.comp_def]
    rfl
  . field_simp
    ring

private theorem primeReciprocal_sub_logLog_eq_finite_thetaError
    {x : Real} (hx : 2 <= x) :
    ((Finset.Ioc 0 (Nat.floor x)).filter Nat.Prime).sum
        (fun p => 1 / (p : Real)) - log (log x) =
      (1 / log 2 - log (log 2)) +
        (Chebyshev.theta x - x) / (x * log x) +
        intervalIntegral (fun t : Real =>
          (Chebyshev.theta t - t) * (1 + log t) / (t ^ 2 * log t ^ 2))
          2 x volume := by
  have herror : IntervalIntegrable (fun t : Real =>
      (Chebyshev.theta t - t) * (1 + log t) / (t ^ 2 * log t ^ 2))
      volume 2 x :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).mpr
      (integrableOn_thetaError_nicolasKernel.mono_set Set.Ioc_subset_Ioi_self)
  have hmain : IntervalIntegrable (fun t : Real =>
      t * (1 + log t) / (t ^ 2 * log t ^ 2)) volume 2 x := by
    apply ContinuousOn.intervalIntegrable_of_Icc hx
    intro t ht
    have ht0 : Not (t = 0) := by linarith [ht.1]
    have hl0 : Not (log t = 0) := (log_pos (by linarith [ht.1])).ne'
    have hden : Not (t ^ 2 * log t ^ 2 = 0) :=
      mul_ne_zero (pow_ne_zero 2 ht0) (pow_ne_zero 2 hl0)
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption))
  have hsplit :
      intervalIntegral (fun t : Real =>
          Chebyshev.theta t * (1 + log t) / (t ^ 2 * log t ^ 2)) 2 x volume =
        intervalIntegral (fun t : Real =>
          (Chebyshev.theta t - t) * (1 + log t) / (t ^ 2 * log t ^ 2)) 2 x volume +
        intervalIntegral (fun t : Real =>
          t * (1 + log t) / (t ^ 2 * log t ^ 2)) 2 x volume := by
    rw [<- intervalIntegral.integral_add herror hmain]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    ring
  have hAbel := Chebyshev.sum_prime_reciprocal_eq_theta_div_add_integral hx
  rw [primeFilter_Icc_eq_Ioc, hsplit, integral_nicolas_main_kernel hx] at hAbel
  rw [hAbel]
  have hx0 : Not (x = 0) := by linarith
  have hl0 : Not (log x = 0) := (log_pos (by linarith)).ne'
  have hTwo : Not (log (2 : Real) = 0) := (log_pos (by norm_num)).ne'
  field_simp
  ring

theorem tendsto_thetaError_div_mul_log :
    Tendsto (fun x : Real => (Chebyshev.theta x - x) / (x * log x))
      atTop (nhds 0) := by
  refine Exists.elim exists_thetaError_bound_div_log_sq ?_
  intro C hC
  apply squeeze_zero_norm'
    (a := fun x : Real => C / log x ^ 3) ?_
    (((tendsto_pow_atTop (by norm_num : Not ((3 : Nat) = 0))).comp
      tendsto_log_atTop).const_div_atTop C)
  filter_upwards [eventually_ge_atTop (2 : Real)] with x hx
  have hx0 : 0 < x := by linarith
  have hl : 0 < log x := log_pos (by linarith)
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hx0, abs_of_pos hl]
  calc
    abs (Chebyshev.theta x - x) / (x * log x)
        <= (C * x / log x ^ 2) / (x * log x) :=
      div_le_div_of_nonneg_right (hC.2 x hx) (by positivity)
    _ = C / log x ^ 3 := by
      field_simp

private theorem primeReciprocal_mertens_error_isLittleO :
    Asymptotics.IsLittleO atTop
      (fun x : Real =>
        ((Finset.Ioc 0 (Nat.floor x)).filter Nat.Prime).sum
          (fun p => 1 / (p : Real)) - log (log x) - Mertens.M)
      (fun _ : Real => (1 : Real)) := by
  run_tac
    let declaration := Lean.Name.str
      (Lean.Name.str (Lean.Name.mkSimple "Mertens")
        ("E" ++ String.singleton (Char.ofNat 8322) ++ "p")) "bound'"
    let proofSyntax <- `(tactic| exact $(Lean.mkIdent declaration))
    Lean.Elab.Tactic.evalTactic proofSyntax

theorem tendsto_primeReciprocal_sub_logLog :
    Tendsto (fun x : Real =>
      ((Finset.Ioc 0 (Nat.floor x)).filter Nat.Prime).sum
        (fun p => 1 / (p : Real)) - log (log x))
      atTop (nhds Mertens.M) := by
  have h := ((Asymptotics.isLittleO_one_iff Real).mp
    primeReciprocal_mertens_error_isLittleO).add_const Mertens.M
  simpa only [sub_add_cancel, zero_add] using h

theorem mertensConstant_eq_thetaError_integral :
    Mertens.M = (1 / log 2 - log (log 2)) +
      integral (volume.restrict (Set.Ioi 2)) (fun t : Real =>
        (Chebyshev.theta t - t) * (1 + log t) / (t ^ 2 * log t ^ 2)) := by
  have hi : Tendsto
      (fun x : Real => intervalIntegral (fun t : Real =>
        (Chebyshev.theta t - t) * (1 + log t) / (t ^ 2 * log t ^ 2)) 2 x volume)
      atTop (nhds (integral (volume.restrict (Set.Ioi 2)) (fun t : Real =>
        (Chebyshev.theta t - t) * (1 + log t) / (t ^ 2 * log t ^ 2)))) := by
    exact intervalIntegral_tendsto_integral_Ioi 2
      integrableOn_thetaError_nicolasKernel tendsto_id
  have hconst : Tendsto
      (fun _ : Real => (1 / log 2 - log (log 2) : Real))
      atTop (nhds (1 / log 2 - log (log 2))) := tendsto_const_nhds
  have hlimit := (hconst.add tendsto_thetaError_div_mul_log).add hi
  have htransport : Tendsto
      (fun x : Real => ((Finset.Ioc 0 (Nat.floor x)).filter Nat.Prime).sum
        (fun p => 1 / (p : Real)) - log (log x))
      atTop (nhds ((1 / log 2 - log (log 2)) +
        integral (volume.restrict (Set.Ioi 2)) (fun t : Real =>
          (Chebyshev.theta t - t) * (1 + log t) / (t ^ 2 * log t ^ 2)))) := by
    apply (show Tendsto
      (fun x : Real => (1 / log 2 - log (log 2)) +
        (Chebyshev.theta x - x) / (x * log x) +
        intervalIntegral (fun t : Real =>
          (Chebyshev.theta t - t) * (1 + log t) / (t ^ 2 * log t ^ 2)) 2 x volume)
      atTop _ from by simpa only [add_zero] using hlimit).congr'
    filter_upwards [eventually_ge_atTop (2 : Real)] with x hx
    exact (primeReciprocal_sub_logLog_eq_finite_thetaError hx).symm
  exact tendsto_nhds_unique tendsto_primeReciprocal_sub_logLog htransport

theorem primeReciprocal_eq_mertens_thetaError_tail {x : Real} (hx : 2 <= x) :
    (Nat.primesLE (Nat.floor x)).sum (fun p => 1 / (p : Real)) =
      log (log x) + Mertens.M +
        (Chebyshev.theta x - x) / (x * log x) -
        integral (volume.restrict (Set.Ioi x)) (fun t : Real =>
          (Chebyshev.theta t - t) * (1 + log t) / (t ^ 2 * log t ^ 2)) := by
  have htail : IntegrableOn (fun t : Real =>
      (Chebyshev.theta t - t) * (1 + log t) / (t ^ 2 * log t ^ 2))
      (Set.Ioi x) :=
    integrableOn_thetaError_nicolasKernel.mono_set (Set.Ioi_subset_Ioi hx)
  have hsplit :
      intervalIntegral (fun t : Real =>
        (Chebyshev.theta t - t) * (1 + log t) / (t ^ 2 * log t ^ 2)) 2 x volume +
      integral (volume.restrict (Set.Ioi x)) (fun t : Real =>
        (Chebyshev.theta t - t) * (1 + log t) / (t ^ 2 * log t ^ 2)) =
      integral (volume.restrict (Set.Ioi 2)) (fun t : Real =>
        (Chebyshev.theta t - t) * (1 + log t) / (t ^ 2 * log t ^ 2)) := by
    rw [intervalIntegral.integral_of_le hx, <- setIntegral_union
      Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      (integrableOn_thetaError_nicolasKernel.mono_set Set.Ioc_subset_Ioi_self)
      htail, Set.Ioc_union_Ioi_eq_Ioi hx]
  rw [Nat.primesLE_eq_filter_Icc_zero, primeFilter_Icc_eq_Ioc]
  have hfinite := primeReciprocal_sub_logLog_eq_finite_thetaError hx
  rw [mertensConstant_eq_thetaError_integral]
  linarith

end PrimeFactorOscillations
