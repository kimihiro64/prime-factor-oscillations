/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import PrimeFactorOscillations.Helpers.PrimeClassSamplingProbability

/-!
# The entire Euler product for one summable prime class

The literal class supplies the factors 1+(z-1)/p. Summability proves uniform
convergence and entireness, including at factor zeros. The exact zero set
retains every prime label; finite prefixes converge to the same product.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open Filter

theorem classPowerWeight_one_le
    (P : Set Nat) (sigma : Real) (hs1 : sigma <= 1) (p : Nat) :
    classPowerWeight P 1 p <= classPowerWeight P sigma p := by
  classical
  unfold classPowerWeight
  split_ifs with hp
  case pos =>
    apply Real.rpow_le_rpow_of_exponent_le
    case hx => exact_mod_cast hp.1.one_lt.le
    case hyz => linarith
  case neg => exact le_refl 0

theorem classPowerWeight_one_summable
    (P : Set Nat) (sigma : Real) (hs1 : sigma <= 1)
    (hsum : Summable (classPowerWeight P sigma)) :
    Summable (classPowerWeight P 1) :=
  hsum.of_nonneg_of_le (classPowerWeight_nonneg P 1)
    (classPowerWeight_one_le P sigma hs1)

noncomputable def classEulerFactor (P : Set Nat) (p : Nat) (z : Complex) : Complex :=
  1 + (classPowerWeight P 1 p : Complex) * (z - 1)

noncomputable def classEulerProfile (P : Set Nat) (z : Complex) : Complex :=
  tprod (fun p : Nat => classEulerFactor P p z)

theorem norm_classEulerFactor_sub_one (P : Set Nat) (p : Nat) (z : Complex) :
    norm (classEulerFactor P p z - 1) =
      classPowerWeight P 1 p * norm (z - 1) := by
  simp only [classEulerFactor, add_sub_cancel_left, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (classPowerWeight_nonneg P 1 p)]

theorem summable_norm_classEulerFactor_sub_one
    (P : Set Nat) (hsum : Summable (classPowerWeight P 1)) (z : Complex) :
    Summable (fun p : Nat => norm (classEulerFactor P p z - 1)) := by
  simpa only [norm_classEulerFactor_sub_one] using hsum.mul_right (norm (z - 1))

theorem hasProdUniformlyOn_classEulerFactor
    (P : Set Nat) (hsum : Summable (classPowerWeight P 1))
    (R : Real) :
    HasProdUniformlyOn (classEulerFactor P) (classEulerProfile P)
      (Metric.closedBall (1 : Complex) R) := by
  have hbound : forall p : Nat, forall z : Complex,
      Membership.mem (Metric.closedBall (1 : Complex) R) z ->
      norm ((classPowerWeight P 1 p : Complex) * (z - 1)) <=
        R * classPowerWeight P 1 p := by
    intro p z hz
    have hnorm : norm (z - 1) <= R := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (classPowerWeight_nonneg P 1 p)]
    calc
      _ <= classPowerWeight P 1 p * R :=
        mul_le_mul_of_nonneg_left hnorm (classPowerWeight_nonneg P 1 p)
      _ = _ := mul_comm _ _
  have hcts : forall p : Nat,
      ContinuousOn (fun z : Complex => (classPowerWeight P 1 p : Complex) * (z - 1))
        (Metric.closedBall (1 : Complex) R) := by
    intro p
    fun_prop
  exact Summable.hasProdUniformlyOn_one_add
    (isCompact_closedBall (1 : Complex) R) (hsum.mul_left R)
    (Filter.Eventually.of_forall hbound) hcts

theorem differentiable_classEulerProfile
    (P : Set Nat) (hsum : Summable (classPowerWeight P 1)) :
    Differentiable Complex (classEulerProfile P) := by
  intro z
  let R := norm (z - 1) + 1
  have hp := hasProdUniformlyOn_classEulerFactor P hsum R
  have hlimit : TendstoLocallyUniformlyOn
      (fun s : Finset Nat => fun w => s.prod (fun p => classEulerFactor P p w))
      (classEulerProfile P) atTop (Metric.ball (1 : Complex) R) :=
    (hp.mono Metric.ball_subset_closedBall).hasProdLocallyUniformlyOn
  have hfinite : forall s : Finset Nat,
      Differentiable Complex (fun w => s.prod (fun p => classEulerFactor P p w)) := by
    intro s
    unfold classEulerFactor
    fun_prop
  have hd := hlimit.differentiableOn
    (Filter.Eventually.of_forall (fun s => (hfinite s).differentiableOn))
    Metric.isOpen_ball
  have hz : Membership.mem (Metric.ball (1 : Complex) R) z := by
    simpa only [Metric.mem_ball, dist_eq_norm, R] using lt_add_one (norm (z - 1))
  exact (hd z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)

theorem classEulerProfile_one (P : Set Nat) :
    classEulerProfile P 1 = 1 := by
  simp [classEulerProfile, classEulerFactor]

theorem classEulerFactor_eq_zero_iff (P : Set Nat) (p : Nat) (z : Complex) :
    classEulerFactor P p z = 0 <->
      And (Nat.Prime p) (And (Membership.mem P p) (z = 1 - (p : Complex))) := by
  classical
  by_cases hp : And (Nat.Prime p) (Membership.mem P p)
  case pos =>
    have hpC : Not ((p : Complex) = 0) := Nat.cast_ne_zero.mpr hp.1.ne_zero
    have hfactor : classEulerFactor P p z = 1 + (p : Complex) ^ (-1 : Int) * (z - 1) := by
      simp [classEulerFactor, classPowerWeight, hp, Real.rpow_neg_one]
    rw [hfactor]
    constructor
    case mp =>
      intro hz
      refine And.intro hp.1 (And.intro hp.2 ?_)
      have hid := congrArg (fun w : Complex => (p : Complex) * w) hz
      simp only [mul_zero, zpow_neg_one] at hid
      field_simp [hpC] at hid
      linear_combination hid
    case mpr =>
      intro hz
      rw [hz.2.2]
      simp only [zpow_neg_one]
      field_simp [hpC]
      ring
  case neg =>
    have hfactor : classEulerFactor P p z = 1 := by
      simp [classEulerFactor, classPowerWeight, hp]
    rw [hfactor]
    constructor
    case mp => intro h; exact False.elim (one_ne_zero h)
    case mpr => intro h; exact False.elim (hp (And.intro h.1 h.2.1))

theorem classEulerProfile_eq_zero_iff
    (P : Set Nat) (hsum : Summable (classPowerWeight P 1)) (z : Complex) :
    classEulerProfile P z = 0 <->
      exists p : Nat, And (Nat.Prime p)
        (And (Membership.mem P p) (z = 1 - (p : Complex))) := by
  have hraw : classEulerProfile P z = 0 <->
      exists p : Nat, classEulerFactor P p z = 0 := by
    constructor
    case mp =>
      intro hz
      by_contra hnone
      have hne : forall p : Nat, Not (1 + (classEulerFactor P p z - 1) = 0) := by
        intro p hp
        apply hnone
        exact Exists.intro p (by simpa only [add_sub_cancel] using hp)
      have hnonzero := tprod_one_add_ne_zero_of_summable hne
        (summable_norm_classEulerFactor_sub_one P hsum z)
      simp only [add_sub_cancel] at hnonzero
      exact hnonzero hz
    case mpr =>
      intro h
      exact tprod_of_exists_eq_zero h
  simpa only [classEulerFactor_eq_zero_iff] using hraw

theorem primeClassPrefix_prod_eulerFactor (P : Set Nat) (Y : Nat) (z : Complex) :
    (primeClassPrefix P Y).prod (fun p => classEulerFactor P p z) =
      (Finset.range (Y + 1)).prod (fun p => classEulerFactor P p z) := by
  classical
  apply Finset.prod_subset
  case h =>
    intro p hp
    have hd := Finset.mem_filter.mp hp
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hd.1).2)
  case hf =>
    intro p hp hnot
    have hmask : Not (And (Nat.Prime p) (Membership.mem P p)) := by
      intro hactive
      apply hnot
      apply Finset.mem_filter.mpr
      exact And.intro (Finset.mem_Icc.mpr (And.intro hactive.1.two_le
        (Nat.le_of_lt_succ (Finset.mem_range.mp hp)))) hactive
    simp [classEulerFactor, classPowerWeight, hmask]

theorem finiteReference_euler_eval (P : Set Nat) (Y : Nat) (z : Complex) :
    ((finiteReferencePolynomial (primeClassPrefix P Y)).map Complex.ofRealHom).eval z =
      (primeClassPrefix P Y).prod (fun p => classEulerFactor P p z) := by
  classical
  rw [finiteReferencePolynomial_eq_bernoulli_product]
  change ((Polynomial.evalRingHom z).comp (Polynomial.mapRingHom Complex.ofRealHom))
    ((primeClassPrefix P Y).prod (fun p =>
      Polynomial.C (1 - 1 / (p : Real)) +
        Polynomial.C (1 / (p : Real)) * Polynomial.X)) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro p hp
  have hactive := (Finset.mem_filter.mp hp).2
  simp [classEulerFactor, classPowerWeight, hactive, Real.rpow_neg_one]
  ring

theorem finiteReference_euler_eval_tendsto
    (P : Set Nat) (hsum : Summable (classPowerWeight P 1)) (z : Complex) :
    Tendsto (fun Y : Nat =>
      ((finiteReferencePolynomial (primeClassPrefix P Y)).map Complex.ofRealHom).eval z)
      atTop (nhds (classEulerProfile P z)) := by
  have hdev := summable_norm_classEulerFactor_sub_one P hsum z
  have hprod : Multipliable (fun p : Nat => classEulerFactor P p z) := by
    simpa only [add_sub_cancel] using multipliable_one_add_of_summable hdev
  have hsucc : Tendsto (fun Y : Nat => Y + 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with Y hY
    omega
  have hlimit := hprod.hasProd.tendsto_prod_nat.comp hsucc
  change Tendsto (fun Y : Nat =>
    (Finset.range (Y + 1)).prod (fun p => classEulerFactor P p z))
      atTop (nhds (classEulerProfile P z)) at hlimit
  simpa only [<- primeClassPrefix_prod_eulerFactor,
    <- finiteReference_euler_eval] using hlimit

end PrimeFactorOscillations.PrimeClassSampling
