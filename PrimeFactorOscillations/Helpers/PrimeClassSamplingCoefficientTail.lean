/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassSamplingGrowth

/-!
# Quantitative coefficient tails for the literal class profile

Cauchy's coefficient bound uses the full summable prime-class mass. The
logarithmic coefficient envelope is then retained at every rank in a tail.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open BombieriVinogradov.ComplexAnalysis

theorem abs_classProfileMass_le_cauchy
    (P : Set Nat) (sigma r : Real) (hs : 0 < sigma) (hs1 : sigma <= 1)
    (hsum : Summable (classPowerWeight P sigma)) (hr : 0 < r) (k : Nat) :
    abs (classProfileMass P k) <=
      Real.exp ((tsum (classPowerWeight P sigma)) * r ^ sigma / sigma) / r ^ k := by
  have hbound : forall z : Complex, Membership.mem (Metric.sphere (0 : Complex) r) z ->
      norm (classEulerProfile P z) <=
        Real.exp ((tsum (classPowerWeight P sigma)) * r ^ sigma / sigma) := by
    intro z hz
    have hnorm : norm z = r := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hz
    exact norm_classEulerProfile_le_exp_rpow P sigma r hs hs1 hsum hr.le z hnorm.le
  exact (Complex.abs_re_le_norm _).trans (norm_taylorCoefficient_le k hr
    (differentiable_classEulerProfile P (classPowerWeight_one_summable P sigma hs1 hsum))
    hbound)

theorem abs_classProfileMass_le_exp_log
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma) (hs1 : sigma <= 1)
    (hsum : Summable (classPowerWeight P sigma)) (k : Nat) (hk : 1 <= k) :
    abs (classProfileMass P k) <=
      Real.exp ((tsum (classPowerWeight P sigma) / sigma) * (k : Real) -
        ((k : Real) / sigma) * Real.log (k : Real)) := by
  have hkpos : (0 : Real) < (k : Real) := by exact_mod_cast hk
  let r : Real := (k : Real) ^ (1 / sigma)
  have hr : 0 < r := Real.rpow_pos_of_pos hkpos _
  have hrpower : r ^ sigma = (k : Real) := by
    dsimp [r]
    rw [<- Real.rpow_mul hkpos.le]
    have hexp : (1 : Real) / sigma * sigma = 1 := by field_simp
    rw [hexp, Real.rpow_one]
  have hlogr : Real.log r = Real.log (k : Real) / sigma := by
    dsimp [r]
    rw [Real.log_rpow hkpos]
    ring
  have hden : r ^ k = Real.exp (((k : Real) / sigma) * Real.log (k : Real)) := by
    rw [<- Real.exp_log (pow_pos hr k), Real.log_pow, hlogr]
    congr 1
    ring
  have h := abs_classProfileMass_le_cauchy P sigma r hs hs1 hsum hr k
  rw [hrpower, hden, <- Real.exp_sub] at h
  have heq : tsum (classPowerWeight P sigma) * (k : Real) / sigma =
      (tsum (classPowerWeight P sigma) / sigma) * (k : Real) := by ring
  simpa only [heq] using h

theorem abs_classProfileMass_mul_pow_le_exp_tail
    (P : Set Nat) (sigma r : Real) (hs : 0 < sigma) (hs1 : sigma <= 1)
    (hsum : Summable (classPowerWeight P sigma)) (hr : 0 < r)
    (m k : Nat) (hm : 1 <= m) (hmk : m <= k) :
    abs (classProfileMass P k) * r ^ k <=
      Real.exp (- (Real.log (m : Real) / sigma - Real.log r -
        tsum (classPowerWeight P sigma) / sigma) * (k : Real)) := by
  have hk : 1 <= k := hm.trans hmk
  have hmpos : (0 : Real) < (m : Real) := by exact_mod_cast hm
  have hmkreal : (m : Real) <= (k : Real) := by exact_mod_cast hmk
  have hlog := Real.log_le_log hmpos hmkreal
  have hmul := mul_le_mul_of_nonneg_left hlog
    (div_nonneg (show (0 : Real) <= (k : Real) by positivity) hs.le)
  have hrpow : r ^ k = Real.exp ((k : Real) * Real.log r) := by
    rw [Real.exp_nat_mul, Real.exp_log hr]
  calc
    _ <= Real.exp ((tsum (classPowerWeight P sigma) / sigma) * (k : Real) -
          ((k : Real) / sigma) * Real.log (k : Real)) * r ^ k :=
      mul_le_mul_of_nonneg_right
        (abs_classProfileMass_le_exp_log P sigma hs hs1 hsum k hk) (pow_nonneg hr.le k)
    _ = Real.exp ((tsum (classPowerWeight P sigma) / sigma) * (k : Real) -
          ((k : Real) / sigma) * Real.log (k : Real) + (k : Real) * Real.log r) := by
      rw [hrpow, Real.exp_add]
    _ <= _ := by
      apply Real.exp_le_exp.mpr
      have heq : - (Real.log (m : Real) / sigma - Real.log r -
          tsum (classPowerWeight P sigma) / sigma) * (k : Real) =
          (tsum (classPowerWeight P sigma) / sigma) * (k : Real) -
            ((k : Real) / sigma) * Real.log (m : Real) + (k : Real) * Real.log r := by ring
      rw [heq]
      linarith

end PrimeFactorOscillations.PrimeClassSampling
