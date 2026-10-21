/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassSamplingSeries

/-!
# The complete empirical error on a complex disc

Actual finite integer counts supply the polynomial coefficients. The
complete error retains the sampling allowance and the omitted model tail;
both estimates are uniform at every point of the same complex disc.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open PrimeFactorOscillations.PrimeClassDecoder

noncomputable def truncatedSampleProfile
    (P : Set Nat) (N M : Nat) (z : Complex) : Complex :=
  (Finset.range (M + 1)).sum
    (fun k => (((sampleCount P N k : Real) / (N : Real) : Real) : Complex) * z ^ k)

theorem norm_truncatedSample_sub_modelPrefix_le
    (P : Set Nat) (N M : Nat) (hN : 0 < N)
    (sigma r : Real) (hs0 : 0 <= sigma) (hs1 : sigma < 1)
    (hsum : Summable (classPowerWeight P sigma)) (hr : 1 <= r)
    (z : Complex) (hz : norm z <= r) :
    norm (truncatedSampleProfile P N M z - (Finset.range (M + 1)).sum
      (fun k => (classProfileMass P k : Complex) * z ^ k)) <=
      ((N : Real) ^ (sigma - 1) * Real.exp (2 * tsum (classPowerWeight P sigma))) *
        r ^ M := by
  have hlaw := (classEulerProfile_count_sampling_law P sigma hs0 hs1 hsum).2.2.2 N hN
  let e := fun k : Nat =>
    abs ((sampleCount P N k : Real) / (N : Real) - classProfileMass P k)
  have heq : truncatedSampleProfile P N M z - (Finset.range (M + 1)).sum
      (fun k => (classProfileMass P k : Complex) * z ^ k) =
      (Finset.range (M + 1)).sum (fun k =>
        (((sampleCount P N k : Real) / (N : Real) - classProfileMass P k : Real) : Complex) *
          z ^ k) := by
    rw [truncatedSampleProfile, <- Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    push_cast
    ring
  rw [heq]
  calc
    _ <= (Finset.range (M + 1)).sum (fun k =>
        norm ((((sampleCount P N k : Real) / (N : Real) -
          classProfileMass P k : Real) : Complex) * z ^ k)) := norm_sum_le _ _
    _ <= (Finset.range (M + 1)).sum (fun k => e k * r ^ M) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkm : k <= M := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hpow : norm z ^ k <= r ^ M := by
        calc
          _ <= r ^ k := by gcongr
          _ <= r ^ M := by gcongr
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
    _ = (Finset.range (M + 1)).sum e * r ^ M := (Finset.sum_mul _ _ _).symm
    _ <= tsum e * r ^ M := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith : 0 <= r) M)
      exact hlaw.1.sum_le_tsum _ (fun k _ => abs_nonneg _)
    _ <= _ := mul_le_mul_of_nonneg_right hlaw.2 (pow_nonneg (by linarith : 0 <= r) M)

theorem norm_truncatedSample_sub_classEulerProfile_le
    (P : Set Nat) (N M : Nat) (hN : 0 < N)
    (sigma r : Real) (hs : 0 < sigma) (hs1 : sigma < 1)
    (hsum : Summable (classPowerWeight P sigma)) (hr : 1 <= r)
    (ha : 0 < Real.log ((M + 1 : Nat) : Real) / sigma - Real.log r -
      tsum (classPowerWeight P sigma) / sigma)
    (z : Complex) (hz : norm z <= r) :
    norm (truncatedSampleProfile P N M z - classEulerProfile P z) <=
      ((N : Real) ^ (sigma - 1) * Real.exp (2 * tsum (classPowerWeight P sigma))) * r ^ M +
        Real.exp (- (Real.log ((M + 1 : Nat) : Real) / sigma - Real.log r -
          tsum (classPowerWeight P sigma) / sigma) * ((M + 1 : Nat) : Real)) /
          (1 - Real.exp (- (Real.log ((M + 1 : Nat) : Real) / sigma - Real.log r -
            tsum (classPowerWeight P sigma) / sigma))) := by
  let q := (Finset.range (M + 1)).sum
    (fun k => (classProfileMass P k : Complex) * z ^ k)
  have hsample := norm_truncatedSample_sub_modelPrefix_le P N M hN sigma r
    hs.le hs1 hsum hr z hz
  have htail := norm_classEulerProfile_sub_prefix_le P sigma r hs hs1 hsum
    (by linarith) (M + 1) (Nat.succ_le_succ (Nat.zero_le M)) ha z hz
  rw [norm_sub_rev] at htail
  have hid : truncatedSampleProfile P N M z - classEulerProfile P z =
      (truncatedSampleProfile P N M z - q) + (q - classEulerProfile P z) := by ring
  rw [hid]
  exact (norm_add_le _ _).trans (add_le_add hsample htail)

end PrimeFactorOscillations.PrimeClassSampling
