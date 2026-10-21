/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.GCongr
import PrimeFactorOscillations.Helpers.PrimeClassSamplingCoefficientTail

/-!
# The complete profile series and its geometric tail

The Taylor series represents the actual Euler product at every complex
point. The entire omitted rank tail is bounded with a single summable
geometric majorant, including finite and empty prime classes.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open BombieriVinogradov.ComplexAnalysis

theorem entire_hasSum_taylorCoefficient
    (f : Complex -> Complex) (hf : Differentiable Complex f) (z : Complex) :
    HasSum (fun k : Nat => taylorCoefficient f 0 k * z ^ k) (f z) := by
  have hpower := hf.hasFPowerSeriesOnBall 0 (R := 1) (by norm_num)
  have hsum := hpower.hasSum_iteratedFDeriv
    (y := z) (Metric.mem_eball.mpr (edist_lt_top z 0))
  simp only [zero_add] at hsum
  convert hsum using 1
  funext k
  simp only [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, taylorCoefficient, div_eq_mul_inv]
  ring

theorem classEulerProfile_hasSum
    (P : Set Nat) (sigma : Real) (hs0 : 0 <= sigma) (hs1 : sigma < 1)
    (hsum : Summable (classPowerWeight P sigma)) (z : Complex) :
    HasSum (fun k : Nat => (classProfileMass P k : Complex) * z ^ k)
      (classEulerProfile P z) := by
  have h := entire_hasSum_taylorCoefficient (classEulerProfile P)
    (differentiable_classEulerProfile P
      (classPowerWeight_one_summable P sigma hs1.le hsum)) z
  have heq : (fun k : Nat => taylorCoefficient (classEulerProfile P) 0 k * z ^ k) =
      (fun k : Nat => (classProfileMass P k : Complex) * z ^ k) := by
    funext k
    rw [classEulerProfile_taylor_eq_limitingCoefficient P sigma hs0 hs1 hsum,
      classProfileMass_eq_limitingCoefficient P sigma hs0 hs1 hsum]
  rwa [heq] at h

theorem shifted_exponential_hasSum
    (a : Real) (ha : 0 < a) (m : Nat) :
    HasSum (fun j : Nat => Real.exp (-a * ((j + m : Nat) : Real)))
      (Real.exp (-a * (m : Real)) / (1 - Real.exp (-a))) := by
  have hgeo := hasSum_geometric_of_lt_one (Real.exp_nonneg (-a))
    (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ha))
  have h := hgeo.mul_left (Real.exp (-a * (m : Real)))
  have heq : (fun j : Nat => Real.exp (-a * ((j + m : Nat) : Real))) =
      (fun j : Nat => Real.exp (-a * (m : Real)) * Real.exp (-a) ^ j) := by
    funext j
    rw [<- Real.exp_nat_mul, <- Real.exp_add]
    congr 1
    push_cast
    ring
  rw [heq]
  simpa only [div_eq_mul_inv] using h

theorem norm_classProfile_tail_le
    (P : Set Nat) (sigma r : Real) (hs : 0 < sigma) (hs1 : sigma <= 1)
    (hsum : Summable (classPowerWeight P sigma)) (hr : 0 < r)
    (m : Nat) (hm : 1 <= m)
    (ha : 0 < Real.log (m : Real) / sigma - Real.log r -
      tsum (classPowerWeight P sigma) / sigma)
    (z : Complex) (hz : norm z <= r) :
    norm (tsum (fun j : Nat =>
      (classProfileMass P (j + m) : Complex) * z ^ (j + m))) <=
      Real.exp (- (Real.log (m : Real) / sigma - Real.log r -
        tsum (classPowerWeight P sigma) / sigma) * (m : Real)) /
          (1 - Real.exp (- (Real.log (m : Real) / sigma - Real.log r -
            tsum (classPowerWeight P sigma) / sigma))) := by
  let a := Real.log (m : Real) / sigma - Real.log r -
    tsum (classPowerWeight P sigma) / sigma
  have hgeo := shifted_exponential_hasSum a ha m
  have hbound : forall j : Nat,
      norm ((classProfileMass P (j + m) : Complex) * z ^ (j + m)) <=
        Real.exp (-a * ((j + m : Nat) : Real)) := by
    intro j
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ <= abs (classProfileMass P (j + m)) * r ^ (j + m) := by gcongr
      _ <= _ := abs_classProfileMass_mul_pow_le_exp_tail P sigma r hs hs1 hsum hr
        m (j + m) hm (Nat.le_add_left m j)
  have hnorm := hgeo.summable.of_nonneg_of_le (fun j => norm_nonneg _) hbound
  calc
    _ <= tsum (fun j : Nat =>
        norm ((classProfileMass P (j + m) : Complex) * z ^ (j + m))) :=
      norm_tsum_le_tsum_norm hnorm
    _ <= tsum (fun j : Nat => Real.exp (-a * ((j + m : Nat) : Real))) :=
      hnorm.tsum_le_tsum hbound hgeo.summable
    _ = _ := hgeo.tsum_eq

theorem norm_classEulerProfile_sub_prefix_le
    (P : Set Nat) (sigma r : Real) (hs : 0 < sigma) (hs1 : sigma < 1)
    (hsum : Summable (classPowerWeight P sigma)) (hr : 0 < r)
    (m : Nat) (hm : 1 <= m)
    (ha : 0 < Real.log (m : Real) / sigma - Real.log r -
      tsum (classPowerWeight P sigma) / sigma)
    (z : Complex) (hz : norm z <= r) :
    norm (classEulerProfile P z - (Finset.range m).sum
      (fun k => (classProfileMass P k : Complex) * z ^ k)) <=
      Real.exp (- (Real.log (m : Real) / sigma - Real.log r -
        tsum (classPowerWeight P sigma) / sigma) * (m : Real)) /
          (1 - Real.exp (- (Real.log (m : Real) / sigma - Real.log r -
            tsum (classPowerWeight P sigma) / sigma))) := by
  have hseries := classEulerProfile_hasSum P sigma hs.le hs1 hsum z
  have hsplit := hseries.summable.sum_add_tsum_nat_add m
  rw [hseries.tsum_eq] at hsplit
  have hid : classEulerProfile P z - (Finset.range m).sum
      (fun k => (classProfileMass P k : Complex) * z ^ k) =
      tsum (fun j : Nat => (classProfileMass P (j + m) : Complex) * z ^ (j + m)) := by
    rw [<- hsplit]
    exact add_sub_cancel_left _ _
  rw [hid]
  exact norm_classProfile_tail_le P sigma r hs hs1.le hsum hr m hm ha z hz

end PrimeFactorOscillations.PrimeClassSampling
