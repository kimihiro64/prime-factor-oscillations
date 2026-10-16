/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.BoundedAmplitudeDetector

/-!
# Uniform Carrier Product

Uniform finite Euler-product and coefficient perturbation estimates for canonical laws.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.UniformCarrier

open BombieriVinogradov.ComplexAnalysis

def kernelConstant (R : Real) : Real :=
  (R / 2 + R ^ 2 * Real.exp R) * Real.exp R

def productBound (R : Real) : Real :=
  Real.exp (kernelConstant R *
    tsum (fun p : Nat.Primes => (primeProfileWeight (p : Nat)) ^ 2))

theorem canonical_factor_bound (law : PrimeClockLaw)
    (hs : law.scale = 1) (he : law.error = 0)
    (R : Real) (hR : 0 <= R) (z : Complex) (hz : norm z <= R) (p : Nat.Primes) :
    norm (law.complexFactor p z - 1) <=
      kernelConstant R * (primeProfileWeight (p : Nat)) ^ 2 := by
  have h := law.norm_complexFactor_sub_one_le p R z hR hz
  simp only [PrimeClockLaw.complexTailConstant, hs, he, zero_add,
    one_pow, one_mul] at h
  convert h using 1 <;> dsimp [kernelConstant] <;> ring

theorem canonical_product_bounds (law : PrimeClockLaw)
    (hs : law.scale = 1) (he : law.error = 0)
    (R : Real) (hR : 0 <= R) (z : Complex) (hz : norm z <= R) :
    forall t : Finset Nat.Primes,
      norm (t.prod (fun p => law.complexFactor p z)) <= productBound R /\
      norm (t.prod (fun p => law.complexFactor p z) - 1) <=
        kernelConstant R * productBound R *
          t.sum (fun p => (primeProfileWeight (p : Nat)) ^ 2) := by
  classical
  let K := kernelConstant R
  let S := tsum (fun p : Nat.Primes => (primeProfileWeight (p : Nat)) ^ 2)
  have hK : 0 <= K := by dsimp [K, kernelConstant]; positivity
  intro t
  let u := t.sum (fun p => norm (law.complexFactor p z - 1))
  have hu : 0 <= u := Finset.sum_nonneg (fun p _ => norm_nonneg _)
  have hsum : u <= K * t.sum (fun p => (primeProfileWeight (p : Nat)) ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun p _ => canonical_factor_bound law hs he R hR z hz p)
  have hmass : t.sum (fun p => (primeProfileWeight (p : Nat)) ^ 2) <= S :=
    summable_primeProfileWeight_sq.sum_le_tsum t (fun p _ => sq_nonneg _)
  have hAll : u <= K * S := hsum.trans (mul_le_mul_of_nonneg_left hmass hK)
  have hsub : norm (t.prod (fun p => law.complexFactor p z) - 1) <= Real.exp u - 1 := by
    simpa only [add_sub_cancel] using
      t.norm_prod_one_add_sub_one_le (fun p => law.complexFactor p z - 1)
  have hexp : Real.exp u <= productBound R := Real.exp_le_exp.mpr hAll
  have helin : Real.exp u - 1 <= u * Real.exp u := by
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-u)) (Real.exp_nonneg u)
    rw [<- Real.exp_add, add_neg_cancel, Real.exp_zero] at h
    nlinarith
  constructor
  . have hn := norm_le_norm_sub_add (t.prod (fun p => law.complexFactor p z)) 1
    rw [norm_one] at hn
    linarith
  . calc
      _ <= Real.exp u - 1 := hsub
      _ <= u * Real.exp u := helin
      _ <= (K * t.sum (fun p => (primeProfileWeight (p : Nat)) ^ 2)) *
          productBound R :=
        mul_le_mul hsum hexp (Real.exp_nonneg u) (by positivity)
      _ = _ := by ring

theorem finite_profile_comparison (R : Real) (hR : 0 <= R)
    (A B : PrimeClockLaw) (hAs : A.scale = 1) (hAe : A.error = 0)
    (hBs : B.scale = 1) (hBe : B.error = 0)
    (N : Nat) (T : Finset Nat.Primes) (hT : T <= primeProfilePrefixSet N)
    (hSame : forall p, Membership.mem (primeProfilePrefixSet N \ T) p ->
      A.weight p = B.weight p /\ A.compensator p = B.compensator p)
    (z : Complex) (hz : norm z <= R) :
    norm (A.complexPrefix N z - B.complexPrefix N z) <=
      (2 * kernelConstant R * productBound R ^ 2) *
        T.sum (fun p => (primeProfileWeight (p : Nat)) ^ 2) := by
  classical
  let S := primeProfilePrefixSet N \ T
  have heq : S.prod (fun p => A.complexFactor p z) =
      S.prod (fun p => B.complexFactor p z) := by
    apply Finset.prod_congr rfl
    intro p hp
    simp only [PrimeClockLaw.complexFactor, (hSame p hp).1, (hSame p hp).2]
  have hsplit (law : PrimeClockLaw) :
      law.complexPrefix N z =
        S.prod (fun p => law.complexFactor p z) *
          T.prod (fun p => law.complexFactor p z) := by
    exact (Finset.prod_sdiff hT).symm
  have hA := canonical_product_bounds A hAs hAe R hR z hz T
  have hB := canonical_product_bounds B hBs hBe R hR z hz T
  have hS := (canonical_product_bounds A hAs hAe R hR z hz S).1
  rw [hsplit A, hsplit B, <- heq, <- mul_sub, norm_mul]
  have hdiff : norm (T.prod (fun p => A.complexFactor p z) -
      T.prod (fun p => B.complexFactor p z)) <=
        2 * kernelConstant R * productBound R *
          T.sum (fun p => (primeProfileWeight (p : Nat)) ^ 2) := by
    calc
      _ <= norm (T.prod (fun p => A.complexFactor p z) - 1) +
          norm (T.prod (fun p => B.complexFactor p z) - 1) := by
        simpa only [norm_sub_rev] using
          norm_sub_le_norm_sub_add_norm_sub
            (T.prod (fun p => A.complexFactor p z)) 1
            (T.prod (fun p => B.complexFactor p z))
      _ <= _ := by linarith [hA.2, hB.2]
  calc
    _ <= productBound R * (2 * kernelConstant R * productBound R *
        T.sum (fun p => (primeProfileWeight (p : Nat)) ^ 2)) :=
      mul_le_mul hS hdiff (norm_nonneg _) (by dsimp [productBound]; positivity)
    _ = _ := by ring

theorem finite_coefficient_comparison (R : Real) (hR : 0 < R)
    (A B : PrimeClockLaw) (hAs : A.scale = 1) (hAe : A.error = 0)
    (hBs : B.scale = 1) (hBe : B.error = 0)
    (N : Nat) (T : Finset Nat.Primes) (hT : T <= primeProfilePrefixSet N)
    (hSame : forall p, Membership.mem (primeProfilePrefixSet N \ T) p ->
      A.weight p = B.weight p /\ A.compensator p = B.compensator p)
    (j : Nat) :
    norm (taylorCoefficient (A.complexPrefix N) 0 j -
      taylorCoefficient (B.complexPrefix N) 0 j) <=
      ((2 * kernelConstant R * productBound R ^ 2) *
        T.sum (fun p => (primeProfileWeight (p : Nat)) ^ 2)) / R ^ j := by
  have hf := (A.differentiable_complexPrefix N).sub (B.differentiable_complexPrefix N)
  have hbound := norm_taylorCoefficient_le j hR hf (by
    intro z hz
    apply finite_profile_comparison R hR.le A B hAs hAe hBs hBe N T hT hSame z
    have hball : Membership.mem (Metric.closedBall (0 : Complex) R) z :=
      Metric.sphere_subset_closedBall hz
    simpa only [Metric.mem_closedBall, dist_zero_right] using hball)
  have hid : iteratedDeriv j (A.complexPrefix N - B.complexPrefix N) 0 =
      iteratedDeriv j (A.complexPrefix N) 0 - iteratedDeriv j (B.complexPrefix N) 0 :=
    iteratedDeriv_fun_sub (A.differentiable_complexPrefix N).contDiff.contDiffAt
      (B.differentiable_complexPrefix N).contDiff.contDiffAt
  simpa only [taylorCoefficient, hid, sub_div] using hbound

end PrimeFactorOscillations.UniformCarrier
