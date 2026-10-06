/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.QuadraticProfileAnalytic

/-! # Uniform inverse-cutoff approximation of the entire family profile -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QuadraticPrimeLaw

theorem exists_complexPrefix_uniform_error (law : QuadraticPrimeLaw) (R : Real) (hR : 0 <= R) :
    exists C : Real, 0 <= C /\ forall N : Nat, 1 <= N -> forall z : Complex,
      Membership.mem (Metric.closedBall (0 : Complex) R) z ->
        norm (law.complexPrefix N z - law.complexProfile z) <= C / (N : Real) := by
  classical
  let K := law.complexTailConstant R
  let S := tsum (fun p : Nat.Primes => (primeProfileWeight (p : Nat)) ^ 2)
  let E := Real.exp (K * S)
  have hK : 0 <= K := law.complexTailConstant_nonneg R hR
  have hE : 0 <= E := Real.exp_nonneg _
  refine Exists.intro (2 * K * E * E) (And.intro (by positivity) ?_)
  intro N hN z hz
  let F : Nat.Primes -> Complex := fun p =>
    law.complexFactor p z
  have hzR : norm z <= R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  have hlocal : forall p, norm (F p - 1) <= K * (primeProfileWeight (p : Nat)) ^ 2 := by
    intro p
    exact law.norm_complexFactor_sub_one_le p R z hR hzR
  have hsum : forall t : Finset Nat.Primes,
      t.sum (fun p => norm (F p - 1)) <=
        K * t.sum (fun p => (primeProfileWeight (p : Nat)) ^ 2) := by
    intro t
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun p _ => hlocal p)
  have hmass : forall t : Finset Nat.Primes,
      t.sum (fun p => (primeProfileWeight (p : Nat)) ^ 2) <= S := by
    intro t
    exact summable_primeProfileWeight_sq.sum_le_tsum t (fun p _ => sq_nonneg _)
  have hsumAll : forall t : Finset Nat.Primes,
      t.sum (fun p => norm (F p - 1)) <= K * S := by
    intro t
    exact (hsum t).trans (mul_le_mul_of_nonneg_left (hmass t) hK)
  have hsub : forall t : Finset Nat.Primes,
      norm (t.prod F - 1) <= Real.exp (t.sum (fun p => norm (F p - 1))) - 1 := by
    intro t
    simpa only [add_sub_cancel] using t.norm_prod_one_add_sub_one_le (fun p => F p - 1)
  have hnorm : forall t : Finset Nat.Primes, norm (t.prod F) <= E := by
    intro t
    have h := norm_le_norm_sub_add (t.prod F) 1
    have hb := (hsub t).trans (sub_le_sub_right (Real.exp_le_exp.mpr (hsumAll t)) 1)
    rw [norm_one] at h
    dsimp [E]
    linarith
  have hdiff : forall s t : Finset Nat.Primes, s <= t ->
      norm (t.prod F - s.prod F) <=
        K * E * E * (t \ s).sum (fun p => (primeProfileWeight (p : Nat)) ^ 2) := by
    intro s t hst
    let u := (t \ s).sum (fun p => norm (F p - 1))
    have hu : 0 <= u := Finset.sum_nonneg (fun p _ => norm_nonneg _)
    have helin : Real.exp u - 1 <= u * Real.exp u := by
      have he := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-u)) (Real.exp_nonneg u)
      rw [<- Real.exp_add, add_neg_cancel, Real.exp_zero] at he
      nlinarith
    have htail : norm ((t \ s).prod F - 1) <=
        (K * (t \ s).sum (fun p => (primeProfileWeight (p : Nat)) ^ 2)) * E := by
      calc
        norm ((t \ s).prod F - 1) <= Real.exp u - 1 := hsub (t \ s)
        _ <= u * Real.exp u := helin
        _ <= (K * (t \ s).sum (fun p => (primeProfileWeight (p : Nat)) ^ 2)) * E :=
          mul_le_mul (hsum (t \ s)) (Real.exp_le_exp.mpr (hsumAll (t \ s)))
            (Real.exp_nonneg u) (by positivity)
    have hid : t.prod F - s.prod F = ((t \ s).prod F - 1) * s.prod F := by
      rw [sub_mul, one_mul, Finset.prod_sdiff hst]
    rw [hid, norm_mul]
    calc
      norm ((t \ s).prod F - 1) * norm (s.prod F) <=
          ((K * (t \ s).sum (fun p => (primeProfileWeight (p : Nat)) ^ 2)) * E) * E :=
        mul_le_mul htail (hnorm s) (norm_nonneg _) (by positivity)
      _ = K * E * E * (t \ s).sum (fun p => (primeProfileWeight (p : Nat)) ^ 2) := by ring
  have hfinite : forall M : Nat, N <= M ->
      norm (law.complexPrefix M z - law.complexPrefix N z) <=
        (2 * K * E * E) / (N : Real) := by
    intro M hNM
    have hd := hdiff (primeProfilePrefixSet N) (primeProfilePrefixSet M)
      (monotone_primeProfilePrefixSet hNM)
    have ht := sum_primeProfileWeight_sq_tail_le
      (primeProfilePrefixSet M \ primeProfilePrefixSet N) N hN (by
        intro p hp
        have hn := (Finset.mem_sdiff.mp hp).2
        have hnot : Not ((p : Nat) <= N) := fun h =>
          hn ((mem_primeProfilePrefixSet p N).mpr h)
        exact Nat.lt_of_not_ge hnot)
    calc
      norm (law.complexPrefix M z - law.complexPrefix N z) <=
          K * E * E * (primeProfilePrefixSet M \ primeProfilePrefixSet N).sum
            (fun p => (primeProfileWeight (p : Nat)) ^ 2) := hd
      _ <= K * E * E * (2 / (N : Real)) := mul_le_mul_of_nonneg_left ht (by positivity)
      _ = (2 * K * E * E) / (N : Real) := by ring
  have hlim := ((law.tendstoUniformlyOn_complexPrefix R hR).tendsto_at hz).sub_const
    (law.complexPrefix N z)
  have hb : norm (law.complexProfile z - law.complexPrefix N z) <=
      (2 * K * E * E) / (N : Real) := by
    exact le_of_tendsto hlim.norm
      (Filter.eventually_atTop.mpr (Exists.intro N (fun M hNM => hfinite M hNM)))
  simpa only [norm_sub_rev] using hb

end PrimeFactorOscillations.QuadraticPrimeLaw

