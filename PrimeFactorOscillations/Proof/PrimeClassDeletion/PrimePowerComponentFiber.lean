/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassSamplingModel

/-!
# Exact fibers for the full prime-power component

For a positive integer supported on the finite prime set, divisibility by a
and absence of every support prime from m/a characterize the component atom.
The finite counting identity retains the complete signed floor correction.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

def primePowerComponentFiber (s : Finset Nat) (N a : Nat) : Finset Nat :=
  (Finset.Icc 1 N).filter (fun m =>
    And (Dvd.dvd a m) ((s.filter (fun p => Dvd.dvd p (m / a))).card = 0))

noncomputable def finitePrimeComponentSurvival (s : Finset Nat) : Real :=
  s.prod (fun p => 1 - 1 / (p : Real))

theorem primePowerComponentFiber_card_eq_zero_sample
    (s : Finset Nat) (N a : Nat) (ha : 0 < a) :
    (primePowerComponentFiber s N a).card =
      ((Finset.Icc 1 (N / a)).filter (fun k =>
        (s.filter (fun p => Dvd.dvd p k)).card = 0)).card := by
  classical
  symm
  apply Finset.card_bij (fun k _ => a * k)
  case hi =>
    intro k hk
    have hkData := Finset.mem_filter.mp hk
    have hkInterval := Finset.mem_Icc.mp hkData.1
    have hk0 : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_one hkInterval.1
    have hProduct : 1 <= a * k := Nat.succ_le_of_lt (Nat.mul_pos ha hk0)
    have hUpper : a * k <= N := by
      simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le ha).mp hkInterval.2
    have hQuotient : a * k / a = k :=
      Nat.eq_of_mul_eq_mul_left ha (Nat.mul_div_cancel' (dvd_mul_right a k))
    apply Finset.mem_filter.mpr
    refine And.intro (Finset.mem_Icc.mpr (And.intro hProduct hUpper)) ?_
    exact And.intro (dvd_mul_right a k) (by simpa only [hQuotient] using hkData.2)
  case i_inj =>
    intro k hk l hl hkl
    exact Nat.eq_of_mul_eq_mul_left ha hkl
  case i_surj =>
    intro m hm
    have hmData := Finset.mem_filter.mp hm
    have hmInterval := Finset.mem_Icc.mp hmData.1
    have hm0 : 0 < m := Nat.lt_of_lt_of_le Nat.zero_lt_one hmInterval.1
    have haLe : a <= m := Nat.le_of_dvd hm0 hmData.2.1
    have hQuotient0 : 0 < m / a := Nat.div_pos haLe ha
    have hQuotient : Membership.mem
        ((Finset.Icc 1 (N / a)).filter (fun k =>
          (s.filter (fun p => Dvd.dvd p k)).card = 0)) (m / a) := by
      apply Finset.mem_filter.mpr
      exact And.intro
        (Finset.mem_Icc.mpr (And.intro (Nat.succ_le_of_lt hQuotient0)
          (Nat.div_le_div_right hmInterval.2))) hmData.2.2
    exact Exists.intro (m / a) (Exists.intro hQuotient (Nat.mul_div_cancel' hmData.2.1))

theorem primePowerComponentFiber_card_eq_subset_floor_sum
    (s : Finset Nat) (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p)
    (N a : Nat) (ha : 0 < a) :
    ((primePowerComponentFiber s N a).card : Real) =
      s.powerset.sum (fun t =>
        (-1 : Real) ^ t.card * ((N / (a * t.prod (fun p => p)) : Nat) : Real)) := by
  classical
  have hIndicator (k : Nat) :
      (0 : Real) ^ (s.filter (fun p => Dvd.dvd p k)).card =
        if (s.filter (fun p => Dvd.dvd p k)).card = 0 then 1 else 0 := by
    by_cases h : (s.filter (fun p => Dvd.dvd p k)).card = 0 <;> simp [h]
  have hSum :
      (Finset.Icc 1 (N / a)).sum
        (fun k => (0 : Real) ^ (s.filter (fun p => Dvd.dvd p k)).card) =
      (((Finset.Icc 1 (N / a)).filter (fun k =>
        (s.filter (fun p => Dvd.dvd p k)).card = 0)).card : Real) := by
    simp only [hIndicator, Finset.sum_boole]
  have h := finitePrimeSupport_sampling_identity s hprime (N / a) (0 : Real)
  rw [hSum] at h
  rw [primePowerComponentFiber_card_eq_zero_sample s N a ha]
  simpa only [zero_sub, Nat.div_div_eq_div_mul] using h

theorem finitePrimeComponentSurvival_div_eq_subset_sum
    (s : Finset Nat) (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p)
    (a : Nat) (ha : 0 < a) :
    finitePrimeComponentSurvival s / (a : Real) =
      s.powerset.sum (fun t =>
        (-1 : Real) ^ t.card / ((a * t.prod (fun p => p) : Nat) : Real)) := by
  classical
  have h := congrArg (Polynomial.eval (0 : Real))
    (finiteReferencePolynomial_eq_bernoulli_product s)
  simp only [finiteReferencePolynomial, Polynomial.eval_finsetSum, Polynomial.eval_add,
    Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_one, zero_sub, Polynomial.eval_prod, mul_zero, add_zero] at h
  change _ = finitePrimeComponentSurvival s at h
  rw [<- h, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  have hProduct : 0 < t.prod (fun p => p) := by
    apply Finset.prod_pos
    intro p hp
    exact (hprime p ((Finset.mem_powerset.mp ht) hp)).pos
  have haR : Not ((a : Real) = 0) := Nat.cast_ne_zero.mpr (Nat.ne_of_gt ha)
  have hProductR : Not (((t.prod (fun p => p) : Nat) : Real) = 0) :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hProduct)
  rw [Nat.cast_mul]
  field_simp [haR, hProductR]

theorem primePowerComponentFiber_signed_probability_error
    (s : Finset Nat) (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p)
    (N a : Nat) (ha : 0 < a) :
    ((primePowerComponentFiber s N a).card : Real) / (N : Real) -
        finitePrimeComponentSurvival s / (a : Real) =
      s.powerset.sum (fun t => (-1 : Real) ^ t.card *
        (((N / (a * t.prod (fun p => p)) : Nat) : Real) / (N : Real) -
          1 / ((a * t.prod (fun p => p) : Nat) : Real))) := by
  rw [primePowerComponentFiber_card_eq_subset_floor_sum s hprime N a ha,
    finitePrimeComponentSurvival_div_eq_subset_sum s hprime a ha,
    div_eq_mul_inv, Finset.sum_mul, <- Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  ring

theorem abs_primePowerComponentFiber_probability_error_le
    (s : Finset Nat) (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p)
    (N a : Nat) (hN : 0 < N) (ha : 0 < a)
    (sigma : Real) (hs0 : 0 <= sigma) (hs1 : sigma <= 1) :
    abs (((primePowerComponentFiber s N a).card : Real) / (N : Real) -
        finitePrimeComponentSurvival s / (a : Real)) <=
      (N : Real) ^ (sigma - 1) * (a : Real) ^ (-sigma) *
        s.prod (fun p => 1 + (p : Real) ^ (-sigma)) := by
  classical
  have hBudget :
      s.powerset.sum (fun t => ((t.prod (fun p => p) : Nat) : Real) ^ (-sigma)) =
        s.prod (fun p => 1 + (p : Real) ^ (-sigma)) := by
    calc
      _ = s.powerset.sum (fun t => t.prod (fun p => (p : Real) ^ (-sigma))) := by
        apply Finset.sum_congr rfl
        intro t ht
        exact nat_prod_rpow t (-sigma)
      _ = s.prod (fun p => (p : Real) ^ (-sigma) + 1) :=
        (Finset.prod_add_one s).symm
      _ = _ := by
        apply Finset.prod_congr rfl
        intro p hp
        exact add_comm _ _
  rw [primePowerComponentFiber_signed_probability_error s hprime N a ha]
  calc
    _ <= s.powerset.sum (fun t => abs ((-1 : Real) ^ t.card *
        (((N / (a * t.prod (fun p => p)) : Nat) : Real) / (N : Real) -
          1 / ((a * t.prod (fun p => p) : Nat) : Real)))) :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= s.powerset.sum (fun t => (N : Real) ^ (sigma - 1) *
        ((a * t.prod (fun p => p) : Nat) : Real) ^ (-sigma)) := by
      apply Finset.sum_le_sum
      intro t ht
      have hProduct : 0 < t.prod (fun p => p) := by
        apply Finset.prod_pos
        intro p hp
        exact (hprime p ((Finset.mem_powerset.mp ht) hp)).pos
      have hq : 0 < a * t.prod (fun p => p) := Nat.mul_pos ha hProduct
      have hNeg :
          ((N / (a * t.prod (fun p => p)) : Nat) : Real) / (N : Real) -
              1 / ((a * t.prod (fun p => p) : Nat) : Real) =
            -floorSamplingError N (a * t.prod (fun p => p)) := by
        unfold floorSamplingError
        ring
      rw [hNeg]
      simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg (floorSamplingError_nonneg N _ hN hq)] using
          floorSamplingError_le_rpow N _ hN hq sigma hs0 hs1
    _ = ((N : Real) ^ (sigma - 1) * (a : Real) ^ (-sigma)) *
        s.powerset.sum (fun t => ((t.prod (fun p => p) : Nat) : Real) ^ (-sigma)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg _)]
      ring
    _ = _ := by rw [hBudget]

end PrimeFactorOscillations.PrimeClassSampling
