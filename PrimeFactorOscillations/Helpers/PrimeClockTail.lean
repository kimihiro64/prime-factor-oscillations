/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClockProfile

/-!
# Uniform prefix errors and coefficients for prime clocks

The entire product, its real positive restriction, and its Taylor coefficients retain the complete compensator.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClockLaw

open Filter

theorem exists_complexPrefix_uniform_error (law : PrimeClockLaw) (R : Real) (hR : 0 <= R) :
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

open Filter

theorem complexFactor_ofReal_eq_exp (law : PrimeClockLaw) (p : Nat.Primes)
    (t : Real) (ht : 0 <= t) :
    law.complexFactor p (t : Complex) = (Real.exp (law.logFactor t p) : Complex) := by
  have hpos : 0 < 1 + law.weight p * t := by
    have h := mul_nonneg (law.weight_nonneg p) ht
    linarith
  unfold complexFactor logFactor
  rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hpos]
  push_cast
  congr 1
  congr 1
  ring

theorem complexPrefix_ofReal_eq_exp (law : PrimeClockLaw) (N : Nat)
    (t : Real) (ht : 0 <= t) :
    law.complexPrefix N (t : Complex) =
      (Real.exp ((primeProfilePrefixSet N).sum (law.logFactor t)) : Complex) := by
  rw [Real.exp_sum]
  simp only [Complex.ofReal_prod]
  exact Finset.prod_congr rfl (fun p _ => law.complexFactor_ofReal_eq_exp p t ht)

theorem complexProfile_ofReal_eq_exp (law : PrimeClockLaw) (t : Real) (ht : 0 <= t) :
    law.complexProfile (t : Complex) = (Real.exp (law.logProfile t) : Complex) := by
  have hNat := (Real.continuous_exp.tendsto (law.logProfile t)).comp
    ((law.summable_logFactor t ht).hasSum.comp tendsto_primeProfilePrefixSet)
  have hCast := (Complex.continuous_ofReal.tendsto (Real.exp (law.logProfile t))).comp hNat
  have hReal : Tendsto (fun N : Nat => law.complexPrefix N (t : Complex)) atTop
      (nhds (Real.exp (law.logProfile t) : Complex)) := by
    apply hCast.congr'
    filter_upwards [] with N
    exact (law.complexPrefix_ofReal_eq_exp N t ht).symm
  have hBall : Membership.mem (Metric.closedBall (0 : Complex) t) (t : Complex) := by
    simp only [Metric.mem_closedBall, dist_zero_right, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ht, le_rfl]
  exact tendsto_nhds_unique ((law.tendstoUniformlyOn_complexPrefix t ht).tendsto_at hBall) hReal

theorem complexProfile_re_pos (law : PrimeClockLaw) (t : Real) (ht : 0 <= t) :
    0 < (law.complexProfile (t : Complex)).re := by
  rw [law.complexProfile_ofReal_eq_exp t ht, Complex.ofReal_re]
  exact Real.exp_pos _

theorem logTailConstant_mono (law : PrimeClockLaw) (a b : Real)
    (ha : 0 <= a) (hab : a <= b) : law.logTailConstant a <= law.logTailConstant b := by
  have hD := law.error_nonneg
  have hNu := law.scale_pos
  unfold logTailConstant
  gcongr

theorem positiveLowerBound_pos (law : PrimeClockLaw) (b : Real) :
    0 < law.positiveLowerBound b := Real.exp_pos _

theorem complexProfile_re_lower_bound (law : PrimeClockLaw) (b t : Real)
    (hb : 0 <= b) (ht : 0 <= t) (htb : t <= b) :
    law.positiveLowerBound b <= (law.complexProfile (t : Complex)).re := by
  have hSum := (summable_primeProfileWeight_sq.mul_left (law.logTailConstant t)).hasSum
  have hBound := tsum_of_norm_bounded hSum (fun p =>
    (show norm (law.logFactor t p) <= law.logTailConstant t *
      (primeProfileWeight (p : Nat)) ^ 2 from by
      simpa only [Real.norm_eq_abs] using law.abs_logFactor_le t ht p))
  have hMass : 0 <= tsum (fun p : Nat.Primes => (primeProfileWeight (p : Nat)) ^ 2) :=
    tsum_nonneg (fun p => sq_nonneg _)
  have hConst := mul_le_mul_of_nonneg_right (law.logTailConstant_mono t b ht htb) hMass
  rw [law.complexProfile_ofReal_eq_exp t ht, Complex.ofReal_re]
  apply Real.exp_le_exp.mpr
  change -(law.logTailConstant b * tsum (fun p : Nat.Primes =>
    (primeProfileWeight (p : Nat)) ^ 2)) <= law.logProfile t
  have hAbs : abs (law.logProfile t) <= law.logTailConstant t *
      tsum (fun p : Nat.Primes => (primeProfileWeight (p : Nat)) ^ 2) := by
    simpa only [Real.norm_eq_abs, logProfile, tsum_mul_left] using hBound
  linarith only [(abs_le.mp hAbs).1, hConst]

open BombieriVinogradov.ComplexAnalysis

theorem exists_prefixProfile_taylor_error (law : PrimeClockLaw) (R : Real) (hR : 0 < R) :
    exists C : Real, 0 <= C /\ forall N : Nat, 1 <= N -> forall j : Nat,
      norm (taylorCoefficient (law.complexPrefix N) 0 j -
        taylorCoefficient law.complexProfile 0 j) <= C / ((N : Real) * R ^ j) := by
  obtain h := law.exists_complexPrefix_uniform_error R hR.le
  choose C hC using h
  refine Exists.intro C (And.intro hC.1 ?_)
  intro N hN j
  have hf : Differentiable Complex (fun z => law.complexPrefix N z - law.complexProfile z) :=
    (law.differentiable_complexPrefix N).sub law.differentiable_complexProfile
  have hbound := norm_taylorCoefficient_le j hR hf (by
    intro z hz
    exact hC.2 N hN z (Metric.sphere_subset_closedBall hz))
  have hid : iteratedDeriv j (fun z => law.complexPrefix N z - law.complexProfile z) 0 =
      iteratedDeriv j (law.complexPrefix N) 0 - iteratedDeriv j law.complexProfile 0 :=
    iteratedDeriv_fun_sub (law.differentiable_complexPrefix N).contDiff.contDiffAt
      law.differentiable_complexProfile.contDiff.contDiffAt
  simpa only [taylorCoefficient, hid, sub_div, div_div] using hbound

open BombieriVinogradov.ComplexAnalysis

theorem hasSum_realCoefficient (law : PrimeClockLaw) (t : Real) :
    HasSum (fun j : Nat => law.realCoefficient j * t ^ j)
      (law.complexProfile (t : Complex)).re := by
  have h := Complex.hasSum_taylorSeries_of_entire law.differentiable_complexProfile 0 (t : Complex)
  have hc : HasSum (fun j : Nat => taylorCoefficient law.complexProfile 0 j * (t : Complex) ^ j)
      (law.complexProfile (t : Complex)) := by
    simpa only [taylorCoefficient, sub_zero, smul_eq_mul, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc] using h
  simpa only [realCoefficient, <- Complex.ofReal_pow,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    using Complex.hasSum_re hc

theorem exists_realCoefficient_bound (law : PrimeClockLaw) (R : Real) (hR : 0 < R) :
    exists C : Real, 0 <= C /\ forall j : Nat,
      norm (law.realCoefficient j) <= C / R ^ j := by
  obtain h := (isCompact_closedBall (0 : Complex) R).exists_bound_of_continuousOn
    law.differentiable_complexProfile.continuous.continuousOn
  choose C hC using h
  have hC0 : 0 <= C := (norm_nonneg (law.complexProfile 0)).trans
    (hC 0 (by simpa only [Metric.mem_closedBall, dist_self] using hR.le))
  refine Exists.intro C (And.intro hC0 ?_)
  intro j
  calc
    norm (law.realCoefficient j) <= norm (taylorCoefficient law.complexProfile 0 j) :=
      Complex.abs_re_le_norm _
    _ <= C / R ^ j := norm_taylorCoefficient_le j hR law.differentiable_complexProfile
      (fun z hz => hC z (Metric.sphere_subset_closedBall hz))

theorem summable_realCoefficient_norm_mul_pow (law : PrimeClockLaw) (r : NNReal) :
    Summable (fun j : Nat => norm (law.realCoefficient j) * (r : Real) ^ j) := by
  let R : Real := (r : Real) + 1
  have hR : 0 < R := by dsimp [R]; positivity
  obtain h := law.exists_realCoefficient_bound R hR
  choose C hC using h
  have hq0 : 0 <= (r : Real) / R := div_nonneg r.coe_nonneg hR.le
  have hq1 : (r : Real) / R < 1 := (div_lt_one hR).mpr (by dsimp [R]; linarith)
  have hg := (summable_geometric_of_lt_one hq0 hq1).mul_left C
  apply Summable.of_nonneg_of_le (fun j => by positivity) _ hg
  intro j
  calc
    norm (law.realCoefficient j) * (r : Real) ^ j <=
        (C / R ^ j) * (r : Real) ^ j :=
      mul_le_mul_of_nonneg_right (hC.2 j) (pow_nonneg r.coe_nonneg j)
    _ = C * ((r : Real) / R) ^ j := by rw [div_pow]; ring

theorem realCoefficient_radius_eq_top (law : PrimeClockLaw) :
    (FormalMultilinearSeries.ofScalars Real law.realCoefficient).radius =
      (Top.top : ENNReal) := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro r
  simpa only [FormalMultilinearSeries.ofScalars_norm] using
    law.summable_realCoefficient_norm_mul_pow r

end PrimeFactorOscillations.PrimeClockLaw
