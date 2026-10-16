/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.QuadraticProfileLinearization

/-!
# Entire profiles for nonconstant prime clocks

A bounded nonnegative compensator retains character variation in the first-order prime coefficient.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

structure PrimeClockLaw where
  weight : Nat.Primes -> Real
  compensator : Nat.Primes -> Real
  scale : Real
  error : Real
  scale_pos : 0 < scale
  error_nonneg : 0 <= error
  weight_nonneg : forall p, 0 <= weight p
  compensator_nonneg : forall p, 0 <= compensator p
  compensator_le : forall p, compensator p <= scale * primeProfileWeight (p : Nat)
  quadratic_error : forall p,
    abs (weight p - compensator p) <= error * (primeProfileWeight (p : Nat)) ^ 2

namespace PrimeClockLaw

noncomputable def logFactor (law : PrimeClockLaw) (z : Real) (p : Nat.Primes) : Real :=
  Real.log (1 + law.weight p * z) - law.compensator p * z

noncomputable def logProfile (law : PrimeClockLaw) (z : Real) : Real :=
  tsum (law.logFactor z)

noncomputable def profile (law : PrimeClockLaw) (z : Real) : Real :=
  Real.exp (law.logProfile z)

noncomputable def prefixProduct (law : PrimeClockLaw) (N : Nat) (z : Real) : Real :=
  (primeProfilePrefixSet N).prod (fun p => 1 + law.weight p * z)

noncomputable def logTailConstant (law : PrimeClockLaw) (z : Real) : Real :=
  z ^ 2 * (law.scale + law.error) ^ 2 / 2 + z * law.error + z * law.scale / 2

noncomputable def complexFactor (law : PrimeClockLaw) (p : Nat.Primes) (z : Complex) : Complex :=
  (1 + (law.weight p : Complex) * z) * Complex.exp (-(law.compensator p : Complex) * z)

noncomputable def complexProfile (law : PrimeClockLaw) (z : Complex) : Complex :=
  tprod (fun p : Nat.Primes => law.complexFactor p z)

noncomputable def complexPrefix (law : PrimeClockLaw) (N : Nat) (z : Complex) : Complex :=
  (primeProfilePrefixSet N).prod (fun p => law.complexFactor p z)

noncomputable def complexTailConstant (law : PrimeClockLaw) (R : Real) : Real :=
  ((law.error + law.scale / 2) * R +
    law.scale ^ 2 * R ^ 2 * Real.exp (law.scale * R)) * Real.exp (law.scale * R)

noncomputable def realCoefficient (law : PrimeClockLaw) (j : Nat) : Real :=
  (BombieriVinogradov.ComplexAnalysis.taylorCoefficient law.complexProfile 0 j).re

noncomputable def positiveLowerBound (law : PrimeClockLaw) (b : Real) : Real :=
  Real.exp (-(law.logTailConstant b *
    tsum (fun p : Nat.Primes => (primeProfileWeight (p : Nat)) ^ 2)))

end PrimeClockLaw

end PrimeFactorOscillations

namespace PrimeFactorOscillations.PrimeClockLaw

open Filter

theorem weight_le (law : PrimeClockLaw) (p : Nat.Primes) :
    law.weight p <= (law.scale + law.error) * primeProfileWeight (p : Nat) := by
  have hv := primeProfileWeight_nonneg (p : Nat)
  have hv1 := primeProfileWeight_le_one p
  have he := (abs_le.mp (law.quadratic_error p)).2
  have hc := law.compensator_le p
  have hsq : (primeProfileWeight (p : Nat)) ^ 2 <= primeProfileWeight (p : Nat) := by
    nlinarith
  have h := mul_le_mul_of_nonneg_left hsq law.error_nonneg
  nlinarith only [he, h, hc]

theorem logTailConstant_nonneg (law : PrimeClockLaw) (z : Real) (hz : 0 <= z) :
    0 <= law.logTailConstant z := by
  have hD := law.error_nonneg
  have hNu := law.scale_pos
  unfold logTailConstant
  positivity

theorem abs_logFactor_le (law : PrimeClockLaw) (z : Real) (hz : 0 <= z)
    (p : Nat.Primes) :
    abs (law.logFactor z p) <=
      law.logTailConstant z * (primeProfileWeight (p : Nat)) ^ 2 := by
  let v := primeProfileWeight (p : Nat)
  let w := law.weight p
  have hv : 0 <= v := primeProfileWeight_nonneg _
  have hw : 0 <= w := law.weight_nonneg p
  have hD := law.error_nonneg
  have hScale := law.scale_pos
  have hWeight : w <= (law.scale + law.error) * v := law.weight_le p
  have hSquare : (w * z) ^ 2 <= (law.scale + law.error) ^ 2 * v ^ 2 * z ^ 2 := by
    calc
      (w * z) ^ 2 <= ((law.scale + law.error) * v * z) ^ 2 := by gcongr
      _ = _ := by ring
  have hOne := Real.sub_log_one_add_bounds (w * z) (mul_nonneg hw hz)
  have hE := abs_le.mp (law.quadratic_error p)
  have hELow := mul_le_mul_of_nonneg_right hE.1 hz
  have hEHigh := mul_le_mul_of_nonneg_right hE.2 hz
  have hPos1 : 0 <= z * law.error * v ^ 2 := by positivity
  have hPos2 : 0 <= law.scale * z * v ^ 2 := by positivity
  have hPos3 : 0 <= z ^ 2 * (law.scale + law.error) ^ 2 * v ^ 2 := by positivity
  change abs (Real.log (1 + w * z) - law.compensator p * z) <=
    (z ^ 2 * (law.scale + law.error) ^ 2 / 2 + z * law.error + z * law.scale / 2) * v ^ 2
  change -(law.error * v ^ 2) * z <= (w - law.compensator p) * z at hELow
  change (w - law.compensator p) * z <= law.error * v ^ 2 * z at hEHigh
  apply abs_le.mpr
  constructor <;> nlinarith only [hOne.1, hOne.2, hSquare, hELow, hEHigh, hPos1, hPos2, hPos3]

theorem summable_logFactor (law : PrimeClockLaw) (z : Real) (hz : 0 <= z) :
    Summable (law.logFactor z) := by
  apply (summable_primeProfileWeight_sq.mul_left (law.logTailConstant z)).of_norm_bounded
  intro p
  simpa only [Real.norm_eq_abs] using law.abs_logFactor_le z hz p

theorem logProfile_tail_bound (law : PrimeClockLaw) (N : Nat) (hN : 1 <= N)
    (z : Real) (hz : 0 <= z) :
    abs (law.logProfile z - (primeProfilePrefixSet N).sum (law.logFactor z)) <=
      2 * law.logTailConstant z / N := by
  classical
  have hK := law.logTailConstant_nonneg z hz
  have hFinite (M : Nat) (hNM : N <= M) :
      abs ((primeProfilePrefixSet M).sum (law.logFactor z) -
        (primeProfilePrefixSet N).sum (law.logFactor z)) <=
          2 * law.logTailConstant z / N := by
    let s := primeProfilePrefixSet M \ primeProfilePrefixSet N
    have hTail := sum_primeProfileWeight_sq_tail_le s N hN (by
      intro p hp
      have hn := (Finset.mem_sdiff.mp hp).2
      exact Nat.lt_of_not_ge (fun h => hn ((mem_primeProfilePrefixSet p N).mpr h)))
    rw [<- Finset.sum_sdiff (monotone_primeProfilePrefixSet hNM), add_sub_cancel_right]
    calc
      abs (s.sum (law.logFactor z)) <= s.sum (fun p => abs (law.logFactor z p)) :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= s.sum (fun p => law.logTailConstant z *
          (primeProfileWeight (p : Nat)) ^ 2) :=
        Finset.sum_le_sum (fun p _ => law.abs_logFactor_le z hz p)
      _ = law.logTailConstant z * s.sum (fun p => (primeProfileWeight (p : Nat)) ^ 2) :=
        (Finset.mul_sum _ _ _).symm
      _ <= law.logTailConstant z * (2 / (N : Real)) :=
        mul_le_mul_of_nonneg_left hTail hK
      _ = 2 * law.logTailConstant z / N := by ring
  have hLim := ((law.summable_logFactor z hz).hasSum.comp tendsto_primeProfilePrefixSet).sub_const
    ((primeProfilePrefixSet N).sum (law.logFactor z))
  exact le_of_tendsto hLim.abs (eventually_atTop.mpr (Exists.intro N hFinite))

theorem profile_pos (law : PrimeClockLaw) (z : Real) : 0 < law.profile z :=
  Real.exp_pos _

theorem prefixProduct_pos (law : PrimeClockLaw) (N : Nat) (z : Real)
    (hz : 0 <= z) : 0 < law.prefixProduct N z := by
  apply Finset.prod_pos
  intro p _
  have h := mul_nonneg (law.weight_nonneg p) hz
  linarith

theorem complexTailConstant_nonneg (law : PrimeClockLaw) (R : Real) (hR : 0 <= R) :
    0 <= law.complexTailConstant R := by
  have hD := law.error_nonneg
  have hNu := law.scale_pos
  unfold complexTailConstant
  positivity

theorem norm_complexFactor_sub_one_le (law : PrimeClockLaw)
    (p : Nat.Primes) (R : Real) (z : Complex) (hR : 0 <= R) (hz : norm z <= R) :
    norm (law.complexFactor p z - 1) <=
      law.complexTailConstant R * (primeProfileWeight (p : Nat)) ^ 2 := by
  let v := primeProfileWeight (p : Nat)
  let a := law.weight p
  let b := law.compensator p
  let u : Complex := (b : Complex) * z
  have hv : 0 <= v := primeProfileWeight_nonneg _
  have hv1 : v <= 1 := primeProfileWeight_le_one p
  have hNu := law.scale_pos
  have hD := law.error_nonneg
  have hb0 : 0 <= b := law.compensator_nonneg p
  have hbn : b <= law.scale * v := law.compensator_le p

  have hbu : b <= law.scale := hbn.trans (by nlinarith only [hv1, hNu])
  have herror : abs (a - b) <= (law.error + law.scale / 2) * v ^ 2 := by
    have he : abs (a - b) <= law.error * v ^ 2 := law.quadratic_error p
    have hExtra : 0 <= (law.scale / 2) * v ^ 2 := by positivity
    nlinarith only [he, hExtra]

  have hu : norm u <= law.scale * v * R := by
    calc
      norm u = b * norm z := by
        simp only [u, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb0]
      _ <= (law.scale * v) * R := mul_le_mul hbn hz (norm_nonneg z) (by positivity)
  have huR : norm u <= law.scale * R := hu.trans (by
    exact mul_le_mul_of_nonneg_right (by nlinarith only [hv1, hNu]) hR)
  have hexp : norm (Complex.exp (-u)) <= Real.exp (law.scale * R) := by
    exact (Complex.norm_exp_le_exp_norm (-u)).trans
      (Real.exp_le_exp.mpr (by simpa only [norm_neg] using huR))
  have hrem : norm (Complex.exp u - 1 - u) <= norm u ^ 2 * Real.exp (norm u) := by
    simpa [Finset.sum_range_succ, Nat.factorial, sub_eq_add_neg,
      add_assoc, add_comm, add_left_comm] using Complex.norm_exp_sub_sum_le_norm_mul_exp u 2
  have hremBound : norm (Complex.exp u - 1 - u) <=
      law.scale ^ 2 * v ^ 2 * R ^ 2 * Real.exp (law.scale * R) := by
    calc
      _ <= norm u ^ 2 * Real.exp (norm u) := hrem
      _ <= (law.scale * v * R) ^ 2 * Real.exp (law.scale * R) := by gcongr
      _ = _ := by ring
  have hlinear : norm (((a : Complex) - (b : Complex)) * z) <=
      (law.error + law.scale / 2) * v ^ 2 * R := by
    rw [<- Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul herror hz (norm_nonneg _) (by positivity)
  have he : Complex.exp u * Complex.exp (-u) = 1 := by
    rw [<- Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hid : law.complexFactor p z - 1 =
      (((a : Complex) - (b : Complex)) * z - (Complex.exp u - 1 - u)) *
        Complex.exp (-u) := by
    change (1 + (a : Complex) * z) * Complex.exp (-(b : Complex) * z) - 1 = _
    rw [show -(b : Complex) * z = -u by dsimp [u]; ring]
    calc
      _ = (1 + (a : Complex) * z) * Complex.exp (-u) -
          Complex.exp u * Complex.exp (-u) := by rw [he]
      _ = _ := by dsimp [u]; ring
  rw [hid, norm_mul]
  have hsum := (norm_sub_le (((a : Complex) - (b : Complex)) * z)
    (Complex.exp u - 1 - u)).trans (add_le_add hlinear hremBound)
  calc
    _ <= ((law.error + law.scale / 2) * v ^ 2 * R +
        law.scale ^ 2 * v ^ 2 * R ^ 2 * Real.exp (law.scale * R)) * Real.exp (law.scale * R) :=
      mul_le_mul hsum hexp (norm_nonneg _) (by positivity)
    _ = law.complexTailConstant R * v ^ 2 := by unfold complexTailConstant; ring

theorem hasProdUniformlyOn_complexProfile (law : PrimeClockLaw) (R : Real) (hR : 0 <= R) :
    HasProdUniformlyOn (fun p z => law.complexFactor p z) law.complexProfile
      (Metric.closedBall (0 : Complex) R) := by
  have hbound : forall p, forall z,
      Membership.mem (Metric.closedBall (0 : Complex) R) z ->
      norm (law.complexFactor p z - 1) <=
        law.complexTailConstant R * (primeProfileWeight (p : Nat)) ^ 2 := by
    intro p z hz
    exact law.norm_complexFactor_sub_one_le p R z hR
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)
  have hcts : forall p, ContinuousOn (fun z => law.complexFactor p z - 1)
      (Metric.closedBall (0 : Complex) R) := by
    intro p
    apply Continuous.continuousOn
    unfold complexFactor
    fun_prop
  have hp := Summable.hasProdUniformlyOn_one_add
    (f := fun p z => law.complexFactor p z - 1) (isCompact_closedBall (0 : Complex) R)
    (summable_primeProfileWeight_sq.mul_left (law.complexTailConstant R))
    (Filter.Eventually.of_forall hbound) hcts
  unfold complexProfile
  convert hp using 1 <;> simp only [add_sub_cancel]

theorem differentiable_complexProfile (law : PrimeClockLaw) :
    Differentiable Complex law.complexProfile := by
  intro z
  let R := norm z + 1
  have hR : 0 <= R := by dsimp [R]; positivity
  have hp := law.hasProdUniformlyOn_complexProfile R hR
  have hlim : TendstoLocallyUniformlyOn
      (fun s : Finset Nat.Primes => fun w => s.prod (fun p => law.complexFactor p w))
      law.complexProfile Filter.atTop (Metric.ball (0 : Complex) R) :=
    (hp.mono Metric.ball_subset_closedBall).hasProdLocallyUniformlyOn
  have hfin : forall s : Finset Nat.Primes,
      Differentiable Complex (fun w => s.prod (fun p => law.complexFactor p w)) := by
    intro s
    unfold complexFactor
    fun_prop
  have hd := hlim.differentiableOn
    (Filter.Eventually.of_forall (fun s => (hfin s).differentiableOn)) Metric.isOpen_ball
  have hz : Membership.mem (Metric.ball (0 : Complex) R) z := by
    simpa only [Metric.mem_ball, dist_zero_right, R] using lt_add_one (norm z)
  exact (hd z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)

theorem tendstoUniformlyOn_complexPrefix (law : PrimeClockLaw) (R : Real) (hR : 0 <= R) :
    TendstoUniformlyOn law.complexPrefix law.complexProfile Filter.atTop
      (Metric.closedBall (0 : Complex) R) := by
  have hp := (law.hasProdUniformlyOn_complexProfile R hR).tendstoUniformlyOn
  intro u hu
  exact tendsto_primeProfilePrefixSet.eventually (hp u hu)

theorem differentiable_complexPrefix (law : PrimeClockLaw) (N : Nat) :
    Differentiable Complex (law.complexPrefix N) := by
  unfold complexPrefix complexFactor
  fun_prop

end PrimeFactorOscillations.PrimeClockLaw
