/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Definitions.QuadraticPrimeProfile
import PrimeFactorOscillations.Helpers.QuadraticPrimeLog

/-!
# Analytic construction of the entire family profile

The quadratic local bound controls all complex disks, including zeros of
finite factors. No factor is divided out. All constants retain the dimension
and the finite-exception bound of the actual law.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QuadraticPrimeLaw

theorem complexTailConstant_nonneg (law : QuadraticPrimeLaw) (R : Real) (hR : 0 <= R) :
    0 <= law.complexTailConstant R := by
  have hD := law.error_nonneg
  have hNu := law.nu_pos
  unfold complexTailConstant
  positivity

theorem norm_complexFactor_sub_one_le (law : QuadraticPrimeLaw)
    (p : Nat.Primes) (R : Real) (z : Complex) (hR : 0 <= R) (hz : norm z <= R) :
    norm (law.complexFactor p z - 1) <=
      law.complexTailConstant R * (primeProfileWeight (p : Nat)) ^ 2 := by
  let v := primeProfileWeight (p : Nat)
  let a := law.weight p
  let b := law.nu * Real.log (1 + v)
  let u : Complex := (b : Complex) * z
  have hv : 0 <= v := primeProfileWeight_nonneg _
  have hv1 : v <= 1 := primeProfileWeight_le_one p
  have hNu := law.nu_pos
  have hD := law.error_nonneg
  have hb0 : 0 <= b := mul_nonneg hNu.le (Real.log_nonneg (by linarith))
  have hlog := Real.sub_log_one_add_bounds v hv
  have hbn : b <= law.nu * v := by
    exact mul_le_mul_of_nonneg_left (by linarith only [hlog.1]) hNu.le
  have hbu : b <= law.nu := hbn.trans (by nlinarith only [hv1, hNu])
  have herror : abs (a - b) <= (law.error + law.nu / 2) * v ^ 2 := by
    have he : -(law.error * v ^ 2) <= a - law.nu * v /\
        a - law.nu * v <= law.error * v ^ 2 := abs_le.mp (law.quadratic_error p)
    have hlo := mul_nonneg hNu.le hlog.1
    have hhi := mul_le_mul_of_nonneg_left hlog.2 hNu.le
    have hp : 0 <= law.nu * v ^ 2 := by positivity
    change abs (a - law.nu * Real.log (1 + v)) <= _
    apply abs_le.mpr
    constructor <;> nlinarith only [he.1, he.2, hlo, hhi, hp]
  have hu : norm u <= law.nu * v * R := by
    calc
      norm u = b * norm z := by
        simp only [u, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb0]
      _ <= (law.nu * v) * R := mul_le_mul hbn hz (norm_nonneg z) (by positivity)
  have huR : norm u <= law.nu * R := hu.trans (by
    exact mul_le_mul_of_nonneg_right (by nlinarith only [hv1, hNu]) hR)
  have hexp : norm (Complex.exp (-u)) <= Real.exp (law.nu * R) := by
    exact (Complex.norm_exp_le_exp_norm (-u)).trans
      (Real.exp_le_exp.mpr (by simpa only [norm_neg] using huR))
  have hrem : norm (Complex.exp u - 1 - u) <= norm u ^ 2 * Real.exp (norm u) := by
    simpa [Finset.sum_range_succ, Nat.factorial, sub_eq_add_neg,
      add_assoc, add_comm, add_left_comm] using Complex.norm_exp_sub_sum_le_norm_mul_exp u 2
  have hremBound : norm (Complex.exp u - 1 - u) <=
      law.nu ^ 2 * v ^ 2 * R ^ 2 * Real.exp (law.nu * R) := by
    calc
      _ <= norm u ^ 2 * Real.exp (norm u) := hrem
      _ <= (law.nu * v * R) ^ 2 * Real.exp (law.nu * R) := by gcongr
      _ = _ := by ring
  have hlinear : norm (((a : Complex) - (b : Complex)) * z) <=
      (law.error + law.nu / 2) * v ^ 2 * R := by
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
    _ <= ((law.error + law.nu / 2) * v ^ 2 * R +
        law.nu ^ 2 * v ^ 2 * R ^ 2 * Real.exp (law.nu * R)) * Real.exp (law.nu * R) :=
      mul_le_mul hsum hexp (norm_nonneg _) (by positivity)
    _ = law.complexTailConstant R * v ^ 2 := by unfold complexTailConstant; ring

theorem hasProdUniformlyOn_complexProfile (law : QuadraticPrimeLaw) (R : Real) (hR : 0 <= R) :
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

theorem differentiable_complexProfile (law : QuadraticPrimeLaw) :
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

theorem tendstoUniformlyOn_complexPrefix (law : QuadraticPrimeLaw) (R : Real) (hR : 0 <= R) :
    TendstoUniformlyOn law.complexPrefix law.complexProfile Filter.atTop
      (Metric.closedBall (0 : Complex) R) := by
  have hp := (law.hasProdUniformlyOn_complexProfile R hR).tendstoUniformlyOn
  intro u hu
  exact tendsto_primeProfilePrefixSet.eventually (hp u hu)

theorem differentiable_complexPrefix (law : QuadraticPrimeLaw) (N : Nat) :
    Differentiable Complex (law.complexPrefix N) := by
  unfold complexPrefix complexFactor
  fun_prop

end PrimeFactorOscillations.QuadraticPrimeLaw
