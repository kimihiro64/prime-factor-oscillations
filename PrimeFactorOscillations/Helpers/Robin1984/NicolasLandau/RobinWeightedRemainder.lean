/-
Source port from Robin1984 bfa72aec0c25c8ee29cefe4449d778ff30412bee.
Original file: Robin1984/NicolasLandau/RobinWeightedIntegral.lean
Original source lines 395-768. Apache-2.0.
Statements and proof bodies retained; split at existing declaration boundaries.
-/
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.RobinWeightedKernel

/-!
# The signed kernel decomposition and remainder estimates

A source-preserving component of the written RH negative-envelope argument.
-/

namespace Robin1984

noncomputable section

open Complex MeasureTheory Set
open scoped BigOperators

/-- Critical-line bound for the bracket in Robin's zero-kernel remainder. -/
theorem norm_robinZeroKernelRemainder_bracket_le
    {n : Nat} (hn : 1 <= n) {rho : Complex}
    (hRe : rho.re = (1 / 2 : Real)) {x : Real} (hx : 1 < x) :
    norm
        (-((x : Complex) ^ (rho - (n : Complex))) /
            ((Real.log x : Real) : Complex) ^ (2 : Nat) +
          2 * robinCpowLogTail (rho - (n : Complex)) 3 x) <=
      x ^ ((1 / 2 : Real) - (n : Real)) *
          Inv.inv ((Real.log x) ^ (2 : Nat)) +
        2 *
          ((-x ^ ((1 / 2 : Real) - (n : Real)) /
                ((1 / 2 : Real) - (n : Real))) *
            Inv.inv ((Real.log x) ^ (3 : Nat))) := by
  have hxPos : 0 < x := lt_trans Real.zero_lt_one hx
  have hLogPos : 0 < Real.log x := Real.log_pos hx
  have haRe : (rho - (n : Complex)).re < 0 := by
    rw [Complex.sub_re, Complex.natCast_re, hRe]
    have hnReal : (1 : Real) <= (n : Real) := by
      exact_mod_cast hn
    linarith
  have hMainNorm :
      norm
          (-((x : Complex) ^ (rho - (n : Complex))) /
            ((Real.log x : Real) : Complex) ^ (2 : Nat)) =
        x ^ ((1 / 2 : Real) - (n : Real)) *
          Inv.inv ((Real.log x) ^ (2 : Nat)) := by
    rw [norm_div, norm_neg,
      Complex.norm_cpow_eq_rpow_re_of_pos hxPos, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hLogPos]
    simp only [Complex.sub_re, Complex.natCast_re, hRe]
    rw [div_eq_mul_inv]
  have hTail := norm_robinCpowLogTail_le hx haRe 3
  have hTailExact :
      norm (robinCpowLogTail (rho - (n : Complex)) 3 x) <=
        (-x ^ ((1 / 2 : Real) - (n : Real)) /
            ((1 / 2 : Real) - (n : Real))) *
          Inv.inv ((Real.log x) ^ (3 : Nat)) := by
    simpa only [Complex.sub_re, Complex.natCast_re, hRe] using hTail
  calc
    norm
        (-((x : Complex) ^ (rho - (n : Complex))) /
            ((Real.log x : Real) : Complex) ^ (2 : Nat) +
          2 * robinCpowLogTail (rho - (n : Complex)) 3 x) <=
        norm
            (-((x : Complex) ^ (rho - (n : Complex))) /
              ((Real.log x : Real) : Complex) ^ (2 : Nat)) +
          norm (2 * robinCpowLogTail (rho - (n : Complex)) 3 x) :=
      norm_add_le _ _
    _ = x ^ ((1 / 2 : Real) - (n : Real)) *
          Inv.inv ((Real.log x) ^ (2 : Nat)) +
        2 * norm (robinCpowLogTail (rho - (n : Complex)) 3 x) := by
      rw [hMainNorm, norm_mul]
      norm_num
    _ <= x ^ ((1 / 2 : Real) - (n : Real)) *
          Inv.inv ((Real.log x) ^ (2 : Nat)) +
        2 *
          ((-x ^ ((1 / 2 : Real) - (n : Real)) /
                ((1 / 2 : Real) - (n : Real))) *
            Inv.inv ((Real.log x) ^ (3 : Nat))) := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hTailExact zero_le_two)

/-- Robin 1984, Lemma 1 remainder bound in the form needed for summing over
the multiplicity-carrying xi divisor. -/
theorem norm_robinZeroKernelRemainder_div_rho_le
    {n : Nat} (hn : 1 <= n) {rho : Complex}
    (hRho : Not (rho = 0)) (hRe : rho.re = (1 / 2 : Real))
    {x : Real} (hx : 1 < x) :
    norm (robinZeroKernelRemainder n rho x / rho) <=
      (Inv.inv (norm rho)) ^ (2 : Nat) *
        (x ^ ((1 / 2 : Real) - (n : Real)) *
            Inv.inv ((Real.log x) ^ (2 : Nat)) +
          2 *
            ((-x ^ ((1 / 2 : Real) - (n : Real)) /
                  ((1 / 2 : Real) - (n : Real))) *
              Inv.inv ((Real.log x) ^ (3 : Nat)))) := by
  have hNormLe : norm rho <= norm (rho - (n : Complex)) :=
    norm_le_norm_sub_nat_of_re_eq_half hn hRe
  have hNormPos : 0 < norm rho := norm_pos_iff.mpr hRho
  have hNormSqPos : 0 < (norm rho) ^ (2 : Nat) :=
    pow_pos hNormPos 2
  have hNormSqLe :
      (norm rho) ^ (2 : Nat) <=
        (norm (rho - (n : Complex))) ^ (2 : Nat) := by
    nlinarith [norm_nonneg (rho - (n : Complex))]
  have hInvNormLe :
      norm (Inv.inv ((rho - (n : Complex)) ^ (2 : Nat))) <=
        (Inv.inv (norm rho)) ^ (2 : Nat) := by
    rw [norm_inv, norm_pow]
    simpa [one_div, inv_pow] using
      one_div_le_one_div_of_le hNormSqPos hNormSqLe
  have hBracket :=
    norm_robinZeroKernelRemainder_bracket_le hn hRe hx
  rw [robinZeroKernelRemainder_div_rho hRho, norm_mul]
  exact mul_le_mul hInvNormLe hBracket (norm_nonneg _)
    (pow_nonneg (inv_nonneg.mpr (norm_nonneg rho)) 2)


/-- Split Robin's kernel into its two logarithmic complex-power tails. -/
theorem robinZeroKernel_eq_nat_mul_tail_one_add_tail_two
    {n : Nat} {rho : Complex} {x : Real} (hx : 1 < x)
    (hRe : rho.re < n) :
    robinZeroKernel n rho x =
      (n : Complex) * robinCpowLogTail (rho - (n : Complex)) 1 x +
        robinCpowLogTail (rho - (n : Complex)) 2 x := by
  let a : Complex := rho - (n : Complex)
  have hExponent : (a - 1).re < -1 := by
    dsimp [a]
    linarith
  have hOne :
      IntegrableOn (fun t : Real =>
        (t : Complex) ^ (a - 1) *
          (((Inv.inv (Real.log t) : Real) : Complex))) (Ioi x) := by
    simpa using integrableOn_cpow_div_log_pow hx hExponent 1
  have hTwo :
      IntegrableOn (fun t : Real =>
        (t : Complex) ^ (a - 1) *
          (((Inv.inv ((Real.log t) ^ (2 : Nat)) : Real) : Complex)))
        (Ioi x) :=
    integrableOn_cpow_div_log_pow hx hExponent 2
  change robinZeroKernel n rho x =
    (n : Complex) * robinCpowLogTail a 1 x +
      robinCpowLogTail a 2 x
  unfold robinZeroKernel robinCpowLogTail
  have hFunctions :
      (fun t : Real =>
        (t : Complex) ^ (rho - (n : Complex) - 1) *
          (((n : Real) * Real.log t + 1) /
            (Real.log t) ^ (2 : Nat) : Real)) =
        (fun t : Real =>
          (n : Complex) *
              ((t : Complex) ^ (a - 1) *
                (((Inv.inv (Real.log t) : Real) : Complex))) +
            (t : Complex) ^ (a - 1) *
              (((Inv.inv ((Real.log t) ^ (2 : Nat)) : Real) : Complex))) := by
    funext t
    dsimp [a]
    rw [show rho - (n : Complex) - 1 =
        (rho - (n : Complex)) - 1 by ring]
    push_cast
    by_cases hLog : Real.log t = 0
    case pos => simp [hLog]
    case neg => field_simp [hLog]
  rw [hFunctions, integral_add (hOne.const_mul (n : Complex)) hTwo,
    integral_const_mul]
  simp only [pow_one]

/-- One integration by parts exposes the exact atom-matching form: the
boundary atom plus `rho` times the first logarithmic tail. -/
theorem robinZeroKernel_eq_boundary_add_rho_mul_tail_one
    {n : Nat} {rho : Complex} {x : Real} (hx : 1 < x)
    (hRe : rho.re < n) :
    robinZeroKernel n rho x =
      (x : Complex) ^ (rho - (n : Complex)) *
          (((Inv.inv (Real.log x) : Real) : Complex)) +
        rho * robinCpowLogTail (rho - (n : Complex)) 1 x := by
  let a : Complex := rho - (n : Complex)
  have haRe : a.re < 0 := by
    dsimp [a]
    simp
    exact hRe
  have haZero : Not (a = 0) := by
    intro h
    have hReal := congrArg Complex.re h
    rw [Complex.zero_re] at hReal
    linarith
  rw [robinZeroKernel_eq_nat_mul_tail_one_add_tail_two hx hRe]
  have hRecOne := robinCpowLogTail_recurrence hx haRe 1
  have hRecScaled :
      a * robinCpowLogTail a 1 x =
        -(x : Complex) ^ a *
            (((Inv.inv (Real.log x) : Real) : Complex)) +
          robinCpowLogTail a 2 x := by
    rw [hRecOne]
    push_cast
    field_simp [haZero]
  have hRho : rho = (n : Complex) + a := by
    dsimp [a]
    ring
  have hTailTwo :
      robinCpowLogTail a 2 x =
        a * robinCpowLogTail a 1 x +
          (x : Complex) ^ a *
            (((Inv.inv (Real.log x) : Real) : Complex)) := by
    clear hRho
    linear_combination -hRecScaled
  change (n : Complex) * robinCpowLogTail a 1 x +
      robinCpowLogTail a 2 x =
    (x : Complex) ^ a *
        (((Inv.inv (Real.log x) : Real) : Complex)) +
      rho * robinCpowLogTail a 1 x
  rw [hTailTwo, hRho]
  ring

/-- Dividing the atom-matching identity by `rho` gives exactly the Mellin
transform split into the lower constant block and the upper logarithmic tail. -/
theorem robinZeroKernel_div_rho_eq_boundary_div_add_tail_one
    {n : Nat} {rho : Complex} (hRho : Not (rho = 0))
    {x : Real} (hx : 1 < x) (hRe : rho.re < n) :
    robinZeroKernel n rho x / rho =
      (x : Complex) ^ (rho - (n : Complex)) /
          (rho * ((Real.log x : Real) : Complex)) +
        robinCpowLogTail (rho - (n : Complex)) 1 x := by
  rw [robinZeroKernel_eq_boundary_add_rho_mul_tail_one hx hRe]
  push_cast
  field_simp [hRho]

/-- Robin 1984, Lemma 1: the zero kernel is its leading term plus the
twice-integrated remainder. -/
theorem robinZeroKernel_eq_main_add_remainder
    {n : Nat} (hn : 1 <= n) {rho : Complex} {x : Real}
    (hx : 1 < x) (hRe : rho.re < n) :
    robinZeroKernel n rho x =
      ((n : Complex) / ((n : Complex) - rho)) *
          (x : Complex) ^ (rho - (n : Complex)) *
          (((Inv.inv (Real.log x) : Real) : Complex)) +
        robinZeroKernelRemainder n rho x := by
  let a : Complex := rho - (n : Complex)
  have haRe : a.re < 0 := by
    dsimp [a]
    simp
    exact hRe
  have haZero : Not (a = 0) := by
    intro h
    have hReal := congrArg Complex.re h
    rw [Complex.zero_re] at hReal
    linarith
  have hExponent : (a - 1).re < -1 := by
    simp
    linarith
  have hOne :
      IntegrableOn (fun t : Real =>
        (t : Complex) ^ (a - 1) *
          (((Inv.inv (Real.log t) : Real) : Complex))) (Ioi x) := by
    simpa using integrableOn_cpow_div_log_pow hx hExponent 1
  have hTwo :
      IntegrableOn (fun t : Real =>
        (t : Complex) ^ (a - 1) *
          (((Inv.inv ((Real.log t) ^ (2 : Nat)) : Real) : Complex)))
        (Ioi x) :=
    integrableOn_cpow_div_log_pow hx hExponent 2
  have hKernelSplit :
      robinZeroKernel n rho x =
        (n : Complex) * robinCpowLogTail a 1 x +
          robinCpowLogTail a 2 x := by
    unfold robinZeroKernel robinCpowLogTail
    have hFunctions :
        (fun t : Real =>
          (t : Complex) ^ (rho - (n : Complex) - 1) *
            (((n : Real) * Real.log t + 1) /
              (Real.log t) ^ (2 : Nat) : Real)) =
          (fun t : Real =>
            (n : Complex) *
                ((t : Complex) ^ (a - 1) *
                  (((Inv.inv (Real.log t) : Real) : Complex))) +
              (t : Complex) ^ (a - 1) *
                (((Inv.inv ((Real.log t) ^ (2 : Nat)) : Real) : Complex))) := by
      funext t
      dsimp [a]
      rw [show rho - (n : Complex) - 1 =
          (rho - (n : Complex)) - 1 by ring]
      push_cast
      by_cases hLog : Real.log t = 0
      case pos => simp [hLog]
      case neg =>
        field_simp [hLog]
    rw [hFunctions, integral_add (hOne.const_mul (n : Complex)) hTwo,
      integral_const_mul]
    simp only [pow_one]
  have hRecOne := robinCpowLogTail_recurrence hx haRe 1
  have hRecTwo := robinCpowLogTail_recurrence hx haRe 2
  rw [hKernelSplit, hRecOne, hRecTwo]
  unfold robinZeroKernelRemainder
  have hLog : Not (Real.log x = 0) := ne_of_gt (Real.log_pos hx)
  have hOpp : (n : Complex) - rho = -a := by
    dsimp [a]
    ring
  have hDiff : rho - (n : Complex) = a := by
    rfl
  rw [hOpp, hDiff]
  push_cast
  field_simp [haZero, hLog]
  ring

/-- Complete critical-line majorant for one multiplicity-carrying zero atom. -/
theorem norm_robinZeroKernel_div_rho_le_robinXiZeroWeight
    {n : Nat} (hn : 1 <= n) {rho : Complex}
    (hRho : Not (rho = 0)) (hRe : rho.re = (1 / 2 : Real))
    {x : Real} (hx : 1 < x) :
    norm (robinZeroKernel n rho x / rho) <=
      (Inv.inv (norm rho)) ^ (2 : Nat) *
        ((n : Real) * x ^ ((1 / 2 : Real) - (n : Real)) *
            Inv.inv (Real.log x) +
          (x ^ ((1 / 2 : Real) - (n : Real)) *
              Inv.inv ((Real.log x) ^ (2 : Nat)) +
            2 *
              ((-x ^ ((1 / 2 : Real) - (n : Real)) /
                    ((1 / 2 : Real) - (n : Real))) *
                Inv.inv ((Real.log x) ^ (3 : Nat))))) := by
  have hReLt : rho.re < (n : Real) := by
    have hnReal : (1 : Real) <= (n : Real) := by
      exact_mod_cast hn
    rw [hRe]
    linarith
  have hLogPos : 0 < Real.log x := Real.log_pos hx
  have hCoefficient :=
    norm_nat_div_sub_div_le_robinXiZeroWeight hn hRho hRe
  have hFactorNorm :
      norm
          ((x : Complex) ^ (rho - (n : Complex)) *
            (((Inv.inv (Real.log x) : Real) : Complex))) =
        x ^ ((1 / 2 : Real) - (n : Real)) * Inv.inv (Real.log x) := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos
      (lt_trans Real.zero_lt_one hx), Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hLogPos)]
    simp only [Complex.sub_re, Complex.natCast_re, hRe]
  have hMain :
      norm
          ((((n : Complex) / ((n : Complex) - rho)) *
              (x : Complex) ^ (rho - (n : Complex)) *
              (((Inv.inv (Real.log x) : Real) : Complex))) / rho) <=
        (Inv.inv (norm rho)) ^ (2 : Nat) *
          ((n : Real) * x ^ ((1 / 2 : Real) - (n : Real)) *
            Inv.inv (Real.log x)) := by
    have hRewrite :
        (((n : Complex) / ((n : Complex) - rho)) *
              (x : Complex) ^ (rho - (n : Complex)) *
              (((Inv.inv (Real.log x) : Real) : Complex))) / rho =
          (((n : Complex) / ((n : Complex) - rho)) / rho) *
            ((x : Complex) ^ (rho - (n : Complex)) *
              (((Inv.inv (Real.log x) : Real) : Complex))) := by
      ring
    rw [hRewrite, norm_mul, hFactorNorm]
    have hFactorNonneg :
        0 <= x ^ ((1 / 2 : Real) - (n : Real)) * Inv.inv (Real.log x) :=
      mul_nonneg (Real.rpow_nonneg (le_of_lt (lt_trans Real.zero_lt_one hx)) _)
        (inv_nonneg.mpr hLogPos.le)
    calc
      norm (((n : Complex) / ((n : Complex) - rho)) / rho) *
          (x ^ ((1 / 2 : Real) - (n : Real)) * Inv.inv (Real.log x)) <=
        ((n : Real) * (Inv.inv (norm rho)) ^ (2 : Nat)) *
          (x ^ ((1 / 2 : Real) - (n : Real)) * Inv.inv (Real.log x)) :=
        mul_le_mul_of_nonneg_right hCoefficient hFactorNonneg
      _ = (Inv.inv (norm rho)) ^ (2 : Nat) *
          ((n : Real) * x ^ ((1 / 2 : Real) - (n : Real)) *
            Inv.inv (Real.log x)) := by ring
  have hRemainder :=
    norm_robinZeroKernelRemainder_div_rho_le hn hRho hRe hx
  rw [robinZeroKernel_eq_main_add_remainder hn hx hReLt, add_div]
  calc
    norm
        ((((n : Complex) / ((n : Complex) - rho)) *
              (x : Complex) ^ (rho - (n : Complex)) *
              (((Inv.inv (Real.log x) : Real) : Complex))) / rho +
          robinZeroKernelRemainder n rho x / rho) <=
        norm
            ((((n : Complex) / ((n : Complex) - rho)) *
                (x : Complex) ^ (rho - (n : Complex)) *
                (((Inv.inv (Real.log x) : Real) : Complex))) / rho) +
          norm (robinZeroKernelRemainder n rho x / rho) :=
      norm_add_le _ _
    _ <= (Inv.inv (norm rho)) ^ (2 : Nat) *
          ((n : Real) * x ^ ((1 / 2 : Real) - (n : Real)) *
            Inv.inv (Real.log x)) +
        (Inv.inv (norm rho)) ^ (2 : Nat) *
          (x ^ ((1 / 2 : Real) - (n : Real)) *
              Inv.inv ((Real.log x) ^ (2 : Nat)) +
            2 *
              ((-x ^ ((1 / 2 : Real) - (n : Real)) /
                    ((1 / 2 : Real) - (n : Real))) *
                Inv.inv ((Real.log x) ^ (3 : Nat)))) :=
      add_le_add hMain hRemainder
    _ = _ := by ring

end

end Robin1984
