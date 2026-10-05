/-
Source port from Robin1984 bfa72aec0c25c8ee29cefe4449d778ff30412bee.
Original file: Robin1984/NicolasLandau/WeightedMellin.lean
Original source lines 26-424. Apache-2.0.
Statements and proof bodies retained; only the required declaration block is selected.
-/
import Mathlib.Analysis.MellinInversion
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.RobinWeightedIntegral

/-!
# The cutoff test and absolute Mellin inversion

Part of the written RH negative-envelope argument.
-/

namespace Robin1984

noncomputable section

open Complex MeasureTheory Set

/-- The sharp continuous test whose prime-power sum is Robin's weighted
Chebyshev integral. -/
def robinCutoffMellinTest (n : Nat) (x t : Real) : Complex :=
  if t <= x then
    (x : Complex) ^ (-(n : Complex)) *
      (((Inv.inv (Real.log x) : Real) : Complex))
  else
    (t : Complex) ^ (-(n : Complex)) *
      (((Inv.inv (Real.log t) : Real) : Complex))

theorem continuous_robinCutoffMellinTest
    (n : Nat) {x : Real} (hx : 1 < x) :
    Continuous (robinCutoffMellinTest n x) := by
  unfold robinCutoffMellinTest
  apply continuous_if_le continuous_id continuous_const
  . exact continuous_const.continuousOn
  . intro t ht
    have htOne : 1 < t := lt_of_lt_of_le hx ht
    have htZero : Not (t = 0) :=
      ne_of_gt (lt_trans Real.zero_lt_one htOne)
    have hLogZero : Not (Real.log t = 0) :=
      ne_of_gt (Real.log_pos htOne)
    have hPower : ContinuousAt (fun y : Real =>
        (y : Complex) ^ (-(n : Complex))) t :=
      Complex.continuousAt_ofReal_cpow_const t (-(n : Complex)) (Or.inr htZero)
    have hLogInv : ContinuousAt (fun y : Real => Inv.inv (Real.log y)) t :=
      ((Real.hasDerivAt_log htZero).inv hLogZero).continuousAt
    exact (hPower.mul
      (Complex.continuous_ofReal.continuousAt.comp hLogInv)).continuousWithinAt
  . intro t ht
    dsimp at ht
    rw [ht]

theorem robinCutoffMellinIntegrand_eq_lower
    (n : Nat) (s : Complex) {x t : Real} (ht : t <= x) :
    (t : Complex) ^ (s - 1) * robinCutoffMellinTest n x t =
      (t : Complex) ^ (s - 1) *
        ((x : Complex) ^ (-(n : Complex)) *
          (((Inv.inv (Real.log x) : Real) : Complex))) := by
  simp only [robinCutoffMellinTest, if_pos ht]

theorem robinCutoffMellinIntegrand_eq_upper
    (n : Nat) (s : Complex) {x t : Real} (hx : 1 < x) (ht : x < t) :
    (t : Complex) ^ (s - 1) * robinCutoffMellinTest n x t =
      (t : Complex) ^ (s - (n : Complex) - 1) *
        (((Inv.inv (Real.log t) : Real) : Complex)) := by
  have htZero : Not ((t : Complex) = 0) :=
    Complex.ofReal_ne_zero.mpr
      (ne_of_gt (lt_trans (lt_trans Real.zero_lt_one hx) ht))
  simp only [robinCutoffMellinTest, if_neg (not_le.mpr ht)]
  rw [<- mul_assoc, <- Complex.cpow_add (s - 1) (-(n : Complex)) htZero]
  congr 1
  congr 1
  ring

theorem mellinConvergent_robinCutoffMellinTest
    {n : Nat} {s : Complex} {x : Real} (hx : 1 < x)
    (hsPos : 0 < s.re) (hsLt : s.re < n) :
    MellinConvergent (robinCutoffMellinTest n x) s := by
  have hxPos : 0 < x := lt_trans Real.zero_lt_one hx
  have hLowExponent : -1 < (s - 1).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hHighExponent : (s - (n : Complex) - 1).re < -1 := by
    simp only [Complex.sub_re, Complex.natCast_re, Complex.one_re]
    linarith
  have hLowBase :
      IntegrableOn (fun t : Real => (t : Complex) ^ (s - 1)) (Ioc 0 x) := by
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hxPos.le).mp
      (intervalIntegral.intervalIntegrable_cpow' hLowExponent)
  have hLow :
      IntegrableOn (fun t : Real =>
        (t : Complex) ^ (s - 1) * robinCutoffMellinTest n x t) (Ioc 0 x) := by
    have hLowScaled :
        IntegrableOn (fun t : Real =>
          (t : Complex) ^ (s - 1) *
            ((x : Complex) ^ (-(n : Complex)) *
              (((Inv.inv (Real.log x) : Real) : Complex)))) (Ioc 0 x) :=
      hLowBase.mul_const _
    exact hLowScaled.congr_fun
      (fun t ht => (robinCutoffMellinIntegrand_eq_lower n s ht.2).symm)
      measurableSet_Ioc
  have hHighBase :
      IntegrableOn (fun t : Real =>
        (t : Complex) ^ (s - (n : Complex) - 1) *
          (((Inv.inv (Real.log t) : Real) : Complex))) (Ioi x) := by
    simpa using integrableOn_cpow_div_log_pow hx hHighExponent 1
  have hHigh :
      IntegrableOn (fun t : Real =>
        (t : Complex) ^ (s - 1) * robinCutoffMellinTest n x t) (Ioi x) := by
    exact hHighBase.congr_fun
      (fun t ht => (robinCutoffMellinIntegrand_eq_upper n s hx ht).symm)
      measurableSet_Ioi
  unfold MellinConvergent
  simp only [smul_eq_mul]
  rw [<- Ioc_union_Ioi_eq_Ioi hxPos.le]
  exact hLow.union hHigh

/-- The exact cutoff transform, in the strip where both endpoint blocks are
integrable. -/
theorem mellin_robinCutoffMellinTest_eq_zeroKernel_div
    {n : Nat} {s : Complex} {x : Real} (hx : 1 < x)
    (hsPos : 0 < s.re) (hsLt : s.re < n) :
    mellin (robinCutoffMellinTest n x) s = robinZeroKernel n s x / s := by
  have hxPos : 0 < x := lt_trans Real.zero_lt_one hx
  have hxZero : Not ((x : Complex) = 0) :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hxPos)
  have hsZero : Not (s = 0) := by
    intro h
    rw [h] at hsPos
    norm_num at hsPos
  have hLogZero : Not (Real.log x = 0) := ne_of_gt (Real.log_pos hx)
  have hConv := mellinConvergent_robinCutoffMellinTest hx hsPos hsLt
  have hIntegrable :
      IntegrableOn (fun t : Real =>
        (t : Complex) ^ (s - 1) * robinCutoffMellinTest n x t) (Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul] using hConv
  have hLow := hIntegrable.mono_set (Ioc_subset_Ioi_self : Ioc 0 x <= Ioi 0)
  have hHigh := hIntegrable.mono_set (Ioi_subset_Ioi hxPos.le)
  unfold mellin
  simp only [smul_eq_mul]
  rw [<- Ioc_union_Ioi_eq_Ioi hxPos.le,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hLow hHigh]
  have hLower :
      integral (volume.restrict (Ioc 0 x)) (fun t : Real =>
          (t : Complex) ^ (s - 1) * robinCutoffMellinTest n x t) =
        (x : Complex) ^ (s - (n : Complex)) /
          (s * ((Real.log x : Real) : Complex)) := by
    calc
      integral (volume.restrict (Ioc 0 x)) (fun t : Real =>
          (t : Complex) ^ (s - 1) * robinCutoffMellinTest n x t) =
          integral (volume.restrict (Ioc 0 x)) (fun t : Real =>
            (t : Complex) ^ (s - 1) *
              ((x : Complex) ^ (-(n : Complex)) *
                (((Inv.inv (Real.log x) : Real) : Complex)))) := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro t ht
        exact robinCutoffMellinIntegrand_eq_lower n s ht.2
      _ = ((x : Complex) ^ s / s) *
          ((x : Complex) ^ (-(n : Complex)) *
            (((Inv.inv (Real.log x) : Real) : Complex))) := by
        rw [integral_mul_const,
          <- intervalIntegral.integral_of_le hxPos.le,
          integral_cpow (Or.inl (by
            simp only [Complex.sub_re, Complex.one_re]
            linarith : -1 < (s - 1).re))]
        rw [show s - 1 + 1 = s by ring]
        simp only [Complex.ofReal_zero, Complex.zero_cpow hsZero, sub_zero]
      _ = ((x : Complex) ^ s * (x : Complex) ^ (-(n : Complex))) /
          (s * ((Real.log x : Real) : Complex)) := by
        push_cast
        field_simp [hsZero, hLogZero]
      _ = (x : Complex) ^ (s - (n : Complex)) /
          (s * ((Real.log x : Real) : Complex)) := by
        rw [<- Complex.cpow_add s (-(n : Complex)) hxZero]
        congr 2
  have hUpper :
      integral (volume.restrict (Ioi x)) (fun t : Real =>
          (t : Complex) ^ (s - 1) * robinCutoffMellinTest n x t) =
        robinCpowLogTail (s - (n : Complex)) 1 x := by
    unfold robinCpowLogTail
    simp only [pow_one]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    exact robinCutoffMellinIntegrand_eq_upper n s hx ht
  rw [hLower, hUpper]
  exact (robinZeroKernel_div_rho_eq_boundary_div_add_tail_one hsZero hx hsLt).symm

/-- The inverse-square norm on a nonzero vertical line is integrable. -/
theorem integrable_inverseSquare_verticalLine
    {a : Real} (ha : Not (a = 0)) :
    Integrable (fun t : Real =>
      (Inv.inv (norm ((a : Complex) + (t : Complex) * Complex.I))) ^ (2 : Nat)) := by
  have hScaled :
      Integrable (fun t : Real => Inv.inv (1 + (t / a) ^ (2 : Nat))) :=
    integrable_inv_one_add_sq.comp_div ha
  have hMajor :
      Integrable (fun t : Real =>
        Inv.inv (1 + (t / a) ^ (2 : Nat)) * Inv.inv (a ^ (2 : Nat))) :=
    hScaled.mul_const _
  apply hMajor.congr
  filter_upwards with t
  have hNormSq :
      norm ((a : Complex) + (t : Complex) * Complex.I) ^ (2 : Nat) =
        a ^ (2 : Nat) + t ^ (2 : Nat) := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hSumPos : 0 < a ^ (2 : Nat) + t ^ (2 : Nat) := by
    exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero ha) (sq_nonneg t)
  rw [inv_pow, hNormSq]
  field_simp [ha, ne_of_gt hSumPos]

/-- A fixed-real-part remainder bound, used for absolute Mellin inversion
strictly inside the convergence strip. -/
theorem norm_robinZeroKernelRemainder_bracket_le_re
    {n : Nat} {s : Complex} {x : Real} (hx : 1 < x) (hs : s.re < n) :
    norm
        (-((x : Complex) ^ (s - (n : Complex))) /
            ((Real.log x : Real) : Complex) ^ (2 : Nat) +
          2 * robinCpowLogTail (s - (n : Complex)) 3 x) <=
      x ^ (s.re - (n : Real)) * Inv.inv ((Real.log x) ^ (2 : Nat)) +
        2 * ((-x ^ (s.re - (n : Real)) / (s.re - (n : Real))) *
          Inv.inv ((Real.log x) ^ (3 : Nat))) := by
  have hxPos : 0 < x := lt_trans Real.zero_lt_one hx
  have hLogPos : 0 < Real.log x := Real.log_pos hx
  have haRe : (s - (n : Complex)).re < 0 := by
    simp only [Complex.sub_re, Complex.natCast_re]
    linarith
  have hMainNorm :
      norm
          (-((x : Complex) ^ (s - (n : Complex))) /
            ((Real.log x : Real) : Complex) ^ (2 : Nat)) =
        x ^ (s.re - (n : Real)) * Inv.inv ((Real.log x) ^ (2 : Nat)) := by
    rw [norm_div, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hxPos,
      norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hLogPos]
    simp only [Complex.sub_re, Complex.natCast_re]
    rw [div_eq_mul_inv]
  have hTail :
      norm (robinCpowLogTail (s - (n : Complex)) 3 x) <=
        (-x ^ (s.re - (n : Real)) / (s.re - (n : Real))) *
          Inv.inv ((Real.log x) ^ (3 : Nat)) := by
    simpa only [Complex.sub_re, Complex.natCast_re] using
      norm_robinCpowLogTail_le hx haRe 3
  calc
    norm
        (-((x : Complex) ^ (s - (n : Complex))) /
            ((Real.log x : Real) : Complex) ^ (2 : Nat) +
          2 * robinCpowLogTail (s - (n : Complex)) 3 x) <=
        norm (-((x : Complex) ^ (s - (n : Complex))) /
          ((Real.log x : Real) : Complex) ^ (2 : Nat)) +
          norm (2 * robinCpowLogTail (s - (n : Complex)) 3 x) :=
      norm_add_le _ _
    _ = x ^ (s.re - (n : Real)) * Inv.inv ((Real.log x) ^ (2 : Nat)) +
        2 * norm (robinCpowLogTail (s - (n : Complex)) 3 x) := by
      rw [hMainNorm, norm_mul]
      norm_num
    _ <= _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hTail zero_le_two)

theorem norm_nat_div_sub_div_le_inverseSquares
    (n : Nat) (s : Complex) :
    norm (((n : Complex) / ((n : Complex) - s)) / s) <=
      ((n : Real) / 2) *
        ((Inv.inv (norm s)) ^ (2 : Nat) +
          (Inv.inv (norm (s - (n : Complex)))) ^ (2 : Nat)) := by
  have hOppNorm :
      norm ((n : Complex) - s) = norm (s - (n : Complex)) := by
    rw [show (n : Complex) - s = -(s - (n : Complex)) by ring, norm_neg]
  have hAM :
      Inv.inv (norm (s - (n : Complex))) * Inv.inv (norm s) <=
        ((Inv.inv (norm s)) ^ (2 : Nat) +
          (Inv.inv (norm (s - (n : Complex)))) ^ (2 : Nat)) / 2 := by
    nlinarith [sq_nonneg
      (Inv.inv (norm s) - Inv.inv (norm (s - (n : Complex))))]
  rw [norm_div, norm_div, Complex.norm_natCast, hOppNorm]
  calc
    (n : Real) / norm (s - (n : Complex)) / norm s =
        (n : Real) *
          (Inv.inv (norm (s - (n : Complex))) * Inv.inv (norm s)) := by ring
    _ <= (n : Real) *
        (((Inv.inv (norm s)) ^ (2 : Nat) +
          (Inv.inv (norm (s - (n : Complex)))) ^ (2 : Nat)) / 2) :=
      mul_le_mul_of_nonneg_left hAM (Nat.cast_nonneg n)
    _ = _ := by ring

/-- The exact decomposition yields an integrable inverse-square majorant on
each fixed vertical line in the convergence strip. -/
theorem norm_robinZeroKernel_div_le_inverseSquares
    {n : Nat} (hn : 1 <= n) {s : Complex} (hsZero : Not (s = 0))
    {x : Real} (hx : 1 < x) (hs : s.re < n) :
    norm (robinZeroKernel n s x / s) <=
      (((n : Real) / 2) * x ^ (s.re - (n : Real)) * Inv.inv (Real.log x)) *
        ((Inv.inv (norm s)) ^ (2 : Nat) +
          (Inv.inv (norm (s - (n : Complex)))) ^ (2 : Nat)) +
      (x ^ (s.re - (n : Real)) * Inv.inv ((Real.log x) ^ (2 : Nat)) +
        2 * ((-x ^ (s.re - (n : Real)) / (s.re - (n : Real))) *
          Inv.inv ((Real.log x) ^ (3 : Nat)))) *
        (Inv.inv (norm (s - (n : Complex)))) ^ (2 : Nat) := by
  have hxPos : 0 < x := lt_trans Real.zero_lt_one hx
  have hLogPos : 0 < Real.log x := Real.log_pos hx
  have hFactorNorm :
      norm ((x : Complex) ^ (s - (n : Complex)) *
        (((Inv.inv (Real.log x) : Real) : Complex))) =
        x ^ (s.re - (n : Real)) * Inv.inv (Real.log x) := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxPos,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hLogPos)]
    simp only [Complex.sub_re, Complex.natCast_re]
  have hFactorNonneg : 0 <= x ^ (s.re - (n : Real)) * Inv.inv (Real.log x) :=
    mul_nonneg (Real.rpow_nonneg hxPos.le _) (inv_nonneg.mpr hLogPos.le)
  have hMain :
      norm ((((n : Complex) / ((n : Complex) - s)) *
          (x : Complex) ^ (s - (n : Complex)) *
          (((Inv.inv (Real.log x) : Real) : Complex))) / s) <=
        (((n : Real) / 2) * x ^ (s.re - (n : Real)) * Inv.inv (Real.log x)) *
          ((Inv.inv (norm s)) ^ (2 : Nat) +
            (Inv.inv (norm (s - (n : Complex)))) ^ (2 : Nat)) := by
    have hRewrite :
        (((n : Complex) / ((n : Complex) - s)) *
            (x : Complex) ^ (s - (n : Complex)) *
            (((Inv.inv (Real.log x) : Real) : Complex))) / s =
          (((n : Complex) / ((n : Complex) - s)) / s) *
            ((x : Complex) ^ (s - (n : Complex)) *
              (((Inv.inv (Real.log x) : Real) : Complex))) := by ring
    rw [hRewrite, norm_mul, hFactorNorm]
    calc
      norm (((n : Complex) / ((n : Complex) - s)) / s) *
          (x ^ (s.re - (n : Real)) * Inv.inv (Real.log x)) <=
          (((n : Real) / 2) *
            ((Inv.inv (norm s)) ^ (2 : Nat) +
              (Inv.inv (norm (s - (n : Complex)))) ^ (2 : Nat))) *
            (x ^ (s.re - (n : Real)) * Inv.inv (Real.log x)) :=
        mul_le_mul_of_nonneg_right
          (norm_nat_div_sub_div_le_inverseSquares n s) hFactorNonneg
      _ = _ := by ring
  have hRem :
      norm (robinZeroKernelRemainder n s x / s) <=
        (x ^ (s.re - (n : Real)) * Inv.inv ((Real.log x) ^ (2 : Nat)) +
          2 * ((-x ^ (s.re - (n : Real)) / (s.re - (n : Real))) *
            Inv.inv ((Real.log x) ^ (3 : Nat)))) *
          (Inv.inv (norm (s - (n : Complex)))) ^ (2 : Nat) := by
    rw [robinZeroKernelRemainder_div_rho hsZero, norm_mul, norm_inv, norm_pow]
    have hB := norm_robinZeroKernelRemainder_bracket_le_re hx hs
    have h := mul_le_mul_of_nonneg_left hB
      (inv_nonneg.mpr (sq_nonneg (norm (s - (n : Complex)))))
    simpa only [inv_pow, mul_comm] using h
  rw [robinZeroKernel_eq_main_add_remainder hn hx hs, add_div]
  exact (norm_add_le _ _).trans (add_le_add hMain hRem)

/-- Absolute vertical integrability of the exact sharp cutoff transform. -/
theorem verticalIntegrable_mellin_robinCutoffMellinTest
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x)
    {c : Real} (hcPos : 0 < c) (hcLt : c < n) :
    Complex.VerticalIntegrable (mellin (robinCutoffMellinTest n x)) c := by
  let A : Real := ((n : Real) / 2) * x ^ (c - (n : Real)) * Inv.inv (Real.log x)
  let B : Real := x ^ (c - (n : Real)) * Inv.inv ((Real.log x) ^ (2 : Nat)) +
    2 * ((-x ^ (c - (n : Real)) / (c - (n : Real))) *
      Inv.inv ((Real.log x) ^ (3 : Nat)))
  have hcZero : Not (c = 0) := ne_of_gt hcPos
  have hcnZero : Not (c - (n : Real) = 0) := ne_of_lt (sub_neg.mpr hcLt)
  have hC := integrable_inverseSquare_verticalLine hcZero
  have hN := integrable_inverseSquare_verticalLine hcnZero
  have hMajor : Integrable (fun t : Real =>
      A *
          ((Inv.inv (norm ((c : Complex) + (t : Complex) * Complex.I))) ^ (2 : Nat) +
            (Inv.inv (norm (((c - (n : Real) : Real) : Complex) +
              (t : Complex) * Complex.I))) ^ (2 : Nat)) +
        B * (Inv.inv (norm (((c - (n : Real) : Real) : Complex) +
          (t : Complex) * Complex.I))) ^ (2 : Nat)) :=
    ((hC.add hN).const_mul A).add (hN.const_mul B)
  have hPowerMeas : Measurable (fun z : Prod Real Real =>
      (z.2 : Complex) ^ ((c : Complex) + (z.1 : Complex) * Complex.I - 1)) := by
    fun_prop
  have hTestMeas : Measurable (fun z : Prod Real Real => robinCutoffMellinTest n x z.2) :=
    (continuous_robinCutoffMellinTest n hx).measurable.comp measurable_snd
  have hJoint := (hPowerMeas.mul hTestMeas).stronglyMeasurable
  have hLineMeas : AEStronglyMeasurable (fun t : Real =>
      mellin (robinCutoffMellinTest n x) ((c : Complex) + (t : Complex) * Complex.I))
      volume := by
    have h : StronglyMeasurable (fun t : Real =>
        integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
          (u : Complex) ^ ((c : Complex) + (t : Complex) * Complex.I - 1) *
            robinCutoffMellinTest n x u)) := hJoint.integral_prod_right'
    simpa only [mellin, smul_eq_mul] using h.aestronglyMeasurable
  unfold Complex.VerticalIntegrable
  apply hMajor.mono' hLineMeas
  filter_upwards with t
  have hsRe : ((c : Complex) + (t : Complex) * Complex.I).re = c := by simp
  have hsZero : Not (((c : Complex) + (t : Complex) * Complex.I) = 0) := by
    intro h
    have hRe := congrArg Complex.re h
    rw [hsRe, Complex.zero_re] at hRe
    exact hcZero hRe
  have hsPos : 0 < ((c : Complex) + (t : Complex) * Complex.I).re := by
    rw [hsRe]
    exact hcPos
  have hsLt : ((c : Complex) + (t : Complex) * Complex.I).re < (n : Real) := by
    rw [hsRe]
    exact hcLt
  rw [mellin_robinCutoffMellinTest_eq_zeroKernel_div hx hsPos hsLt]
  have hBound := norm_robinZeroKernel_div_le_inverseSquares hn hsZero hx hsLt
  have hShift :
      (c : Complex) + (t : Complex) * Complex.I - (n : Complex) =
        ((c - (n : Real) : Real) : Complex) + (t : Complex) * Complex.I := by
    push_cast
    ring
  simpa only [hsRe, hShift, A, B] using hBound

/-- Absolute Mellin inversion for Robin's continuous cutoff test. -/
theorem mellinInv_mellin_robinCutoffMellinTest
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x)
    {c : Real} (hcPos : 0 < c) (hcLt : c < n)
    {t : Real} (ht : 0 < t) :
    mellinInv c (mellin (robinCutoffMellinTest n x)) t =
      robinCutoffMellinTest n x t := by
  apply mellinInv_mellin_eq c (robinCutoffMellinTest n x) ht
  . exact mellinConvergent_robinCutoffMellinTest hx
      (by simpa using hcPos) (by simpa using hcLt)
  . exact verticalIntegrable_mellin_robinCutoffMellinTest hn hx hcPos hcLt
  . exact (continuous_robinCutoffMellinTest n hx).continuousAt

end

end Robin1984
