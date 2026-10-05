/-
Source port from Robin1984 bfa72aec0c25c8ee29cefe4449d778ff30412bee.
Original file: Robin1984/Analytic/RiemannZetaRealNonzero.lean
Original source lines 472-742. Apache-2.0.
Statements and proof bodies retained; split at existing declaration boundaries.
-/
import PrimeFactorOscillations.Helpers.Robin1984.Analytic.RiemannZetaRealEuler

/-!
# Uniform majorants across the real critical interval

A source-preserving component of the written Nicolas/Landau/Mellin proof.
-/

namespace Robin1984

open Filter MeasureTheory Set

noncomputable section

theorem norm_nicolasJShiftNumeratorFilled_le_threeQuarter
    {u : Real} (hu : 1 < u) {z : Complex}
    (hz : Membership.mem (Metric.closedBall (0 : Complex) (3 / 4 : Real)) z) :
    norm (nicolasJShiftNumeratorFilled u z) <=
      5 * (Real.log 4 + 5) *
        (3 : Real) ^ (-u + (3 / 4 : Real)) := by
  have hzNorm : norm z <= (3 / 4 : Real) := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz
  have hzRe : z.re <= (3 / 4 : Real) :=
    (Complex.re_le_norm z).trans hzNorm
  let s0 : Complex := ((u + 1 : Real) : Complex)
  let s1 : Complex := s0 - z
  have hs0 : 1 < s0.re := by
    dsimp [s0]
    linarith
  have hs1 : 1 < s1.re := by
    dsimp [s1, s0]
    linarith
  have hDen1 : (1 / 4 : Real) < s1.re - 1 := by
    dsimp [s1, s0]
    linarith
  have hShiftRaw := norm_nicolasPsiMellinTailContinuationFilled_le hs1
  have hShiftNumerator : (3 : Real) ^ (1 - s1.re) <=
      (3 : Real) ^ (-u + (3 / 4 : Real)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    dsimp [s1, s0]
    linarith
  have hShiftPowerNonneg : 0 <= (3 : Real) ^ (1 - s1.re) :=
    Real.rpow_nonneg (by norm_num) _
  have hShiftFraction : (3 : Real) ^ (1 - s1.re) / (s1.re - 1) <=
      4 * (3 : Real) ^ (-u + (3 / 4 : Real)) := by
    calc
      (3 : Real) ^ (1 - s1.re) / (s1.re - 1) <=
          (3 : Real) ^ (1 - s1.re) / (1 / 4 : Real) :=
        div_le_div_of_nonneg_left hShiftPowerNonneg (by norm_num) hDen1.le
      _ = 4 * (3 : Real) ^ (1 - s1.re) := by ring
      _ <= 4 * (3 : Real) ^ (-u + (3 / 4 : Real)) :=
        mul_le_mul_of_nonneg_left hShiftNumerator (by norm_num)
  have hShift : norm (nicolasPsiMellinTailContinuationFilled s1) <=
      4 * (Real.log 4 + 5) *
        (3 : Real) ^ (-u + (3 / 4 : Real)) := by
    calc
      norm (nicolasPsiMellinTailContinuationFilled s1) <=
          (Real.log 4 + 5) *
            ((3 : Real) ^ (1 - s1.re) / (s1.re - 1)) := hShiftRaw
      _ <= (Real.log 4 + 5) *
          (4 * (3 : Real) ^ (-u + (3 / 4 : Real))) :=
        mul_le_mul_of_nonneg_left hShiftFraction (by positivity)
      _ = 4 * (Real.log 4 + 5) *
          (3 : Real) ^ (-u + (3 / 4 : Real)) := by ring
  have hBaseRaw := norm_nicolasPsiMellinTailContinuationFilled_le hs0
  have hBase : norm (nicolasPsiMellinTailContinuationFilled s0) <=
      (Real.log 4 + 5) * (3 : Real) ^ (-u) := by
    have huPos : 0 < u := lt_trans zero_lt_one hu
    have hPowNonneg : 0 <= (3 : Real) ^ (-u) :=
      Real.rpow_nonneg (by norm_num) _
    have hS0Exponent : 1 - s0.re = -u := by
      dsimp [s0]
      ring
    have hS0Denominator : s0.re - 1 = u := by
      dsimp [s0]
      ring
    rw [hS0Exponent, hS0Denominator] at hBaseRaw
    calc
      norm (nicolasPsiMellinTailContinuationFilled s0) <=
          (Real.log 4 + 5) * ((3 : Real) ^ (-u) / u) := hBaseRaw
      _ <= (Real.log 4 + 5) * ((3 : Real) ^ (-u) / 1) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left hPowNonneg zero_lt_one hu.le)
          (by positivity)
      _ = (Real.log 4 + 5) * (3 : Real) ^ (-u) := by ring
  have hPowerNorm : norm ((3 : Complex) ^ z) =
      (3 : Real) ^ z.re := by
    change norm (((3 : Real) : Complex) ^ z) =
      (3 : Real) ^ z.re
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
  have hPowerProduct : norm ((3 : Complex) ^ z *
      nicolasPsiMellinTailContinuationFilled s0) <=
      (Real.log 4 + 5) *
        (3 : Real) ^ (-u + (3 / 4 : Real)) := by
    rw [norm_mul, hPowerNorm]
    calc
      (3 : Real) ^ z.re *
          norm (nicolasPsiMellinTailContinuationFilled s0) <=
          (3 : Real) ^ z.re *
            ((Real.log 4 + 5) * (3 : Real) ^ (-u)) :=
        mul_le_mul_of_nonneg_left hBase
          (Real.rpow_nonneg (by norm_num) _)
      _ = (Real.log 4 + 5) *
          ((3 : Real) ^ z.re * (3 : Real) ^ (-u)) := by ring
      _ = (Real.log 4 + 5) * (3 : Real) ^ (z.re + (-u)) := by
        rw [Real.rpow_add (by norm_num : (0 : Real) < 3)]
      _ = (Real.log 4 + 5) * (3 : Real) ^ (z.re - u) := by
        congr 2
      _ <= (Real.log 4 + 5) *
          (3 : Real) ^ (-u + (3 / 4 : Real)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        linarith
  unfold nicolasJShiftNumeratorFilled
  change norm (nicolasPsiMellinTailContinuationFilled s1 -
      (3 : Complex) ^ z * nicolasPsiMellinTailContinuationFilled s0) <= _
  calc
    norm (nicolasPsiMellinTailContinuationFilled s1 -
        (3 : Complex) ^ z * nicolasPsiMellinTailContinuationFilled s0) <=
        norm (nicolasPsiMellinTailContinuationFilled s1) +
          norm ((3 : Complex) ^ z *
            nicolasPsiMellinTailContinuationFilled s0) := norm_sub_le _ _
    _ <= 4 * (Real.log 4 + 5) *
          (3 : Real) ^ (-u + (3 / 4 : Real)) +
        (Real.log 4 + 5) *
          (3 : Real) ^ (-u + (3 / 4 : Real)) :=
      add_le_add hShift hPowerProduct
    _ = 5 * (Real.log 4 + 5) *
        (3 : Real) ^ (-u + (3 / 4 : Real)) := by ring

theorem nicolasJShiftNumeratorFilled_differentiableOn_threeQuarter
    {u : Real} (hu : 1 < u) :
    DifferentiableOn Complex (nicolasJShiftNumeratorFilled u)
      (Metric.ball (0 : Complex) (3 / 4 : Real)) := by
  intro z hz
  have hzNorm : norm z < (3 / 4 : Real) := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hzRe : z.re < (3 / 4 : Real) :=
    (Complex.re_le_norm z).trans_lt hzNorm
  let s0 : Complex := ((u + 1 : Real) : Complex)
  let s1 : Complex := s0 - z
  have hs1 : 1 < s1.re := by
    dsimp [s1, s0]
    linarith
  have hTail : AnalyticAt Complex
      nicolasPsiMellinTailContinuationFilled s1 :=
    nicolasPsiMellinTailContinuationFilled_analyticAt_of_one_lt_re hs1
  have hAffine : AnalyticAt Complex (fun w : Complex => s0 - w) z :=
    analyticAt_const.sub analyticAt_id
  have hShift : AnalyticAt Complex (fun w : Complex =>
      nicolasPsiMellinTailContinuationFilled (s0 - w)) z := by
    have hComp := hTail.comp_of_eq hAffine (by dsimp [s1])
    apply hComp.congr
    exact Eventually.of_forall (fun _ => rfl)
  have hPowerDifferentiable : Differentiable Complex
      (fun w : Complex => (3 : Complex) ^ w) := by
    intro w
    exact DifferentiableAt.const_cpow differentiableAt_id
      (Or.inl (by norm_num))
  have hPower : AnalyticAt Complex
      (fun w : Complex => (3 : Complex) ^ w) z :=
    hPowerDifferentiable.analyticAt z
  have hTailConst : AnalyticAt Complex (fun _ : Complex =>
      nicolasPsiMellinTailContinuationFilled s0) z := analyticAt_const
  unfold nicolasJShiftNumeratorFilled
  change DifferentiableWithinAt Complex (fun w : Complex =>
      nicolasPsiMellinTailContinuationFilled (s0 - w) -
        (3 : Complex) ^ w *
          nicolasPsiMellinTailContinuationFilled s0)
    (Metric.ball (0 : Complex) (3 / 4 : Real)) z
  exact (hShift.sub (hPower.mul hTailConst)).differentiableAt.differentiableWithinAt

theorem norm_nicolasJMellinShiftIntegrandFilled_le_threeQuarter
    {u : Real} (hu : 1 < u) {z : Complex}
    (hz : Membership.mem (Metric.ball (0 : Complex) (3 / 4 : Real)) z) :
    norm (nicolasJMellinShiftIntegrandFilled z u) <=
      (20 / 3 : Real) * (Real.log 4 + 5) * (u + 1) *
        (3 : Real) ^ (-u + (3 / 4 : Real)) := by
  let R : Real := 3 / 4
  let M : Real := 5 * (Real.log 4 + 5) *
    (3 : Real) ^ (-u + (3 / 4 : Real))
  have hMaps : MapsTo (nicolasJShiftNumeratorFilled u)
      (Metric.ball (0 : Complex) R)
      (Metric.closedBall (nicolasJShiftNumeratorFilled u 0) M) := by
    intro w hw
    rw [nicolasJShiftNumeratorFilled_zero]
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_nicolasJShiftNumeratorFilled_le_threeQuarter hu
      (Metric.ball_subset_closedBall hw)
  have hDslope := Complex.norm_dslope_le_div_of_mapsTo_ball
    (nicolasJShiftNumeratorFilled_differentiableOn_threeQuarter hu)
    hMaps hz
  have huOnePos : 0 < u + 1 := by linarith
  unfold nicolasJMellinShiftIntegrandFilled
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos huOnePos]
  calc
    (u + 1) * norm (dslope (nicolasJShiftNumeratorFilled u) 0 z) <=
        (u + 1) * (M / R) :=
      mul_le_mul_of_nonneg_left hDslope huOnePos.le
    _ = (20 / 3 : Real) * (Real.log 4 + 5) * (u + 1) *
        (3 : Real) ^ (-u + (3 / 4 : Real)) := by
      dsimp [M, R]
      ring

def nicolasJLargeMajorantHalf (u : Real) : Real :=
  (20 / 3 : Real) * (Real.log 4 + 5) * (u + 1) *
    (3 : Real) ^ (-u + (3 / 4 : Real))

theorem nicolasJLargeMajorantHalf_integrableOn :
    IntegrableOn nicolasJLargeMajorantHalf (Ioi (1 : Real)) := by
  have hLog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hExp : IntegrableOn
      (fun u : Real => Real.exp (-(Real.log 3) * u))
      (Ioi (1 : Real)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : Real)) (s := (0 : Real)) (b := Real.log 3)
      (by norm_num) (by norm_num) hLog
    have hSubset : Ioi (1 : Real) <= Ioi (0 : Real) := by
      intro u hu
      exact zero_lt_one.trans (mem_Ioi.mp hu)
    apply (h.mono_set hSubset).congr_fun _ measurableSet_Ioi
    intro u hu
    simp
  have hUExp : IntegrableOn
      (fun u : Real => u * Real.exp (-(Real.log 3) * u))
      (Ioi (1 : Real)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : Real)) (s := (1 : Real)) (b := Real.log 3)
      (by norm_num) (by norm_num) hLog
    have hSubset : Ioi (1 : Real) <= Ioi (0 : Real) := by
      intro u hu
      exact zero_lt_one.trans (mem_Ioi.mp hu)
    apply (h.mono_set hSubset).congr_fun _ measurableSet_Ioi
    intro u hu
    simp
  have hLinear : IntegrableOn
      (fun u : Real => (u + 1) * Real.exp (-(Real.log 3) * u))
      (Ioi (1 : Real)) := by
    apply (hUExp.add hExp).congr_fun _ measurableSet_Ioi
    intro u hu
    change u * Real.exp (-(Real.log 3) * u) +
      Real.exp (-(Real.log 3) * u) =
        (u + 1) * Real.exp (-(Real.log 3) * u)
    ring
  have hScaled : IntegrableOn
      (fun u : Real =>
        ((20 / 3 : Real) * (Real.log 4 + 5) *
            Real.exp (3 * Real.log 3 / 4)) *
          ((u + 1) * Real.exp (-(Real.log 3) * u)))
      (Ioi (1 : Real)) :=
    hLinear.const_mul
      ((20 / 3 : Real) * (Real.log 4 + 5) *
        Real.exp (3 * Real.log 3 / 4))
  apply hScaled.congr_fun _ measurableSet_Ioi
  intro u hu
  unfold nicolasJLargeMajorantHalf
  rw [Real.rpow_def_of_pos (by norm_num : (0 : Real) < 3)]
  rw [show Real.log 3 * (-u + (3 / 4 : Real)) =
      3 * Real.log 3 / 4 + (-(Real.log 3) * u) by ring]
  rw [Real.exp_add]
  ring

theorem nicolasJMellinShiftIntegrandFilled_differentiableOn_threeQuarter
    {u : Real} (hu : 1 < u) :
    DifferentiableOn Complex
      (fun z : Complex => nicolasJMellinShiftIntegrandFilled z u)
      (Metric.ball (0 : Complex) (3 / 4 : Real)) := by
  intro z hz
  by_cases hzZero : z = 0
  case pos =>
    subst z
    exact (nicolasJMellinShiftIntegrandFilled_analyticAt_zero
      (by linarith)).differentiableAt.differentiableWithinAt
  case neg =>
    have hNumeratorAt : DifferentiableAt Complex
        (nicolasJShiftNumeratorFilled u) z :=
      (nicolasJShiftNumeratorFilled_differentiableOn_threeQuarter
        hu z hz).differentiableAt
        (Metric.isOpen_ball.mem_nhds hz)
    have hDslopeAt : DifferentiableAt Complex
        (dslope (nicolasJShiftNumeratorFilled u) 0) z :=
      (differentiableAt_dslope_of_ne hzZero).2 hNumeratorAt
    unfold nicolasJMellinShiftIntegrandFilled
    exact (analyticAt_const.differentiableAt.mul hDslopeAt).differentiableWithinAt

end

end Robin1984

