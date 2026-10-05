/-
Source port from Robin1984 bfa72aec0c25c8ee29cefe4449d778ff30412bee.
Original file: Robin1984/NicolasLandau/RobinWeightedIntegral.lean
Original source lines 27-393. Apache-2.0.
Statements and proof bodies retained; split at existing declaration boundaries.
-/
import Robin1984.NicolasLandau.XiZeroConstant

/-!
# Robin's zero kernel and logarithmic tail

A source-preserving component of the written RH negative-envelope argument.
-/

namespace Robin1984

noncomputable section

open Complex MeasureTheory Set
open scoped BigOperators

/-- The complex zero kernel in Robin 1984, Lemma 1. -/
def robinZeroKernel (n : Nat) (rho : Complex) (x : Real) : Complex :=
  integral (volume.restrict (Ioi x)) (fun t : Real =>
    (t : Complex) ^ (rho - (n : Complex) - 1) *
      (((n : Real) * Real.log t + 1) /
        (Real.log t) ^ (2 : Nat) : Real))

/-- A negative complex power remains integrable after division by a fixed
positive power of `log` on a tail beginning above one. -/
theorem integrableOn_cpow_div_log_pow
    {a : Complex} {x : Real} (hx : 1 < x) (ha : a.re < -1)
    (k : Nat) :
    IntegrableOn (fun t : Real =>
      (t : Complex) ^ a *
        (((Inv.inv ((Real.log t) ^ k) : Real) : Complex))) (Ioi x) := by
  have hxPos : 0 < x := lt_trans Real.zero_lt_one hx
  have hBase :
      IntegrableOn (fun t : Real => (t : Complex) ^ a) (Ioi x) :=
    integrableOn_Ioi_cpow_of_lt ha hxPos
  have hLogPos : 0 < Real.log x := Real.log_pos hx
  apply hBase.mul_bdd (c := Inv.inv ((Real.log x) ^ k))
  . have hMeasReal :
        Measurable (fun t : Real => Inv.inv ((Real.log t) ^ k)) :=
      (Measurable.pow_const Real.measurable_log k).inv
    exact
      (Complex.continuous_ofReal.measurable.comp hMeasReal).aestronglyMeasurable
  . filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hxt : x <= t := ht.le
    have hLog : Real.log x <= Real.log t := Real.log_le_log hxPos hxt
    have hLogTPos : 0 < Real.log t := lt_of_lt_of_le hLogPos hLog
    have hPow : (Real.log x) ^ k <= (Real.log t) ^ k := by
      induction k with
      | zero => simp
      | succ k ih =>
          rw [pow_succ, pow_succ]
          exact mul_le_mul ih hLog hLogPos.le
            (pow_nonneg hLogTPos.le k)
    have hPowPos : 0 < (Real.log t) ^ k := pow_pos hLogTPos k
    have hPowXPos : 0 < (Real.log x) ^ k := pow_pos hLogPos k
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hPowPos)]
    simpa [one_div] using one_div_le_one_div_of_le hPowXPos hPow

/-- The logarithmically weighted complex-power tail. -/
def robinCpowLogTail (a : Complex) (k : Nat) (x : Real) : Complex :=
  integral (volume.restrict (Ioi x)) (fun t : Real =>
    (t : Complex) ^ (a - 1) *
      (((Inv.inv ((Real.log t) ^ k) : Real) : Complex)))

/-- The twice-integrated remainder in Robin 1984, Lemma 1. -/
def robinZeroKernelRemainder
    (n : Nat) (rho : Complex) (x : Real) : Complex :=
  rho / (rho - (n : Complex)) ^ (2 : Nat) *
    (-((x : Complex) ^ (rho - (n : Complex))) /
        ((Real.log x : Real) : Complex) ^ (2 : Nat) +
      2 * robinCpowLogTail (rho - (n : Complex)) 3 x)

/-- Dividing Robin's remainder by the zero removes its numerator exactly. -/
theorem robinZeroKernelRemainder_div_rho
    {n : Nat} {rho : Complex} {x : Real} (hRho : Not (rho = 0)) :
    robinZeroKernelRemainder n rho x / rho =
      Inv.inv ((rho - (n : Complex)) ^ (2 : Nat)) *
        (-((x : Complex) ^ (rho - (n : Complex))) /
            ((Real.log x : Real) : Complex) ^ (2 : Nat) +
          2 * robinCpowLogTail (rho - (n : Complex)) 3 x) := by
  unfold robinZeroKernelRemainder
  simp only [div_eq_mul_inv]
  calc
    rho * Inv.inv ((rho - (n : Complex)) ^ (2 : Nat)) *
          (-((x : Complex) ^ (rho - (n : Complex))) *
              Inv.inv (((Real.log x : Real) : Complex) ^ (2 : Nat)) +
            2 * robinCpowLogTail (rho - (n : Complex)) 3 x) *
        Inv.inv rho =
        (rho * Inv.inv rho) *
          (Inv.inv ((rho - (n : Complex)) ^ (2 : Nat)) *
            (-((x : Complex) ^ (rho - (n : Complex))) *
                Inv.inv (((Real.log x : Real) : Complex) ^ (2 : Nat)) +
              2 * robinCpowLogTail (rho - (n : Complex)) 3 x)) := by
      ring
    _ = _ := by
      simp [hRho]

/-- On the critical line, translating a zero left by a positive integer does
not decrease its norm. -/
theorem norm_le_norm_sub_nat_of_re_eq_half
    {n : Nat} (hn : 1 <= n) {rho : Complex}
    (hRe : rho.re = (1 / 2 : Real)) :
    norm rho <= norm (rho - (n : Complex)) := by
  apply le_of_sq_le_sq
  case h =>
    rw [Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.natCast_re, Complex.natCast_im, sub_zero, hRe]
    have hnReal : (1 : Real) <= (n : Real) := by
      exact_mod_cast hn
    nlinarith
  case hb => exact norm_nonneg _

/-- The leading critical-line coefficient has the same inverse-square zero
majorant as the remainder. -/
theorem norm_nat_div_sub_div_le_robinXiZeroWeight
    {n : Nat} (hn : 1 <= n) {rho : Complex}
    (hRho : Not (rho = 0)) (hRe : rho.re = (1 / 2 : Real)) :
    norm (((n : Complex) / ((n : Complex) - rho)) / rho) <=
      (n : Real) * (Inv.inv (norm rho)) ^ (2 : Nat) := by
  have hNormLe : norm rho <= norm (rho - (n : Complex)) :=
    norm_le_norm_sub_nat_of_re_eq_half hn hRe
  have hOppNorm :
      norm ((n : Complex) - rho) = norm (rho - (n : Complex)) := by
    rw [show (n : Complex) - rho = -(rho - (n : Complex)) by ring,
      norm_neg]
  have hNormPos : 0 < norm rho := norm_pos_iff.mpr hRho
  have hInvLe :
      Inv.inv (norm ((n : Complex) - rho)) <= Inv.inv (norm rho) := by
    rw [hOppNorm]
    simpa [one_div] using one_div_le_one_div_of_le hNormPos hNormLe
  rw [norm_div, norm_div, Complex.norm_natCast]
  calc
    (n : Real) / norm ((n : Complex) - rho) / norm rho =
        (n : Real) * Inv.inv (norm ((n : Complex) - rho)) *
          Inv.inv (norm rho) := by ring
    _ <= (n : Real) * Inv.inv (norm rho) * Inv.inv (norm rho) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hInvLe (Nat.cast_nonneg n))
        (inv_nonneg.mpr (norm_nonneg rho))
    _ = (n : Real) * (Inv.inv (norm rho)) ^ (2 : Nat) := by
      ring

/-- A primitive used in the integration-by-parts recurrence for
`robinCpowLogTail`. -/
def robinCpowLogPrimitive (a : Complex) (k : Nat) (t : Real) : Complex :=
  Inv.inv a * (t : Complex) ^ a *
    (((Inv.inv ((Real.log t) ^ k) : Real) : Complex))

theorem hasDerivAt_robinCpowLogPrimitive
    {a : Complex} (ha : Not (a = 0)) (k : Nat)
    {t : Real} (ht : 1 < t) :
    HasDerivAt (robinCpowLogPrimitive a k)
      ((t : Complex) ^ (a - 1) *
          (((Inv.inv ((Real.log t) ^ k) : Real) : Complex)) -
        ((k : Complex) * Inv.inv a) *
          (t : Complex) ^ (a - 1) *
          (((Inv.inv ((Real.log t) ^ (k + 1)) : Real) : Complex))) t := by
  have htZero : Not (t = 0) := ne_of_gt (lt_trans Real.zero_lt_one ht)
  have htOne : Not (t = 1) := ne_of_gt ht
  have hLogZero : Not (Real.log t = 0) :=
    Real.log_ne_zero_of_pos_of_ne_one
      (lt_trans Real.zero_lt_one ht) htOne
  have hPower := hasDerivAt_ofReal_cpow_const htZero ha
  cases k with
  | zero =>
      have hFunction :
          robinCpowLogPrimitive a 0 =
            (fun y : Real => Inv.inv a * (y : Complex) ^ a) := by
        funext y
        simp [robinCpowLogPrimitive]
      rw [hFunction]
      simpa [ha] using hPower.const_mul (Inv.inv a)
  | succ k =>
      have hLogPower := (Real.hasDerivAt_log htZero).pow (k + 1)
      have hLogPowerZero :
          Not ((Real.log t) ^ (k + 1) = 0) :=
        pow_ne_zero (k + 1) hLogZero
      have hInverse := (hLogPower.inv hLogPowerZero).ofReal_comp
      have hRaw := (hPower.mul hInverse).const_mul (Inv.inv a)
      have hFunction :
          robinCpowLogPrimitive a (k + 1) =
            (fun y : Real => Inv.inv a *
              ((fun z : Real => (z : Complex) ^ a) y *
                (fun z : Real =>
                  (((Inv.inv ((Real.log z) ^ (k + 1)) : Real) : Complex))) y)) := by
        funext y
        simp [robinCpowLogPrimitive, mul_assoc]
      have hCoefficient :
          Inv.inv a *
              (a * (t : Complex) ^ (a - 1) *
                  (((Inv.inv ((Real.log t) ^ (k + 1)) : Real) : Complex)) +
                (t : Complex) ^ a *
                  (((-( (k + 1 : Real) * (Real.log t) ^ k * Inv.inv t) /
                    ((Real.log t) ^ (k + 1)) ^ (2 : Nat) : Real) : Complex))) =
            (t : Complex) ^ (a - 1) *
                (((Inv.inv ((Real.log t) ^ (k + 1)) : Real) : Complex)) -
              (((k + 1 : Nat) : Complex) * Inv.inv a) *
                (t : Complex) ^ (a - 1) *
                (((Inv.inv ((Real.log t) ^ (k + 2)) : Real) : Complex)) := by
        rw [Complex.cpow_sub a 1 (Complex.ofReal_ne_zero.mpr htZero),
          Complex.cpow_one]
        push_cast
        field_simp [ha, hLogZero, htZero]
        ring
      rw [hFunction]
      have hNormalized := hRaw
      simp only [Pi.pow_apply, Pi.inv_apply, Nat.cast_add, Nat.cast_one,
        add_tsub_cancel_right] at hNormalized
      rw [hCoefficient] at hNormalized
      simpa [Nat.add_assoc] using hNormalized

theorem tendsto_robinCpowLogPrimitive_atTop
    {a : Complex} (ha : a.re < 0) (k : Nat) :
    Filter.Tendsto (robinCpowLogPrimitive a k) Filter.atTop (nhds 0) := by
  have haZero : Not (a = 0) := by
    intro h
    rw [h] at ha
    norm_num at ha
  have hRpow :
      Filter.Tendsto (fun t : Real => t ^ a.re) Filter.atTop (nhds 0) := by
    have hNeg : 0 < -a.re := neg_pos.mpr ha
    simpa [neg_neg] using tendsto_rpow_neg_atTop hNeg
  have hCpowNorm :
      Filter.Tendsto (fun t : Real => norm ((t : Complex) ^ a))
        Filter.atTop (nhds 0) :=
    (Filter.tendsto_congr' (norm_ofReal_cpow_eventually_eq_atTop a)).mpr hRpow
  have hMajor :
      Filter.Tendsto
        (fun t : Real => norm (Inv.inv a) * norm ((t : Complex) ^ a))
        Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hCpowNorm)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun t => norm_nonneg _) ?_ hMajor
  filter_upwards [Filter.eventually_ge_atTop (Real.exp 1)] with t ht
  have htPos : 0 < t := lt_of_lt_of_le (Real.exp_pos 1) ht
  have hLogOne : 1 <= Real.log t := by
    rw [<- Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) ht
  have hPowOne : 1 <= (Real.log t) ^ k := by
    induction k with
    | zero => simp
      | succ k ih =>
        rw [pow_succ]
        simpa using mul_le_mul ih hLogOne zero_le_one
          (pow_nonneg (le_trans zero_le_one hLogOne) k)
  have hPowPos : 0 < (Real.log t) ^ k := lt_of_lt_of_le zero_lt_one hPowOne
  have hInvLe : Inv.inv ((Real.log t) ^ k) <= 1 := by
    simpa [one_div] using one_div_le_one_div_of_le zero_lt_one hPowOne
  rw [robinCpowLogPrimitive, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hPowPos)]
  simpa using mul_le_mul_of_nonneg_left hInvLe
    (mul_nonneg (norm_nonneg (Inv.inv a))
      (norm_nonneg ((t : Complex) ^ a)))

/-- Exact integration-by-parts recurrence for the logarithmically weighted
complex-power tail. -/
theorem robinCpowLogTail_recurrence
    {a : Complex} {x : Real} (hx : 1 < x) (ha : a.re < 0)
    (k : Nat) :
    robinCpowLogTail a k x =
      -Inv.inv a * (x : Complex) ^ a *
          (((Inv.inv ((Real.log x) ^ k) : Real) : Complex)) +
        ((k : Complex) * Inv.inv a) * robinCpowLogTail a (k + 1) x := by
  have haZero : Not (a = 0) := by
    intro h
    rw [h] at ha
    norm_num at ha
  have hExponent : (a - 1).re < -1 := by
    simp
    linarith
  have hFirst :
      IntegrableOn (fun t : Real =>
        (t : Complex) ^ (a - 1) *
          (((Inv.inv ((Real.log t) ^ k) : Real) : Complex))) (Ioi x) :=
    integrableOn_cpow_div_log_pow hx hExponent k
  have hNext :
      IntegrableOn (fun t : Real =>
        (t : Complex) ^ (a - 1) *
          (((Inv.inv ((Real.log t) ^ (k + 1)) : Real) : Complex))) (Ioi x) :=
    integrableOn_cpow_div_log_pow hx hExponent (k + 1)
  have hScaledNext :
      IntegrableOn (fun t : Real =>
        ((k : Complex) * Inv.inv a) *
          ((t : Complex) ^ (a - 1) *
            (((Inv.inv ((Real.log t) ^ (k + 1)) : Real) : Complex))))
        (Ioi x) :=
    hNext.const_mul ((k : Complex) * Inv.inv a)
  have hDifference :
      IntegrableOn (fun t : Real =>
        (t : Complex) ^ (a - 1) *
            (((Inv.inv ((Real.log t) ^ k) : Real) : Complex)) -
          ((k : Complex) * Inv.inv a) *
            ((t : Complex) ^ (a - 1) *
              (((Inv.inv ((Real.log t) ^ (k + 1)) : Real) : Complex))))
        (Ioi x) :=
    hFirst.sub hScaledNext
  have hIntegral :=
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
      (f := robinCpowLogPrimitive a k)
      (f' := fun t : Real =>
        (t : Complex) ^ (a - 1) *
            (((Inv.inv ((Real.log t) ^ k) : Real) : Complex)) -
          ((k : Complex) * Inv.inv a) *
            ((t : Complex) ^ (a - 1) *
              (((Inv.inv ((Real.log t) ^ (k + 1)) : Real) : Complex))))
      (fun t ht => by
        simpa [mul_assoc] using
          hasDerivAt_robinCpowLogPrimitive haZero k
            (lt_of_lt_of_le hx ht))
      hDifference (tendsto_robinCpowLogPrimitive_atTop ha k)
  have hSplit :
      integral (volume.restrict (Ioi x)) (fun t : Real =>
          (t : Complex) ^ (a - 1) *
              (((Inv.inv ((Real.log t) ^ k) : Real) : Complex)) -
            ((k : Complex) * Inv.inv a) *
              ((t : Complex) ^ (a - 1) *
                (((Inv.inv ((Real.log t) ^ (k + 1)) : Real) : Complex)))) =
        robinCpowLogTail a k x -
          ((k : Complex) * Inv.inv a) * robinCpowLogTail a (k + 1) x := by
    rw [integral_sub hFirst hScaledNext, integral_const_mul]
    rfl
  rw [hSplit] at hIntegral
  unfold robinCpowLogPrimitive at hIntegral
  linear_combination hIntegral

/-- The logarithmic denominator can be frozen at the left endpoint of the
tail.  This is the quantitative estimate used in Robin 1984, Lemma 1. -/
theorem norm_robinCpowLogTail_le
    {a : Complex} {x : Real} (hx : 1 < x) (ha : a.re < 0)
    (k : Nat) :
    norm (robinCpowLogTail a k x) <=
      (-x ^ a.re / a.re) * Inv.inv ((Real.log x) ^ k) := by
  have hxPos : 0 < x := lt_trans Real.zero_lt_one hx
  have hLogXPos : 0 < Real.log x := Real.log_pos hx
  have hExponent : a.re - 1 < -1 := by
    linarith
  have hBase :
      IntegrableOn (fun t : Real => t ^ (a.re - 1)) (Ioi x) :=
    integrableOn_Ioi_rpow_of_lt hExponent hxPos
  have hMajor :
      IntegrableOn (fun t : Real =>
        t ^ (a.re - 1) * Inv.inv ((Real.log x) ^ k)) (Ioi x) :=
    hBase.mul_const _
  unfold robinCpowLogTail
  calc
    norm (integral (volume.restrict (Ioi x)) (fun t : Real =>
        (t : Complex) ^ (a - 1) *
          (((Inv.inv ((Real.log t) ^ k) : Real) : Complex)))) <=
        integral (volume.restrict (Ioi x)) (fun t : Real =>
          t ^ (a.re - 1) * Inv.inv ((Real.log x) ^ k)) := by
      apply norm_integral_le_of_norm_le hMajor
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hxt : x <= t := ht.le
      have htPos : 0 < t := lt_of_lt_of_le hxPos hxt
      have hLogLe : Real.log x <= Real.log t :=
        Real.log_le_log hxPos hxt
      have hLogTPos : 0 < Real.log t :=
        lt_of_lt_of_le hLogXPos hLogLe
      have hPowLe : (Real.log x) ^ k <= (Real.log t) ^ k := by
        clear hMajor
        induction k with
        | zero => simp
        | succ k ih =>
            rw [pow_succ, pow_succ]
            exact mul_le_mul ih hLogLe hLogXPos.le
              (pow_nonneg hLogTPos.le k)
      have hPowXPos : 0 < (Real.log x) ^ k := pow_pos hLogXPos k
      have hPowTPos : 0 < (Real.log t) ^ k := pow_pos hLogTPos k
      have hInvLe :
          Inv.inv ((Real.log t) ^ k) <=
            Inv.inv ((Real.log x) ^ k) := by
        simpa [one_div] using one_div_le_one_div_of_le hPowXPos hPowLe
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos htPos,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hPowTPos)]
      simp only [Complex.sub_re, Complex.one_re]
      exact mul_le_mul_of_nonneg_left hInvLe
        (Real.rpow_nonneg htPos.le _)
    _ = (-x ^ a.re / a.re) * Inv.inv ((Real.log x) ^ k) := by
      rw [integral_mul_const,
        integral_Ioi_rpow_of_lt hExponent hxPos]
      ring_nf

end

end Robin1984
