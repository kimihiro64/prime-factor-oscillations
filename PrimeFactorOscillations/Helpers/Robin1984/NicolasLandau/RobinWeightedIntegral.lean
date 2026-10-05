/-
Source port from Robin1984 bfa72aec0c25c8ee29cefe4449d778ff30412bee.
Original file: Robin1984/NicolasLandau/RobinWeightedIntegral.lean
Original source lines 770-1122. Apache-2.0.
Statements and proof bodies retained; split at existing declaration boundaries.
-/
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.RobinWeightedRemainder

/-!
# Complete zero-kernel bounds and real weighted integrals

A source-preserving component of the written RH negative-envelope argument.
-/

namespace Robin1984

noncomputable section

open Complex MeasureTheory Set
open scoped BigOperators

/-- The complete multiplicity-counted Robin zero-kernel series is absolutely
summable under RH. -/
theorem summable_robinZeroKernel_div_rho
    (hRH : RiemannHypothesis) {n : Nat} (hn : 1 <= n)
    {x : Real} (hx : 1 < x) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      robinZeroKernel n (riemannXiDivisorZeroValue p) x /
        riemannXiDivisorZeroValue p) := by
  let C : Real :=
    (n : Real) * x ^ ((1 / 2 : Real) - (n : Real)) *
        Inv.inv (Real.log x) +
      (x ^ ((1 / 2 : Real) - (n : Real)) *
          Inv.inv ((Real.log x) ^ (2 : Nat)) +
        2 *
          ((-x ^ ((1 / 2 : Real) - (n : Real)) /
                ((1 / 2 : Real) - (n : Real))) *
            Inv.inv ((Real.log x) ^ (3 : Nat))))
  have hMajor :
      Summable (fun p : RiemannXiDivisorZeroIndex =>
        (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ (2 : Nat) * C) :=
    summable_robinXiZeroWeight.mul_right C
  apply hMajor.of_norm_bounded
  intro p
  dsimp [C]
  exact norm_robinZeroKernel_div_rho_le_robinXiZeroWeight hn
    (riemannXiDivisorZeroValue_ne_zero p)
    (riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH p) hx

/-- Robin's exact xi zero constant controls the complete zero-kernel sum. -/
theorem norm_tsum_robinZeroKernel_div_rho_le
    (hRH : RiemannHypothesis) {n : Nat} (hn : 1 <= n)
    {x : Real} (hx : 1 < x) :
    norm (tsum (fun p : RiemannXiDivisorZeroIndex =>
        robinZeroKernel n (riemannXiDivisorZeroValue p) x /
          riemannXiDivisorZeroValue p)) <=
      (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) *
        ((n : Real) * x ^ ((1 / 2 : Real) - (n : Real)) *
            Inv.inv (Real.log x) +
          (x ^ ((1 / 2 : Real) - (n : Real)) *
              Inv.inv ((Real.log x) ^ (2 : Nat)) +
            2 *
              ((-x ^ ((1 / 2 : Real) - (n : Real)) /
                    ((1 / 2 : Real) - (n : Real))) *
                Inv.inv ((Real.log x) ^ (3 : Nat))))) := by
  let C : Real :=
    (n : Real) * x ^ ((1 / 2 : Real) - (n : Real)) *
        Inv.inv (Real.log x) +
      (x ^ ((1 / 2 : Real) - (n : Real)) *
          Inv.inv ((Real.log x) ^ (2 : Nat)) +
        2 *
          ((-x ^ ((1 / 2 : Real) - (n : Real)) /
                ((1 / 2 : Real) - (n : Real))) *
            Inv.inv ((Real.log x) ^ (3 : Nat))))
  have hSeries := summable_robinZeroKernel_div_rho hRH hn hx
  have hNormSeries := hSeries.norm
  have hMajor :
      Summable (fun p : RiemannXiDivisorZeroIndex =>
        (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ (2 : Nat) * C) :=
    summable_robinXiZeroWeight.mul_right C
  have hPointwise : forall p : RiemannXiDivisorZeroIndex,
      norm (robinZeroKernel n (riemannXiDivisorZeroValue p) x /
        riemannXiDivisorZeroValue p) <=
      (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ (2 : Nat) * C := by
    intro p
    dsimp [C]
    exact norm_robinZeroKernel_div_rho_le_robinXiZeroWeight hn
      (riemannXiDivisorZeroValue_ne_zero p)
      (riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH p) hx
  calc
    norm (tsum (fun p : RiemannXiDivisorZeroIndex =>
        robinZeroKernel n (riemannXiDivisorZeroValue p) x /
          riemannXiDivisorZeroValue p)) <=
        tsum (fun p : RiemannXiDivisorZeroIndex =>
          norm (robinZeroKernel n (riemannXiDivisorZeroValue p) x /
            riemannXiDivisorZeroValue p)) :=
      norm_tsum_le_tsum_norm hNormSeries
    _ <= tsum (fun p : RiemannXiDivisorZeroIndex =>
        (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ (2 : Nat) * C) :=
      hNormSeries.tsum_le_tsum hPointwise hMajor
    _ = (tsum (fun p : RiemannXiDivisorZeroIndex =>
          (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ (2 : Nat))) * C := by
      rw [tsum_mul_right]
    _ = (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) * C := by
      rw [robinXiZeroConstant_eq_of_riemannHypothesis hRH]
    _ = _ := by rfl

/-- The scalar obtained from the leading zero atom and the twice-integrated
remainder is exactly Robin's printed Lemma 2 scalar. -/
theorem robinCriticalLineKernelScalar_eq_paper
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x) :
    (n : Real) * x ^ ((1 / 2 : Real) - (n : Real)) *
          Inv.inv (Real.log x) +
        (x ^ ((1 / 2 : Real) - (n : Real)) *
            Inv.inv ((Real.log x) ^ (2 : Nat)) +
          2 *
            ((-x ^ ((1 / 2 : Real) - (n : Real)) /
                  ((1 / 2 : Real) - (n : Real))) *
              Inv.inv ((Real.log x) ^ (3 : Nat)))) =
      x ^ ((1 / 2 : Real) - (n : Real)) * Inv.inv (Real.log x) *
        ((n : Real) + Inv.inv (Real.log x) +
          4 * Inv.inv (((2 * n - 1 : Nat) : Real) *
            (Real.log x) ^ (2 : Nat))) := by
  have hLog : Not (Real.log x = 0) := ne_of_gt (Real.log_pos hx)
  have hOddNat : Not (2 * n - 1 = 0) := by
    omega
  have hOddReal : Not ((((2 * n - 1 : Nat) : Real)) = 0) := by
    exact_mod_cast hOddNat
  have hOneLeTwoN : 1 <= 2 * n := by
    omega
  have hOddCast :
      (((2 * n - 1 : Nat) : Real)) = 2 * (n : Real) - 1 := by
    rw [Nat.cast_sub hOneLeTwoN]
    push_cast
    rfl
  have hExponentEq :
      (1 / 2 : Real) - (n : Real) =
        -(((2 * n - 1 : Nat) : Real)) / 2 := by
    rw [hOddCast]
    ring
  have hInvSq :
      Inv.inv ((Real.log x) ^ (2 : Nat)) =
        Inv.inv (Real.log x) * Inv.inv (Real.log x) := by
    rw [<- inv_pow]
    ring
  have hThird :
      2 *
          ((-x ^ ((1 / 2 : Real) - (n : Real)) /
                ((1 / 2 : Real) - (n : Real))) *
            Inv.inv ((Real.log x) ^ (3 : Nat))) =
        x ^ ((1 / 2 : Real) - (n : Real)) * Inv.inv (Real.log x) *
          (4 * Inv.inv ((((2 * n - 1 : Nat) : Real)) *
            (Real.log x) ^ (2 : Nat))) := by
    rw [hExponentEq]
    field_simp [hLog, hOddReal]
    ring
  rw [hThird, hInvSq]
  ring

/-- Robin 1984, Lemma 2: the complete nontrivial-zero contribution in the
printed scalar normalization. -/
theorem norm_tsum_robinZeroKernel_div_rho_le_paper
    (hRH : RiemannHypothesis) {n : Nat} (hn : 1 <= n)
    {x : Real} (hx : 1 < x) :
    norm (tsum (fun p : RiemannXiDivisorZeroIndex =>
        robinZeroKernel n (riemannXiDivisorZeroValue p) x /
          riemannXiDivisorZeroValue p)) <=
      (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) *
        (x ^ ((1 / 2 : Real) - (n : Real)) * Inv.inv (Real.log x) *
          ((n : Real) + Inv.inv (Real.log x) +
            4 * Inv.inv (((2 * n - 1 : Nat) : Real) *
              (Real.log x) ^ (2 : Nat)))) := by
  have hBound := norm_tsum_robinZeroKernel_div_rho_le hRH hn hx
  rw [robinCriticalLineKernelScalar_eq_paper hn hx] at hBound
  exact hBound

/-- The positive real weight in Robin 1984, Lemma 2. -/
def robinRealWeight (n : Nat) (t : Real) : Real :=
  t ^ (-(n : Real) - 1) *
    (((n : Real) * Real.log t + 1) /
      (Real.log t) ^ (2 : Nat))

/-- A primitive whose derivative is Robin's positive real weight. -/
def robinRealWeightPrimitive (n : Nat) (t : Real) : Real :=
  -(t ^ (-(n : Real)) * Inv.inv (Real.log t))

theorem hasDerivAt_robinRealWeightPrimitive
    (n : Nat) {t : Real} (ht : 1 < t) :
    HasDerivAt (robinRealWeightPrimitive n)
      (robinRealWeight n t) t := by
  have htZero : Not (t = 0) :=
    ne_of_gt (lt_trans Real.zero_lt_one ht)
  have hLogZero : Not (Real.log t = 0) :=
    ne_of_gt (Real.log_pos ht)
  have htPos : 0 < t := lt_trans Real.zero_lt_one ht
  have hRpow :
      t ^ (-(n : Real)) = t ^ (-(n : Real) - 1) * t := by
    calc
      t ^ (-(n : Real)) = t ^ ((-(n : Real) - 1) + 1) := by
        congr 1
        ring
      _ = t ^ (-(n : Real) - 1) * t ^ (1 : Real) :=
        Real.rpow_add htPos _ _
      _ = t ^ (-(n : Real) - 1) * t := by
        rw [Real.rpow_one]
  have hPow :=
    Real.hasDerivAt_rpow_const (p := -(n : Real)) (Or.inl htZero)
  have hLogInv := (Real.hasDerivAt_log htZero).inv hLogZero
  have hRaw := (hPow.mul hLogInv).neg
  refine hRaw.congr_deriv ?_
  simp only [Pi.inv_apply]
  unfold robinRealWeight
  rw [hRpow]
  field_simp [htZero, hLogZero] <;> ring

theorem robinRealWeight_nonneg
    {n : Nat} {t : Real} (ht : 1 < t) :
    0 <= robinRealWeight n t := by
  unfold robinRealWeight
  have hLogPos : 0 < Real.log t := Real.log_pos ht
  exact mul_nonneg (Real.rpow_nonneg (le_of_lt (lt_trans Real.zero_lt_one ht)) _)
    (div_nonneg
      (add_nonneg
        (mul_nonneg (Nat.cast_nonneg n) hLogPos.le) zero_le_one)
      (sq_nonneg (Real.log t)))

theorem tendsto_robinRealWeightPrimitive_atTop
    {n : Nat} (hn : 1 <= n) :
    Filter.Tendsto (robinRealWeightPrimitive n) Filter.atTop (nhds 0) := by
  have hnReal : 0 < (n : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hPow :
      Filter.Tendsto (fun t : Real => t ^ (-(n : Real)))
        Filter.atTop (nhds 0) := by
    simpa using tendsto_rpow_neg_atTop hnReal
  have hLogInv :
      Filter.Tendsto (fun t : Real => Inv.inv (Real.log t))
        Filter.atTop (nhds 0) :=
    Real.tendsto_log_atTop.inv_tendsto_atTop
  change Filter.Tendsto
    (fun t : Real => -(t ^ (-(n : Real)) * Inv.inv (Real.log t)))
    Filter.atTop (nhds 0)
  simpa only [zero_mul, neg_zero] using (hPow.mul hLogInv).neg

/-- The total mass of Robin's weight is the exact cutoff boundary atom. -/
theorem integral_robinRealWeight
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x) :
    integral (volume.restrict (Ioi x)) (robinRealWeight n) =
      x ^ (-(n : Real)) * Inv.inv (Real.log x) := by
  have hDeriv : forall t : Real, Membership.mem (Ici x) t ->
      HasDerivAt (robinRealWeightPrimitive n)
        (robinRealWeight n t) t := by
    intro t ht
    exact hasDerivAt_robinRealWeightPrimitive n (lt_of_lt_of_le hx ht)
  have hNonneg : forall t : Real, Membership.mem (Ioi x) t ->
      0 <= robinRealWeight n t := by
    intro t ht
    exact robinRealWeight_nonneg (lt_trans hx ht)
  have hIntegral := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'
    hDeriv hNonneg (tendsto_robinRealWeightPrimitive_atTop hn)
  rw [hIntegral]
  simp [robinRealWeightPrimitive]

theorem integrableOn_robinRealWeight
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 1 < x) :
    IntegrableOn (robinRealWeight n) (Ioi x) := by
  apply MeasureTheory.integrableOn_Ioi_deriv_of_nonneg'
    (g := robinRealWeightPrimitive n)
  . intro t ht
    exact hasDerivAt_robinRealWeightPrimitive n (lt_of_lt_of_le hx ht)
  . intro t ht
    exact robinRealWeight_nonneg (lt_trans hx ht)
  . exact tendsto_robinRealWeightPrimitive_atTop hn

/-- The pole/trivial-zero correction factor in Robin's weighted explicit
formula. -/
def robinTrivialZeroCorrectionFactor (t : Real) : Real :=
  Real.log (2 * Real.pi) +
    (1 / 2 : Real) * Real.log (1 - 1 / t ^ (2 : Nat))

theorem robinTrivialZeroCorrectionFactor_bounds
    {t : Real} (ht : 2 <= t) :
    And (0 <= robinTrivialZeroCorrectionFactor t)
      (robinTrivialZeroCorrectionFactor t <= Real.log (2 * Real.pi)) := by
  have htSq : (4 : Real) <= t ^ (2 : Nat) := by
    nlinarith
  have hInvLe : (1 : Real) / t ^ (2 : Nat) <= 1 / 4 :=
    one_div_le_one_div_of_le (by norm_num) htSq
  have hInvNonneg : 0 <= (1 : Real) / t ^ (2 : Nat) := by
    positivity
  have hInnerHalf : (1 / 2 : Real) <= 1 - 1 / t ^ (2 : Nat) := by
    linarith
  have hInnerPos : 0 < 1 - 1 / t ^ (2 : Nat) := by
    linarith
  have hInnerLeOne : 1 - 1 / t ^ (2 : Nat) <= 1 := by
    linarith
  have hLogNonpos : Real.log (1 - 1 / t ^ (2 : Nat)) <= 0 :=
    Real.log_nonpos hInnerPos.le hInnerLeOne
  have hLogLower :
      Real.log (1 / 2 : Real) <= Real.log (1 - 1 / t ^ (2 : Nat)) :=
    Real.log_le_log (by norm_num) hInnerHalf
  have hLogHalf : Real.log (1 / 2 : Real) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  have hLogTwoPos : 0 < Real.log (2 : Real) :=
    Real.log_pos (by norm_num)
  have hTwoPi : (2 : Real) <= 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hLogTwoPi : Real.log (2 : Real) <= Real.log (2 * Real.pi) :=
    Real.log_le_log (by norm_num) hTwoPi
  rw [hLogHalf] at hLogLower
  unfold robinTrivialZeroCorrectionFactor
  exact And.intro (by nlinarith) (by linarith)

/-- The complete pole/trivial-zero correction in Robin's weighted explicit
formula. -/
def robinTrivialZeroCorrection (n : Nat) (x : Real) : Real :=
  integral (volume.restrict (Ioi x)) (fun t : Real =>
    robinRealWeight n t * robinTrivialZeroCorrectionFactor t)

theorem integrableOn_robinTrivialZeroCorrection_integrand
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 2 <= x) :
    IntegrableOn (fun t : Real =>
      robinRealWeight n t * robinTrivialZeroCorrectionFactor t) (Ioi x) := by
  have hxOne : 1 < x := lt_of_lt_of_le (by norm_num) hx
  have hWeight := integrableOn_robinRealWeight hn hxOne
  apply hWeight.mul_bdd (c := Real.log (2 * Real.pi))
  . have hMeas : Measurable robinTrivialZeroCorrectionFactor := by
      unfold robinTrivialZeroCorrectionFactor
      fun_prop
    exact hMeas.aestronglyMeasurable
  . filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hBounds :=
      robinTrivialZeroCorrectionFactor_bounds (le_trans hx ht.le)
    rw [Real.norm_eq_abs, abs_of_nonneg hBounds.1]
    exact hBounds.2

/-- The correction is nonnegative and at most its constant `log(2*pi)` part
times the exact total weight. -/
theorem robinTrivialZeroCorrection_bounds
    {n : Nat} (hn : 1 <= n) {x : Real} (hx : 2 <= x) :
    And (0 <= robinTrivialZeroCorrection n x)
      (robinTrivialZeroCorrection n x <=
        Real.log (2 * Real.pi) * x ^ (-(n : Real)) *
          Inv.inv (Real.log x)) := by
  have hxOne : 1 < x := lt_of_lt_of_le (by norm_num) hx
  have hWeight := integrableOn_robinRealWeight hn hxOne
  have hCorrection := integrableOn_robinTrivialZeroCorrection_integrand hn hx
  refine And.intro ?_ ?_
  . unfold robinTrivialZeroCorrection
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg
      (robinRealWeight_nonneg (lt_trans hxOne ht))
      (robinTrivialZeroCorrectionFactor_bounds (le_trans hx ht.le)).1
  . unfold robinTrivialZeroCorrection
    have hCompare :
        integral (volume.restrict (Ioi x)) (fun t : Real =>
            robinRealWeight n t * robinTrivialZeroCorrectionFactor t) <=
          integral (volume.restrict (Ioi x)) (fun t : Real =>
            robinRealWeight n t * Real.log (2 * Real.pi)) := by
      apply integral_mono_ae hCorrection (hWeight.mul_const _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_le_mul_of_nonneg_left
        (robinTrivialZeroCorrectionFactor_bounds (le_trans hx ht.le)).2
        (robinRealWeight_nonneg (lt_trans hxOne ht))
    calc
      integral (volume.restrict (Ioi x)) (fun t : Real =>
          robinRealWeight n t * robinTrivialZeroCorrectionFactor t) <=
          integral (volume.restrict (Ioi x)) (fun t : Real =>
            robinRealWeight n t * Real.log (2 * Real.pi)) := hCompare
      _ = Real.log (2 * Real.pi) * x ^ (-(n : Real)) *
          Inv.inv (Real.log x) := by
        rw [integral_mul_const, integral_robinRealWeight hn hxOne]
        ring

end

end Robin1984
