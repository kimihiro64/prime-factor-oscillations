/-
Source port from Robin1984 bfa72aec0c25c8ee29cefe4449d778ff30412bee.
Original file: Robin1984/NicolasLandau/NicolasLandauPositiveTail.lean
Original source lines 30-346. Apache-2.0.
Statements and proof bodies retained; split at existing declaration boundaries.
-/
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.IntegrableExpMul
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.NicolasLandau

/-!
# The filled analytic continuation in the Nicolas positive-tail proof

A source-preserving component of the written Nicolas/Landau/Mellin proof.
-/

namespace Robin1984

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section

def nicolasLandauPositiveTail (b x : Real) : Real :=
  nicolasJ x + x ^ (-b)

def nicolasLandauPositiveDensity (b x : Real) : ENNReal :=
  ENNReal.ofReal (x ^ (-1 : Real) * nicolasLandauPositiveTail b x)

def nicolasLandauPositiveMeasure (X b : Real) : Measure Real :=
  (volume.restrict (Ioi X)).withDensity
    (nicolasLandauPositiveDensity b)

def nicolasLandauPositiveMellin (X b a : Real) : Real :=
  integral (volume.restrict (Ioi X)) (fun x : Real =>
    x ^ (a - 1) * nicolasLandauPositiveTail b x)

def nicolasLandauRpowMellinContinuation (X b a : Real) : Real :=
  X ^ (a - b) / (b - a)

def nicolasJShiftedRealContinuation (a : Real) : Real :=
  Complex.re (integral (volume.restrict (Ioi (0 : Real)))
    (nicolasJMellinShiftIntegrand (a : Complex)))

def nicolasJRealMellinStartup (X a : Real) : Real :=
  integral (volume.restrict (Ioc (3 : Real) X)) (fun x : Real =>
    x ^ (a - 1) * nicolasJ x)

def nicolasLandauPositiveMellinContinuation (X b a : Real) : Real :=
  nicolasJShiftedRealContinuation a - nicolasJRealMellinStartup X a +
    nicolasLandauRpowMellinContinuation X b a

def nicolasPsiMellinContinuationFilled (s : Complex) : Complex :=
  -(logDeriv nicolasZetaPoleFactor s + 1) / s

theorem nicolasPsiMellinContinuationFilled_analyticAt_one :
    AnalyticAt Complex nicolasPsiMellinContinuationFilled 1 := by
  have hFactor : AnalyticAt Complex nicolasZetaPoleFactor 1 :=
    nicolasZetaPoleFactor_differentiable.analyticAt 1
  have hFactorDeriv : AnalyticAt Complex
      (deriv nicolasZetaPoleFactor) 1 :=
    nicolasZetaPoleFactor_differentiable.deriv.analyticAt 1
  have hLogDeriv : AnalyticAt Complex
      (logDeriv nicolasZetaPoleFactor) 1 := by
    unfold logDeriv
    exact hFactorDeriv.div hFactor (by simp)
  unfold nicolasPsiMellinContinuationFilled
  have hOne : AnalyticAt Complex (fun _ : Complex => (1 : Complex)) 1 :=
    analyticAt_const
  have hNumerator : AnalyticAt Complex
      (fun s : Complex => -(logDeriv nicolasZetaPoleFactor s + 1)) 1 :=
    (hLogDeriv.add hOne).neg
  exact hNumerator.div analyticAt_id (by norm_num)

theorem nicolasPsiMellinContinuationFilled_eq_raw
    {s : Complex} (hsZero : Not (s = 0)) (hsOne : Not (s = 1))
    (hZeta : Not (riemannZeta s = 0)) :
    nicolasPsiMellinContinuationFilled s =
      nicolasPsiMellinContinuation s := by
  exact (nicolasPsiMellinContinuation_eq_poleFactor
    hsZero hsOne hZeta).symm

theorem nicolasPsiMellinStartup_three_differentiableAt (s0 : Complex) :
    DifferentiableAt Complex (nicolasPsiMellinStartup 3) s0 := by
  letI : AddCommGroup Complex := Complex.addCommGroup
  letI : Module Complex Complex := Semiring.toModule
  let F : Complex -> Real -> Complex := fun s t =>
    (nicolasPsiError t : Complex) * (t : Complex) ^ (-(s + 1))
  let F' : Complex -> Real -> Complex := fun s t =>
    -((Real.log t : Real) : Complex) * F s t
  let base : Real -> Complex := fun t =>
    (nicolasPsiError t : Complex) * (t : Complex) ^ (-3 : Complex)
  let ratio : Complex -> Real -> Complex := fun s t =>
    (t : Complex) ^ ((2 : Complex) - s)
  let majorant : Real -> Real := fun t =>
    norm (base t) * (3 : Real) ^ (abs s0.re + 4)
  have hBaseIntegrable : Integrable base
      (volume.restrict (Ioc (1 : Real) 3)) := by
    dsimp [base]
    change IntegrableOn
      (fun t : Real => (nicolasPsiError t : Complex) *
        (t : Complex) ^ (-3 : Complex)) (Ioc (1 : Real) 3)
    have h :=
      (nicolasPsiErrorMellin_integrable (s := (2 : Complex))
        (by norm_num)).mono_set
        (show Ioc (1 : Real) 3 <= Ioi 1 from Ioc_subset_Ioi_self)
    apply h.congr_fun
    . intro t ht
      congr 2
      norm_num
    . exact measurableSet_Ioc
  have hMajorantIntegrable : Integrable majorant
      (volume.restrict (Ioc (1 : Real) 3)) := by
    have h := hBaseIntegrable.norm.const_mul
      ((3 : Real) ^ (abs s0.re + 4))
    simpa [majorant, mul_comm] using h
  have hMeasurable : forall s : Complex, AEStronglyMeasurable (F s)
      (volume.restrict (Ioc (1 : Real) 3)) := by
    intro s
    have hRatioContinuous : ContinuousOn (ratio s) (Ioc (1 : Real) 3) := by
      apply continuousOn_of_forall_continuousAt
      intro t ht
      dsimp [ratio]
      have htPos : 0 < t := lt_trans zero_lt_one ht.1
      exact (continuousAt_cpow_const
        (Complex.ofReal_mem_slitPlane.2 htPos)).comp
          Complex.continuous_ofReal.continuousAt
    have hProduct := hBaseIntegrable.aestronglyMeasurable.mul
      (hRatioContinuous.aestronglyMeasurable measurableSet_Ioc)
    apply hProduct.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htZero : Not ((t : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans zero_lt_one ht.1))
    dsimp [F, base, ratio]
    rw [mul_assoc, <- Complex.cpow_add _ _ htZero]
    congr 2
    ring
  have hBound : forall s : Complex, dist s s0 < 1 ->
      forall t : Real, 1 < t -> t <= 3 ->
        norm (F s t) <= majorant t := by
    intro s hs t htOneStrict htThree
    have hDist : norm (s - s0) < 1 := by
      simpa [dist_eq_norm] using hs
    have hReAbs : abs (s.re - s0.re) <= norm (s - s0) := by
      simpa using Complex.abs_re_le_norm (s - s0)
    have hReLower : s0.re - 1 < s.re := by
      have hAbsLt : abs (s.re - s0.re) < 1 := lt_of_le_of_lt hReAbs hDist
      linarith [(abs_lt.mp hAbsLt).1]
    have htPos : 0 < t := lt_trans zero_lt_one htOneStrict
    have htOne : 1 <= t := le_of_lt htOneStrict
    have hExponent : 2 - s.re <= abs s0.re + 4 := by
      have hNeg : -s0.re <= abs s0.re := neg_le_abs s0.re
      linarith
    have hExponentNonneg : 0 <= abs s0.re + 4 := by positivity
    have hRatioBound : norm (ratio s t) <=
        (3 : Real) ^ (abs s0.re + 4) := by
      dsimp [ratio]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos htPos]
      calc
        t ^ (2 - s.re) <= t ^ (abs s0.re + 4) :=
          Real.rpow_le_rpow_of_exponent_le htOne hExponent
        _ <= (3 : Real) ^ (abs s0.re + 4) :=
          Real.rpow_le_rpow (le_of_lt htPos) htThree hExponentNonneg
    have htZero : Not ((t : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt htPos)
    dsimp [F]
    rw [show -(s + 1) = (-3 : Complex) + ((2 : Complex) - s) by ring,
      Complex.cpow_add _ _ htZero, norm_mul]
    dsimp [majorant, base]
    simp only [norm_mul]
    simpa [mul_assoc] using
      (mul_le_mul_of_nonneg_left hRatioBound
        (mul_nonneg (norm_nonneg ((nicolasPsiError t : Complex)))
          (norm_nonneg ((t : Complex) ^ (-3 : Complex)))))
  have hFIntegrable : Integrable (F s0)
      (volume.restrict (Ioc (1 : Real) 3)) := by
    apply Integrable.mono hMajorantIntegrable (hMeasurable s0)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hMajorantNonneg : 0 <= majorant t := by
      dsimp [majorant]
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hMajorantNonneg]
    exact hBound s0 (by simp [dist_self]) t ht.1 ht.2
  have hDerivativeMeasurable : AEStronglyMeasurable (F' s0)
      (volume.restrict (Ioc (1 : Real) 3)) := by
    have hRealLogOn : ContinuousOn (fun t : Real => Real.log t)
        (Ioc (1 : Real) 3) := by
      apply Real.continuousOn_log.mono
      intro t ht
      exact Set.mem_compl_singleton_iff.mpr
        (ne_of_gt (lt_trans zero_lt_one ht.1))
    have hRealLog : AEStronglyMeasurable (fun t : Real => Real.log t)
        (volume.restrict (Ioc (1 : Real) 3)) :=
      hRealLogOn.aestronglyMeasurable measurableSet_Ioc
    have hLog : AEStronglyMeasurable
        (fun t : Real => ((Real.log t : Real) : Complex))
        (volume.restrict (Ioc (1 : Real) 3)) :=
      Complex.continuous_ofReal.comp_aestronglyMeasurable hRealLog
    exact hLog.neg.mul (hMeasurable s0)
  have hDerivativeBound : Filter.Eventually
      (fun t : Real => forall s : Complex, Membership.mem (Metric.ball s0 1) s ->
        norm (F' s t) <= 3 * majorant t)
      (ae (volume.restrict (Ioc (1 : Real) 3))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro s hs
    have htPos : 0 < t := lt_trans zero_lt_one ht.1
    have hLogNonneg : 0 <= Real.log t := Real.log_nonneg ht.1.le
    have hLogBound : Real.log t <= 3 := by
      have hLogSub := Real.log_le_sub_one_of_pos htPos
      linarith [ht.2]
    have hFBound : norm (F s t) <= majorant t :=
      hBound s (by simpa [Metric.mem_ball] using hs) t ht.1 ht.2
    dsimp [F']
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hLogNonneg]
    exact mul_le_mul hLogBound hFBound (norm_nonneg _) (by norm_num)
  have hDerivativeIntegrable : Integrable (fun t : Real => 3 * majorant t)
      (volume.restrict (Ioc (1 : Real) 3)) :=
    hMajorantIntegrable.const_mul 3
  have hDerivative : Filter.Eventually
      (fun t : Real => forall s : Complex, Membership.mem (Metric.ball s0 1) s ->
        HasDerivAt (fun z : Complex => F z t) (F' s t) s)
      (ae (volume.restrict (Ioc (1 : Real) 3))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro s hs
    have htPos : 0 < t := lt_trans zero_lt_one ht.1
    have htZero : Not ((t : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt htPos)
    have hExponent : HasDerivAt (fun z : Complex => -(z + 1)) (-1) s := by
      have hRaw := ((hasDerivAt_id' s).add_const 1).neg
      exact hRaw.congr_of_eventuallyEq
        (Eventually.of_forall (fun _ => rfl))
    have hPower := hExponent.const_cpow (Or.inl htZero)
    have hProduct := hPower.const_smul (nicolasPsiError t : Complex)
    have hProduct' : HasDerivAt
        (fun z : Complex => (nicolasPsiError t : Complex) *
          (t : Complex) ^ (-(z + 1)))
        ((nicolasPsiError t : Complex) *
          ((t : Complex) ^ (-(s + 1)) * Complex.log (t : Complex) * -1)) s := by
      convert hProduct using 1 <;> try rfl
    dsimp [F, F']
    apply hProduct'.congr_deriv
    rw [Complex.ofReal_log htPos.le]
    ring
  unfold nicolasPsiMellinStartup
  have hMain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds s0 zero_lt_one)
    (Eventually.of_forall hMeasurable) hFIntegrable
    hDerivativeMeasurable hDerivativeBound hDerivativeIntegrable hDerivative
  exact hMain.2.differentiableAt

theorem nicolasPsiMellinStartup_three_differentiable :
    Differentiable Complex (nicolasPsiMellinStartup 3) :=
  nicolasPsiMellinStartup_three_differentiableAt

theorem nicolasPsiMellinStartup_three_analyticAt (s0 : Complex) :
    AnalyticAt Complex (nicolasPsiMellinStartup 3) s0 :=
  nicolasPsiMellinStartup_three_differentiable.analyticAt s0

def nicolasPsiMellinTailContinuationFilled (s : Complex) : Complex :=
  nicolasPsiMellinContinuationFilled s - nicolasPsiMellinStartup 3 s

theorem nicolasPsiMellinTailContinuationFilled_analyticAt_one :
    AnalyticAt Complex nicolasPsiMellinTailContinuationFilled 1 := by
  unfold nicolasPsiMellinTailContinuationFilled
  exact nicolasPsiMellinContinuationFilled_analyticAt_one.sub
    (nicolasPsiMellinStartup_three_analyticAt 1)

theorem nicolasPsiMellinTailContinuationFilled_eq_raw
    {s : Complex} (hsZero : Not (s = 0)) (hsOne : Not (s = 1))
    (hZeta : Not (riemannZeta s = 0)) :
    nicolasPsiMellinTailContinuationFilled s =
      nicolasPsiMellinTailContinuation 3 s := by
  unfold nicolasPsiMellinTailContinuationFilled
    nicolasPsiMellinTailContinuation
  rw [nicolasPsiMellinContinuationFilled_eq_raw hsZero hsOne hZeta]

theorem nicolasZetaPoleFactor_ne_zero_of_zeta_ne_zero
    {s : Complex} (hsOne : Not (s = 1))
    (hZeta : Not (riemannZeta s = 0)) :
    Not (nicolasZetaPoleFactor s = 0) := by
  intro hFactor
  have hIdentity := riemannZeta_eq_nicolasZetaPoleFactor_div hsOne
  rw [hFactor, zero_div] at hIdentity
  exact hZeta hIdentity

theorem nicolasPsiMellinContinuationFilled_analyticAt
    {s : Complex} (hsZero : Not (s = 0))
    (hFactor : Not (nicolasZetaPoleFactor s = 0)) :
    AnalyticAt Complex nicolasPsiMellinContinuationFilled s := by
  have hPoleFactor : AnalyticAt Complex nicolasZetaPoleFactor s :=
    nicolasZetaPoleFactor_differentiable.analyticAt s
  have hPoleFactorDeriv : AnalyticAt Complex
      (deriv nicolasZetaPoleFactor) s :=
    nicolasZetaPoleFactor_differentiable.deriv.analyticAt s
  have hLogDeriv : AnalyticAt Complex
      (logDeriv nicolasZetaPoleFactor) s := by
    unfold logDeriv
    exact hPoleFactorDeriv.div hPoleFactor hFactor
  have hOne : AnalyticAt Complex (fun _ : Complex => (1 : Complex)) s :=
    analyticAt_const
  have hNumerator : AnalyticAt Complex
      (fun w : Complex => -(logDeriv nicolasZetaPoleFactor w + 1)) s :=
    (hLogDeriv.add hOne).neg
  unfold nicolasPsiMellinContinuationFilled
  exact hNumerator.div analyticAt_id hsZero

theorem nicolasPsiMellinTailContinuationFilled_analyticAt_of_one_lt_re
    {s : Complex} (hs : 1 < s.re) :
    AnalyticAt Complex nicolasPsiMellinTailContinuationFilled s := by
  have hsZero : Not (s = 0) := by
    intro hZero
    rw [hZero] at hs
    norm_num at hs
  have hsOne : Not (s = 1) := by
    intro hOne
    rw [hOne] at hs
    norm_num at hs
  have hZeta : Not (riemannZeta s = 0) :=
    riemannZeta_ne_zero_of_one_lt_re hs
  have hFactor := nicolasZetaPoleFactor_ne_zero_of_zeta_ne_zero hsOne hZeta
  unfold nicolasPsiMellinTailContinuationFilled
  exact (nicolasPsiMellinContinuationFilled_analyticAt hsZero hFactor).sub
    (nicolasPsiMellinStartup_three_analyticAt s)

theorem nicolasPsiMellinTailContinuationFilled_eq_raw_of_one_lt_re
    {s : Complex} (hs : 1 < s.re) :
    nicolasPsiMellinTailContinuationFilled s =
      nicolasPsiMellinTailContinuation 3 s := by
  have hsZero : Not (s = 0) := by
    intro hZero
    rw [hZero] at hs
    norm_num at hs
  have hsOne : Not (s = 1) := by
    intro hOne
    rw [hOne] at hs
    norm_num at hs
  exact nicolasPsiMellinTailContinuationFilled_eq_raw
    hsZero hsOne (riemannZeta_ne_zero_of_one_lt_re hs)

end

end Robin1984

