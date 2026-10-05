/-
Source port from Robin1984 bfa72aec0c25c8ee29cefe4449d778ff30412bee.
Original file: Robin1984/NicolasLandau/NicolasLandau.lean
Original source lines 1260-1454. Apache-2.0.
Statements and proof bodies retained; split at existing declaration boundaries.
-/
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.NicolasLandauPoleOrder

/-!
# The finite startup term and the simple-pole limit

A source-preserving component of the written Nicolas/Landau/Mellin proof.
-/

namespace Robin1984

open Asymptotics Filter MeasureTheory Set

noncomputable section

/-- The finite startup contribution on `(1, 3]` is continuous in the Mellin
parameter.  Consequently it cannot remove a pole of the complete Mellin
continuation. -/
theorem nicolasPsiMellinStartup_three_continuousAt (s0 : Complex) :
    ContinuousAt (nicolasPsiMellinStartup 3) s0 := by
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
      (nicolasPsiErrorMellin_integrable (s := (2 : Complex)) (by norm_num)).mono_set
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
  have hMeasurable : forall s : Complex, AEStronglyMeasurable
      (fun t : Real => (nicolasPsiError t : Complex) *
        (t : Complex) ^ (-(s + 1)))
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
    dsimp [base, ratio]
    rw [mul_assoc, <- Complex.cpow_add _ _ htZero]
    congr 2
    ring
  have hBound : forall s : Complex, dist s s0 < 1 ->
      forall t : Real, 1 < t -> t <= 3 ->
        norm ((nicolasPsiError t : Complex) *
          (t : Complex) ^ (-(s + 1))) <= majorant t := by
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
    rw [show -(s + 1) = (-3 : Complex) + ((2 : Complex) - s) by ring,
      Complex.cpow_add _ _ htZero, norm_mul]
    dsimp [majorant, base]
    simp only [norm_mul]
    simpa [mul_assoc] using
      (mul_le_mul_of_nonneg_left hRatioBound
        (mul_nonneg (norm_nonneg
          ((nicolasPsiError t : Complex)))
          (norm_nonneg ((t : Complex) ^ (-3 : Complex)))))
  unfold nicolasPsiMellinStartup
  apply continuousAt_of_dominated
      (F := fun s : Complex => fun t : Real =>
        (nicolasPsiError t : Complex) * (t : Complex) ^ (-(s + 1)))
      (bound := majorant)
  . exact Eventually.of_forall hMeasurable
  . filter_upwards [Metric.ball_mem_nhds s0 zero_lt_one] with s hs
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hBound s (by simpa [Metric.mem_ball] using hs) t ht.1 ht.2
  . exact hMajorantIntegrable
  . filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htZero : Not ((t : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr
        (ne_of_gt (lt_trans zero_lt_one ht.1))
    have hExponent : ContinuousAt (fun s : Complex => -(s + 1)) s0 := by
      fun_prop
    exact continuousAt_const.mul
      ((continuousAt_const_cpow htZero).comp hExponent)


/-- The surviving pole has a nonzero first Laurent coefficient.  This is the
exact fixed-direction information needed at the endpoint of the Landau
integral; mere growth of the norm would not be enough. -/
theorem nicolasPsiMellinTailContinuation_three_simplePoleLimit
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hRhoZero : Not (rho = 0)) (hOne : Not (rho = 1)) :
    Exists fun c : Complex => And (Not (c = 0))
      (Tendsto
        (fun s : Complex => (s - rho) *
          nicolasPsiMellinTailContinuation 3 s)
        (nhdsWithin rho (Set.compl {rho})) (nhds c)) := by
  have hOrder : meromorphicOrderAt nicolasPsiMellinContinuation rho = -1 :=
    nicolasPsiMellinContinuation_order_eq_neg_one hZero hRhoZero hOne
  have hOrderNeg : meromorphicOrderAt nicolasPsiMellinContinuation rho < 0 := by
    rw [hOrder]
    exact WithTop.coe_lt_coe.mpr (by norm_num)
  have hMeromorphic : MeromorphicAt nicolasPsiMellinContinuation rho :=
    meromorphicAt_of_meromorphicOrderAt_ne_zero hOrderNeg.ne
  choose g hgAnalytic hgZero hgFactor using
    (meromorphicOrderAt_eq_int_iff hMeromorphic).1 hOrder
  have hFullScaled : Tendsto
      (fun s : Complex => (s - rho) * nicolasPsiMellinContinuation s)
      (nhdsWithin rho (Set.compl {rho})) (nhds (g rho)) := by
    apply hgAnalytic.continuousAt.continuousWithinAt.tendsto.congr'
    filter_upwards [hgFactor, self_mem_nhdsWithin] with s hs hsrho
    have hsNe : Not (s - rho = 0) := by
      exact sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hsrho)
    rw [hs]
    simp [zpow_neg_one, hsNe]
  have hDifference : Tendsto (fun s : Complex => s - rho)
      (nhdsWithin rho (Set.compl {rho})) (nhds 0) := by
    have hContinuous : ContinuousAt (fun s : Complex => s - rho) rho := by
      fun_prop
    simpa using hContinuous.tendsto.mono_left nhdsWithin_le_nhds
  have hStartup : Tendsto (nicolasPsiMellinStartup 3)
      (nhdsWithin rho (Set.compl {rho}))
      (nhds (nicolasPsiMellinStartup 3 rho)) :=
    (nicolasPsiMellinStartup_three_continuousAt rho).tendsto.mono_left
      nhdsWithin_le_nhds
  have hStartupScaled : Tendsto
      (fun s : Complex => (s - rho) * nicolasPsiMellinStartup 3 s)
      (nhdsWithin rho (Set.compl {rho})) (nhds 0) := by
    simpa using hDifference.mul hStartup
  refine Exists.intro (g rho) (And.intro hgZero ?_)
  have hTail := hFullScaled.sub hStartupScaled
  convert hTail using 1
  . funext s
    unfold nicolasPsiMellinTailContinuation
    ring
  . ring

/-- The nonzero Laurent coefficient remains visible on the positive real ray
entering the zeta zero. -/
theorem nicolasPsiMellinTailContinuation_three_simplePoleLimit_Ioi
    {rho : Complex} (hZero : riemannZeta rho = 0)
    (hRhoZero : Not (rho = 0)) (hOne : Not (rho = 1)) :
    Exists fun c : Complex => And (Not (c = 0))
      (Tendsto
        (fun u : Real => (u : Complex) *
          nicolasPsiMellinTailContinuation 3 (rho + (u : Complex)))
        (nhdsWithin 0 (Ioi 0)) (nhds c)) := by
  choose c hc hLimit using
    nicolasPsiMellinTailContinuation_three_simplePoleLimit
      hZero hRhoZero hOne
  have hRay : Tendsto (fun u : Real => rho + (u : Complex))
      (nhdsWithin 0 (Ioi 0))
      (nhdsWithin rho (Set.compl {rho})) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    . have hContinuous : ContinuousAt
          (fun u : Real => rho + (u : Complex)) 0 := by
        fun_prop
      simpa using hContinuous.tendsto.mono_left nhdsWithin_le_nhds
    . filter_upwards [self_mem_nhdsWithin] with u hu
      apply Set.mem_compl_singleton_iff.mpr
      intro hEq
      have huZero : ((u : Real) : Complex) = 0 := by
        apply add_left_cancel (a := rho)
        simpa using hEq
      exact (Complex.ofReal_ne_zero.mpr (ne_of_gt hu)) huZero
  refine Exists.intro c (And.intro hc ?_)
  simpa [Function.comp_def] using hLimit.comp hRay

end

end Robin1984

