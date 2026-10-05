/-
Source port from Robin1984 bfa72aec0c25c8ee29cefe4449d778ff30412bee.
Original file: Robin1984/NicolasLandau/NicolasLandau.lean
Original source lines 439-752. Apache-2.0.
Statements and proof bodies retained; split at existing declaration boundaries.
-/
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.NicolasLandauPsiMellin

/-!
# The exact Frullani representation and Mellin cell

A source-preserving component of the written Nicolas/Landau/Mellin proof.
-/

namespace Robin1984

open Asymptotics Filter MeasureTheory Set

noncomputable section

/-- Nicolas's kernel is a positive Frullani/Gamma mixture of pure powers.
This exact identity exposes the zeta logarithmic derivative inside `J`. -/
theorem nicolasTailKernel_eq_frullani
    {t : Real} (ht : 1 < t) :
    nicolasTailKernel t =
      integral (volume.restrict (Ioi (0 : Real)))
        (fun u : Real => (u + 1) * t ^ (-(u + 2))) := by
  have htPos : 0 < t := lt_trans (by norm_num) ht
  have hLog : 0 < Real.log t := Real.log_pos ht
  have hPoint : forall u : Real,
      (u + 1) * t ^ (-(u + 2)) =
        t ^ (-(2 : Real)) *
          (u * Real.exp (-(Real.log t * u)) +
            Real.exp (-(Real.log t * u))) := by
    intro u
    have hPower : t ^ (-(u + 2)) =
        t ^ (-(2 : Real)) * Real.exp (-(Real.log t * u)) := by
      rw [Real.rpow_def_of_pos htPos, Real.rpow_def_of_pos htPos]
      rw [<- Real.exp_add]
      congr 1
      ring
    rw [hPower]
    ring
  have hExpInt : IntegrableOn
      (fun u : Real => Real.exp (-(Real.log t * u))) (Ioi 0) := by
    have hBase := integrableOn_exp_mul_Ioi
      (a := -Real.log t) (by linarith) 0
    apply hBase.congr_fun
    . intro u hu
      congr 1
      ring
    . exact measurableSet_Ioi
  have hMulInt := integrableOn_mul_exp_neg_mul_Ioi_zero hLog
  calc
    nicolasTailKernel t =
        t ^ (-(2 : Real)) *
          (1 / (Real.log t) ^ 2 + 1 / Real.log t) := by
      unfold nicolasTailKernel
      rw [Real.rpow_neg htPos.le, Real.rpow_two]
      field_simp [htPos.ne', hLog.ne']
      ring
    _ = t ^ (-(2 : Real)) *
        (integral (volume.restrict (Ioi (0 : Real)))
            (fun u : Real => u * Real.exp (-(Real.log t * u))) +
          integral (volume.restrict (Ioi (0 : Real)))
            (fun u : Real => Real.exp (-(Real.log t * u)))) := by
      rw [integral_mul_exp_neg_mul_Ioi_zero hLog,
        integral_exp_neg_mul_Ioi_zero hLog]
    _ = integral (volume.restrict (Ioi (0 : Real)))
        (fun u : Real => (u + 1) * t ^ (-(u + 2))) := by
      rw [<- integral_add hMulInt hExpInt, <- integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      symm
      exact hPoint u

theorem nicolasFrullaniKernel_integrable
    {t : Real} (ht : 1 < t) :
    IntegrableOn (fun u : Real => (u + 1) * t ^ (-(u + 2))) (Ioi 0) := by
  have htPos : 0 < t := lt_trans (by norm_num) ht
  have hLog : 0 < Real.log t := Real.log_pos ht
  have hExpInt : IntegrableOn
      (fun u : Real => Real.exp (-(Real.log t * u))) (Ioi 0) := by
    have hBase := integrableOn_exp_mul_Ioi
      (a := -Real.log t) (by linarith) 0
    apply hBase.congr_fun
    . intro u hu
      congr 1
      ring
    . exact measurableSet_Ioi
  have hMulInt := integrableOn_mul_exp_neg_mul_Ioi_zero hLog
  have hSumInt := hMulInt.add hExpInt
  have hScaled := hSumInt.const_mul (t ^ (-(2 : Real)))
  change Integrable (fun u : Real => (u + 1) * t ^ (-(u + 2)))
    (volume.restrict (Ioi 0))
  apply hScaled.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hPower : t ^ (-(u + 2)) =
      t ^ (-(2 : Real)) * Real.exp (-(Real.log t * u)) := by
    rw [Real.rpow_def_of_pos htPos, Real.rpow_def_of_pos htPos]
    rw [<- Real.exp_add]
    congr 1
    ring
  calc
    t ^ (-(2 : Real)) *
        (u * Real.exp (-(Real.log t * u)) +
          Real.exp (-(Real.log t * u))) =
        (u + 1) * t ^ (-(u + 2)) := by
      rw [hPower]
      ring

/-- The complete Nicolas `J` tail as a two-variable Frullani integral.  No
Schedule, endpoint, or tail is discarded; this is the exact surface on which
Fubini connects `J` to the zeta logarithmic derivative. -/
theorem nicolasJ_eq_frullaniDouble
    {x : Real} (hx : 1 <= x) :
    nicolasJ x =
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
          nicolasPsiError t * (u + 1) * t ^ (-(u + 2)))) := by
  unfold nicolasJ
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have htOne : 1 < t := lt_of_le_of_lt hx ht
  change nicolasPsiError t * nicolasTailKernel t =
    integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
      nicolasPsiError t * (u + 1) * t ^ (-(u + 2)))
  rw [nicolasTailKernel_eq_frullani htOne]
  rw [<- integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  ring

/-- Absolute integrability of the complete two-variable Frullani carrier.
This is the Tonelli/Fubini gate needed to turn the exact `J` representation
into the zeta-logarithmic-derivative integral. -/
theorem nicolasFrullaniDouble_integrable
    {x : Real} (hx : 3 <= x) :
    Integrable
      (fun p : Prod Real Real =>
        nicolasPsiError p.1 * (p.2 + 1) * p.1 ^ (-(p.2 + 2)))
      ((volume.restrict (Ioi x)).prod
        (volume.restrict (Ioi (0 : Real)))) := by
  let f : Prod Real Real -> Real := fun p =>
    nicolasPsiError p.1 * (p.2 + 1) * p.1 ^ (-(p.2 + 2))
  have hMeas : AEStronglyMeasurable f
      ((volume.restrict (Ioi x)).prod
        (volume.restrict (Ioi (0 : Real)))) := by
    apply AEMeasurable.aestronglyMeasurable
    have hFst : AEMeasurable (fun p : Prod Real Real => p.1)
        ((volume.restrict (Ioi x)).prod
          (volume.restrict (Ioi (0 : Real)))) :=
      measurable_fst.aemeasurable
    have hSnd : AEMeasurable (fun p : Prod Real Real => p.2)
        ((volume.restrict (Ioi x)).prod
          (volume.restrict (Ioi (0 : Real)))) :=
      measurable_snd.aemeasurable
    have hPsi : AEMeasurable
        (fun p : Prod Real Real => nicolasPsiError p.1)
        ((volume.restrict (Ioi x)).prod
          (volume.restrict (Ioi (0 : Real)))) := by
      unfold nicolasPsiError
      exact ((Chebyshev.psi_mono.measurable.comp_aemeasurable hFst).sub hFst)
    have hExponent : AEMeasurable
        (fun p : Prod Real Real => -(p.2 + 2))
        ((volume.restrict (Ioi x)).prod
          (volume.restrict (Ioi (0 : Real)))) :=
      (hSnd.add_const 2).neg
    have hPower : AEMeasurable
        (fun p : Prod Real Real => p.1 ^ (-(p.2 + 2)))
        ((volume.restrict (Ioi x)).prod
          (volume.restrict (Ioi (0 : Real)))) :=
      hFst.pow hExponent
    exact (hPsi.mul (hSnd.add_const 1)).mul hPower
  change Integrable f
    ((volume.restrict (Ioi x)).prod
      (volume.restrict (Ioi (0 : Real))))
  apply (integrable_prod_iff hMeas).2
  constructor
  . filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htOne : 1 < t :=
      lt_trans (by norm_num) (lt_of_le_of_lt hx ht)
    have hKernel := nicolasFrullaniKernel_integrable htOne
    have hScaled := hKernel.const_mul (nicolasPsiError t)
    change Integrable (fun u : Real => f (t, u))
      (volume.restrict (Ioi (0 : Real)))
    apply hScaled.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    dsimp [f]
    ring
  . have hTail := nicolasPsiTail_integrableOn_Ioi_three.mono_set
      (Ioi_subset_Ioi hx)
    have hTailNorm := hTail.norm
    change Integrable
      (fun t : Real => integral (volume.restrict (Ioi (0 : Real)))
        (fun u : Real => norm (f (t, u))))
      (volume.restrict (Ioi x))
    apply hTailNorm.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htOne : 1 < t :=
      lt_trans (by norm_num) (lt_of_le_of_lt hx ht)
    have hKernelNonneg : 0 <= nicolasTailKernel t :=
      nicolasTailKernel_nonneg htOne.le
    change norm (nicolasPsiError t * nicolasTailKernel t) =
      integral (volume.restrict (Ioi (0 : Real)))
        (fun u : Real => norm (f (t, u)))
    calc
      norm (nicolasPsiError t * nicolasTailKernel t) =
          |nicolasPsiError t| * nicolasTailKernel t := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hKernelNonneg]
      _ = |nicolasPsiError t| *
          integral (volume.restrict (Ioi (0 : Real)))
            (fun u : Real => (u + 1) * t ^ (-(u + 2))) := by
        rw [nicolasTailKernel_eq_frullani htOne]
      _ = integral (volume.restrict (Ioi (0 : Real)))
          (fun u : Real => |nicolasPsiError t| *
            ((u + 1) * t ^ (-(u + 2)))) := by
        rw [integral_const_mul]
      _ = integral (volume.restrict (Ioi (0 : Real)))
          (fun u : Real => norm (f (t, u))) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u hu
        have huPos : 0 < u := hu
        have huNonneg : 0 <= u + 1 := by linarith
        have htPos : 0 < t := lt_trans (by norm_num) htOne
        have hPowerNonneg : 0 <= t ^ (-(u + 2)) :=
          Real.rpow_nonneg htPos.le _
        dsimp [f]
        rw [abs_mul, abs_mul,
          abs_of_nonneg huNonneg, abs_of_nonneg hPowerNonneg]
        ring


/-- The finite Mellin cell used when the `x`-integral is exchanged with a
psi-error tail.  Positivity of the lower endpoint removes the branch issue
for complex powers. -/
theorem integral_Ioc_cpow_sub_one
    {a b : Real} {z : Complex} (ha : 0 < a) (hab : a <= b)
    (hz : Not (z = 0)) :
    integral (volume.restrict (Ioc a b)) (fun x : Real =>
        (x : Complex) ^ (z - 1)) =
      ((b : Complex) ^ z - (a : Complex) ^ z) / z := by
  rw [<- intervalIntegral.integral_of_le hab]
  have hExponent : Not (z - 1 = -1) := by
    intro h
    apply hz
    calc
      z = (z - 1) + 1 := by ring
      _ = -1 + 1 := by rw [h]
      _ = 0 := by ring
  have hZeroOutside : Not (And (a <= 0) (0 <= b)) := by
    intro h
    linarith
  rw [integral_cpow (Or.inr (And.intro hExponent (by
    simpa only [uIcc_of_le hab, mem_Icc] using hZeroOutside)))]
  congr 3 <;> ring


theorem nicolasPsiErrorMellinCell_eq_shift
    {a : Real} {s z : Complex} (ha : 1 <= a) (hs : 1 < s.re)
    (hzRe : z.re < 0) :
    integral (volume.restrict (Ioi a)) (fun t : Real =>
        ((nicolasPsiError t : Complex) *
          (t : Complex) ^ (-(s + 1))) *
          (((t : Complex) ^ z - (a : Complex) ^ z) / z)) =
      (nicolasPsiMellinTailContinuation a (s - z) -
        (a : Complex) ^ z * nicolasPsiMellinTailContinuation a s) / z := by
  have haPos : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hzZero : Not (z = 0) := by
    intro hz
    subst z
    norm_num at hzRe
  have hsShift : 1 < (s - z).re := by
    simp only [Complex.sub_re]
    linarith
  let hfun : Real -> Complex := fun t =>
    (nicolasPsiError t : Complex) * (t : Complex) ^ (-(s + 1))
  let hShift : Real -> Complex := fun t =>
    (nicolasPsiError t : Complex) *
      (t : Complex) ^ (-((s - z) + 1))
  have hH : Integrable hfun (volume.restrict (Ioi a)) := by
    dsimp [hfun]
    exact (nicolasPsiErrorMellin_integrable hs).mono_set
      (Ioi_subset_Ioi ha)
  have hHShift : Integrable hShift (volume.restrict (Ioi a)) := by
    dsimp [hShift]
    exact (nicolasPsiErrorMellin_integrable hsShift).mono_set
      (Ioi_subset_Ioi ha)
  have hPowerShift : forall t : Real, a < t ->
      hfun t * (t : Complex) ^ z = hShift t := by
    intro t ht
    have htZero : Not ((t : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans haPos ht))
    dsimp [hfun, hShift]
    calc
      ((nicolasPsiError t : Complex) *
          (t : Complex) ^ (-(s + 1))) * (t : Complex) ^ z =
          (nicolasPsiError t : Complex) *
            ((t : Complex) ^ (-(s + 1)) * (t : Complex) ^ z) := by
        ring
      _ = (nicolasPsiError t : Complex) *
          (t : Complex) ^ (-(s + 1) + z) := by
        rw [Complex.cpow_add _ _ htZero]
      _ = (nicolasPsiError t : Complex) *
          (t : Complex) ^ (-((s - z) + 1)) := by
        congr 2
        ring
  change integral (volume.restrict (Ioi a)) (fun t : Real =>
      hfun t * (((t : Complex) ^ z - (a : Complex) ^ z) / z)) = _
  calc
    integral (volume.restrict (Ioi a)) (fun t : Real =>
        hfun t * (((t : Complex) ^ z - (a : Complex) ^ z) / z)) =
        integral (volume.restrict (Ioi a)) (fun t : Real =>
          (hShift t - (a : Complex) ^ z * hfun t) / z) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      calc
        hfun t * (((t : Complex) ^ z - (a : Complex) ^ z) / z) =
            (hfun t * (t : Complex) ^ z -
              (a : Complex) ^ z * hfun t) / z := by
          ring
        _ = (hShift t - (a : Complex) ^ z * hfun t) / z := by
          rw [hPowerShift t ht]
    _ = (integral (volume.restrict (Ioi a)) hShift -
        (a : Complex) ^ z * integral (volume.restrict (Ioi a)) hfun) / z := by
      rw [integral_div]
      rw [integral_sub hHShift (hH.const_mul ((a : Complex) ^ z))]
      rw [integral_const_mul]
    _ = (nicolasPsiMellinTailContinuation a (s - z) -
        (a : Complex) ^ z * nicolasPsiMellinTailContinuation a s) / z := by
      dsimp [hShift, hfun]
      rw [nicolasPsiErrorTailMellin_eq_continuation ha hsShift,
        nicolasPsiErrorTailMellin_eq_continuation ha hs]

end

end Robin1984

