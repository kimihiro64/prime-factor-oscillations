/-
Source port from Robin1984 bfa72aec0c25c8ee29cefe4449d778ff30412bee.
Original file: Robin1984/NicolasLandau/NicolasLandauCompactBlock.lean
Original source lines 1068-1186. Apache-2.0.
Statements and proof bodies retained; split at existing declaration boundaries.
-/
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.NicolasLandauCompactContinuation

/-!
# The real analytic positive-tail continuation at zero

A source-preserving component of the written Nicolas/Landau/Mellin proof.
-/

namespace Robin1984

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

theorem realAnalyticAt_re_comp_of_complexAnalyticAt
    {f : Complex -> Complex} {a : Real}
    (hf : AnalyticAt Complex f (a : Complex)) :
    AnalyticAt Real (fun x : Real => Complex.re (f (x : Complex))) a := by
  have hRestricted : AnalyticAt Real f (a : Complex) :=
    hf.restrictScalars
  have hInput : AnalyticAt Real
      (Function.comp f Complex.ofRealCLM) a :=
    hRestricted.compContinuousLinearMap
  change AnalyticAt Real
    (Function.comp Complex.reCLM
      (Function.comp f Complex.ofRealCLM)) a
  choose p hp using hInput
  choose r hr using hp
  refine Exists.intro (Complex.reCLM.compFormalMultilinearSeries p) ?_
  exact Exists.intro r (Complex.reCLM.comp_hasFPowerSeriesOnBall hr)

theorem nicolasJShiftedRealContinuationFilled_analyticAt_zero :
    AnalyticAt Real nicolasJShiftedRealContinuationFilled 0 := by
  unfold nicolasJShiftedRealContinuationFilled
  exact realAnalyticAt_re_comp_of_complexAnalyticAt
    nicolasJShiftedComplexContinuationFilled_analyticAt_zero

def nicolasLandauPositiveMellinContinuationFilled
    (X b a : Real) : Real :=
  nicolasJShiftedRealContinuationFilled a -
    Complex.re (nicolasJComplexMellinStartup X (a : Complex)) +
      nicolasLandauRpowMellinContinuation X b a

theorem nicolasLandauPositiveMellinContinuationFilled_analyticAt_zero
    {X b : Real} (hX : 3 <= X) (hb : 0 < b) :
    AnalyticAt Real (nicolasLandauPositiveMellinContinuationFilled X b) 0 := by
  have hStartup : AnalyticAt Real
      (fun a : Real =>
        Complex.re (nicolasJComplexMellinStartup X (a : Complex))) 0 :=
    realAnalyticAt_re_comp_of_complexAnalyticAt
      (nicolasJComplexMellinStartup_analyticAt hX 0)
  have hRpow := nicolasLandauRpowMellinContinuation_analyticAt
    (X := X) (b := b) (sigma := (0 : Real))
    (lt_of_lt_of_le (by norm_num) hX) hb
  unfold nicolasLandauPositiveMellinContinuationFilled
  exact nicolasJShiftedRealContinuationFilled_analyticAt_zero.sub
    hStartup |>.add hRpow

theorem re_nicolasJComplexMellinStartup_eq_real_of_neg
    {X a : Real} (hX : 3 <= X) (ha : a < 0) :
    Complex.re (nicolasJComplexMellinStartup X (a : Complex)) =
      nicolasJRealMellinStartup X a := by
  have hReal : IntegrableOn (fun x : Real =>
      x ^ (a - 1) * nicolasJ x) (Ioc (3 : Real) X) :=
    (nicolasJ_realMellin_integrableOn_Ioi_three ha).mono_set
      Ioc_subset_Ioi_self
  have hCast : IntegrableOn (fun x : Real =>
      ((x ^ (a - 1) * nicolasJ x : Real) : Complex))
      (Ioc (3 : Real) X) :=
    Complex.ofRealCLM.integrable_comp hReal
  have hComplex : IntegrableOn (fun x : Real =>
      (x : Complex) ^ ((a : Complex) - 1) * (nicolasJ x : Complex))
      (Ioc (3 : Real) X) := by
    apply hCast.congr_fun
    . intro x hx
      have hxPos : 0 < x := lt_trans (by norm_num) hx.1
      change ((x ^ (a - 1) * nicolasJ x : Real) : Complex) =
        (x : Complex) ^ ((a : Complex) - 1) * (nicolasJ x : Complex)
      rw [show (a : Complex) - 1 = ((a - 1 : Real) : Complex) by
        push_cast
        rfl]
      rw [<- Complex.ofReal_cpow hxPos.le (a - 1)]
      push_cast
      rfl
    . exact measurableSet_Ioc
  have hRe := integral_re hComplex
  unfold nicolasJComplexMellinStartup nicolasJRealMellinStartup
  calc
    Complex.re (integral (volume.restrict (Ioc (3 : Real) X))
        (fun x : Real =>
          (x : Complex) ^ ((a : Complex) - 1) * (nicolasJ x : Complex))) =
        integral (volume.restrict (Ioc (3 : Real) X)) (fun x : Real =>
          Complex.re ((x : Complex) ^ ((a : Complex) - 1) *
            (nicolasJ x : Complex))) := hRe.symm
    _ = integral (volume.restrict (Ioc (3 : Real) X)) (fun x : Real =>
          x ^ (a - 1) * nicolasJ x) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      have hxPos : 0 < x := lt_trans (by norm_num) hx.1
      rw [show (a : Complex) - 1 = ((a - 1 : Real) : Complex) by
        push_cast
        rfl]
      have hPoint :
          (x : Complex) ^ ((a - 1 : Real) : Complex) *
              (nicolasJ x : Complex) =
            ((x ^ (a - 1) * nicolasJ x : Real) : Complex) := by
        calc
          (x : Complex) ^ ((a - 1 : Real) : Complex) *
                (nicolasJ x : Complex) =
              ((x ^ (a - 1) : Real) : Complex) *
                (nicolasJ x : Complex) := by
            congr 1
            exact (Complex.ofReal_cpow hxPos.le (a - 1)).symm
          _ = ((x ^ (a - 1) * nicolasJ x : Real) : Complex) := by
            push_cast
            rfl
      change Complex.re
          ((x : Complex) ^ ((a - 1 : Real) : Complex) *
            (nicolasJ x : Complex)) =
        x ^ (a - 1) * nicolasJ x
      rw [hPoint]
      simp

theorem nicolasLandauPositiveMellinContinuationFilled_eq_raw_of_neg
    {X b a : Real} (hX : 3 <= X) (ha : a < 0) :
    nicolasLandauPositiveMellinContinuationFilled X b a =
      nicolasLandauPositiveMellinContinuation X b a := by
  unfold nicolasLandauPositiveMellinContinuationFilled
    nicolasLandauPositiveMellinContinuation
  rw [nicolasJShiftedRealContinuationFilled_eq_raw ha,
    re_nicolasJComplexMellinStartup_eq_real_of_neg hX ha]

end

end Robin1984

