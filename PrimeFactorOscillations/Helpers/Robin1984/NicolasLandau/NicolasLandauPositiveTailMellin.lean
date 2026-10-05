/-
Source port from Robin1984 bfa72aec0c25c8ee29cefe4449d778ff30412bee.
Original file: Robin1984/NicolasLandau/NicolasLandauPositiveTail.lean
Original source lines 1283-1523. Apache-2.0.
Statements and proof bodies retained; split at existing declaration boundaries.
-/
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.NicolasLandauPositiveTailDerivative

/-!
# The real Mellin identity for the positive tail

A source-preserving component of the written Nicolas/Landau/Mellin proof.
-/

namespace Robin1984

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section

def nicolasJShiftedComplexContinuationFilled (z : Complex) : Complex :=
  integral (volume.restrict (Ioi (0 : Real)))
    (nicolasJMellinShiftIntegrandFilled z)

def nicolasJShiftedRealContinuationFilled (a : Real) : Real :=
  Complex.re (nicolasJShiftedComplexContinuationFilled (a : Complex))

theorem nicolasJShiftedRealContinuationFilled_eq_raw
    {a : Real} (ha : a < 0) :
    nicolasJShiftedRealContinuationFilled a =
      nicolasJShiftedRealContinuation a := by
  unfold nicolasJShiftedRealContinuationFilled
    nicolasJShiftedComplexContinuationFilled
    nicolasJShiftedRealContinuation
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  exact nicolasJMellinShiftIntegrandFilled_eq_raw
    (by simpa using ha) hu

theorem nicolasLandauRpowTailMellin_eq_continuation
    {X b a : Real} (hX : 0 < X) (ha : a < b) :
    integral (volume.restrict (Ioi X)) (fun x : Real =>
        x ^ (a - 1) * x ^ (-b)) =
      nicolasLandauRpowMellinContinuation X b a := by
  calc
    integral (volume.restrict (Ioi X)) (fun x : Real =>
        x ^ (a - 1) * x ^ (-b)) =
        integral (volume.restrict (Ioi X)) (fun x : Real =>
          x ^ (a - b - 1)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hxPos : 0 < x := hX.trans hx
      change x ^ (a - 1) * x ^ (-b) = x ^ (a - b - 1)
      rw [<- Real.rpow_add hxPos]
      congr 1
      ring
    _ = -X ^ (a - b - 1 + 1) / (a - b - 1 + 1) := by
      exact integral_Ioi_rpow_of_lt (by linarith) hX
    _ = nicolasLandauRpowMellinContinuation X b a := by
      unfold nicolasLandauRpowMellinContinuation
      have hab : Not (a - b = 0) := sub_ne_zero.mpr (ne_of_lt ha)
      have hba : Not (b - a = 0) := sub_ne_zero.mpr (Ne.symm (ne_of_lt ha))
      rw [show a - b - 1 + 1 = a - b by ring]
      field_simp [hab, hba]
      ring

theorem nicolasLandauRpowMellinContinuation_analyticAt
    {X b sigma : Real} (hX : 0 < X) (hSigma : sigma < b) :
    AnalyticAt Real (nicolasLandauRpowMellinContinuation X b) sigma := by
  have hFunction : nicolasLandauRpowMellinContinuation X b =
      fun a : Real => Real.exp (Real.log X * (a - b)) / (b - a) := by
    funext a
    unfold nicolasLandauRpowMellinContinuation
    rw [Real.rpow_def_of_pos hX]
  rw [hFunction]
  have hNumerator : AnalyticAt Real
      (fun a : Real => Real.exp (Real.log X * (a - b))) sigma := by
    fun_prop
  have hDenominator : AnalyticAt Real (fun a : Real => b - a) sigma := by
    fun_prop
  exact hNumerator.div hDenominator (sub_ne_zero.mpr (ne_of_gt hSigma))

theorem nicolasJKernel_integrableOn_Ioi_three :
    IntegrableOn
      (fun t : Real => nicolasPsiError t * nicolasTailKernel t)
      (Ioi (3 : Real)) := by
  have hDouble := nicolasFrullaniDouble_integrable
    (x := (3 : Real)) (by norm_num)
  have hSlice := hDouble.integral_prod_left
  apply hSlice.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htOne : 1 < t := lt_trans (by norm_num) ht
  change
    integral (volume.restrict (Ioi (0 : Real))) (fun u : Real =>
      nicolasPsiError t * (u + 1) * t ^ (-(u + 2))) =
        nicolasPsiError t * nicolasTailKernel t
  rw [nicolasTailKernel_eq_frullani htOne, <- integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  ring

theorem nicolasJ_realMellin_integrableOn_Ioi_three
    {a : Real} (ha : a < 0) :
    IntegrableOn (fun x : Real =>
      x ^ (a - 1) * nicolasJ x) (Ioi (3 : Real)) := by
  have hTriple := nicolasJMellinTriple_integrable
    (z := (a : Complex)) (by simpa using ha)
  have hOuter := hTriple.integral_prod_left
  have hComplex : Integrable
      (fun x : Real =>
        (x : Complex) ^ ((a : Complex) - 1) * (nicolasJ x : Complex))
      (volume.restrict (Ioi (3 : Real))) := by
    apply hOuter.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact nicolasJMellinTriple_inner_eq hx.le
  have hRealPart := Complex.reCLM.integrable_comp hComplex
  apply hRealPart.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hxPos : 0 < x := lt_trans (by norm_num) hx
  have hPower : (x : Complex) ^ ((a : Complex) - 1) =
      ((x ^ (a - 1) : Real) : Complex) := by
    rw [show (a : Complex) - 1 = ((a - 1 : Real) : Complex) by
      push_cast
      rfl]
    rw [<- Complex.ofReal_cpow hxPos.le]
  rw [hPower]
  simp

theorem nicolasJ_realMellin_eq_shiftedRealContinuation
    {a : Real} (ha : a < 0) :
    integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
        x ^ (a - 1) * nicolasJ x) =
      nicolasJShiftedRealContinuation a := by
  have hCast :
      ((integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
        x ^ (a - 1) * nicolasJ x) : Real) : Complex) =
        nicolasJMellin (a : Complex) := by
    unfold nicolasJMellin
    calc
      ((integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
          x ^ (a - 1) * nicolasJ x) : Real) : Complex) =
          integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
            ((x ^ (a - 1) * nicolasJ x : Real) : Complex)) :=
        integral_ofReal.symm
      _ = integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
          (x : Complex) ^ ((a : Complex) - 1) *
            (nicolasJ x : Complex)) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hxPos : 0 < x := lt_trans (by norm_num) hx
        have hPower : (x : Complex) ^ ((a : Complex) - 1) =
            ((x ^ (a - 1) : Real) : Complex) := by
          rw [show (a : Complex) - 1 = ((a - 1 : Real) : Complex) by
            push_cast
            rfl]
          rw [<- Complex.ofReal_cpow hxPos.le]
        rw [hPower]
        push_cast
        rfl
  have hShift := nicolasJMellin_eq_integral_shift
    (z := (a : Complex)) (by simpa using ha)
  unfold nicolasJShiftedRealContinuation
  have hValue :
      ((integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
        x ^ (a - 1) * nicolasJ x) : Real) : Complex) =
        integral (volume.restrict (Ioi (0 : Real)))
          (nicolasJMellinShiftIntegrand (a : Complex)) := by
    rw [hCast, hShift]
    rfl
  exact Complex.ofReal_injective (by
    simpa using congrArg Complex.re hValue)

theorem nicolasLandauPositiveMellin_eq_continuation_of_neg
    {X b a : Real} (hX : 3 <= X) (hb : 0 < b) (ha : a < 0) :
    nicolasLandauPositiveMellin X b a =
      nicolasLandauPositiveMellinContinuation X b a := by
  have hJThree := nicolasJ_realMellin_integrableOn_Ioi_three ha
  have hJX : IntegrableOn (fun x : Real =>
      x ^ (a - 1) * nicolasJ x) (Ioi X) :=
    hJThree.mono_set (Ioi_subset_Ioi hX)
  have hJStartup : IntegrableOn (fun x : Real =>
      x ^ (a - 1) * nicolasJ x) (Ioc 3 X) :=
    hJThree.mono_set Ioc_subset_Ioi_self
  have hJSplit :
      integral (volume.restrict (Ioi (3 : Real))) (fun x : Real =>
          x ^ (a - 1) * nicolasJ x) =
        nicolasJRealMellinStartup X a +
          integral (volume.restrict (Ioi X)) (fun x : Real =>
            x ^ (a - 1) * nicolasJ x) := by
    unfold nicolasJRealMellinStartup
    rw [<- Ioc_union_Ioi_eq_Ioi hX,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi]
    . exact hJStartup
    . exact hJX
  have hXPos : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have haB : a < b := lt_trans ha hb
  have hRpowBase : IntegrableOn (fun x : Real =>
      x ^ (a - b - 1)) (Ioi X) := by
    rw [integrableOn_Ioi_rpow_iff hXPos]
    linarith
  have hRpow : IntegrableOn (fun x : Real =>
      x ^ (a - 1) * x ^ (-b)) (Ioi X) := by
    apply hRpowBase.congr_fun
    . intro x hx
      have hxPos : 0 < x := hXPos.trans hx
      change x ^ (a - b - 1) = x ^ (a - 1) * x ^ (-b)
      rw [<- Real.rpow_add hxPos]
      congr 1
      ring
    . exact measurableSet_Ioi
  unfold nicolasLandauPositiveMellin nicolasLandauPositiveTail
    nicolasLandauPositiveMellinContinuation
  have hDecomp :
      (fun x : Real => x ^ (a - 1) * (nicolasJ x + x ^ (-b))) =
        (fun x : Real => x ^ (a - 1) * nicolasJ x) +
          (fun x : Real => x ^ (a - 1) * x ^ (-b)) := by
    funext x
    dsimp
    ring
  rw [hDecomp]
  change integral (volume.restrict (Ioi X)) (fun x : Real =>
      x ^ (a - 1) * nicolasJ x + x ^ (a - 1) * x ^ (-b)) =
    nicolasJShiftedRealContinuation a - nicolasJRealMellinStartup X a +
      nicolasLandauRpowMellinContinuation X b a
  rw [integral_add hJX hRpow]
  rw [nicolasLandauRpowTailMellin_eq_continuation hXPos haB]
  rw [nicolasJ_realMellin_eq_shiftedRealContinuation ha] at hJSplit
  linarith

theorem nicolasLandauPositiveTail_integrableOn_of_neg
    {X b a : Real} (hX : 3 <= X) (hb : 0 < b) (ha : a < 0) :
    IntegrableOn (fun x : Real =>
      x ^ (a - 1) * nicolasLandauPositiveTail b x) (Ioi X) := by
  have hJ : IntegrableOn (fun x : Real =>
      x ^ (a - 1) * nicolasJ x) (Ioi X) :=
    nicolasJ_realMellin_integrableOn_Ioi_three ha |>.mono_set
      (Ioi_subset_Ioi hX)
  have hXPos : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hPowerBase : IntegrableOn (fun x : Real =>
      x ^ (a - b - 1)) (Ioi X) := by
    rw [integrableOn_Ioi_rpow_iff hXPos]
    linarith
  have hRpow : IntegrableOn (fun x : Real =>
      x ^ (a - 1) * x ^ (-b)) (Ioi X) := by
    apply hPowerBase.congr_fun
    . intro x hx
      have hxPos : 0 < x := hXPos.trans hx
      change x ^ (a - b - 1) = x ^ (a - 1) * x ^ (-b)
      rw [<- Real.rpow_add hxPos]
      congr 1
      ring
    . exact measurableSet_Ioi
  apply (hJ.add hRpow).congr_fun
  . intro x hx
    unfold nicolasLandauPositiveTail
    change x ^ (a - 1) * nicolasJ x + x ^ (a - 1) * x ^ (-b) =
      x ^ (a - 1) * (nicolasJ x + x ^ (-b))
    ring
  . exact measurableSet_Ioi

end

end Robin1984

