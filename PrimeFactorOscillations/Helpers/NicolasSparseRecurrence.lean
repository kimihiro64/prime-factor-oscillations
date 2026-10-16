/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.XiZeroLogSpectrum
import PrimeFactorOscillations.Mathlib.Analysis.Fourier.LogarithmicRecurrence

/-!
# Sharp amplitude on sparse meshes

Simultaneous phase returns and logarithmic mesh approximation give the exact limsup without independence assumptions.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter
open scoped Topology

noncomputable section

namespace PrimeFactorOscillations

open Robin1984 Complex

theorem countable_xiZeroIndex : Countable RiemannXiDivisorZeroIndex := by
  have hSupport : Function.support (fun p : RiemannXiDivisorZeroIndex =>
      (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ 2) = Set.univ := by
    ext p
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact pow_ne_zero 2 (inv_ne_zero (norm_ne_zero_iff.mpr (riemannXiDivisorZeroValue_ne_zero p)))
  have hCount := summable_robinXiZeroWeight.countable_support
  rw [hSupport] at hCount
  exact Set.countable_univ_iff.mp hCount

theorem exists_nicolasZeroWave_return_sequence (hRH : RiemannHypothesis) :
    Exists (fun d : Nat -> Nat => Tendsto d atTop atTop /\
      Tendsto (fun n : Nat => nicolasZeroWave (Real.exp (d n : Real))) atTop
        (nhds (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)))) := by
  letI : Countable RiemannXiDivisorZeroIndex := countable_xiZeroIndex
  refine (exists_logSpectrum_return_sequence xiWaveWeight
    (fun p => (riemannXiDivisorZeroValue p).im) (summable_xiWaveWeight hRH)).imp ?_
  intro d hd
  have hSum : tsum xiWaveWeight = Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi) := by
    calc
      _ = tsum (fun p : RiemannXiDivisorZeroIndex =>
          (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ 2) :=
        tsum_congr (xiWaveWeight_eq_norm hRH)
      _ = _ := robinXiZeroConstant_eq_of_riemannHypothesis hRH
  have hReturn : Tendsto (fun n : Nat =>
      (logSpectrum (fun p => (xiWaveWeight p : Complex))
        (fun p => (riemannXiDivisorZeroValue p).im) (Real.exp (d n : Real))).re)
      atTop (nhds (tsum xiWaveWeight)) := hd.2
  rw [hSum] at hReturn
  refine And.intro hd.1 ?_
  apply hReturn.congr'
  filter_upwards [hd.1.eventually_ge_atTop 1] with n hn
  have hPos : (0 : Real) < d n :=
    Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  exact (nicolasZeroWave_eq_logSpectrum hRH (Real.one_lt_exp_iff.mpr hPos)).symm


/-- The full spectral amplitude is approached along every admissible sparse mesh. -/
theorem exists_nicolasZeroWave_mesh_return_sequence (hRH : RiemannHypothesis)
    (u : Nat -> Nat) (hu : StrictMono u) (hmesh : Nat.SubpowerGapBound u (3 / 4 : Real)) :
    Exists (fun j : Nat -> Nat => Tendsto j atTop atTop /\
      Tendsto (fun n : Nat => nicolasZeroWave (u (j n) : Real)) atTop
        (nhds (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)))) := by
  letI : Countable RiemannXiDivisorZeroIndex := countable_xiZeroIndex
  let f : RiemannXiDivisorZeroIndex -> Real := fun p => (riemannXiDivisorZeroValue p).im
  refine (exists_simultaneous_phase_returns f).elim ?_
  intro d hd
  have hDReal : Tendsto (fun n : Nat => (d n : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hd.1
  refine (Nat.exists_subpower_mesh_log_approximation u hu hmesh
    (fun n : Nat => (d n : Real)) hDReal).imp ?_
  intro j hj
  have hChar (p : RiemannXiDivisorZeroIndex) :
      Tendsto (fun n : Nat => logCharacter (f p) (u (j n) : Real)) atTop (nhds 1) := by
    have hCircle := (continuous_subtype_val.tendsto (1 : Circle)).comp (hd.2 p)
    change Tendsto (fun n : Nat => (Circle.exp (f p * (d n : Real)) : Complex))
      atTop (nhds 1) at hCircle
    have hError : Tendsto (fun n : Nat =>
        ((Real.log (u (j n) : Real) - (d n : Real) : Real) : Complex)) atTop (nhds 0) := by
      simpa only [Function.comp_def, Complex.ofReal_zero] using
        (Complex.continuous_ofReal.tendsto (0 : Real)).comp hj.2
    have hProd : Tendsto (fun n : Nat =>
        (f p : Complex) * Complex.I *
          ((Real.log (u (j n) : Real) - (d n : Real) : Real) : Complex))
        atTop (nhds 0) := by
      simpa only [mul_zero] using (tendsto_const_nhds.mul hError)
    have hSmall : Tendsto (fun n : Nat =>
        Complex.exp ((f p : Complex) * Complex.I *
          ((Real.log (u (j n) : Real) - (d n : Real) : Real) : Complex)))
        atTop (nhds 1) := by
      simpa only [Function.comp_def, Complex.exp_zero] using
        (Complex.continuous_exp.tendsto (0 : Complex)).comp hProd
    have hMult := hCircle.mul hSmall
    norm_num only [mul_one] at hMult
    have hId (n : Nat) :
        (Circle.exp (f p * (d n : Real)) : Complex) *
          Complex.exp ((f p : Complex) * Complex.I *
            ((Real.log (u (j n) : Real) - (d n : Real) : Real) : Complex)) =
        logCharacter (f p) (u (j n) : Real) := by
      rw [Circle.coe_exp, <- Complex.exp_add]
      unfold logCharacter
      congr 1 <;> push_cast <;> ring
    exact hMult.congr' (Filter.Eventually.of_forall hId)
  have hSpec := tendsto_logSpectrum_of_phase_tendsto_one xiWaveWeight f
    (summable_xiWaveWeight hRH) (fun n : Nat => (u (j n) : Real)) hChar
  have hSum : tsum xiWaveWeight = Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi) := by
    calc
      _ = tsum (fun p : RiemannXiDivisorZeroIndex =>
          (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ 2) :=
        tsum_congr (xiWaveWeight_eq_norm hRH)
      _ = _ := robinXiZeroConstant_eq_of_riemannHypothesis hRH
  rw [hSum] at hSpec
  have hY : Tendsto (fun n : Nat => (u (j n) : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (hu.tendsto_atTop.comp hj.1)
  refine And.intro hj.1 ?_
  apply hSpec.congr'
  filter_upwards [hY.eventually_gt_atTop 1] with n hn
  exact (nicolasZeroWave_eq_logSpectrum hRH hn).symm

namespace QuadraticPrimeLaw

/-- The full spectral amplitude is the exact limsup of every qualifying family
on every admissible subpower mesh. -/
theorem limsup_normalizedFloorRatioWave_subpower_mesh
    (law : QuadraticPrimeLaw) (alpha : Real) (ha : 0 < alpha)
    (hRH : RiemannHypothesis) (u : Nat -> Nat) (hu : StrictMono u)
    (hmesh : Nat.SubpowerGapBound u (3 / 4 : Real)) :
    Filter.limsup (fun j : Nat => law.normalizedFloorRatioWave alpha (u j)) atTop =
      Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi) := by
  let b : Real := Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)
  have hError : Tendsto (fun j : Nat =>
      law.normalizedFloorRatioWave alpha (u j) - nicolasZeroWave (u j : Real))
      atTop (nhds 0) :=
    (law.tendsto_normalizedFloorRatioWave_sub_zeroWave alpha ha hRH).comp hu.tendsto_atTop
  refine (exists_nicolasZeroWave_mesh_return_sequence hRH u hu hmesh).elim ?_
  intro j hj
  have hLimit : Tendsto (fun n : Nat => law.normalizedFloorRatioWave alpha (u (j n)))
      atTop (nhds b) := by
    have h := (hError.comp hj.1).add hj.2
    simpa only [Function.comp_def, sub_add_cancel, zero_add] using h
  apply limsup_eq_of_eventually_le_and_frequently_gt _ b
  . intro eps heps
    have hSmall := hError.eventually (eventually_le_nhds heps)
    have hLarge := hu.tendsto_atTop.eventually_ge_atTop 2
    filter_upwards [hSmall, hLarge] with k hk hN
    have hNReal : (1 : Real) < u k := by
      have hNat : 1 < u k := Nat.lt_of_lt_of_le (by decide : 1 < 2) hN
      simpa only [Nat.cast_one] using
        (Nat.cast_lt.mpr hNat : ((1 : Nat) : Real) < (u k : Real))
    have hW : nicolasZeroWave (u k : Real) <= b :=
      (le_abs_self _).trans (abs_nicolasZeroWave_le hRH hNReal)
    linarith
  . intro eps heps
    change Not (Filter.Eventually (fun k : Nat =>
      Not (b - eps < law.normalizedFloorRatioWave alpha (u k))) atTop)
    intro hNot
    have hPull := hj.1.eventually hNot
    have hPos := hLimit.eventually (eventually_gt_nhds (by linarith : b - eps < b))
    have hFalse : Filter.Eventually (fun _ : Nat => False) atTop := by
      filter_upwards [hPull, hPos] with n hn hp
      exact hn hp
    exact Exists.elim hFalse.exists (fun _ h => h)

end QuadraticPrimeLaw

end PrimeFactorOscillations
