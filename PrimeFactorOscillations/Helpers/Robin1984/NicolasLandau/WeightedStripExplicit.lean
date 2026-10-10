/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors

Generalizes the maintained Robin1984 explicit-formula proof,
ported from bfa72aec0c25c8ee29cefe4449d778ff30412bee (Apache-2.0).
-/
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.WeightedExplicitFormula
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.WeightedPsiError
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.WeightedStripInterchange

/-!
# Weighted explicit formula under an upper strip bound

The complete zero series, arithmetic prime-power sum, and trivial-zero
correction are retained. The sole zero-location hypothesis is Re(rho) <= 1;
no critical-line assumption is used. Integer weights satisfy n >= 2.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Robin1984
open Complex MeasureTheory Set

theorem integrable_complete_xi_test_strip
    (hUpper : forall p : RiemannXiDivisorZeroIndex,
      (riemannXiDivisorZeroValue p).re <= 1) {H : Real -> Complex} (hH : Integrable H)
    {C : Real} (hC : 0 <= C)
    (hBound : forall t : Real, norm (H t) <=
      C * (Inv.inv (norm ((3 / 2 : Complex) + (t : Complex) * Complex.I))) ^ (2 : Nat)) :
    Integrable (fun t : Real => H t *
      tsum (fun p : RiemannXiDivisorZeroIndex =>
        1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I - riemannXiDivisorZeroValue p) +
          1 / riemannXiDivisorZeroValue p)) := by
  let := countable_robinXiDivisorZeroIndex
  have hInt := integrable_complex_series_of_integral_norm
    (fun p => integrable_paired_xi_atom_strip hH
      (hUpper p))
    (summable_integral_norm_paired_xi_atoms_strip hUpper hH hC hBound)
  apply hInt.congr
  filter_upwards with t
  rw [tsum_mul_left]

/-- The exact arithmetic weighted explicit formula, retaining every zero
with analytic multiplicity and every negative-even gamma term. -/
theorem robinPrimePowerSum_eq_weighted_explicit_series_strip
    (hUpper : forall p : RiemannXiDivisorZeroIndex,
      (riemannXiDivisorZeroValue p).re <= 1) {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    tsum (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex) *
      robinCutoffMellinTest n x (m : Real)) =
      robinZeroKernel n 1 x -
        tsum (fun p : RiemannXiDivisorZeroIndex =>
          robinZeroKernel n (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p) -
        (Real.log (2 * Real.pi) : Complex) * robinCutoffMellinTest n x 1 +
        tsum (fun k : Nat =>
          robinZeroKernel n (-(2 * ((k : Complex) + 1))) x / (2 * ((k : Complex) + 1))) := by
  choose C hC hBound using exists_robinCutoffMellin_safeLine_majorant hn hx
  have hnOne : 1 <= n := by omega
  have hnReal : (2 : Real) <= n := by exact_mod_cast hn
  have hcPos : (0 : Real) < 3 / 2 := by norm_num
  have hc : (1 : Real) < 3 / 2 := by norm_num
  have hcLt : (3 / 2 : Real) < n := by linarith
  let K : Complex := (((1 / (2 * Real.pi) : Real) : Complex))
  let H : Real -> Complex := fun t =>
    mellin (robinCutoffMellinTest n x) ((3 / 2 : Complex) + (t : Complex) * Complex.I)
  let C0 : Complex := -logDeriv riemannXi 0 -
    (1 / 2 : Complex) * (Real.log Real.pi : Complex) -
      (Real.eulerMascheroniConstant : Complex) / 2
  let Z : Real -> Complex := fun t => H t *
    tsum (fun p : RiemannXiDivisorZeroIndex =>
      1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I - riemannXiDivisorZeroValue p) +
        1 / riemannXiDivisorZeroValue p)
  let B : Real -> Complex := fun t =>
    H t / ((3 / 2 : Complex) + (t : Complex) * Complex.I - 1)
  let G : Real -> Complex := fun t => H t *
    ((1 / 2 : Complex) * Complex.digamma
      (((3 / 2 : Complex) + (t : Complex) * Complex.I) / 2 + 1) +
        (Real.eulerMascheroniConstant : Complex) / 2)
  have hH : Integrable H := by
    simpa [H, Complex.VerticalIntegrable] using! verticalIntegrable_mellin_robinCutoffMellinTest
      hnOne hx hcPos hcLt
  have hZ : Integrable Z := integrable_complete_xi_test_strip hUpper hH hC hBound
  have hB : Integrable B := by
    simpa [B] using! integrable_vertical_resolvent hH
      (c := (3 / 2 : Real)) (rho := 1) (by norm_num)
  have hG : Integrable G := integrable_shifted_gamma_test hH hC hBound
  have hConst : Integrable (fun t : Real => C0 * H t) := hH.const_mul C0
  have hSource : forall t : Real,
      (-deriv riemannZeta ((3 / 2 : Complex) + (t : Complex) * Complex.I) /
        riemannZeta ((3 / 2 : Complex) + (t : Complex) * Complex.I)) * H t =
        C0 * H t - Z t + B t + G t := by
    intro t
    rw [neg_riemannZeta_logDeriv_eq_xiDivisor_tsum (by simp; norm_num)]
    dsimp only [C0, Z, B, G]
    ring
  have hArithmetic : tsum (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex) *
      robinCutoffMellinTest n x (m : Real)) =
      K * integral volume (fun t : Real =>
        (-deriv riemannZeta ((3 / 2 : Complex) + (t : Complex) * Complex.I) /
          riemannZeta ((3 / 2 : Complex) + (t : Complex) * Complex.I)) * H t) := by
    simpa [K, H] using! robinPrimePowerSum_eq_safeLineIntegral hnOne hx hc hcLt
  have hIntegral : integral volume (fun t : Real =>
      (-deriv riemannZeta ((3 / 2 : Complex) + (t : Complex) * Complex.I) /
        riemannZeta ((3 / 2 : Complex) + (t : Complex) * Complex.I)) * H t) =
      C0 * integral volume H - integral volume Z + integral volume B + integral volume G := by
    calc
      integral volume (fun t : Real =>
          (-deriv riemannZeta ((3 / 2 : Complex) + (t : Complex) * Complex.I) /
            riemannZeta ((3 / 2 : Complex) + (t : Complex) * Complex.I)) * H t) =
          integral volume (fun t : Real => C0 * H t - Z t + B t + G t) :=
        integral_congr_ae (Filter.Eventually.of_forall hSource)
      _ = _ := by
        have hAdd := integral_add ((hConst.sub hZ).add hB) hG
        have hMid := integral_add (hConst.sub hZ) hB
        have hSub := integral_sub hConst hZ
        simp only [Pi.add_apply, Pi.sub_apply] at hAdd hMid hSub
        rw [hAdd, hMid, hSub, integral_const_mul]
  have hAtOne : K * integral volume H = robinCutoffMellinTest n x 1 := by
    have h := mellinInv_mellin_robinCutoffMellinTest hnOne hx hcPos hcLt Real.zero_lt_one
    simpa [mellinInv, RCLike.real_smul_eq_coe_mul, smul_eq_mul, H, K] using! h
  have hZeros : K * integral volume Z =
      tsum (fun p : RiemannXiDivisorZeroIndex =>
        robinZeroKernel n (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p) := by
    simpa [K, Z, H] using! robinCutoffMellin_complete_zero_pairing_strip hUpper hn hx
  have hGamma : K * integral volume G =
      tsum (fun k : Nat =>
        robinZeroKernel n (-(2 * ((k : Complex) + 1))) x / (2 * ((k : Complex) + 1))) := by
    simpa [K, G, H] using! robinCutoffMellin_complete_gamma_pairing hn hx
  have hPole : K * integral volume B = robinZeroKernel n 1 x - robinCutoffMellinTest n x 1 := by
    have h := robinCutoffMellin_resolvent_pairing hnOne hx hcPos hcLt
      (rho := 1) (by norm_num)
    rw [robinCutoffMellinTest_power_tail_eq hx (by norm_num : Not ((1 : Complex) = 0))
      (by simp; linarith : (1 : Complex).re < (n : Real))] at h
    simpa [K, B, H] using! h
  have hC0 : C0 - 1 = -(Real.log (2 * Real.pi) : Complex) := robin_weighted_explicit_constant
  rw [hArithmetic, hIntegral]
  have hAlgebra : K * (C0 * integral volume H - integral volume Z +
      integral volume B + integral volume G) =
      C0 * (K * integral volume H) - K * integral volume Z +
        K * integral volume B + K * integral volume G := by ring
  rw [hAlgebra, hAtOne, hZeros, hPole, hGamma]
  linear_combination robinCutoffMellinTest n x 1 * hC0

theorem robinPsiWeightedErrorIntegral_eq_zero_sum_correction_strip
    (hUpper : forall p : RiemannXiDivisorZeroIndex,
      (riemannXiDivisorZeroValue p).re <= 1) {n : Nat} (hn : 2 <= n) {x : Real} (hx : 2 <= x) :
    (robinPsiWeightedErrorIntegral n x : Complex) =
      -tsum (fun p : RiemannXiDivisorZeroIndex =>
        robinZeroKernel n (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p) -
          (robinTrivialZeroCorrection n x : Complex) := by
  have hxOne : 1 < x := by linarith
  have hnOne : 1 <= n := by omega
  have hPsi := integrableOn_complex_psi_robinRealWeight hn hxOne
  have hMain := integrableOn_complex_t_robinRealWeight hn hxOne
  have hError : (robinPsiWeightedErrorIntegral n x : Complex) =
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        ((Chebyshev.psi t * robinRealWeight n t : Real) : Complex)) -
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        ((t * robinRealWeight n t : Real) : Complex)) := by
    rw [robinPsiWeightedErrorIntegral, <- integral_complex_ofReal]
    have hFunction : (fun t : Real => (((Chebyshev.psi t - t) * robinRealWeight n t : Real) : Complex)) =
        (fun t : Real => ((Chebyshev.psi t * robinRealWeight n t : Real) : Complex) -
          ((t * robinRealWeight n t : Real) : Complex)) := by
      funext t
      push_cast
      ring
    rw [hFunction]
    exact integral_sub hPsi hMain
  rw [hError, <- robinPrimePowerSum_eq_integral_psi_weight hn hxOne,
    <- robinZeroKernel_one_eq_integral_t_weight n hxOne,
    robinPrimePowerSum_eq_weighted_explicit_series_strip hUpper hn hxOne]
  have hCorrection := robin_explicit_correction_eq hnOne hx
  linear_combination hCorrection

end Robin1984
