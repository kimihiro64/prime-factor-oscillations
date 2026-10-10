/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors

Generalizes the maintained Robin1984 weighted Hadamard interchange proof,
ported from bfa72aec0c25c8ee29cefe4449d778ff30412bee (Apache-2.0).
-/
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.WeightedZeroInterchange

/-!
# Full Hadamard interchange with zeros left of the line one

The paired resolvent is bounded before summation. A fixed wider majorant
replaces the critical-line geometry and proves absolute integrated
summability for all canonical zeros with real part at most one.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace Robin1984
open Complex MeasureTheory Set

theorem safeLine_shift_norm_comparison {rho : Complex} (hUpper : rho.re <= 1)
    (t : Real) :
    norm ((1 : Complex) + ((t - rho.im : Real) : Complex) * Complex.I) <=
      2 * norm ((3 / 2 : Complex) + (t : Complex) * Complex.I - rho) := by
  apply le_of_sq_le_sq _ (by positivity)
  rw [mul_pow, Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re, Complex.one_im]
  norm_num
  nlinarith only [hUpper, sq_nonneg (rho.re - 1), sq_nonneg (t - rho.im)]

theorem safeLine_shift_three_halves_le {rho : Complex} (hUpper : rho.re <= 1)
    (t : Real) :
    (Inv.inv (norm ((3 / 2 : Complex) + (t : Complex) * Complex.I - rho))) ^
        (3 / 2 : Real) <=
      3 * (Inv.inv (norm ((1 : Complex) + ((t - rho.im : Real) : Complex) * Complex.I))) ^
        (3 / 2 : Real) := by
  let a := norm ((3 / 2 : Complex) + (t : Complex) * Complex.I - rho)
  let b := norm ((1 : Complex) + ((t - rho.im : Real) : Complex) * Complex.I)
  have hb : 0 < b := by
    apply norm_pos_iff.mpr
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
  have hcomp : b <= 2 * a := safeLine_shift_norm_comparison hUpper t
  have ha : 0 < a := by linarith
  have hInv : Inv.inv a <= 2 * Inv.inv b := by
    calc
      _ <= 1 / (b / 2) := by
        simpa only [one_div] using div_le_div_of_nonneg_left
          (show (0 : Real) <= 1 by norm_num) (by positivity : 0 < b / 2)
          (show b / 2 <= a by linarith)
      _ = _ := by ring
  have hPow := Real.rpow_le_rpow (inv_nonneg.mpr ha.le) hInv
    (by norm_num : (0 : Real) <= 3 / 2)
  have hTwo : (2 : Real) ^ (3 / 2 : Real) <= 3 := by
    rw [show (3 / 2 : Real) = 1 + 1 / 2 by norm_num,
      Real.rpow_add (by norm_num), Real.rpow_one, <- Real.sqrt_eq_rpow]
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : Real) <= 2), Real.sqrt_nonneg (2 : Real)]
  change (Inv.inv a) ^ (3 / 2 : Real) <= 3 * (Inv.inv b) ^ (3 / 2 : Real)
  calc
    _ <= (2 * Inv.inv b) ^ (3 / 2 : Real) := hPow
    _ = (2 : Real) ^ (3 / 2 : Real) * (Inv.inv b) ^ (3 / 2 : Real) :=
      Real.mul_rpow (by norm_num) (inv_nonneg.mpr hb.le)
    _ <= _ := mul_le_mul_of_nonneg_right hTwo (Real.rpow_nonneg (inv_nonneg.mpr hb.le) _)

/-- The paired cancellation is kept before the uniform strip estimate. -/
theorem norm_paired_hadamard_atom_mul_le_strip
    {C : Real} (hC : 0 <= C) {z rho : Complex} {t : Real}
    (hRhoZero : Not (rho = 0)) (hUpper : rho.re <= 1)
    (hz : norm z <= C *
      (Inv.inv (norm ((3 / 2 : Complex) + (t : Complex) * Complex.I))) ^ (2 : Nat)) :
    norm (z * (1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I - rho) + 1 / rho)) <=
      6 * C * (Inv.inv (norm rho)) ^ (3 / 2 : Real) *
        ((Inv.inv (norm ((3 / 2 : Complex) + (t : Complex) * Complex.I))) ^ (3 / 2 : Real) +
         (Inv.inv (norm ((1 : Complex) + ((t - rho.im : Real) : Complex) * Complex.I))) ^
           (3 / 2 : Real)) := by
  let s : Complex := (3 / 2 : Complex) + (t : Complex) * Complex.I
  have hsRe : s.re = (3 / 2 : Real) := by simp [s]
  have hsZero : Not (s = 0) := by
    intro h
    rw [h] at hsRe
    norm_num at hsRe
  have hSubZero : Not (s - rho = 0) := by
    intro h
    have hh := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.zero_re, hsRe] at hh
    linarith
  have hR := norm_pos_iff.mpr hRhoZero
  have ha := norm_pos_iff.mpr hsZero
  have hb := norm_pos_iff.mpr hSubZero
  have hTriangle : norm rho <= norm s + norm (s - rho) := by
    calc
      norm rho = norm (s - (s - rho)) := by congr 1; ring
      _ <= _ := norm_sub_le _ _
  have hAtom : 1 / (s - rho) + 1 / rho = s / (rho * (s - rho)) := by
    field_simp
    ring
  have hShift := safeLine_shift_three_halves_le hUpper t
  change (Inv.inv (norm (s - rho))) ^ (3 / 2 : Real) <= _ at hShift
  change norm (z * (1 / (s - rho) + 1 / rho)) <= _
  change norm z <= C * (Inv.inv (norm s)) ^ (2 : Nat) at hz
  rw [norm_mul, hAtom, norm_div, norm_mul]
  calc
    norm z * (norm s / (norm rho * norm (s - rho))) <=
        (C * (Inv.inv (norm s)) ^ (2 : Nat)) *
          (norm s / (norm rho * norm (s - rho))) :=
      mul_le_mul_of_nonneg_right hz (by positivity)
    _ = C * (1 / (norm rho * norm s * norm (s - rho))) := by field_simp
    _ <= C * (2 * (Inv.inv (norm rho)) ^ (3 / 2 : Real) *
        ((Inv.inv (norm s)) ^ (3 / 2 : Real) +
          (Inv.inv (norm (s - rho))) ^ (3 / 2 : Real))) :=
      mul_le_mul_of_nonneg_left (inv_triple_product_le_three_halves hR ha hb hTriangle) hC
    _ <= _ := by
      have hLeft : 0 <= (Inv.inv (norm s)) ^ (3 / 2 : Real) := by positivity
      have hW : 0 <= C * (Inv.inv (norm rho)) ^ (3 / 2 : Real) := by positivity
      have hM := mul_le_mul_of_nonneg_left hShift hW
      have hL := mul_nonneg hW hLeft
      dsimp [s] at hM hL
      dsimp [s]
      nlinarith only [hM, hL]

theorem integrable_paired_xi_atom_strip
    {H : Real -> Complex} (hH : Integrable H) {rho : Complex}
    (hUpper : rho.re <= 1) :
    Integrable (fun t : Real => H t *
      (1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I - rho) + 1 / rho)) := by
  have hR : Integrable (fun t : Real =>
      H t / ((3 / 2 : Complex) + (t : Complex) * Complex.I - rho)) := by
    simpa using! integrable_vertical_resolvent hH (c := (3 / 2 : Real)) (by linarith)
  apply (hR.add (hH.div_const rho)).congr
  filter_upwards with t
  simp only [Pi.add_apply]
  ring

theorem summable_integral_norm_paired_xi_atoms_strip
    (hUpper : forall p : RiemannXiDivisorZeroIndex,
      (riemannXiDivisorZeroValue p).re <= 1) {H : Real -> Complex} (hH : Integrable H)
    {C : Real} (hC : 0 <= C)
    (hBound : forall t : Real, norm (H t) <=
      C * (Inv.inv (norm ((3 / 2 : Complex) + (t : Complex) * Complex.I))) ^ (2 : Nat)) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      integral volume (fun t : Real => norm (H t *
        (1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I - riemannXiDivisorZeroValue p) +
          1 / riemannXiDivisorZeroValue p)))) := by
  let K : Real -> Real -> Real := fun a t =>
    (Inv.inv (norm ((a : Complex) + (t : Complex) * Complex.I))) ^ (3 / 2 : Real)
  let F : RiemannXiDivisorZeroIndex -> Real -> Complex := fun p t => H t *
    (1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I - riemannXiDivisorZeroValue p) +
      1 / riemannXiDivisorZeroValue p)
  have hKLeft : Integrable (K (3 / 2)) :=
    integrable_three_halves_verticalLine (by norm_num)
  have hKRight : Integrable (K 1) :=
    integrable_three_halves_verticalLine le_rfl
  have hF : forall p : RiemannXiDivisorZeroIndex, Integrable (F p) := by
    intro p
    exact integrable_paired_xi_atom_strip hH
      (hUpper p)
  have hMajorIntegral : forall p : RiemannXiDivisorZeroIndex,
      integral volume (fun t : Real => norm (F p t)) <=
        (6 * C * (integral volume (K (3 / 2)) + integral volume (K 1))) *
          (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ (3 / 2 : Real) := by
    intro p
    let rho : Complex := riemannXiDivisorZeroValue p
    let W : Real := (Inv.inv (norm rho)) ^ (3 / 2 : Real)
    have hShiftInt : Integrable (fun t : Real => K 1 (t - rho.im)) :=
      hKRight.comp_sub_right rho.im
    have hMajorInt : Integrable (fun t : Real =>
        6 * C * W * (K (3 / 2) t + K 1 (t - rho.im))) :=
      (hKLeft.add hShiftInt).const_mul _
    calc
      integral volume (fun t : Real => norm (F p t)) <=
          integral volume (fun t : Real =>
            6 * C * W * (K (3 / 2) t + K 1 (t - rho.im))) := by
        apply integral_mono_ae (hF p).norm hMajorInt
        filter_upwards with t
        simpa [F, K, W, rho] using norm_paired_hadamard_atom_mul_le_strip hC
          (riemannXiDivisorZeroValue_ne_zero p) (hUpper p) (hBound t)
      _ = _ := by
        rw [integral_const_mul, integral_add hKLeft hShiftInt,
          integral_sub_right_eq_self]
        dsimp [W, rho]
        ring
  have hSum : Summable (fun p : RiemannXiDivisorZeroIndex =>
      (6 * C * (integral volume (K (3 / 2)) + integral volume (K 1))) *
        (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ (3 / 2 : Real)) :=
    (summable_riemannXiDivisorZero_norm_inv_rpow (by norm_num : (1 : Real) < 3 / 2)).mul_left _
  exact Summable.of_nonneg_of_le
    (fun p => integral_nonneg (fun t => norm_nonneg (F p t))) hMajorIntegral hSum

/-- Fubini for the whole multiplicity-counted xi series, with absolute
integrated norms proved above. -/
theorem integral_tsum_paired_xi_atoms_strip
    (hUpper : forall p : RiemannXiDivisorZeroIndex,
      (riemannXiDivisorZeroValue p).re <= 1) {H : Real -> Complex} (hH : Integrable H)
    {C : Real} (hC : 0 <= C)
    (hBound : forall t : Real, norm (H t) <=
      C * (Inv.inv (norm ((3 / 2 : Complex) + (t : Complex) * Complex.I))) ^ (2 : Nat)) :
    tsum (fun p : RiemannXiDivisorZeroIndex => integral volume (fun t : Real =>
        H t * (1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I - riemannXiDivisorZeroValue p) +
          1 / riemannXiDivisorZeroValue p))) =
      integral volume (fun t : Real => tsum (fun p : RiemannXiDivisorZeroIndex =>
        H t * (1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I - riemannXiDivisorZeroValue p) +
          1 / riemannXiDivisorZeroValue p))) := by
  have hSupport : Function.support (fun p : RiemannXiDivisorZeroIndex =>
      (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ (2 : Nat)) = Set.univ := by
    ext p
    simp only [Function.mem_support, mem_univ, iff_true]
    exact pow_ne_zero _ (inv_ne_zero (norm_ne_zero_iff.mpr
      (riemannXiDivisorZeroValue_ne_zero p)))
  have hCount := summable_riemannXiDivisorZero_norm_inv_sq.countable_support
  rw [hSupport] at hCount
  let : Countable RiemannXiDivisorZeroIndex := Set.countable_univ_iff.mp hCount
  exact integral_tsum_of_summable_integral_norm
    (fun p => integrable_paired_xi_atom_strip hH
      (hUpper p))
    (summable_integral_norm_paired_xi_atoms_strip hUpper hH hC hBound)

/-- The integrated complete zero contribution is exactly Robin's absolutely
convergent kernel sum. -/
theorem robinCutoffMellin_complete_zero_pairing_strip
    (hUpper : forall p : RiemannXiDivisorZeroIndex,
      (riemannXiDivisorZeroValue p).re <= 1) {n : Nat} (hn : 2 <= n) {x : Real} (hx : 1 < x) :
    (((1 / (2 * Real.pi) : Real) : Complex)) *
        integral volume (fun t : Real =>
          mellin (robinCutoffMellinTest n x) ((3 / 2 : Complex) + (t : Complex) * Complex.I) *
            tsum (fun p : RiemannXiDivisorZeroIndex =>
              1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I - riemannXiDivisorZeroValue p) +
                1 / riemannXiDivisorZeroValue p)) =
      tsum (fun p : RiemannXiDivisorZeroIndex =>
        robinZeroKernel n (riemannXiDivisorZeroValue p) x / riemannXiDivisorZeroValue p) := by
  choose C hC hBound using exists_robinCutoffMellin_safeLine_majorant hn hx
  have hnOne : 1 <= n := by omega
  have hnReal : (2 : Real) <= n := by exact_mod_cast hn
  have hcLt : (3 / 2 : Real) < n := by linarith
  let H : Real -> Complex := fun t =>
    mellin (robinCutoffMellinTest n x) ((3 / 2 : Complex) + (t : Complex) * Complex.I)
  have hH : Integrable H := by
    simpa [H, Complex.VerticalIntegrable] using! verticalIntegrable_mellin_robinCutoffMellinTest hnOne hx
      (by norm_num : (0 : Real) < 3 / 2) hcLt
  have hSwap := integral_tsum_paired_xi_atoms_strip hUpper hH hC hBound
  have hIntegral : integral volume (fun t : Real => H t *
      tsum (fun p : RiemannXiDivisorZeroIndex =>
        1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I - riemannXiDivisorZeroValue p) +
          1 / riemannXiDivisorZeroValue p)) =
      tsum (fun p : RiemannXiDivisorZeroIndex => integral volume (fun t : Real =>
        H t * (1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I - riemannXiDivisorZeroValue p) +
          1 / riemannXiDivisorZeroValue p))) := by
    rw [hSwap]
    apply integral_congr_ae
    filter_upwards with t
    rw [tsum_mul_left]
  change (((1 / (2 * Real.pi) : Real) : Complex)) *
    integral volume (fun t : Real => H t *
      tsum (fun p : RiemannXiDivisorZeroIndex =>
        1 / ((3 / 2 : Complex) + (t : Complex) * Complex.I - riemannXiDivisorZeroValue p) +
          1 / riemannXiDivisorZeroValue p)) = _
  rw [hIntegral, <- tsum_mul_left]
  apply tsum_congr
  intro p
  have hRe := hUpper p
  simpa [H] using! robinCutoffMellin_paired_zero_atom hnOne hx
    (by norm_num : (0 : Real) < 3 / 2) hcLt (riemannXiDivisorZeroValue_ne_zero p)
    (by linarith only [hRe] : (riemannXiDivisorZeroValue p).re < (3 / 2 : Real))

end Robin1984
