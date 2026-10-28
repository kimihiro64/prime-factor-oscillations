/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.FinCases
import OAI.NumberTheory.DirichletL.Detector.RadialMellin

/-!
# Reciprocal Gaussian carrier window

The native Fourier transform exchanges the four positive Gaussian scales.
The resulting radial profile has zero value at the origin and is anti-Fourier.
Schwartz carrier qualification and the infinite signed packet are separate.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.CubicReciprocalGaussian
open OAI OAI.SevenEighths
open MeasureTheory EisensteinSchwartzPoisson ProbeRadialMellin
open scoped BigOperators

def gaussian (a : Real) (z : Complex) : Complex :=
  Complex.exp (-((paperConstant * a : Real) : Complex) * (norm z : Complex) ^ 2)

theorem gaussian_integrable (a : Real) (ha : 0 < a) : Integrable (gaussian a) := by
  have hp : 0 < ((paperConstant * a : Real) : Complex).re := by
    simpa only [Complex.ofReal_re] using mul_pos paperConstant_pos ha
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := Complex) hp (0 : Complex) (0 : Complex)
  convert h using 1
  funext z
  simp only [gaussian, zero_mul, add_zero, Complex.ofReal_pow]

theorem phase_integrable (f : Complex -> Complex) (hf : Integrable f) (u : Complex) :
    Integrable (fun z => paperE (-(z * u)) * f z) := by
  have hp : Continuous (fun z : Complex => paperE (-(z * u))) := by
    simp_rw [paperE_eq_exp]
    fun_prop
  apply hf.norm.mono' (hp.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun z => by
    change norm (paperE (-(z * u)) * f z) <= norm (f z)
    rw [norm_mul, paperE_norm, one_mul])

theorem paperFourier_finite_linear {iota : Type} (S : Finset iota)
    (c : iota -> Complex) (f : iota -> Complex -> Complex)
    (hf : forall i, Membership.mem S i -> Integrable (f i)) (u : Complex) :
    paperFourier (fun z => Finset.sum S (fun i => c i * f i z)) u =
      Finset.sum S (fun i => c i * paperFourier (f i) u) := by
  classical
  have he (z : Complex) :
      paperE (-(z * u)) * Finset.sum S (fun i => c i * f i z) =
        Finset.sum S (fun i => c i * (paperE (-(z * u)) * f i z)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  unfold paperFourier
  simp_rw [he]
  rw [integral_finset_sum S (fun i hi => (phase_integrable (f i) (hf i hi) u).const_mul (c i))]
  simp_rw [integral_const_mul]
  simp only [Complex.real_smul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem gaussian_fourier (a : Real) (ha : 0 < a) (u : Complex) :
    paperFourier (gaussian a) u = ((1 / a : Real) : Complex) * gaussian (1 / a) u := by
  have hA : Not (paperConstant = 0) := paperConstant_pos.ne'
  have ha0 : Not (a = 0) := ha.ne'
  have hc : paperConstant / (paperConstant * a) = 1 / a := by field_simp
  have he : paperConstant ^ 2 * norm u ^ 2 / (paperConstant * a) =
      paperConstant * (1 / a) * norm u ^ 2 := by field_simp
  have harg : -((paperConstant * (1 / a) * norm u ^ 2 : Real) : Complex) =
      -((paperConstant * (1 / a) : Real) : Complex) * (norm u : Complex) ^ 2 := by
    push_cast
    ring
  unfold gaussian
  rw [paper_gaussian_fourier _ (mul_pos paperConstant_pos ha) u, hc, he, harg]

def scales : Fin 4 -> Real := ![4, 1 / 4, 16, 1 / 16]
def coefficients : Fin 4 -> Complex := ![5 / 4, -5 / 16, -1, 1 / 16]

def planeWindow (z : Complex) : Complex :=
  Finset.univ.sum (fun i : Fin 4 => coefficients i * gaussian (scales i) z)

def carrierProfile (v : Real) : Complex :=
  Finset.univ.sum (fun i : Fin 4 => coefficients i *
    Complex.exp (-((paperConstant * scales i : Real) : Complex) * (v : Complex)))

theorem scales_pos (i : Fin 4) : 0 < scales i := by
  fin_cases i <;> norm_num [scales]

theorem plane_eq_profile (z : Complex) :
    planeWindow z = carrierProfile (norm z ^ 2) := by
  unfold planeWindow carrierProfile
  apply Finset.sum_congr rfl
  intro i hi
  simp only [gaussian, Complex.ofReal_pow]

theorem planeWindow_anti (u : Complex) :
    paperFourier planeWindow u = -planeWindow u := by
  calc
    _ = Finset.univ.sum (fun i : Fin 4 =>
        coefficients i * paperFourier (gaussian (scales i)) u) :=
      paperFourier_finite_linear Finset.univ coefficients
        (fun i => gaussian (scales i)) (fun i _ => gaussian_integrable _ (scales_pos i)) u
    _ = Finset.univ.sum (fun i : Fin 4 =>
        coefficients i * ((1 / scales i : Real) : Complex) *
          gaussian (1 / scales i) u) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [gaussian_fourier _ (scales_pos i) u]
      ring
    _ = -planeWindow u := by
      norm_num [planeWindow, coefficients, scales, Fin.sum_univ_succ] <;> ring

theorem carrierProfile_zero : carrierProfile 0 = 0 := by
  norm_num [carrierProfile, coefficients, scales, Fin.sum_univ_succ]

theorem carrierProfile_anti (v : Real) (hv : 0 <= v) :
    paperRadialFourier carrierProfile v = -carrierProfile v := by
  have hf : (fun z : Complex => carrierProfile (norm z ^ 2)) = planeWindow := by
    funext z
    exact (plane_eq_profile z).symm
  rw [paperRadialFourier, hf, planeWindow_anti, plane_eq_profile]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg v), Real.sq_sqrt hv]

end PrimeFactorOscillations.CubicReciprocalGaussian
