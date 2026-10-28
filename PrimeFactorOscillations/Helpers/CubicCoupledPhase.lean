/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.CubicInertPhase

/-!
# Coupled cubic Gauss phases and the retained quadrature residual

At the actual pair-specific self-dual scale, phase-projected coefficients
cancel with their transposed pair for every admissible coprime ideal pair.
No individual kernel symmetry or inert-prime phase-cube premise is used.
Both quadratures recover the full coefficient and leave an explicit mixed
residual. The anti-Fourier Schwartz window premise and the independent
signed arithmetic estimate remain explicit; no exponent gain is asserted.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.CubicCoupledPhase
open OAI OAI.SevenEighths
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT CubicSieve
open EisensteinSchwartzPoisson CubicPairReflection
local notation "Eis" => ActualEisensteinCubic.O

def project (g a : Complex) : Complex := a + g * star a

theorem project_balance (g a : Complex) (hg : g * star g = 1) :
    project g a * star g = star (project g a) := by
  unfold project
  rw [star_add, star_mul, star_star]
  calc
    _ = a * star g + (g * star g) * star a := by ring
    _ = _ := by rw [hg]; ring

theorem quadrature_recovery (g a : Complex) :
    project g a - Complex.I * project g (Complex.I * a) = 2 * a := by
  have hi : star Complex.I = -Complex.I := by
    change (starRingEnd Complex) Complex.I = -Complex.I
    exact Complex.conj_I
  simp only [project, star_mul, hi]
  calc
    _ = (g * star a - a) * (1 + Complex.I ^ 2) + 2 * a := by ring
    _ = _ := by rw [Complex.I_sq]; ring

theorem coefficient_phase_swap (g h a b : Complex)
    (ha : a * star g = star a) (hb : b * star h = star b) :
    a * star b * (star g * h) = b * star a := by
  have hb' : star b * h = b := by
    have hh := congrArg star hb
    simpa only [star_mul, star_star, mul_comm h] using hh
  calc
    _ = (a * star g) * (star b * h) := by ring
    _ = _ := by rw [ha, hb']; ring

theorem phase_unit_of_norm (g : Complex) (hg : norm g = 1) :
    g * star g = 1 := by
  change g * (starRingEnd Complex) g = 1
  rw [Complex.mul_conj, <- Complex.sq_norm, hg]
  norm_num

theorem gauss_phase_unit (I : Ideal Eis) (hI : Admissible I) :
    gaussTwo I hI.2 * star (gaussTwo I hI.2) = 1 :=
  phase_unit_of_norm _ (gaussTwo_norm_one I hI)

theorem balanced_pair_zero (I J : Ideal Eis) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) (W : SchwartzMap Real Complex)
    (hanti : forall t : Real, 0 <= t -> paperRadialFourier W t = -W t)
    (a b : Complex)
    (ha : a * star (gaussTwo I hI.2) = star a)
    (hb : b * star (gaussTwo J hJ.2) = star b) :
    a * star b * pairedKernel I J W (pairScale I J) +
      b * star a * pairedKernel J I W (pairScale I J) = 0 := by
  have hC := pairScale_pos I J hI hJ
  have hp := CubicInertPhase.anti_reflection_with_phase I J hI hJ hcop W hanti
    (pairScale I J) hC
  have he : pairScale I J ^ 2 / pairScale I J = pairScale I J := by
    field_simp [hC.ne']
  have hn : Not ((pairScale I J : Complex) = 0) := by exact_mod_cast hC.ne'
  rw [he, div_self hn, neg_one_mul] at hp
  rw [hp]
  have hCoeff := coefficient_phase_swap (gaussTwo I hI.2) (gaussTwo J hJ.2) a b ha hb
  calc
    _ = -(a * star b * (star (gaussTwo I hI.2) * gaussTwo J hJ.2)) *
        pairedKernel J I W (pairScale I J) +
      b * star a * pairedKernel J I W (pairScale I J) := by ring
    _ = _ := by rw [hCoeff]; ring

theorem projected_pair_zero (I J : Ideal Eis) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) (W : SchwartzMap Real Complex)
    (hanti : forall t : Real, 0 <= t -> paperRadialFourier W t = -W t)
    (a b : Complex) :
    project (gaussTwo I hI.2) a * star (project (gaussTwo J hJ.2) b) *
        pairedKernel I J W (pairScale I J) +
      project (gaussTwo J hJ.2) b * star (project (gaussTwo I hI.2) a) *
        pairedKernel J I W (pairScale I J) = 0 :=
  balanced_pair_zero I J hI hJ hcop W hanti _ _
    (project_balance _ _ (gauss_phase_unit I hI))
    (project_balance _ _ (gauss_phase_unit J hJ))

theorem four_term_projection (g h a b : Complex) :
    4 * (a * star b) =
      project g a * star (project h b) +
      project g (Complex.I * a) * star (project h (Complex.I * b)) +
      Complex.I * project g a * star (project h (Complex.I * b)) -
      Complex.I * project g (Complex.I * a) * star (project h b) := by
  have hi : star Complex.I = -Complex.I := by
    change (starRingEnd Complex) Complex.I = -Complex.I
    exact Complex.conj_I
  simp only [project, star_add, star_mul, star_star, star_neg, hi]
  ring_nf
  simp only [Complex.I_sq]
  ring


def crossPair (k l a b c d : Complex) : Complex :=
  a * star d * k + b * star c * l

theorem four_term_pair_assembly (g h k l a b : Complex) :
    4 * (a * star b * k + b * star a * l) =
      crossPair k l (project g a) (project h b) (project g a) (project h b) +
      crossPair k l (project g (Complex.I * a)) (project h (Complex.I * b))
        (project g (Complex.I * a)) (project h (Complex.I * b)) +
      Complex.I * crossPair k l (project g a) (project h b)
        (project g (Complex.I * a)) (project h (Complex.I * b)) -
      Complex.I * crossPair k l (project g (Complex.I * a)) (project h (Complex.I * b))
        (project g a) (project h b) := by
  unfold crossPair
  linear_combination k * four_term_projection g h a b +
    l * four_term_projection h g b a

theorem selfdual_full_residual (I J : Ideal Eis)
    (hI : Admissible I) (hJ : Admissible J) (hcop : IsCoprime I J)
    (W : SchwartzMap Real Complex)
    (hanti : forall t : Real, 0 <= t -> paperRadialFourier W t = -W t)
    (a b : Complex) :
    let k := pairedKernel I J W (pairScale I J)
    let l := pairedKernel J I W (pairScale I J)
    let g := gaussTwo I hI.2
    let h := gaussTwo J hJ.2
    4 * (a * star b * k + b * star a * l) =
      Complex.I * crossPair k l (project g a) (project h b)
        (project g (Complex.I * a)) (project h (Complex.I * b)) -
      Complex.I * crossPair k l (project g (Complex.I * a)) (project h (Complex.I * b))
        (project g a) (project h b) := by
  dsimp only
  have hb := projected_pair_zero I J hI hJ hcop W hanti a b
  have hc := projected_pair_zero I J hI hJ hcop W hanti (Complex.I * a) (Complex.I * b)
  have hh := four_term_pair_assembly (gaussTwo I hI.2) (gaussTwo J hJ.2)
    (pairedKernel I J W (pairScale I J)) (pairedKernel J I W (pairScale I J)) a b
  unfold crossPair at hh
  rw [hb, hc] at hh
  simpa only [zero_add, crossPair] using hh

theorem project_compensation (g A B c : Complex) :
    project g (A - c * B) =
      project g A - c * B - g * star c * star B := by
  simp only [project, star_sub, star_mul]
  ring

theorem project_one_real (x : Real) :
    project 1 (x : Complex) = 2 * (x : Complex) := by
  have hx : star (x : Complex) = (x : Complex) := by
    change (starRingEnd Complex) (x : Complex) = (x : Complex)
    exact Complex.conj_ofReal x
  simp only [project, hx, one_mul]
  ring

theorem phase_weight_re_nonneg (g : Complex) (hg : norm g = 1) :
    0 <= (1 + g).re := by
  have h := Complex.re_le_norm (-g)
  simp only [Complex.neg_re, norm_neg, hg] at h
  simp only [Complex.add_re, Complex.one_re]
  linarith

end PrimeFactorOscillations.CubicCoupledPhase
