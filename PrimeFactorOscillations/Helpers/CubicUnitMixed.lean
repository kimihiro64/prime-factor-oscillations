/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.CubicInertPhase
import PrimeFactorOscillations.Helpers.CubicUnitWindow

/-!
# Dual bounds for the cubic unit-to-primitive row

Exact pair reflection moves the conductor scale to dual scale one. The
resulting isolated dual remainder has size at most the square root of the
conductor times an explicit window constant. The unit ideal's admissibility
and pair scale are proved. The final identity retains all four compensation
terms at independent positive scales. The anti-Fourier Schwartz-window
premise remains explicit; this is not an arithmetic exponent estimate.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.CubicUnitMixed
open OAI OAI.SevenEighths
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT EisensteinEmbedding CubicSieve
open EisensteinSchwartzPoisson CubicPairReflection CubicUnitWindow
local notation "Eis" => ActualEisensteinCubic.O

theorem pair_at_one_bound (I J : Ideal Eis) (W : SchwartzMap Real Complex) :
    norm (pairedKernel I J W 1) <=
      CubicPairRadius.windowSize0 W * (1 + nonzeroLatticeEnvelopeConstant) := by
  let f : Eis -> Complex := fun z =>
    (star (cubicRow I z) * cubicRow J z) * W (norm (eisEmbedding z) ^ 2)
  have hf (z : Eis) :
      (1 + 1 * norm (eisEmbedding z) ^ 2) ^ 2 * norm (f z) <=
        CubicPairRadius.windowSize0 W := by
    have hc := pairedCoefficient_norm_le_one I J z
    change norm ((starRingEnd Complex) (cubicRow I z) * cubicRow J z) <= 1 at hc
    have hm : norm (f z) <= norm (W (norm (eisEmbedding z) ^ 2)) := by
      dsimp [f]
      rw [norm_mul]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hc (norm_nonneg (W (norm (eisEmbedding z) ^ 2)))
    have hh := mul_le_mul_of_nonneg_left hm
      (sq_nonneg (1 + norm (eisEmbedding z) ^ 2))
    simpa only [one_mul] using
      hh.trans (CubicPairRadius.window_bound0 W _ (sq_nonneg _))
  have hb := CubicPairRadius.dominated_lattice_sum f 1
    (CubicPairRadius.windowSize0 W) (by norm_num)
    (CubicPairRadius.windowSize0_nonneg W) hf
  simpa only [one_mul, pairedKernel, div_one, f] using hb.2

theorem pair_at_conductor_bound (I J : Ideal Eis)
    (hI : Admissible I) (hJ : Admissible J) (hcop : IsCoprime I J)
    (W : SchwartzMap Real Complex)
    (hanti : forall t : Real, 0 <= t -> paperRadialFourier W t = -W t) :
    norm (pairedKernel I J W ((pairScale I J) ^ 2)) <=
      pairScale I J *
        (CubicPairRadius.windowSize0 W * (1 + nonzeroLatticeEnvelopeConstant)) := by
  let C := pairScale I J
  have hC : 0 < C := pairScale_pos I J hI hJ
  have h := CubicInertPhase.anti_reflection_with_phase I J hI hJ hcop W hanti
    (C ^ 2) (sq_pos_of_pos hC)
  have hCZ : Not ((C : Complex) = 0) := by exact_mod_cast hC.ne'
  have hratio : norm (-(((C ^ 2 : Real) : Complex) / (C : Complex)) *
      (star (gaussTwo I hI.2) * gaussTwo J hJ.2)) = C := by
    rw [norm_mul, norm_neg, norm_div, norm_mul, norm_star,
      gaussTwo_norm_one I hI, gaussTwo_norm_one J hJ, mul_one]
    rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg C), abs_of_pos hC]
    field_simp
  have he : C ^ 2 / C ^ 2 = 1 := div_self (pow_ne_zero _ hC.ne')
  change pairedKernel I J W (C ^ 2) = _ at h
  rw [he] at h
  rw [h, norm_mul, hratio]
  exact mul_le_mul_of_nonneg_left (pair_at_one_bound J I W) hC.le

theorem unit_admissible : Admissible (1 : Ideal Eis) := by
  constructor
  . simp
  . rw [primaryGenerator_one]
    exact one_ne_zero

theorem unit_pairScale (J : Ideal Eis) :
    pairScale 1 J = norm (eisEmbedding (primaryGenerator J)) := by
  simp only [pairScale, primaryGenerator_one, one_mul]

theorem unit_primitive_bound (J : Ideal Eis) (hJ : Admissible J)
    (W : SchwartzMap Real Complex)
    (hanti : forall t : Real, 0 <= t -> paperRadialFourier W t = -W t) :
    norm (pairedKernel 1 J W (norm (eisEmbedding (primaryGenerator J)) ^ 2)) <=
      norm (eisEmbedding (primaryGenerator J)) *
        (CubicPairRadius.windowSize0 W * (1 + nonzeroLatticeEnvelopeConstant)) := by
  have hb := pair_at_conductor_bound 1 J unit_admissible hJ
    (isCoprime_one_left) W hanti
  simpa only [unit_pairScale] using hb

def fourPacket (I J : Ideal Eis) (W : SchwartzMap Real Complex)
    (c : Complex) (aa ab ba bb : Real) : Complex :=
  pairedKernel I J W aa -
    star c * pairedKernel I J W ab -
    c * pairedKernel I J W ba +
    c * star c * pairedKernel I J W bb

theorem fourPacket_reflection (I J : Ideal Eis)
    (hI : Admissible I) (hJ : Admissible J) (hcop : IsCoprime I J)
    (W : SchwartzMap Real Complex)
    (hanti : forall t : Real, 0 <= t -> paperRadialFourier W t = -W t)
    (c : Complex) (aa ab ba bb : Real)
    (haa : 0 < aa) (hab : 0 < ab) (hba : 0 < ba) (hbb : 0 < bb) :
    fourPacket I J W c aa ab ba bb =
      -(star (gaussTwo I hI.2) * gaussTwo J hJ.2) / (pairScale I J : Complex) *
      ((aa : Complex) * pairedKernel J I W ((pairScale I J) ^ 2 / aa) -
        star c * (ab : Complex) * pairedKernel J I W ((pairScale I J) ^ 2 / ab) -
        c * (ba : Complex) * pairedKernel J I W ((pairScale I J) ^ 2 / ba) +
        c * star c * (bb : Complex) *
          pairedKernel J I W ((pairScale I J) ^ 2 / bb)) := by
  unfold fourPacket
  rw [CubicInertPhase.anti_reflection_with_phase I J hI hJ hcop W hanti aa haa,
    CubicInertPhase.anti_reflection_with_phase I J hI hJ hcop W hanti ab hab,
    CubicInertPhase.anti_reflection_with_phase I J hI hJ hcop W hanti ba hba,
    CubicInertPhase.anti_reflection_with_phase I J hI hJ hcop W hanti bb hbb]
  ring

end PrimeFactorOscillations.CubicUnitMixed
