/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.CubicGaussianWindow

/-!
# Actual Gaussian phase cancellation and the unit row

Uses the actual infinite four-Gaussian window. Projected coprime transpose
pairs cancel at their own self-dual scale without phase-one, symmetry or
Schwartz-window hypotheses. The unit-to-primitive row has an explicit
square-root conductor bound. The final exact dual identity retains all
four compensation terms. No prime-weighted reciprocal-L saving is claimed.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.CubicGaussianCancellation
open OAI OAI.SevenEighths
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT CubicSieve
open EisensteinSchwartzPoisson CubicPairReflection CubicGaussianWindow
open CubicCoupledPhase
local notation "Eis" => ActualEisensteinCubic.O

theorem physical_at_one_bound (I J : Ideal Eis) :
    norm (physicalKernel I J 1) <=
      CubicGaussianUnit.windowConstant * (1 + nonzeroLatticeEnvelopeConstant) := by
  let f : Eis -> Complex := fun z => (star (cubicRow I z) * cubicRow J z) *
    CubicReciprocalGaussian.carrierProfile (norm (eisEmbedding z) ^ 2)
  have hf (z : Eis) : (1 + 1 * norm (eisEmbedding z) ^ 2) ^ 2 * norm (f z) <=
      CubicGaussianUnit.windowConstant := by
    let u : Real := norm (eisEmbedding z) ^ 2
    have hu : 0 <= u := sq_nonneg _
    have hm : norm (f z) <= norm (CubicReciprocalGaussian.carrierProfile u) := by
      have hc := pairedCoefficient_norm_le_one I J z
      change norm ((starRingEnd Complex) (cubicRow I z) * cubicRow J z) <= 1 at hc
      dsimp [f]
      rw [norm_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hc
        (norm_nonneg (CubicReciprocalGaussian.carrierProfile u))
    have hw := CubicGaussianUnit.carrierProfile_weight3 u hu
    have hStep : (1 + u) ^ 2 * norm (CubicReciprocalGaussian.carrierProfile u) <=
        (1 + u) ^ 3 * norm (CubicReciprocalGaussian.carrierProfile u) := by
      have hh := mul_nonneg hu
        (mul_nonneg (sq_nonneg (1 + u))
          (norm_nonneg (CubicReciprocalGaussian.carrierProfile u)))
      nlinarith only [hh]
    have hh := mul_le_mul_of_nonneg_left hm (sq_nonneg (1 + u))
    simpa only [one_mul] using hh.trans (hStep.trans hw)
  have hb := CubicPairRadius.dominated_lattice_sum f 1
    CubicGaussianUnit.windowConstant (by norm_num)
    CubicGaussianUnit.windowConstant_nonneg hf
  simpa only [one_mul, physicalKernel, div_one, f] using hb.2

theorem physical_at_conductor_bound (I J : Ideal Eis)
    (hI : Admissible I) (hJ : Admissible J) (hcop : IsCoprime I J) :
    norm (physicalKernel I J (pairScale I J ^ 2)) <=
      pairScale I J *
        (CubicGaussianUnit.windowConstant * (1 + nonzeroLatticeEnvelopeConstant)) := by
  let C := pairScale I J
  have hC : 0 < C := pairScale_pos I J hI hJ
  have h := physical_anti_reflection I J hI hJ hcop (C ^ 2) (sq_pos_of_pos hC)
  have he : C ^ 2 / C ^ 2 = 1 := div_self (pow_ne_zero _ hC.ne')
  have hRatio : norm (-(((C ^ 2 : Real) : Complex) / (C : Complex)) *
      (star (gaussTwo I hI.2) * gaussTwo J hJ.2)) = C := by
    rw [norm_mul, norm_neg, norm_div, norm_mul, norm_star,
      gaussTwo_norm_one I hI, gaussTwo_norm_one J hJ, mul_one]
    rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg C), abs_of_pos hC]
    field_simp
  change physicalKernel I J (C ^ 2) = _ at h
  rw [he] at h
  rw [h, norm_mul, hRatio]
  exact mul_le_mul_of_nonneg_left (physical_at_one_bound J I) hC.le

theorem physical_unit_primitive_bound (J : Ideal Eis) (hJ : Admissible J) :
    norm (physicalKernel 1 J (norm (eisEmbedding (primaryGenerator J)) ^ 2)) <=
      norm (eisEmbedding (primaryGenerator J)) *
        (CubicGaussianUnit.windowConstant * (1 + nonzeroLatticeEnvelopeConstant)) := by
  have hb := physical_at_conductor_bound 1 J CubicUnitMixed.unit_admissible hJ
    isCoprime_one_left
  simpa only [CubicUnitMixed.unit_pairScale] using hb

theorem physical_balanced_pair_zero (I J : Ideal Eis)
    (hI : Admissible I) (hJ : Admissible J) (hcop : IsCoprime I J)
    (a b : Complex)
    (ha : a * star (gaussTwo I hI.2) = star a)
    (hb : b * star (gaussTwo J hJ.2) = star b) :
    a * star b * physicalKernel I J (pairScale I J) +
      b * star a * physicalKernel J I (pairScale I J) = 0 := by
  have hC := pairScale_pos I J hI hJ
  have hp := physical_anti_reflection I J hI hJ hcop (pairScale I J) hC
  have he : pairScale I J ^ 2 / pairScale I J = pairScale I J := by field_simp [hC.ne']
  have hn : Not ((pairScale I J : Complex) = 0) := by exact_mod_cast hC.ne'
  rw [he, div_self hn, neg_one_mul] at hp
  rw [hp]
  have hCoeff := coefficient_phase_swap (gaussTwo I hI.2) (gaussTwo J hJ.2) a b ha hb
  calc
    _ = -(a * star b * (star (gaussTwo I hI.2) * gaussTwo J hJ.2)) *
        physicalKernel J I (pairScale I J) +
      b * star a * physicalKernel J I (pairScale I J) := by ring
    _ = _ := by rw [hCoeff]; ring

theorem physical_projected_pair_zero (I J : Ideal Eis)
    (hI : Admissible I) (hJ : Admissible J) (hcop : IsCoprime I J)
    (a b : Complex) :
    project (gaussTwo I hI.2) a * star (project (gaussTwo J hJ.2) b) *
        physicalKernel I J (pairScale I J) +
      project (gaussTwo J hJ.2) b * star (project (gaussTwo I hI.2) a) *
        physicalKernel J I (pairScale I J) = 0 :=
  physical_balanced_pair_zero I J hI hJ hcop _ _
    (project_balance _ _ (gauss_phase_unit I hI))
    (project_balance _ _ (gauss_phase_unit J hJ))

def fourPacket (I J : Ideal Eis) (c : Complex) (aa ab ba bb : Real) : Complex :=
  physicalKernel I J aa - star c * physicalKernel I J ab -
    c * physicalKernel I J ba + c * star c * physicalKernel I J bb

theorem physical_four_reflection (I J : Ideal Eis)
    (hI : Admissible I) (hJ : Admissible J) (hcop : IsCoprime I J)
    (c : Complex) (aa ab ba bb : Real)
    (haa : 0 < aa) (hab : 0 < ab) (hba : 0 < ba) (hbb : 0 < bb) :
    fourPacket I J c aa ab ba bb =
      -(star (gaussTwo I hI.2) * gaussTwo J hJ.2) / (pairScale I J : Complex) *
      ((aa : Complex) * physicalKernel J I (pairScale I J ^ 2 / aa) -
        star c * (ab : Complex) * physicalKernel J I (pairScale I J ^ 2 / ab) -
        c * (ba : Complex) * physicalKernel J I (pairScale I J ^ 2 / ba) +
        c * star c * (bb : Complex) * physicalKernel J I (pairScale I J ^ 2 / bb)) := by
  unfold fourPacket
  rw [physical_anti_reflection I J hI hJ hcop aa haa,
    physical_anti_reflection I J hI hJ hcop ab hab,
    physical_anti_reflection I J hI hJ hcop ba hba,
    physical_anti_reflection I J hI hJ hcop bb hbb]
  ring

end PrimeFactorOscillations.CubicGaussianCancellation
