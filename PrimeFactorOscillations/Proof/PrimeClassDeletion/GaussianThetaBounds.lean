/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GaussianSpectralDominance

/-!
# The full zero series and the actual theta probe

The exact identity retains the reference term, physical remainder,
and full prime-power contribution with their signs.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem logGaussianZetaResidue_envelope_norm_bound
    (c tau : Real) (hc : 0 < c) (z0 : ZetaDistinctZero) :
    Exists fun C : Real => And (0 <= C)
      (forall X : Real, Real.exp (1 / c) <= X ->
        norm (tsum (logGaussianZetaResidue X (c * Real.log X) tau)) <=
          C * X ^ (gaussianZetaEnvelope c tau)) := by
  classical
  let X1 : Real := Real.exp (1 / c)
  let S : Set ZetaDistinctZero := Set.univ
  let e : Equiv S ZetaDistinctZero := {
    toFun := Subtype.val
    invFun := fun z => Subtype.mk z (Set.mem_univ z)
    left_inv := fun z => by cases z; rfl
    right_inv := fun z => rfl }
  let Q : Real := tsum (fun z : S =>
    norm (logGaussianZetaResidue X1 (c * Real.log X1) tau z.val))
  let C : Real := Q / X1 ^ (gaussianZetaEnvelope c tau)
  have hX1 : 0 < X1 := Real.exp_pos _
  have hV1 : c * Real.log X1 = 1 := by
    dsimp only [X1]
    rw [Real.log_exp]
    field_simp [hc.ne']
  cases gaussianZetaEnvelope_attained c tau hc z0 with
  | intro w hw =>
    have hScore : forall z : ZetaDistinctZero,
        gaussianZeroExponent c z.val.re z.val.im tau <= gaussianZetaEnvelope c tau := by
      intro z
      rw [hw.1]
      exact hw.2 z
    refine Exists.intro C (And.intro
      (div_nonneg (tsum_nonneg (fun z => norm_nonneg _))
        (Real.rpow_pos_of_pos hX1 _).le) ?_)
    intro X hScale
    have hBound := (logGaussianZetaResidue_subset_sum_norm_bound
      X X1 c tau (gaussianZetaEnvelope c tau) S hX1 hScale
      (by rw [hV1]) (fun z _ => hScore z)).2
    have hSum : tsum (fun z : S =>
        logGaussianZetaResidue X (c * Real.log X) tau z.val) =
        tsum (logGaussianZetaResidue X (c * Real.log X) tau) := by
      simpa only [e] using! e.tsum_eq (logGaussianZetaResidue X (c * Real.log X) tau)
    rw [hSum] at hBound
    calc
      _ <= (X ^ (gaussianZetaEnvelope c tau) / X1 ^ (gaussianZetaEnvelope c tau)) * Q :=
        hBound
      _ = _ := by dsimp only [C]; ring

theorem logGaussianThetaProbe_eq_zeta_zero_formula
    (X V tau : Real) (hX : 1 <= X) (hV : 1 <= V) :
    logGaussianThetaProbe X V tau =
      -tsum (logGaussianZetaResidue X V tau) -
      (Real.log (2 * Real.pi) : Complex) * (Real.exp (-V * tau ^ 2 / 2) : Complex) +
      logGaussianExplicitRemainder X V tau - logGaussianPrimePowerProbe X V tau := by
  have hPsi := logGaussianPsiProbe_eq_zeta_zero_formula X V tau (by linarith) hV
  have hPrime := logGaussianPsiProbe_sub_theta_eq_primePowerProbe X V tau hX (by linarith)
  rw [hPsi] at hPrime
  linear_combination -hPrime

theorem logGaussian_reference_term_norm_bound
    (V tau : Real) (hV : 0 <= V) :
    norm ((Real.log (2 * Real.pi) : Complex) *
      (Real.exp (-V * tau ^ 2 / 2) : Complex)) <= abs (Real.log (2 * Real.pi)) := by
  rw [norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hExp : Real.exp (-V * tau ^ 2 / 2) <= 1 := by
    rw [<- Real.exp_zero]
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonneg hV (sq_nonneg tau)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hExp (abs_nonneg _)

theorem logGaussianThetaProbe_log_scale_error
    (X c tau : Real) (hX : 1 <= X) (hLog : 1 <= Real.log X)
    (hc : 0 < c) (hV : 1 <= c * Real.log X) :
    norm (logGaussianThetaProbe X (c * Real.log X) tau +
      tsum (logGaussianZetaResidue X (c * Real.log X) tau)) <=
        abs (Real.log (2 * Real.pi)) +
        logGaussianExplicitErrorConstant tau * X ^ (-1 + c / 2) +
        (2 * (2 + c / 2 + 2 * c / Real.pi)) *
          X ^ (1 / 2 + c / 8) * Real.log X := by
  let V : Real := c * Real.log X
  let R : Complex := (Real.log (2 * Real.pi) : Complex) *
    (Real.exp (-V * tau ^ 2 / 2) : Complex)
  let Q : Complex := logGaussianPrimePowerProbe X V tau
  let E : Complex := logGaussianExplicitRemainder X V tau
  have hIdentity : logGaussianThetaProbe X V tau +
      tsum (logGaussianZetaResidue X V tau) = -R + E - Q := by
    rw [logGaussianThetaProbe_eq_zeta_zero_formula X V tau hX hV]
    dsimp only [R, E, Q]
    ring
  have hR : norm R <= abs (Real.log (2 * Real.pi)) :=
    logGaussian_reference_term_norm_bound V tau (by linarith)
  have hE : norm E <= logGaussianExplicitErrorConstant tau * X ^ (-1 + c / 2) :=
    logGaussianExplicitRemainder_log_scale_bound X c tau (by linarith) hV
  have hQ : norm Q <= (2 * (2 + c / 2 + 2 * c / Real.pi)) *
      X ^ (1 / 2 + c / 8) * Real.log X := by
    dsimp only [Q]
    rw [<- logGaussianPsiProbe_sub_theta_eq_primePowerProbe X V tau hX (by linarith)]
    exact logGaussian_prime_power_log_scale_bound X c tau hX hLog hc
  change norm (logGaussianThetaProbe X V tau +
    tsum (logGaussianZetaResidue X V tau)) <= _
  rw [hIdentity]
  calc
    _ <= norm (-R + E) + norm Q := norm_sub_le _ _
    _ <= (norm (-R) + norm E) + norm Q :=
      add_le_add (norm_add_le _ _) (le_refl _)
    _ = norm R + norm E + norm Q := by rw [norm_neg]
    _ <= _ := add_le_add (add_le_add hR hE) hQ

end PrimeFactorOscillations.PrimeClassDeletion
