/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GaussianSpectralWeight

/-!
# One fixed summable Gaussian series controls the full growing-scale tail

The exact residue norm and monotonicity of nonpositive powers transfer
a pointwise exponent cap to any subset of the actual zero set. This
keeps the complex sum intact and bounds its norm only after the
principal zero has been separated in the downstream consumer.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem logGaussianZetaResidue_scale_norm_bound
    (X X1 c tau a : Real) (z : ZetaDistinctZero)
    (hX1 : 0 < X1) (hScale : X1 <= X)
    (hScore : gaussianZeroExponent c z.val.re z.val.im tau <= a) :
    norm (logGaussianZetaResidue X (c * Real.log X) tau z) <=
      (X ^ a / X1 ^ a) * norm (logGaussianZetaResidue X1 (c * Real.log X1) tau z) := by
  have hX : 0 < X := lt_of_lt_of_le hX1 hScale
  let A : Real := gaussianZeroExponent c z.val.re z.val.im tau
  have hSplit : X ^ A = X ^ a * X ^ (A - a) := by
    rw [<- Real.rpow_add hX]
    congr 1
    ring
  have hDecay : X ^ (A - a) <= X1 ^ (A - a) :=
    Real.rpow_le_rpow_of_nonpos hX1 hScale (sub_nonpos.mpr hScore)
  calc
    norm (logGaussianZetaResidue X (c * Real.log X) tau z) =
        gaussianZetaAmplitude z * X ^ A :=
      logGaussianZetaResidue_log_scale_norm X c tau z hX
    _ = X ^ a * (gaussianZetaAmplitude z * X ^ (A - a)) := by rw [hSplit]; ring
    _ <= X ^ a * (gaussianZetaAmplitude z * X1 ^ (A - a)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hDecay (gaussianZetaAmplitude_pos z).le)
        (Real.rpow_pos_of_pos hX a).le
    _ = (X ^ a / X1 ^ a) *
        norm (logGaussianZetaResidue X1 (c * Real.log X1) tau z) := by
      rw [logGaussianZetaResidue_log_scale_norm X1 c tau z hX1, Real.rpow_sub hX1]
      ring

theorem logGaussianZetaResidue_subset_sum_norm_bound
    (X X1 c tau a : Real) (S : Set ZetaDistinctZero)
    (hX1 : 0 < X1) (hScale : X1 <= X) (hV1 : 1 <= c * Real.log X1)
    (hScore : forall z : ZetaDistinctZero, Membership.mem S z ->
      gaussianZeroExponent c z.val.re z.val.im tau <= a) :
    And (Summable (fun z : S => logGaussianZetaResidue X (c * Real.log X) tau z.val))
      (norm (tsum (fun z : S => logGaussianZetaResidue X (c * Real.log X) tau z.val)) <=
        (X ^ a / X1 ^ a) *
          tsum (fun z : S => norm (logGaussianZetaResidue X1 (c * Real.log X1) tau z.val))) := by
  let K : Real := X ^ a / X1 ^ a
  have hBase : Summable (fun z : S =>
      norm (logGaussianZetaResidue X1 (c * Real.log X1) tau z.val)) :=
    (logGaussian_zeta_zero_residue_abs_summable X1 (c * Real.log X1) tau hX1 hV1).subtype S
  have hMajor : Summable (fun z : S =>
      K * norm (logGaussianZetaResidue X1 (c * Real.log X1) tau z.val)) :=
    hBase.mul_left K
  have hBound : forall z : S,
      norm (logGaussianZetaResidue X (c * Real.log X) tau z.val) <=
        K * norm (logGaussianZetaResidue X1 (c * Real.log X1) tau z.val) := by
    intro z
    exact logGaussianZetaResidue_scale_norm_bound X X1 c tau a z.val
      hX1 hScale (hScore z.val z.property)
  have hSum : Summable (fun z : S =>
      logGaussianZetaResidue X (c * Real.log X) tau z.val) :=
    Summable.of_norm_bounded hMajor hBound
  refine And.intro hSum ?_
  calc
    _ <= tsum (fun z : S => norm (logGaussianZetaResidue X (c * Real.log X) tau z.val)) :=
      norm_tsum_le_tsum_norm hSum.norm
    _ <= tsum (fun z : S =>
        K * norm (logGaussianZetaResidue X1 (c * Real.log X1) tau z.val)) :=
      Summable.tsum_le_tsum hBound hSum.norm hMajor
    _ = _ := tsum_mul_left

end PrimeFactorOscillations.PrimeClassDeletion
