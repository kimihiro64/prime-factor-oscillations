/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.CubicCoupledPhase
import PrimeFactorOscillations.Helpers.CubicGaussianPair
import PrimeFactorOscillations.Helpers.CubicUnitMixed

/-!
# The actual four-Gaussian cubic physical window

Proves convergence of every infinite row sum, identifies its exact finite
Gaussian expansion and derives anti-reflection from the native periodic
Gaussian Poisson theorem. No negative-axis Schwartz premise remains.
The full phase and every Gaussian component are retained. Arithmetic
prime-weighted reciprocal-L estimates are separate from this transfer.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.CubicGaussianWindow
open OAI OAI.SevenEighths
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT CubicSieve
open CubicReciprocalGaussian CubicGaussianPair CubicPairReflection
local notation "Eis" => ActualEisensteinCubic.O

def physicalKernel (I J : Ideal Eis) (M : Real) : Complex :=
  tsum fun z : Eis => (star (cubicRow I z) * cubicRow J z) *
    carrierProfile (norm (eisEmbedding z) ^ 2 / M)

theorem profile_eq_gaussian_sum (z : Complex) (M : Real) :
    carrierProfile (norm z ^ 2 / M) =
      Finset.univ.sum (fun i : Fin 4 => coefficients i * gaussian (scales i / M) z) := by
  unfold carrierProfile
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  unfold gaussian
  congr 1
  push_cast
  ring

theorem pair_gaussian_summable (I J : Ideal Eis) (a : Real) (ha : 0 < a) :
    Summable (fun z : Eis => (star (cubicRow I z) * cubicRow J z) *
      gaussian a (eisEmbedding z)) := by
  have hs : Summable (fun z : Eis => norm (gaussian a (eisEmbedding z))) := by
    simpa only [div_one] using
      (CubicGaussianUnit.gaussian_lattice_summable a 1 ha (by norm_num)).norm
  have hb (z : Eis) : norm ((star (cubicRow I z) * cubicRow J z) *
      gaussian a (eisEmbedding z)) <= norm (gaussian a (eisEmbedding z)) := by
    have hc := pairedCoefficient_norm_le_one I J z
    change norm ((starRingEnd Complex) (cubicRow I z) * cubicRow J z) <= 1 at hc
    rw [norm_mul]
    change norm ((starRingEnd Complex) (cubicRow I z) * cubicRow J z) *
      norm (gaussian a (eisEmbedding z)) <= norm (gaussian a (eisEmbedding z))
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hc (norm_nonneg (gaussian a (eisEmbedding z)))
  exact (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hs).of_norm

theorem physical_hasSum (I J : Ideal Eis) (M : Real) (hM : 0 < M) :
    HasSum (fun z : Eis => (star (cubicRow I z) * cubicRow J z) *
      carrierProfile (norm (eisEmbedding z) ^ 2 / M))
      (Finset.univ.sum (fun i : Fin 4 => coefficients i * gaussianPair I J (scales i / M))) := by
  classical
  let c : Eis -> Complex := fun z => star (cubicRow I z) * cubicRow J z
  have hfin (S : Finset (Fin 4)) :
      HasSum (fun z : Eis => S.sum (fun i =>
        coefficients i * (c z * gaussian (scales i / M) (eisEmbedding z))))
        (S.sum (fun i => coefficients i * gaussianPair I J (scales i / M))) := by
    induction S using Finset.induction_on with
    | empty =>
      simpa only [Finset.sum_empty] using (hasSum_zero : HasSum (fun _ : Eis => (0 : Complex)) 0)
    | @insert i S hi ih =>
      simp only [Finset.sum_insert hi]
      have hh := (pair_gaussian_summable I J (scales i / M)
        (div_pos (scales_pos i) hM)).hasSum
      change HasSum (fun z : Eis => c z * gaussian (scales i / M) (eisEmbedding z))
        (gaussianPair I J (scales i / M)) at hh
      exact (hh.mul_left (coefficients i)).add ih
  have he (z : Eis) : c z * carrierProfile (norm (eisEmbedding z) ^ 2 / M) =
      Finset.univ.sum (fun i : Fin 4 =>
        coefficients i * (c z * gaussian (scales i / M) (eisEmbedding z))) := by
    rw [profile_eq_gaussian_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simpa only [<- he, c] using hfin Finset.univ

theorem physical_eq_gaussian_sum (I J : Ideal Eis) (M : Real) (hM : 0 < M) :
    physicalKernel I J M =
      Finset.univ.sum (fun i : Fin 4 => coefficients i * gaussianPair I J (scales i / M)) :=
  (physical_hasSum I J M hM).tsum_eq

set_option maxHeartbeats 2000000 in
theorem reciprocal_four_sum (f : Real -> Complex) (M C : Real) (phi : Complex) :
    Finset.univ.sum (fun i : Fin 4 => coefficients i *
      (phi / (((scales i / M : Real) : Complex) * (C : Complex)) *
        f (1 / ((scales i / M) * C ^ 2)))) =
      -((M : Complex) / (C : Complex)) * phi *
        Finset.univ.sum (fun i : Fin 4 => coefficients i * f (scales i / (C ^ 2 / M))) := by
  norm_num [coefficients, scales, Fin.sum_univ_succ, div_eq_mul_inv, mul_comm,
    mul_left_comm, mul_assoc, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_inv]
  ring

theorem physical_anti_reflection (I J : Ideal Eis)
    (hI : Admissible I) (hJ : Admissible J) (hcop : IsCoprime I J)
    (M : Real) (hM : 0 < M) :
    physicalKernel I J M =
      -((M : Complex) / (pairScale I J : Complex)) *
        (star (gaussTwo I hI.2) * gaussTwo J hJ.2) *
          physicalKernel J I (pairScale I J ^ 2 / M) := by
  have hC := pairScale_pos I J hI hJ
  have hDual : 0 < pairScale I J ^ 2 / M := div_pos (sq_pos_of_pos hC) hM
  rw [physical_eq_gaussian_sum I J M hM,
    physical_eq_gaussian_sum J I (pairScale I J ^ 2 / M) hDual]
  calc
    _ = Finset.univ.sum (fun i : Fin 4 => coefficients i *
        ((star (gaussTwo I hI.2) * gaussTwo J hJ.2) /
          (((scales i / M : Real) : Complex) * (pairScale I J : Complex)) *
            gaussianPair J I (1 / ((scales i / M) * pairScale I J ^ 2)))) := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun z : Complex => coefficients i * z)
        (gaussian_pair_poisson I J hI hJ hcop (scales i / M)
          (div_pos (scales_pos i) hM))
    _ = _ := reciprocal_four_sum (gaussianPair J I) M (pairScale I J)
      (star (gaussTwo I hI.2) * gaussTwo J hJ.2)

end PrimeFactorOscillations.CubicGaussianWindow
