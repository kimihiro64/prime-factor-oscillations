/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import OAI.NumberTheory.DirichletL.CubicSieve.PairPoisson
import PrimeFactorOscillations.Helpers.CubicPairRadius
import PrimeFactorOscillations.Helpers.DirichletCompensatedProbe

/-!
# Conditional reciprocal-scale cancellation

The pair Poisson theorem supplies exact reflection. Self-dual vanishing and
the short-window bound retain explicit Fourier, Gauss-phase and kernel-symmetry
hypotheses. No inert-prime realization or detector transfer is asserted here.

The final polynomial-multiplier lemma concerns the Dirichlet readout variable.
It is not an identification with the carrier-window Mellin variable.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CubicPairReflection
open OAI OAI.SevenEighths

open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson GaussGeneratorTransport CubicSieve

local notation "Eis" => ActualEisensteinCubic.O

def pairScale (I J : Ideal Eis) : Real :=
  norm (eisEmbedding (primaryGenerator I * primaryGenerator J))

def pairedKernel (I J : Ideal Eis) (W : SchwartzMap Real Complex) (M : Real) : Complex :=
  tsum (fun z : Eis =>
    star (CubicSieve.cubicRow I z) * CubicSieve.cubicRow J z *
      W (norm (eisEmbedding z) ^ 2 / M))

theorem pairScale_pos (I J : Ideal Eis) (hI : Admissible I) (hJ : Admissible J) :
    0 < pairScale I J := by
  exact norm_pos_iff.mpr (eisEmbedding_ne_zero (mul_ne_zero hI.2 hJ.2))

theorem anti_reflection (I J : Ideal Eis) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) (W : SchwartzMap Real Complex)
    (hanti : forall t : Real, 0 <= t -> paperRadialFourier W t = -W t)
    (hphase : star (gaussTwo I hI.2) * gaussTwo J hJ.2 = 1)
    (M : Real) (hM : 0 < M) :
    pairedKernel I J W M =
      -((M : Complex) / (pairScale I J : Complex)) *
        pairedKernel J I W ((pairScale I J) ^ 2 / M) := by
  have hC : 0 < pairScale I J := pairScale_pos I J hI hJ
  have hp := cubic_pair_poisson I J hI hJ hcop W M hM
  have hsum :
      (tsum fun h : Eis =>
        CubicSieve.cubicRow I h * star (CubicSieve.cubicRow J h) *
          paperRadialFourier W
            (M * norm (eisEmbedding h) ^ 2 / (pairScale I J) ^ 2)) =
        -pairedKernel J I W ((pairScale I J) ^ 2 / M) := by
    rw [pairedKernel, <- tsum_neg]
    apply tsum_congr
    intro h
    have ht : 0 <= M * norm (eisEmbedding h) ^ 2 / (pairScale I J) ^ 2 := by
      positivity
    have he :
        M * norm (eisEmbedding h) ^ 2 / (pairScale I J) ^ 2 =
          norm (eisEmbedding h) ^ 2 / ((pairScale I J) ^ 2 / M) := by
      field_simp [ne_of_gt hC, ne_of_gt hM]
    rw [hanti _ ht, he]
    ring
  change pairedKernel I J W M =
    (M : Complex) * (star (gaussTwo I hI.2) * gaussTwo J hJ.2) /
      (pairScale I J : Complex) *
        (tsum fun h : Eis =>
          CubicSieve.cubicRow I h * star (CubicSieve.cubicRow J h) *
            paperRadialFourier W
              (M * norm (eisEmbedding h) ^ 2 / (pairScale I J) ^ 2)) at hp
  rw [hphase, mul_one, hsum] at hp
  calc
    _ = _ := hp
    _ = _ := by ring

theorem selfdual_zero (I J : Ideal Eis) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) (W : SchwartzMap Real Complex)
    (hanti : forall t : Real, 0 <= t -> paperRadialFourier W t = -W t)
    (hphase : star (gaussTwo I hI.2) * gaussTwo J hJ.2 = 1)
    (hsym : pairedKernel J I W (pairScale I J) =
      pairedKernel I J W (pairScale I J)) :
    pairedKernel I J W (pairScale I J) = 0 := by
  have hC := pairScale_pos I J hI hJ
  have h := anti_reflection I J hI hJ hcop W hanti hphase (pairScale I J) hC
  have he : (pairScale I J) ^ 2 / pairScale I J = pairScale I J := by
    field_simp [ne_of_gt hC]
  have hCZ : Not ((pairScale I J : Complex) = 0) := by
    exact_mod_cast ne_of_gt hC
  rw [he, div_self hCZ, neg_one_mul, hsym] at h
  linear_combination (1 / 2 : Complex) * h


theorem kernel_symmetric_of_conjugation (I J : Ideal Eis)
    (W : SchwartzMap Real Complex) (M : Real)
    (hI : forall z : Eis, CubicSieve.cubicRow I (conjO z) =
      star (CubicSieve.cubicRow I z))
    (hJ : forall z : Eis, CubicSieve.cubicRow J (conjO z) =
      star (CubicSieve.cubicRow J z)) :
    pairedKernel J I W M = pairedKernel I J W M := by
  unfold pairedKernel
  calc
    _ = tsum (fun z : Eis =>
        star (CubicSieve.cubicRow J (conjO z)) *
          CubicSieve.cubicRow I (conjO z) *
            W (norm (eisEmbedding (conjO z)) ^ 2 / M)) :=
      (Equiv.tsum_eq conjO.toEquiv _).symm
    _ = _ := by
      apply tsum_congr
      intro z
      rw [hJ, hI, star_star, eisEmbedding_conjO, norm_star]
      ring

theorem near_selfdual_bound (I J : Ideal Eis)
    (hI : Admissible I) (hJ : Admissible J) (hcop : IsCoprime I J)
    (W : SchwartzMap Real Complex)
    (hanti : forall t : Real, 0 <= t -> paperRadialFourier W t = -W t)
    (hphase : star (gaussTwo I hI.2) * gaussTwo J hJ.2 = 1)
    (hsym : pairedKernel J I W (pairScale I J) =
      pairedKernel I J W (pairScale I J))
    (X H L : Real) (hX : 0 < X) (hH : 0 <= H) (hL : 0 <= L)
    (hBand : X ^ 2 <= pairScale I J /\
      pairScale I J <= (X + H) ^ 2)
    (hLip : forall t u : Real, X <= t -> t <= X + H -> X <= u -> u <= X + H ->
      norm (pairedKernel I J W (t ^ 2) / (t : Complex) -
        pairedKernel I J W (u ^ 2) / (u : Complex)) <= L * abs (t - u)) :
    norm (pairedKernel I J W (X ^ 2)) <= L * X * H := by
  let R : Real := Real.sqrt (pairScale I J)
  have hC := pairScale_pos I J hI hJ
  have hR : 0 <= R := Real.sqrt_nonneg _
  have hRsq : R ^ 2 = pairScale I J := Real.sq_sqrt hC.le
  have hRL : X <= R := by nlinarith [hBand.1]
  have hRU : R <= X + H := by nlinarith [hBand.2]
  have hz := selfdual_zero I J hI hJ hcop W hanti hphase hsym
  have hb := hLip X R le_rfl (by linarith) hRL hRU
  rw [hRsq, hz, zero_div, sub_zero] at hb
  have hAbs : abs (X - R) <= H := by
    apply abs_le.mpr
    constructor <;> linarith
  have hBound : norm (pairedKernel I J W (X ^ 2)) / X <= L * H := by
    have ht := hb.trans (mul_le_mul_of_nonneg_left hAbs hL)
    simpa only [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hX] using ht
  have ht := mul_le_mul_of_nonneg_right hBound hX.le
  have hCancel :
      norm (pairedKernel I J W (X ^ 2)) / X * X =
        norm (pairedKernel I J W (X ^ 2)) := by
    field_simp [ne_of_gt hX]
  rw [hCancel] at ht
  nlinarith

def antiWeight (s : Complex) : Complex := s - 1 / 2

theorem antiWeight_ne_zero (s : Complex) (hs : (1 / 2 : Real) < s.re) :
    Not (antiWeight s = 0) := by
  intro h
  have hr := congrArg Complex.re h
  norm_num [antiWeight] at hr
  linarith

theorem antiWeightedQuarticProbe_order_iff_zero {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {s : Complex | 0 < s.re})
    (rho : Complex) (hr : (1 / 2 : Real) < rho.re) (hOne : Not (rho = 1)) :
    meromorphicOrderAt
      (fun s => antiWeight s *
        PrimeFactorOscillations.DirichletCompensatedProbe.quarticProbe chi G s)
      rho = -1 <-> DirichletCharacter.LFunction chi rho = 0 := by
  have hA : AnalyticAt Complex antiWeight rho :=
    analyticAt_id.sub analyticAt_const
  have he :
      meromorphicOrderAt
        (antiWeight *
          PrimeFactorOscillations.DirichletCompensatedProbe.quarticProbe chi G)
        rho =
        meromorphicOrderAt
          (PrimeFactorOscillations.DirichletCompensatedProbe.quarticProbe chi G)
          rho :=
    meromorphicOrderAt_mul_of_ne_zero hA (antiWeight_ne_zero rho hr)
  change meromorphicOrderAt
    (antiWeight *
      PrimeFactorOscillations.DirichletCompensatedProbe.quarticProbe chi G)
    rho = -1 <-> _
  rw [he]
  exact PrimeFactorOscillations.DirichletCompensatedProbe.quarticProbe_order_iff_zero
    chi G hG rho hr hOne

theorem cubicRow_norm_le_one (I : Ideal Eis) (z : Eis) :
    norm (CubicSieve.cubicRow I z) <= 1 := by
  have hh := congrArg norm (CubicSieve.cubicRow_square_eq_star I z)
  rw [norm_pow, norm_star] at hh
  nlinarith [sq_nonneg (norm (CubicSieve.cubicRow I z) - 1)]

theorem pairedCoefficient_norm_le_one (I J : Ideal Eis) (z : Eis) :
    norm (star (CubicSieve.cubicRow I z) * CubicSieve.cubicRow J z) <= 1 := by
  rw [norm_mul, norm_star]
  simpa only [one_mul] using
    mul_le_mul (cubicRow_norm_le_one I z) (cubicRow_norm_le_one J z)
      (norm_nonneg _) (by norm_num : (0 : Real) <= 1)

theorem pairedKernel_div_radius (I J : Ideal Eis) (W : SchwartzMap Real Complex) (t : Real) :
    pairedKernel I J W (t ^ 2) / (t : Complex) =
      CubicPairRadius.radiusKernel
        (fun z => star (CubicSieve.cubicRow I z) * CubicSieve.cubicRow J z) W t := by
  unfold pairedKernel CubicPairRadius.radiusKernel CubicPairRadius.radiusTerm
  rw [<- tsum_div_const]
  apply tsum_congr
  intro z
  ring

theorem near_selfdual_uniform_bound (I J : Ideal Eis)
    (hI : Admissible I) (hJ : Admissible J) (hcop : IsCoprime I J)
    (W : SchwartzMap Real Complex)
    (hanti : forall t : Real, 0 <= t -> paperRadialFourier W t = -W t)
    (hphase : star (gaussTwo I hI.2) * gaussTwo J hJ.2 = 1)
    (hsym : pairedKernel J I W (pairScale I J) =
      pairedKernel I J W (pairScale I J))
    (X H : Real) (hX : 1 <= X) (hH : 0 <= H) (hHX : H <= X)
    (hBand : X ^ 2 <= pairScale I J /\ pairScale I J <= (X + H) ^ 2) :
    norm (pairedKernel I J W (X ^ 2)) <=
      (4 * CubicPairRadius.windowSize1 W *
        (1 + EisensteinSchwartzPoisson.nonzeroLatticeEnvelopeConstant)) * X * H := by
  have hC := CubicPairRadius.windowSize1_nonneg W
  have hL := EisensteinSchwartzPoisson.nonzeroLatticeEnvelopeConstant_nonneg
  apply near_selfdual_bound I J hI hJ hcop W hanti hphase hsym X H
    (4 * CubicPairRadius.windowSize1 W *
      (1 + EisensteinSchwartzPoisson.nonzeroLatticeEnvelopeConstant))
        (by linarith) hH (by positivity) hBand
  intro t u ht htH hu huH
  rw [pairedKernel_div_radius, pairedKernel_div_radius]
  exact CubicPairRadius.radiusKernel_difference_bound _
    (pairedCoefficient_norm_le_one I J) W X t u hX ht (by linarith) hu (by linarith)

end PrimeFactorOscillations.CubicPairReflection
