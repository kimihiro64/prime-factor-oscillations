/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Hecke.DeletionDerivative
import OAI.NumberTheory.DirichletL.Hecke.DeletionReciprocal

/-!
# InverseDeletionWave

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Jonas. All rights reserved.
Released under Apache 2.0 license as described by LICENSE.
Authors: Jonas
-/


noncomputable section
open scoped BigOperators Classical

namespace OAI.SevenEighths.InverseDeletionWave

open HeckeFamily HeckeDeletionBounds HeckeDeletionDerivative

theorem finite_product_relative_bound {I : Type*} (S : Finset I) (u : I -> Complex) :
    norm ((S.prod u) - 1) <=
      Real.exp (S.sum (fun i => norm (u i - 1))) - 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Real.exp_add]
    have he : u i * S.prod u - 1 =
        (u i - 1) * S.prod u + (S.prod u - 1) := by ring
    have hp : norm (S.prod u) <= norm (S.prod u - 1) + 1 := by
      have h := norm_add_le (S.prod u - 1) (1 : Complex)
      simpa using h
    have hn := norm_nonneg (u i - 1)
    have hexp := Real.add_one_le_exp (norm (u i - 1))
    have hpos := (Real.exp_pos (S.sum (fun j => norm (u j - 1)))).le
    calc
      _ <= norm (u i - 1) * norm (S.prod u) + norm (S.prod u - 1) := by
        rw [he]
        exact (norm_add_le _ _).trans (by rw [norm_mul])
      _ <= (norm (u i - 1) + 1) *
          Real.exp (S.sum (fun j => norm (u j - 1))) - 1 := by nlinarith
      _ <= _ := by nlinarith

theorem factor_deriv_norm_le {sigma N : Real} (hsigma : 0 < sigma)
    (hN : 2 <= N) {a s : Complex} (ha : norm a <= 1) (hs : sigma <= s.re) :
    norm (deriv (EulerFactors.factor N a) s) <= Real.log N := by
  have hN0 : 0 < N := by linarith
  have hlog : 0 <= Real.log N := Real.log_nonneg (by linarith)
  have hterm : norm (a * (N : Complex) ^ (-s)) <= 1 := by
    apply (term_bound hsigma hN ha hs).trans
    exact (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)).le
  rw [factor_deriv hN0, norm_mul, <- Complex.ofReal_log hN0.le,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
  exact mul_le_of_le_one_left hlog hterm

theorem factor_difference_norm_le {sigma N : Real} (hsigma : 0 < sigma)
    (hN : 2 <= N) {a s t : Complex} (ha : norm a <= 1)
    (hs : sigma <= s.re) (ht : sigma <= t.re) :
    norm (EulerFactors.factor N a t - EulerFactors.factor N a s) <=
      Real.log N * norm (t - s) := by
  exact Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z _ => EulerFactors.differentiable_factor (by linarith : 0 < N) a z)
    (fun z hz => factor_deriv_norm_le hsigma hN ha hz)
    (convex_halfSpace_re_ge sigma) hs ht

theorem factor_relative_norm_le {sigma N : Real} (hsigma : 0 < sigma)
    (hN : 2 <= N) {a s t : Complex} (ha : norm a <= 1)
    (hs : sigma <= s.re) (ht : sigma <= t.re) :
    norm (EulerFactors.factor N a t / EulerFactors.factor N a s - 1) <=
      localBound sigma * Real.log N * norm (t - s) := by
  have hne : Not (EulerFactors.factor N a s = 0) :=
    EulerFactors.factor_ne_zero (by linarith : 1 < N) ha (hsigma.trans_le hs)
  have he : EulerFactors.factor N a t / EulerFactors.factor N a s - 1 =
      (EulerFactors.factor N a t - EulerFactors.factor N a s) *
        Inv.inv (EulerFactors.factor N a s) := by
    field_simp
  rw [he, norm_mul]
  calc
    _ <= (Real.log N * norm (t - s)) * localBound sigma :=
      mul_le_mul (factor_difference_norm_le hsigma hN ha hs ht)
        (factor_bounds hsigma hN ha hs).2 (norm_nonneg _)
        (mul_nonneg (Real.log_nonneg (by linarith)) (norm_nonneg _))
    _ = _ := by ring

theorem radical_log_sum (M : Ideal O) :
    (SmoothMobiusCorrection.primeSet M).sum
      (fun P => Real.log (P.val.absNorm : Real)) =
        Real.log ((radical M).absNorm : Real) := by
  have hpos (P : SmoothMobiusCorrection.PrimeIdeal) :
      0 < (P.val.absNorm : Real) := by
    have h := SmoothMobiusCorrection.prime_norm_two_le P
    exact_mod_cast (by omega : 0 < P.val.absNorm)
  rw [<- Real.log_prod (fun P _ => (hpos P).ne')]
  simp only [radical, SmoothMobiusCorrection.primeProduct, map_prod, Nat.cast_prod]

theorem factors_relative_norm_le (sigma : Real) (hsigma : 0 < sigma)
    (M : Ideal O) (psi : Character) {s t : Complex}
    (hs : sigma <= s.re) (ht : sigma <= t.re) :
    norm (HeckeFiniteDeletion.factors M psi t /
      HeckeFiniteDeletion.factors M psi s - 1) <=
        Real.exp (localBound sigma * Real.log ((radical M).absNorm : Real) *
          norm (t - s)) - 1 := by
  let S := SmoothMobiusCorrection.primeSet M
  let u := fun P : SmoothMobiusCorrection.PrimeIdeal =>
    EulerFactors.factor (P.val.absNorm : Real) (idealCoeff psi P.val) t /
      EulerFactors.factor (P.val.absNorm : Real) (idealCoeff psi P.val) s
  have hprod : HeckeFiniteDeletion.factors M psi t /
      HeckeFiniteDeletion.factors M psi s = S.prod u := by
    simp only [HeckeFiniteDeletion.factors, EulerFactors.deletedProduct,
      S, u, Finset.prod_div_distrib]
  rw [hprod]
  apply (finite_product_relative_bound S u).trans
  apply sub_le_sub_right
  apply Real.exp_le_exp.mpr
  calc
    _ <= S.sum (fun P => localBound sigma * Real.log (P.val.absNorm : Real) *
        norm (t - s)) := by
      apply Finset.sum_le_sum
      intro P _
      exact factor_relative_norm_le hsigma
        (by exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le P)
        (idealCoeff_norm_le_one psi P.val) hs ht
    _ = _ := by
      dsimp only [S]
      rw [<- Finset.sum_mul, <- Finset.mul_sum, radical_log_sum]

theorem inverse_relative_norm_le (sigma : Real) (hsigma : 0 < sigma)
    (M : Ideal O) (psi : Character) {s t : Complex}
    (hs : sigma <= s.re) (ht : sigma <= t.re) :
    norm (Inv.inv (HeckeFiniteDeletion.factors M psi s) /
      Inv.inv (HeckeFiniteDeletion.factors M psi t) - 1) <=
        Real.exp (localBound sigma * Real.log ((radical M).absNorm : Real) *
          norm (t - s)) - 1 := by
  simpa only [inv_div_inv] using factors_relative_norm_le sigma hsigma M psi hs ht

theorem inverse_difference_norm_le (sigma : Real) (hsigma : 0 < sigma)
    (M : Ideal O) (psi : Character) {s t : Complex}
    (hs : sigma <= s.re) (ht : sigma <= t.re) :
    norm (Inv.inv (HeckeFiniteDeletion.factors M psi s) -
      Inv.inv (HeckeFiniteDeletion.factors M psi t)) <=
        norm (Inv.inv (HeckeFiniteDeletion.factors M psi t)) *
          (Real.exp (localBound sigma * Real.log ((radical M).absNorm : Real) *
            norm (t - s)) - 1) := by
  have hne := HeckeFiniteDeletion.factors_ne_zero M psi (hsigma.trans_le ht)
  have he : Inv.inv (HeckeFiniteDeletion.factors M psi s) -
      Inv.inv (HeckeFiniteDeletion.factors M psi t) =
        Inv.inv (HeckeFiniteDeletion.factors M psi t) *
          (Inv.inv (HeckeFiniteDeletion.factors M psi s) /
            Inv.inv (HeckeFiniteDeletion.factors M psi t) - 1) := by
    field_simp
  rw [he, norm_mul]
  exact mul_le_mul_of_nonneg_left (inverse_relative_norm_le sigma hsigma M psi hs ht)
    (norm_nonneg _)

theorem radical_norm_pos (M : Ideal O) :
    0 < ((radical M).absNorm : Real) := by
  exact_mod_cast Nat.pos_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (radical_ne_zero M))

theorem inverse_relative_log_window (sigma : Real) (hsigma : 0 < sigma)
    (D kappa : Real) (hD : 1 < D) (hkappa : 0 <= kappa)
    (M : Ideal O) (psi : Character)
    (hmask : ((radical M).absNorm : Real) <= D ^ kappa)
    {s t : Complex} (hs : sigma <= s.re) (ht : sigma <= t.re)
    (hwindow : norm (t - s) <= 1 / (Real.log D) ^ 2) :
    norm (Inv.inv (HeckeFiniteDeletion.factors M psi s) /
      Inv.inv (HeckeFiniteDeletion.factors M psi t) - 1) <=
        Real.exp (localBound sigma * kappa / Real.log D) - 1 := by
  have hD0 : 0 < D := by linarith
  have hlogD : 0 < Real.log D := Real.log_pos hD
  have hlogR : Real.log ((radical M).absNorm : Real) <= kappa * Real.log D := by
    have h := Real.log_le_log (radical_norm_pos M) hmask
    rwa [Real.log_rpow hD0] at h
  have hb := (localBound_pos hsigma).le
  apply (inverse_relative_norm_le sigma hsigma M psi hs ht).trans
  apply sub_le_sub_right
  apply Real.exp_le_exp.mpr
  calc
    _ <= (localBound sigma * (kappa * Real.log D)) * (1 / (Real.log D) ^ 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hlogR hb) hwindow
        (norm_nonneg _) (mul_nonneg hb (mul_nonneg hkappa hlogD.le))
    _ = _ := by
      field_simp

theorem masked_reciprocal_difference (sigma : Real) (hsigma : 0 < sigma)
    (chi psi : Character)
    (hmask : forall I : Ideal O, idealCoeff chi I =
      if IsCoprime I chi.modulus then idealCoeff psi I else 0)
    {s t : Complex} (hs : sigma <= s.re) (ht : sigma <= t.re) :
    norm (HeckeReciprocal.reciprocal chi s -
      HeckeReciprocal.reciprocal psi s *
        Inv.inv (HeckeFiniteDeletion.factors chi.modulus psi t)) <=
      norm (HeckeReciprocal.reciprocal psi s) *
        norm (Inv.inv (HeckeFiniteDeletion.factors chi.modulus psi t)) *
          (Real.exp (localBound sigma *
            Real.log ((radical chi.modulus).absNorm : Real) * norm (t - s)) - 1) := by
  rw [HeckeDeletionReciprocal.reciprocal_eq_of_mask chi psi hmask
    (hsigma.trans_le hs), <- mul_sub, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (inverse_difference_norm_le sigma hsigma chi.modulus psi hs ht) (norm_nonneg _)

theorem masked_wave_leading_limit (chi psi : Character)
    (hmask : forall I : Ideal O, idealCoeff chi I =
      if IsCoprime I chi.modulus then idealCoeff psi I else 0)
    (rho : Complex) (hrho : 0 < rho.re)
    (z weight : Nat -> Complex) (hzpos : forall n, 0 < (z n).re)
    (hz : Filter.Tendsto z Filter.atTop (nhds rho)) (A : Complex)
    (hA : Filter.Tendsto (fun n => weight n * HeckeReciprocal.reciprocal psi (z n))
      Filter.atTop (nhds A)) :
    Filter.Tendsto (fun n => weight n * HeckeReciprocal.reciprocal chi (z n))
      Filter.atTop (nhds (A * Inv.inv (HeckeFiniteDeletion.factors chi.modulus psi rho))) := by
  have hne := HeckeFiniteDeletion.factors_ne_zero chi.modulus psi hrho
  have hc : ContinuousAt (fun s => Inv.inv (HeckeFiniteDeletion.factors chi.modulus psi s)) rho :=
    ((HeckeFiniteDeletion.factors_differentiable chi.modulus psi rho).inv hne).continuousAt
  have ht := hA.mul (hc.tendsto.comp hz)
  convert ht using 1
  funext n
  rw [HeckeDeletionReciprocal.reciprocal_eq_of_mask chi psi hmask (hzpos n)]
  simp only [Function.comp_apply, mul_assoc]

theorem masked_leading_amplitude_ne_zero (M : Ideal O) (psi : Character)
    {rho A : Complex} (hrho : 0 < rho.re) (hA : Not (A = 0)) :
    Not (A * Inv.inv (HeckeFiniteDeletion.factors M psi rho) = 0) :=
  mul_ne_zero hA (inv_ne_zero (HeckeFiniteDeletion.factors_ne_zero M psi hrho))

end OAI.SevenEighths.InverseDeletionWave
