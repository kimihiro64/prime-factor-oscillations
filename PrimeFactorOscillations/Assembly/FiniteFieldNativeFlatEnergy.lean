/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeAgreementEnergy

/-!
# Exact energy and optimal stability for flat native codebooks

The physical diagonal remains one. Every signed coefficient product is
retained, and every finite family is fixed before its field-scale limit.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

open Filter

/-- Flat native agreement has an exact scalar-plus-identity energy. -/
theorem native_flat_agreement_form {I : Type*} [Fintype I]
    (n h : I -> Nat)
    (hflat : forall i j : I, Not (i = j) ->
      nativeAgreementRate (n i) (h i) (n j) (h j) = 3 / 8)
    (c : I -> Real) :
    nativeAgreementForm n h c =
      (3 / 8 : Real) * (Finset.univ.sum c) ^ 2 +
        (5 / 8 : Real) * Finset.univ.sum (fun i => (c i) ^ 2) := by
  classical
  have hK (i j : I) : nativeAgreementKernel n h i j =
      (3 / 8 : Real) + (if i = j then 5 / 8 else 0) := by
    by_cases hij : i = j
    . subst j
      norm_num [nativeAgreementKernel]
    . simp [nativeAgreementKernel, hij, hflat i j hij]
  have hTerm (i j : I) :
      c i * c j * nativeAgreementKernel n h i j =
        (3 / 8 : Real) * (c i * c j) +
          (if i = j then (5 / 8 : Real) * (c i) ^ 2 else 0) := by
    rw [hK i j]
    by_cases hij : i = j
    . subst j
      simp only [ite_true]
      ring
    . simp only [ite_eq_right hij]
      ring
  have hBase : Finset.univ.sum (fun i => Finset.univ.sum (fun j => c i * c j)) =
      (Finset.univ.sum c) ^ 2 := by
    simp only [<- Finset.mul_sum, <- Finset.sum_mul, pow_two]
  have hDiag : Finset.univ.sum (fun i => Finset.univ.sum (fun j =>
      if i = j then (5 / 8 : Real) * (c i) ^ 2 else 0)) =
        (5 / 8 : Real) * Finset.univ.sum (fun i => (c i) ^ 2) := by
    simp only [Fintype.sum_ite_eq, <- Finset.mul_sum]
  unfold nativeAgreementForm
  calc
    Finset.univ.sum (fun i => Finset.univ.sum (fun j =>
        c i * c j * nativeAgreementKernel n h i j)) =
      Finset.univ.sum (fun i => Finset.univ.sum (fun j =>
        (3 / 8 : Real) * (c i * c j) +
          (if i = j then (5 / 8 : Real) * (c i) ^ 2 else 0))) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact hTerm i j
    _ = (3 / 8 : Real) *
          Finset.univ.sum (fun i => Finset.univ.sum (fun j => c i * c j)) +
        Finset.univ.sum (fun i => Finset.univ.sum (fun j =>
          if i = j then (5 / 8 : Real) * (c i) ^ 2 else 0)) := by
      simp only [Finset.sum_add_distrib, <- Finset.mul_sum]
    _ = _ := by rw [hBase, hDiag]

/-- The same exact energy is the limit of the physical agreement mass. -/
theorem native_flat_agreement_mass_form_tendsto {I : Type*} [Fintype I]
    (n h : I -> Nat)
    (hn : forall i, Nat.Prime (n i)) (hnh : forall i, Nat.Prime (n i + h i))
    (hh : forall i, 0 < h i)
    (hinj : Function.Injective (fun i => Prod.mk (n i) (h i)))
    (hflat : forall i j : I, Not (i = j) ->
      nativeAgreementRate (n i) (h i) (n j) (h j) = 3 / 8)
    (c : I -> Real) :
    Tendsto (nativeAgreementMassForm n h c) atTop
      (nhds ((3 / 8 : Real) * (Finset.univ.sum c) ^ 2 +
        (5 / 8 : Real) * Finset.univ.sum (fun i => (c i) ^ 2))) := by
  have ht := native_agreement_mass_form_tendsto n h hn hnh hh hinj c
  rwa [native_flat_agreement_form n h hflat c] at ht

/-- Five eighths is a universal lower stability constant on each flat family. -/
theorem native_flat_agreement_stability {I : Type*} [Fintype I]
    (n h : I -> Nat)
    (hflat : forall i j : I, Not (i = j) ->
      nativeAgreementRate (n i) (h i) (n j) (h j) = 3 / 8)
    (c : I -> Real) :
    (5 / 8 : Real) * Finset.univ.sum (fun i => (c i) ^ 2) <=
      nativeAgreementForm n h c := by
  rw [native_flat_agreement_form n h hflat c]
  nlinarith only [sq_nonneg (Finset.univ.sum c)]

/-- No larger uniform constant works once the flat family has two entries. -/
theorem native_flat_agreement_stability_optimal {I : Type*} [Fintype I]
    (n h : I -> Nat)
    (hflat : forall i j : I, Not (i = j) ->
      nativeAgreementRate (n i) (h i) (n j) (h j) = 3 / 8)
    (i j : I) (hij : Not (i = j)) (kappa : Real)
    (hBound : forall c : I -> Real,
      kappa * Finset.univ.sum (fun k => (c k) ^ 2) <= nativeAgreementForm n h c) :
    kappa <= 5 / 8 := by
  classical
  let c : I -> Real := fun k => (if k = i then 1 else 0) - (if k = j then 1 else 0)
  have hSum : Finset.univ.sum c = 0 := by
    dsimp [c]
    rw [Finset.sum_sub_distrib]
    simp
  have hSquare (k : I) : (c k) ^ 2 =
      (if k = i then (1 : Real) else 0) + (if k = j then 1 else 0) := by
    by_cases hki : k = i
    . subst k
      norm_num [c, hij]
    . by_cases hkj : k = j
      . subst k
        norm_num [c, hki]
      . norm_num [c, hki, hkj]
  have hSquares : Finset.univ.sum (fun k => (c k) ^ 2) = 2 := by
    simp_rw [hSquare]
    rw [Finset.sum_add_distrib]
    norm_num
  have hb := hBound c
  rw [native_flat_agreement_form n h hflat c, hSum, hSquares] at hb
  nlinarith only [hb]

end PrimeFactorOscillations.FiniteFieldIntegerSignature
