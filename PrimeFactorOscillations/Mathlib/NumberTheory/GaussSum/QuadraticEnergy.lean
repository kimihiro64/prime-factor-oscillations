/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Complex.Basic
import PrimeFactorOscillations.Mathlib.NumberTheory.GaussSum.QuadraticPhase

/-!
# Exact energy of quartic cusp packets

The full cusp and coprime row-cusp sums have explicit squared magnitudes.
Both the row-frequency and discriminant zero masks are retained. The result
concerns complete finite-field packets, not short-range arithmetic means.
-/

set_option autoImplicit false
set_option Elab.async false

namespace MulChar

variable {F : Type*} [Field F] [Fintype F]

/-- A nontrivial finite-field Gauss sum has squared modulus equal to the field size. -/
theorem normSq_gaussSum_eq_card (chi : MulChar F Complex)
    (hchi : Not (chi = 1)) (psi : AddChar F Complex) (hpsi : Not (psi = 1)) :
    Complex.normSq (gaussSum chi psi) = (Fintype.card F : Real) := by
  have h := gaussSum_mul_gaussSum_eq_card hchi (AddChar.IsPrimitive.of_ne_one hpsi)
  rw [<- star_gaussSum_eq] at h
  change gaussSum chi psi * (starRingEnd Complex) (gaussSum chi psi) = _ at h
  rw [Complex.mul_conj] at h
  simpa using congrArg Complex.re h

/-- Character values have unit squared modulus away from their zero. -/
theorem normSq_apply_of_ne_zero (chi : MulChar F Complex) (a : F)
    (ha : Not (a = 0)) : Complex.normSq (chi a) = 1 := by
  have h : (Complex.normSq (chi a) : Complex) = 1 := by
    calc
      _ = chi a * (starRingEnd Complex) (chi a) := (Complex.mul_conj _).symm
      _ = chi a * (Inv.inv chi) a := by rw [starRingEnd_apply, MulChar.star_apply']
      _ = (chi * Inv.inv chi) a := rfl
      _ = 1 := by rw [mul_inv_cancel, MulChar.one_apply (isUnit_iff_ne_zero.mpr ha)]
  simpa using congrArg Complex.re h

/-- The entire cusp packet has an exact discriminant mask in its squared modulus. -/
theorem normSq_cuspQuadraticPhase [DecidableEq F] (hF : Not (ringChar F = 2))
    (chi : MulChar F Complex) (hfour : chi ^ 4 = 1)
    (htwo : Not (chi ^ 2 = 1)) (psi : AddChar F Complex)
    (hpsi : Not (psi = 1)) (t nu : F) :
    Complex.normSq (Finset.sum Finset.univ (fun h : F =>
      Finset.sum Finset.univ (fun r : F =>
        (Inv.inv chi) h * psi (h * r ^ 2 + t * r + nu / h)))) =
      if nu - t ^ 2 / 4 = 0 then 0 else (Fintype.card F : Real) ^ 2 := by
  classical
  have hchi : Not (chi = 1) := by
    intro h
    exact htwo (by rw [h, one_pow])
  rw [sum_cuspQuadraticPhase hF chi hfour htwo psi hpsi]
  by_cases hA : nu - t ^ 2 / 4 = 0
  case pos => simp [hA]
  case neg =>
    rw [ite_eq_right hA, map_mul, map_mul, normSq_gaussSum_eq_card _ htwo _ hpsi,
      normSq_gaussSum_eq_card _ (inv_ne_one.mpr hchi) _ hpsi,
      normSq_apply_of_ne_zero chi _ hA, mul_one, pow_two]

/-- The coprime joint packet has only the row-frequency and discriminant zero masks. -/
theorem normSq_coprimeRootCuspPhase [DecidableEq F]
    {E : Type*} [Field E] [Fintype E] [DecidableEq E]
    (xi : MulChar E Complex) (hxi : Not (xi = 1))
    (rho : AddChar E Complex) (hrho : Not (rho = 1)) (s : E)
    (hF : Not (ringChar F = 2)) (chi : MulChar F Complex)
    (hfour : chi ^ 4 = 1) (htwo : Not (chi ^ 2 = 1))
    (psi : AddChar F Complex) (hpsi : Not (psi = 1)) (t nu : F) :
    Complex.normSq (Finset.sum Finset.univ (fun u : E =>
      Finset.sum Finset.univ (fun h : F =>
        Finset.sum Finset.univ (fun r : F =>
          xi u * (Inv.inv chi) h * rho (s * u) *
            psi (h * r ^ 2 + t * r + nu / h))))) =
      if Or (s = 0) (nu - t ^ 2 / 4 = 0) then 0
      else (Fintype.card E : Real) * (Fintype.card F : Real) ^ 2 := by
  classical
  have hchi : Not (chi = 1) := by
    intro h
    exact htwo (by rw [h, one_pow])
  rw [sum_coprimeRootCuspPhase xi hxi rho s hF chi hfour htwo psi hpsi]
  by_cases hs : s = 0
  case pos => simp [hs]
  case neg =>
    by_cases hA : nu - t ^ 2 / 4 = 0
    case pos => simp [hA]
    case neg =>
      simp only [hs, hA, or_self, ite_false]
      simp only [map_mul]
      rw [normSq_gaussSum_eq_card _ hxi _ hrho,
        normSq_gaussSum_eq_card _ htwo _ hpsi,
        normSq_gaussSum_eq_card _ (inv_ne_one.mpr hchi) _ hpsi,
        normSq_apply_of_ne_zero _ _ hs, normSq_apply_of_ne_zero _ _ hA]
      ring

end MulChar
