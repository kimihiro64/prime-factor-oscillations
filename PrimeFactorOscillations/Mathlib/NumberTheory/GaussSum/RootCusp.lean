/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.NumberTheory.GaussSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# A quartic root-cusp kernel

A joint finite-field sum involving a quadratic phase and reciprocal cusp
phase reduces to a quadratic-character correlation. All character values at
zero are retained. The reduction is algebraic and assumes no analytic bound.
-/

set_option autoImplicit false
set_option Elab.async false

namespace MulChar

variable {F : Type*} [Field F] [Fintype F]

/-- The unnormalized joint kernel; the multiplicative characters remove zeros. -/
noncomputable def rootCuspSum (chi : MulChar F Complex)
    (psi : AddChar F Complex) (t nu : F) : Complex :=
  Finset.sum Finset.univ (fun h : F =>
    Finset.sum Finset.univ (fun r : F =>
      chi r * (Inv.inv chi) h *
        psi (h * r ^ 2 + t * r + nu / h)))

/-- Quadratic Gauss scaling, including the zero scale for a nontrivial character. -/
theorem quadraticGaussShift (delta : MulChar F Complex)
    (hdelta : Not (delta = 1)) (hinv : Inv.inv delta = delta)
    (psi : AddChar F Complex) (a : F) :
    Finset.sum Finset.univ (fun r : F => delta r * psi (r * a)) =
      delta a * gaussSum delta psi := by
  classical
  by_cases ha : a = 0
  case pos =>
    subst a
    simpa [MulChar.map_zero] using MulChar.sum_eq_zero_of_ne_one hdelta
  case neg =>
    have h := gaussSum_mulShift_eq delta psi (Units.mk0 a ha)
    rw [hinv] at h
    simpa only [gaussSum, AddChar.mulShift_apply, Units.val_mk0, mul_comm] using h

/-- Reindex the complete coupled sum by y = h * r, retaining zero terms. -/
theorem rootCuspSum_reindex (chi : MulChar F Complex)
    (psi : AddChar F Complex) (t nu : F) :
    rootCuspSum chi psi t nu =
      Finset.sum Finset.univ (fun y : F =>
        (Inv.inv chi) y *
          Finset.sum Finset.univ (fun r : F =>
            chi r ^ 2 * psi (r * (y + t + nu / y)))) := by
  classical
  have hrow (r : F) :
      Finset.sum Finset.univ (fun h : F =>
        chi r * (Inv.inv chi) h * psi (h * r ^ 2 + t * r + nu / h)) =
      Finset.sum Finset.univ (fun y : F =>
        chi r ^ 2 * (Inv.inv chi) y * psi (r * (y + t + nu / y))) := by
    by_cases hr : r = 0
    case pos =>
      simp [hr]
    case neg =>
      have hinj : Function.Injective (fun y : F => y / r) := by
        intro x y hxy
        field_simp [hr] at hxy
        exact hxy
      have hsurj : Function.Surjective (fun y : F => y / r) := by
        intro h
        refine Exists.intro (h * r) ?_
        field_simp [hr]
      have hbij := And.intro hinj hsurj
      apply (Fintype.sum_bijective (fun y : F => y / r) hbij _ _ ?_).symm
      intro y
      by_cases hy : y = 0
      case pos =>
        simp [hy]
      case neg =>
        have hphase :
            (y / r) * r ^ 2 + t * r + nu / (y / r) =
              r * (y + t + nu / y) := by
          field_simp [hr, hy]
        rw [hphase]
        simp only [MulChar.inv_apply', div_eq_mul_inv, map_mul, inv_inv]
        ring
  unfold rootCuspSum
  rw [Finset.sum_comm]
  simp_rw [hrow]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- A quartic root-cusp sum reduces to one quadratic-character correlation. -/
theorem rootCuspSum_eq_quadraticCorrelation (chi : MulChar F Complex)
    (hfour : chi ^ 4 = 1) (htwo : Not (chi ^ 2 = 1))
    (psi : AddChar F Complex) (t nu : F) :
    rootCuspSum chi psi t nu =
      gaussSum (chi ^ 2) psi *
        Finset.sum Finset.univ (fun y : F =>
          chi y * (chi ^ 2) (y ^ 2 + t * y + nu)) := by
  classical
  have hinv : Inv.inv (chi ^ 2) = chi ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    calc
      chi ^ 2 * chi ^ 2 = chi ^ (2 + 2) := (pow_add chi 2 2).symm
      _ = 1 := hfour
  have hchar : Inv.inv chi * chi ^ 2 = chi := by
    simp [pow_two, <- mul_assoc]
  rw [rootCuspSum_reindex]
  simp_rw [<- MulChar.pow_apply' chi (by decide : Not ((2 : Nat) = 0))]
  simp_rw [quadraticGaussShift (chi ^ 2) htwo hinv]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : y = 0
  case pos =>
    simp [hy]
  case neg =>
    have harg : y + t + nu / y = (y ^ 2 + t * y + nu) / y := by
      field_simp [hy]
    rw [harg, div_eq_mul_inv, map_mul]
    rw [<- MulChar.inv_apply', hinv]
    calc
      (Inv.inv chi) y * ((chi ^ 2) (y ^ 2 + t * y + nu) *
          (chi ^ 2) y * gaussSum (chi ^ 2) psi) =
          ((Inv.inv chi) y * (chi ^ 2) y) *
            (gaussSum (chi ^ 2) psi * (chi ^ 2) (y ^ 2 + t * y + nu)) := by ring
      _ = chi y *
          (gaussSum (chi ^ 2) psi * (chi ^ 2) (y ^ 2 + t * y + nu)) := by
            rw [<- MulChar.mul_apply, hchar]
      _ = _ := by ring

/-- The joint quartic kernel vanishes when both additive parameters are zero. -/
theorem rootCuspSum_zero_zero (chi : MulChar F Complex)
    (hfour : chi ^ 4 = 1) (htwo : Not (chi ^ 2 = 1))
    (psi : AddChar F Complex) :
    rootCuspSum chi psi 0 0 = 0 := by
  classical
  have hchi : Not (chi = 1) := by
    intro h
    apply htwo
    rw [h, one_pow]
  have hprod : chi * (chi ^ 2) ^ 2 = chi := by
    rw [<- pow_mul]
    change chi * chi ^ 4 = chi
    rw [hfour, mul_one]
  have hpoint (y : F) : chi y * (chi ^ 2) (y ^ 2) = chi y := by
    rw [map_pow, <- MulChar.pow_apply' (chi ^ 2) (by decide : Not ((2 : Nat) = 0))]
    rw [<- MulChar.mul_apply, hprod]
  rw [rootCuspSum_eq_quadraticCorrelation chi hfour htwo]
  simp only [zero_mul, add_zero]
  simp_rw [hpoint]
  rw [MulChar.sum_eq_zero_of_ne_one hchi, mul_zero]

/-- Normalize the joint kernel by the cardinality of its finite field. -/
noncomputable def normalizedRootCuspSum (chi : MulChar F Complex)
    (psi : AddChar F Complex) (t nu : F) : Complex :=
  rootCuspSum chi psi t nu / (Fintype.card F : Complex)

/-- The same exact correlation identity with the cardinality normalization. -/
theorem normalizedRootCuspSum_eq_quadraticCorrelation
    (chi : MulChar F Complex) (hfour : chi ^ 4 = 1)
    (htwo : Not (chi ^ 2 = 1)) (psi : AddChar F Complex) (t nu : F) :
    normalizedRootCuspSum chi psi t nu =
      (gaussSum (chi ^ 2) psi / (Fintype.card F : Complex)) *
        Finset.sum Finset.univ (fun y : F =>
          chi y * (chi ^ 2) (y ^ 2 + t * y + nu)) := by
  rw [normalizedRootCuspSum, rootCuspSum_eq_quadraticCorrelation chi hfour htwo]
  ring

end MulChar
