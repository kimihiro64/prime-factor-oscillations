/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.GaussSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Complete quadratic cusp energy over finite rings

Primitive additive-character orthogonality gives exact Parseval identities.
When 2 is a unit, each unit-leading quadratic phase has squared magnitude
equal to the ring cardinality. The full normalized cusp mean is the unit
density, with a concrete specialization to every odd prime-power modulus.

These are complete-residue identities; no short-range estimate is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

namespace AddChar

variable {R : Type*} [CommRing R] [Fintype R]

/-- Orthogonality over a full finite ring retains the equal-frequency case. -/
theorem sum_crossPhase [DecidableEq R] (psi : AddChar R Complex)
    (hpsi : psi.IsPrimitive) (a b : R) :
    Finset.sum Finset.univ (fun x : R =>
      psi (x * a) * (starRingEnd Complex) (psi (x * b))) =
      if a = b then (Fintype.card R : Complex) else 0 := by
  simp_rw [<- AddChar.map_neg_eq_conj, <- AddChar.map_add_eq_mul, <- sub_eq_add_neg,
    <- mul_sub]
  rw [AddChar.sum_mulShift _ hpsi]
  by_cases h : a = b
  case pos => simp [h]
  case neg => simp [sub_eq_zero, h]

/-- Exact full-ring Parseval with injective frequencies and arbitrary coefficients. -/
theorem sum_normSq_fourier_injective {I : Type*} [Fintype I]
    (psi : AddChar R Complex) (hpsi : psi.IsPrimitive)
    (freq : I -> R) (hinj : Function.Injective freq) (coeff : I -> Complex) :
    Finset.sum Finset.univ (fun x : R =>
      Complex.normSq (Finset.sum Finset.univ (fun i : I => coeff i * psi (x * freq i)))) =
      (Fintype.card R : Real) *
        Finset.sum Finset.univ (fun i : I => Complex.normSq (coeff i)) := by
  classical
  let S (x : R) := Finset.sum Finset.univ (fun i : I => coeff i * psi (x * freq i))
  have hexpand (x : R) : S x * (starRingEnd Complex) (S x) =
      Finset.sum Finset.univ (fun i : I =>
        Finset.sum Finset.univ (fun j : I =>
          (coeff i * (starRingEnd Complex) (coeff j)) *
            (psi (x * freq i) * (starRingEnd Complex) (psi (x * freq j))))) := by
    simp only [S, map_sum, map_mul, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hc : Finset.sum Finset.univ (fun x : R => S x * (starRingEnd Complex) (S x)) =
      (Fintype.card R : Complex) * Finset.sum Finset.univ
        (fun i : I => coeff i * (starRingEnd Complex) (coeff i)) := by
    simp_rw [hexpand]
    rw [Finset.sum_comm]
    have hinner (i : I) :
        Finset.sum Finset.univ (fun x : R =>
          Finset.sum Finset.univ (fun j : I =>
            (coeff i * (starRingEnd Complex) (coeff j)) *
              (psi (x * freq i) * (starRingEnd Complex) (psi (x * freq j))))) =
        (Fintype.card R : Complex) * (coeff i * (starRingEnd Complex) (coeff i)) := by
      rw [Finset.sum_comm]
      simp_rw [<- Finset.mul_sum, sum_crossPhase psi hpsi]
      simp only [hinj.eq_iff]
      simp [mul_comm]
    simp_rw [hinner]
    rw [Finset.mul_sum]
  simp_rw [Complex.mul_conj] at hc
  have hr := congrArg Complex.re hc
  simpa [S, Complex.mul_re, map_sum] using hr

/-- A quadratic phase with unit leading coefficient has exact energy over an odd ring. -/
theorem normSq_quadraticPhase_unit (psi : AddChar R Complex)
    (hpsi : psi.IsPrimitive) (h2 : IsUnit (2 : R)) (h : Units R) (t : R) :
    Complex.normSq (Finset.sum Finset.univ
      (fun r : R => psi ((h : R) * r ^ 2 + t * r))) = (Fintype.card R : Real) := by
  classical
  let S := Finset.sum Finset.univ (fun r : R => psi ((h : R) * r ^ 2 + t * r))
  have hrow (s : R) :
      Finset.sum Finset.univ (fun r : R =>
        psi ((h : R) * r ^ 2 + t * r) *
          (starRingEnd Complex) (psi ((h : R) * s ^ 2 + t * s))) =
      Finset.sum Finset.univ (fun d : R =>
        psi ((h : R) * d ^ 2 + t * d) * psi (s * (2 * (h : R) * d))) := by
    apply (Fintype.sum_equiv (Equiv.addRight s) _ _ ?_).symm
    intro d
    rw [<- AddChar.map_neg_eq_conj, <- AddChar.map_add_eq_mul,
      <- AddChar.map_add_eq_mul]
    congr 1
    change (h : R) * d ^ 2 + t * d + s * (2 * (h : R) * d) =
      (h : R) * (d + s) ^ 2 + t * (d + s) + -((h : R) * s ^ 2 + t * s)
    ring
  have hc : S * (starRingEnd Complex) S = (Fintype.card R : Complex) := by
    simp only [S, map_sum, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    simp_rw [hrow]
    rw [Finset.sum_comm]
    simp_rw [<- Finset.mul_sum, AddChar.sum_mulShift _ hpsi]
    have hz (d : R) : 2 * (h : R) * d = 0 <-> d = 0 :=
      (h2.mul h.isUnit).mul_right_eq_zero
    simp [hz]
  rw [Complex.mul_conj] at hc
  simpa [S] using congrArg Complex.re hc

/-- Complete cusp energy with arbitrary unit weights, before any absolute-value estimate. -/
theorem sum_normSq_cuspQuadratic [Fintype (Units R)] (psi : AddChar R Complex)
    (hpsi : psi.IsPrimitive) (h2 : IsUnit (2 : R))
    (weight : Units R -> Complex) (t : R) :
    Finset.sum Finset.univ (fun nu : R =>
      Complex.normSq (Finset.sum Finset.univ (fun h : Units R =>
        Finset.sum Finset.univ (fun r : R =>
          weight h * psi ((h : R) * r ^ 2 + t * r + nu * ((Inv.inv h : Units R) : R)))))) =
      (Fintype.card R : Real) ^ 2 *
        Finset.sum Finset.univ (fun h : Units R => Complex.normSq (weight h)) := by
  classical
  let q (h : Units R) := Finset.sum Finset.univ
    (fun r : R => psi ((h : R) * r ^ 2 + t * r))
  have hrow (h : Units R) (nu : R) :
      Finset.sum Finset.univ (fun r : R =>
        weight h * psi ((h : R) * r ^ 2 + t * r + nu * ((Inv.inv h : Units R) : R))) =
      (weight h * q h) * psi (nu * ((Inv.inv h : Units R) : R)) := by
    calc
      _ = Finset.sum Finset.univ (fun r : R =>
          (weight h * psi ((h : R) * r ^ 2 + t * r)) *
            psi (nu * ((Inv.inv h : Units R) : R))) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [AddChar.map_add_eq_mul, mul_assoc]
      _ = (Finset.sum Finset.univ (fun r : R =>
          weight h * psi ((h : R) * r ^ 2 + t * r))) *
            psi (nu * ((Inv.inv h : Units R) : R)) := by rw [Finset.sum_mul]
      _ = _ := by rw [<- Finset.mul_sum]
  simp_rw [hrow]
  have hinj : Function.Injective (fun h : Units R => ((Inv.inv h : Units R) : R)) := by
    intro x y hxy
    exact inv_injective (Units.ext hxy)
  rw [sum_normSq_fourier_injective psi hpsi _ hinj]
  simp_rw [map_mul, q, normSq_quadraticPhase_unit psi hpsi h2]
  change (Fintype.card R : Real) *
    Finset.sum Finset.univ (fun h : Units R => Complex.normSq (weight h) * (Fintype.card R : Real)) = _
  rw [<- Finset.sum_mul]
  ring

end AddChar

namespace MulChar

variable {R : Type*} [CommRing R] [Fintype R]

/-- A multiplicative character on a finite ring has unit squared modulus on units. -/
theorem normSq_apply_unit (chi : MulChar R Complex) (h : Units R) :
    Complex.normSq (chi h) = 1 := by
  have hc : (Complex.normSq (chi h) : Complex) = 1 := by
    calc
      _ = chi h * (starRingEnd Complex) (chi h) := (Complex.mul_conj _).symm
      _ = chi h * (Inv.inv chi) h := by rw [starRingEnd_apply, MulChar.star_apply']
      _ = (chi * Inv.inv chi) h := rfl
      _ = 1 := by rw [mul_inv_cancel, MulChar.one_apply_coe]
  simpa using congrArg Complex.re hc

/-- The cusp-only complete energy is exact over every odd finite ring. -/
theorem sum_normSq_unitCusp [Fintype (Units R)] (chi : MulChar R Complex) (psi : AddChar R Complex)
    (hpsi : psi.IsPrimitive) (h2 : IsUnit (2 : R)) (t : R) :
    Finset.sum Finset.univ (fun nu : R =>
      Complex.normSq (Finset.sum Finset.univ (fun h : Units R =>
        Finset.sum Finset.univ (fun r : R =>
          (Inv.inv chi) h *
            psi ((h : R) * r ^ 2 + t * r + nu * ((Inv.inv h : Units R) : R)))))) =
      (Fintype.card R : Real) ^ 2 * (Fintype.card (Units R) : Real) := by
  rw [AddChar.sum_normSq_cuspQuadratic psi hpsi h2]
  simp only [normSq_apply_unit, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- The average of the cardinality-normalized squared cusp sum is the unit density. -/
theorem mean_normSq_normalizedUnitCusp [Fintype (Units R)]
    (chi : MulChar R Complex) (psi : AddChar R Complex)
    (hpsi : psi.IsPrimitive) (h2 : IsUnit (2 : R)) (t : R) :
    (Finset.sum Finset.univ (fun nu : R =>
      Complex.normSq ((Finset.sum Finset.univ (fun h : Units R =>
        Finset.sum Finset.univ (fun r : R =>
          (Inv.inv chi) h *
            psi ((h : R) * r ^ 2 + t * r + nu * ((Inv.inv h : Units R) : R))))) /
              (Fintype.card R : Complex)))) / (Fintype.card R : Real) =
      (Fintype.card (Units R) : Real) / (Fintype.card R : Real) := by
  have hcard : Not ((Fintype.card R : Real) = 0) := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [Complex.normSq_div, Complex.normSq_natCast]
  rw [<- Finset.sum_div, sum_normSq_unitCusp chi psi hpsi h2]
  field_simp [hcard]

/-- Every odd prime-power modulus has the exact normalized cusp mean 1 - 1/p. -/
theorem mean_normSq_primePowerUnitCusp (p a : Nat) [Fact (Nat.Prime p)]
    (hodd : Odd p) (chi : MulChar (ZMod (p ^ (a + 1))) Complex)
    (psi : AddChar (ZMod (p ^ (a + 1))) Complex) (hpsi : psi.IsPrimitive)
    (t : ZMod (p ^ (a + 1))) :
    (Finset.sum Finset.univ (fun nu : ZMod (p ^ (a + 1)) =>
      Complex.normSq ((Finset.sum Finset.univ
        (fun h : Units (ZMod (p ^ (a + 1))) =>
          Finset.sum Finset.univ (fun r : ZMod (p ^ (a + 1)) =>
            (Inv.inv chi) h * psi ((h : ZMod (p ^ (a + 1))) * r ^ 2 + t * r +
              nu * ((Inv.inv h : Units (ZMod (p ^ (a + 1)))) : ZMod (p ^ (a + 1))))))) /
                (p ^ (a + 1) : Complex)))) / (p ^ (a + 1) : Real) = 1 - 1 / (p : Real) := by
  classical
  have hp : Nat.Prime p := Fact.out
  have hp0 : Not ((p : Real) = 0) := by exact_mod_cast hp.ne_zero
  have h2 : IsUnit (2 : ZMod (p ^ (a + 1))) := by
    exact (ZMod.isUnit_iff_coprime 2 _).mpr
      ((Nat.coprime_two_left.mpr hodd).pow_right (a + 1))
  have hm := mean_normSq_normalizedUnitCusp chi psi hpsi h2 t
  rw [ZMod.card_units_eq_totient, ZMod.card, Nat.totient_prime_pow_succ hp] at hm
  simp only [Nat.cast_pow, Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_one] at hm
  rw [hm]
  rw [pow_succ]
  field_simp [hp0]

end MulChar
