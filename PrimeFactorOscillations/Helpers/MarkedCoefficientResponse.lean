/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Field.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Mathlib.RingTheory.MvPolynomial.Symmetric.OrderedBounds

/-!
# Coupled marked coefficient responses

Replacing one Bernoulli odds weight has an exact signed response. The
background determinant is retained before taking any estimate. A complete
finite class packet separates every pair of distinct marks, with exact energy.
These are the algebraic inputs to the finite-field marked reference transfer;
no finite-field counting or analytic adapter is asserted here.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

open scoped BigOperators

namespace PrimeFactorOscillations.MarkedCoefficientResponse

/-- All background and replacement cross terms remain coupled. -/
theorem swap_ratio_sub (e0 e1 e2 a b : Real)
    (ha : Not (e0 + a * e1 = 0)) (hb : Not (e0 + b * e1 = 0)) :
    (e1 + b * e2) / (e0 + b * e1) -
        (e1 + a * e2) / (e0 + a * e1) =
      (a - b) * (e1 ^ 2 - e0 * e2) /
        ((e0 + a * e1) * (e0 + b * e1)) := by
  rw [div_sub_div _ _ hb ha]
  congr 1 <;> ring

/-- The coupled identity for the actual elementary-symmetric coefficient ratios. -/
theorem esymm_swap_ratio_sub (s : Multiset Real) (r : Nat) (a b : Real)
    (ha : Not (s.esymm (r + 2) + a * s.esymm (r + 1) = 0))
    (hb : Not (s.esymm (r + 2) + b * s.esymm (r + 1) = 0)) :
    (Multiset.cons b s).esymm (r + 1) / (Multiset.cons b s).esymm (r + 2) -
        (Multiset.cons a s).esymm (r + 1) / (Multiset.cons a s).esymm (r + 2) =
      (a - b) * ((s.esymm (r + 1)) ^ 2 - s.esymm (r + 2) * s.esymm r) /
        ((s.esymm (r + 2) + a * s.esymm (r + 1)) *
          (s.esymm (r + 2) + b * s.esymm (r + 1))) := by
  simpa only [Multiset.esymm_cons_succ_ordered] using
    swap_ratio_sub (s.esymm (r + 2)) (s.esymm (r + 1)) (s.esymm r) a b ha hb

/-- Strict Newton positivity makes the smaller inserted weight raise the ratio. -/
theorem swap_ratio_pos (e0 e1 e2 a b : Real)
    (ha : 0 < e0 + a * e1) (hb : 0 < e0 + b * e1)
    (hab : b < a) (hdet : 0 < e1 ^ 2 - e0 * e2) :
    0 < (e1 + b * e2) / (e0 + b * e1) -
      (e1 + a * e2) / (e0 + a * e1) := by
  rw [swap_ratio_sub e0 e1 e2 a b (ne_of_gt ha) (ne_of_gt hb)]
  exact div_pos (mul_pos (sub_pos.mpr hab) hdet) (mul_pos ha hb)

/-- The split/inert norm-form odds contrast, including their overlap correction. -/
theorem norm_form_odds_sub (Q : Real)
    (hminus : Not (Q - 1 = 0)) (hplus : Not (Q + 1 = 0)) :
    (2 * Q - 1) / (Q - 1) ^ 2 - 1 / ((Q - 1) * (Q + 1)) =
      2 * Q ^ 2 / ((Q - 1) ^ 2 * (Q + 1)) := by
  field_simp [hminus, hplus]
  <;> ring

/-- A weighted complete packet has no blind pair of distinct class labels. -/
theorem class_packet_energy {I : Type*} [Fintype I] [DecidableEq I]
    (g : I -> Real) (a b : I) (hab : Not (a = b)) :
    (Finset.univ.sum fun c : I =>
      (g c * ((if c = a then 1 else 0) - (if c = b then 1 else 0))) ^ 2) =
      (g a) ^ 2 + (g b) ^ 2 := by
  have hpoint : forall c : I,
      (g c * ((if c = a then 1 else 0) - (if c = b then 1 else 0))) ^ 2 =
        (if c = a then (g a) ^ 2 else 0) +
          (if c = b then (g b) ^ 2 else 0) := by
    intro c
    by_cases hca : c = a
    . subst c
      simp [hab]
    . by_cases hcb : c = b
      . subst c
        simp [hca]
      . simp [hca, hcb]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The normalized complete packet retains squared edge signal exactly two. -/
theorem class_packet_unit_energy {I : Type*} [Fintype I] [DecidableEq I]
    (a b : I) (hab : Not (a = b)) :
    (Finset.univ.sum fun c : I =>
      (((if c = a then 1 else 0) - (if c = b then 1 else 0)) : Real) ^ 2) = 2 := by
  have h := class_packet_energy (fun _ : I => (1 : Real)) a b hab
  simp only [one_mul] at h
  convert h using 1 <;> ring

/-- The complete signed linear interaction depends only on the two edge classes. -/
theorem class_packet_cross_sum {I : Type*} [Fintype I] [DecidableEq I]
    (g : I -> Real) (a b : I) :
    (Finset.univ.sum fun c : I =>
      g c * ((if c = a then 1 else 0) - (if c = b then 1 else 0))) =
        g a - g b := by
  simp_rw [mul_sub, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_sub_distrib]
  simp

/-- Exact energy expansion retains both endpoint cross terms and every error square. -/
theorem class_packet_energy_expansion {I : Type*} [Fintype I] [DecidableEq I]
    (g : I -> Real) (a b : I) (hab : Not (a = b)) :
    (Finset.univ.sum fun c : I =>
      (g c + ((if c = a then 1 else 0) - (if c = b then 1 else 0))) ^ 2) =
        2 + 2 * (g a - g b) + Finset.univ.sum (fun c : I => (g c) ^ 2) := by
  have hpoint : forall c : I,
      (g c + ((if c = a then 1 else 0) - (if c = b then 1 else 0))) ^ 2 =
        (g c) ^ 2 +
          2 * (g c * ((if c = a then 1 else 0) - (if c = b then 1 else 0))) +
          (((if c = a then 1 else 0) - (if c = b then 1 else 0)) : Real) ^ 2 := by
    intro c
    ring
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hcross :
      (Finset.univ.sum fun c : I =>
        2 * (g c * ((if c = a then 1 else 0) - (if c = b then 1 else 0)))) =
          2 * g a - 2 * g b := by
    simpa only [mul_assoc] using class_packet_cross_sum (fun c : I => 2 * g c) a b
  rw [hcross, class_packet_unit_energy a b hab]
  ring

/-- One-sided endpoint errors suffice; all other class errors help the lower bound. -/
theorem class_packet_energy_lower {I : Type*} [Fintype I] [DecidableEq I]
    (g : I -> Real) (a b : I) (hab : Not (a = b)) (eps : Real)
    (ha : -eps <= g a) (hb : g b <= eps) :
    2 - 4 * eps <=
      (Finset.univ.sum fun c : I =>
        (g c + ((if c = a then 1 else 0) - (if c = b then 1 else 0))) ^ 2) := by
  rw [class_packet_energy_expansion g a b hab]
  have hs : 0 <= Finset.univ.sum (fun c : I => (g c) ^ 2) :=
    Finset.sum_nonneg (fun c _ => sq_nonneg (g c))
  linarith

end PrimeFactorOscillations.MarkedCoefficientResponse
