/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.Basic
import PrimeFactorOscillations.Helpers.HamiltonianWickDiagramCoefficients

/-! # Full finite coefficient convolution mass

Every antidiagonal belongs to its unique total degree. The finite triangular
support is kept until it embeds in the full coefficient rectangle.
This controls diagram remainders after their signed low terms are retained.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

def finitePowerSeriesMass (H : Nat) (f : PowerSeries Complex) : Real :=
  Finset.sum (Finset.range (H + 1)) (fun k => norm (PowerSeries.coeff k f))

theorem finitePowerSeriesMass_nonnegative (H : Nat) (f : PowerSeries Complex) :
    0 <= finitePowerSeriesMass H f :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem finitePowerSeriesMass_zero (H : Nat) :
    finitePowerSeriesMass H (0 : PowerSeries Complex) = 0 := by
  simp only [finitePowerSeriesMass, map_zero, norm_zero, Finset.sum_const_zero]

theorem finitePowerSeriesMass_add (H : Nat) (f g : PowerSeries Complex) :
    finitePowerSeriesMass H (f + g) <=
      finitePowerSeriesMass H f + finitePowerSeriesMass H g := by
  unfold finitePowerSeriesMass
  rw [<- Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k hk
  rw [map_add]
  exact norm_add_le _ _

theorem finitePowerSeriesMass_sum {J : Type*} (H : Nat)
    (S : Finset J) (f : J -> PowerSeries Complex) :
    finitePowerSeriesMass H (Finset.sum S f) <=
      Finset.sum S (fun j => finitePowerSeriesMass H (f j)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, finitePowerSeriesMass_zero, le_refl]
  | @insert j S hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact le_trans (finitePowerSeriesMass_add H _ _) (add_le_add le_rfl ih)

theorem finitePowerSeriesMass_const_mul (H : Nat) (c : Complex)
    (f : PowerSeries Complex) :
    finitePowerSeriesMass H (PowerSeries.C c * f) =
      norm c * finitePowerSeriesMass H f := by
  unfold finitePowerSeriesMass
  simp only [PowerSeries.coeff_C_mul, norm_mul, Finset.mul_sum]

theorem finiteAntidiagonal_triangle_sum (H : Nat) (w : Prod Nat Nat -> Real) :
    Finset.sum (Finset.range (H + 1)) (fun k =>
        Finset.sum (Finset.antidiagonal k) w) =
      Finset.sum
        (((Finset.range (H + 1)).product (Finset.range (H + 1))).filter
          (fun p => p.1 + p.2 <= H)) w := by
  rw [Finset.sum_sigma' (Finset.range (H + 1))
    (fun k => Finset.antidiagonal k) (fun _ p => w p)]
  apply Finset.sum_bij (fun x _ => x.2)
  case hi =>
    intro x hx
    have h := Finset.mem_sigma.mp hx
    have hK := Finset.mem_range.mp h.1
    have hP := Finset.mem_antidiagonal.mp h.2
    apply Finset.mem_filter.mpr
    refine And.intro ?_ (by omega)
    apply Finset.mem_product.mpr
    exact And.intro (Finset.mem_range.mpr (by omega))
      (Finset.mem_range.mpr (by omega))
  case i_inj =>
    intro x hx y hy hPair
    have hX := Finset.mem_sigma.mp hx
    have hY := Finset.mem_sigma.mp hy
    have hXP := Finset.mem_antidiagonal.mp hX.2
    have hYP := Finset.mem_antidiagonal.mp hY.2
    have hFirst : x.1 = y.1 := by
      rw [<- hXP, <- hYP, hPair]
    exact Sigma.ext hFirst (heq_of_eq hPair)
  case i_surj =>
    intro p hp
    have h := Finset.mem_filter.mp hp
    refine Exists.intro (Sigma.mk (p.1 + p.2) p) ?_
    refine Exists.intro ?_ rfl
    apply Finset.mem_sigma.mpr
    exact And.intro (Finset.mem_range.mpr (by
      change p.1 + p.2 < H + 1
      omega)) (Finset.mem_antidiagonal.mpr rfl)
  case h =>
    intro x hx
    rfl

theorem finiteAntidiagonal_nonnegative_bound (H : Nat) (a b : Nat -> Real)
    (ha : forall k, 0 <= a k) (hb : forall k, 0 <= b k) :
    Finset.sum (Finset.range (H + 1)) (fun k =>
        Finset.sum (Finset.antidiagonal k) (fun p => a p.1 * b p.2)) <=
      Finset.sum (Finset.range (H + 1)) a *
        Finset.sum (Finset.range (H + 1)) b := by
  rw [finiteAntidiagonal_triangle_sum, Finset.sum_filter]
  calc
    _ <= Finset.sum ((Finset.range (H + 1)).product (Finset.range (H + 1)))
        (fun p => a p.1 * b p.2) := by
      apply Finset.sum_le_sum
      intro p hp
      split_ifs
      case pos => exact le_refl _
      case neg => exact mul_nonneg (ha _) (hb _)
    _ = _ := by
      calc
        _ = Finset.sum (Finset.range (H + 1)) (fun i =>
            Finset.sum (Finset.range (H + 1)) (fun j => a i * b j)) :=
          Finset.sum_product (Finset.range (H + 1)) (Finset.range (H + 1))
            (fun p : Prod Nat Nat => a p.1 * b p.2)
        _ = _ := by rw [Finset.sum_mul_sum]

theorem finitePowerSeriesMass_mul (H : Nat) (f g : PowerSeries Complex) :
    finitePowerSeriesMass H (f * g) <=
      finitePowerSeriesMass H f * finitePowerSeriesMass H g := by
  unfold finitePowerSeriesMass
  calc
    _ <= Finset.sum (Finset.range (H + 1)) (fun k =>
        Finset.sum (Finset.antidiagonal k) (fun p =>
          norm (PowerSeries.coeff p.1 f) * norm (PowerSeries.coeff p.2 g))) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [PowerSeries.coeff_mul]
      simpa only [norm_mul] using
        (norm_sum_le (Finset.antidiagonal k)
          (fun p => PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g))
    _ <= _ := finiteAntidiagonal_nonnegative_bound H
      (fun k => norm (PowerSeries.coeff k f))
      (fun k => norm (PowerSeries.coeff k g))
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)

theorem finite_geometric_sum_identity (theta : Real) (L : Nat) :
    (1 - theta) * Finset.sum (Finset.range L) (fun k => theta ^ k) =
      1 - theta ^ L := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
    ring

theorem finite_geometric_sum_bound (theta : Real) (hTheta0 : 0 <= theta)
    (hTheta1 : theta < 1) (L : Nat) :
    Finset.sum (Finset.range L) (fun k => theta ^ k) <= 1 / (1 - theta) := by
  have hGap : 0 < 1 - theta := sub_pos.mpr hTheta1
  have hGap0 : Not (1 - theta = 0) := ne_of_gt hGap
  have hDiv : (1 / (1 - theta)) * (1 - theta) = 1 := by field_simp
  by_contra hFalse
  have hMul := mul_lt_mul_of_pos_right (lt_of_not_ge hFalse) hGap
  rw [hDiv] at hMul
  have h := finite_geometric_sum_identity theta L
  nlinarith [pow_nonneg hTheta0 L]

theorem finitePowerSeriesMass_geometric (H : Nat) (f : PowerSeries Complex)
    (c theta : Real) (hc : 0 <= c) (hTheta0 : 0 <= theta) (hTheta1 : theta < 1)
    (hZero : PowerSeries.coeff 0 f = 0)
    (hCoeff : forall k, norm (PowerSeries.coeff (k + 1) f) <= c * theta ^ k) :
    finitePowerSeriesMass H f <= c / (1 - theta) := by
  unfold finitePowerSeriesMass
  rw [Finset.sum_range_succ']
  simp only [hZero, norm_zero, add_zero]
  calc
    _ <= Finset.sum (Finset.range H) (fun k => c * theta ^ k) :=
      Finset.sum_le_sum (fun k _ => hCoeff k)
    _ = c * Finset.sum (Finset.range H) (fun k => theta ^ k) := (Finset.mul_sum _ _ _).symm
    _ <= c * (1 / (1 - theta)) :=
      mul_le_mul_of_nonneg_left (finite_geometric_sum_bound theta hTheta0 hTheta1 H) hc
    _ = c / (1 - theta) := by ring

end PrimeFactorOscillations
