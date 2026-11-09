/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring.Basic

/-! # Centered quadratic gaps under complete-graph coordinates

The exact complete-coordinate decomposition retains every row cross term.
Its energy split proves that appending any coordinate with at least six
classes preserves a centered spectral bound of one fifth. This is the finite
induction step used before transferring a residue-product kernel to primes.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace Finset

variable {I J : Type*}

def kernelBilinear (s : Finset J) (K : J -> J -> Real)
    (f g : J -> Real) : Real :=
  s.sum (fun x => s.sum (fun y => K x y * f x * g y))

theorem kernelBilinear_add_left (s : Finset J) (K : J -> J -> Real)
    (f g h : J -> Real) :
    kernelBilinear s K (fun x => f x + g x) h =
      kernelBilinear s K f h + kernelBilinear s K g h := by
  simp only [kernelBilinear, mul_add, add_mul, sum_add_distrib]

theorem kernelBilinear_add_right (s : Finset J) (K : J -> J -> Real)
    (f g h : J -> Real) :
    kernelBilinear s K f (fun x => g x + h x) =
      kernelBilinear s K f g + kernelBilinear s K f h := by
  simp only [kernelBilinear, mul_add, sum_add_distrib]

theorem kernelBilinear_sum_left (s : Finset J) (a : Finset I)
    (K : J -> J -> Real) (f : I -> J -> Real) (g : J -> Real) :
    kernelBilinear s K (fun x => a.sum (fun i => f i x)) g =
      a.sum (fun i => kernelBilinear s K (f i) g) := by
  simp only [kernelBilinear, mul_sum, sum_mul]
  exact sum_comm_cycle

theorem kernelBilinear_sum_right (s : Finset J) (a : Finset I)
    (K : J -> J -> Real) (f : J -> Real) (g : I -> J -> Real) :
    kernelBilinear s K f (fun x => a.sum (fun i => g i x)) =
      a.sum (fun i => kernelBilinear s K f (g i)) := by
  simp only [kernelBilinear, mul_sum]
  exact sum_comm_cycle

theorem kernelBilinear_const_mul_left (s : Finset J) (K : J -> J -> Real)
    (c : Real) (f g : J -> Real) :
    kernelBilinear s K (fun x => c * f x) g = c * kernelBilinear s K f g := by
  unfold kernelBilinear
  rw [mul_sum]
  apply sum_congr rfl
  intro x hx
  rw [mul_sum]
  apply sum_congr rfl
  intro y hy
  ring1

theorem kernelBilinear_const_mul_right (s : Finset J) (K : J -> J -> Real)
    (c : Real) (f g : J -> Real) :
    kernelBilinear s K f (fun x => c * g x) = c * kernelBilinear s K f g := by
  unfold kernelBilinear
  rw [mul_sum]
  apply sum_congr rfl
  intro x hx
  rw [mul_sum]
  apply sum_congr rfl
  intro y hy
  ring1

theorem sum_centered_rows (a : Finset I) (f : I -> J -> Real)
    (ha : 0 < a.card) (y : J) :
    a.sum (fun i => f i y - a.sum (fun j => f j y) / (a.card : Real)) = 0 := by
  have hm : Not ((a.card : Real) = 0) := by exact_mod_cast Nat.ne_of_gt ha
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
  field_simp
  ring1

/-- Exact signed tensor step for a complete-graph coordinate. -/
theorem kernelBilinear_complete_coordinate (s : Finset J) (a : Finset I)
    [DecidableEq I] (K : J -> J -> Real) (f : I -> J -> Real)
    (g : J -> Real) (r : I -> J -> Real)
    (hf : forall i, Membership.mem a i -> forall y, f i y = g y + r i y)
    (hr : forall y, a.sum (fun i => r i y) = 0) :
    a.sum (fun i => (a.erase i).sum (fun j => kernelBilinear s K (f i) (f j))) =
      (a.card : Real) * ((a.card : Real) - 1) * kernelBilinear s K g g -
        a.sum (fun i => kernelBilinear s K (r i) (r i)) := by
  have hfull : a.sum (fun i => a.sum (fun j => kernelBilinear s K (f i) (f j))) =
      (a.card : Real) ^ 2 * kernelBilinear s K g g := by
    have hsum : (fun y => a.sum (fun i => f i y)) =
        (fun y => (a.card : Real) * g y) := by
      funext y
      calc
        _ = a.sum (fun i => g y + r i y) := sum_congr rfl (fun i hi => hf i hi y)
        _ = _ := by rw [sum_add_distrib, hr, sum_const, nsmul_eq_mul]; ring1
    simp_rw [<- kernelBilinear_sum_right]
    rw [<- kernelBilinear_sum_left]
    rw [hsum, kernelBilinear_const_mul_left, kernelBilinear_const_mul_right]
    ring1
  have hdiag : a.sum (fun i => kernelBilinear s K (f i) (f i)) =
      (a.card : Real) * kernelBilinear s K g g +
        a.sum (fun i => kernelBilinear s K (r i) (r i)) := by
    have hsplit : forall i, Membership.mem a i ->
        kernelBilinear s K (f i) (f i) =
          kernelBilinear s K g g + kernelBilinear s K g (r i) +
            kernelBilinear s K (r i) g + kernelBilinear s K (r i) (r i) := by
      intro i hi
      have heq : f i = fun y => g y + r i y := funext (hf i hi)
      rw [heq, kernelBilinear_add_left, kernelBilinear_add_right,
        kernelBilinear_add_right]
      ring1
    calc
      _ = a.sum (fun i => kernelBilinear s K g g + kernelBilinear s K g (r i) +
          kernelBilinear s K (r i) g + kernelBilinear s K (r i) (r i)) :=
        sum_congr rfl hsplit
      _ = _ := by
        simp only [sum_add_distrib, sum_const, nsmul_eq_mul]
        rw [<- kernelBilinear_sum_right, <- kernelBilinear_sum_left]
        simp only [hr, kernelBilinear, mul_zero, zero_mul, sum_const_zero, add_zero]
  have hoff : a.sum (fun i => (a.erase i).sum
      (fun j => kernelBilinear s K (f i) (f j))) =
      a.sum (fun i => a.sum (fun j => kernelBilinear s K (f i) (f j))) -
        a.sum (fun i => kernelBilinear s K (f i) (f i)) := by
    rw [<- sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    exact sum_erase_eq_sub hi
  rw [hoff, hfull, hdiag]
  ring1


/-- Orthogonal energy split, using the same complete family of residual rows. -/
theorem sum_sq_complete_coordinate (s : Finset J) (a : Finset I)
    (f : I -> J -> Real) (g : J -> Real) (r : I -> J -> Real)
    (hf : forall i, Membership.mem a i -> forall y, f i y = g y + r i y)
    (hr : forall y, a.sum (fun i => r i y) = 0) :
    a.sum (fun i => s.sum (fun y => (f i y) ^ 2)) =
      (a.card : Real) * s.sum (fun y => (g y) ^ 2) +
        a.sum (fun i => s.sum (fun y => (r i y) ^ 2)) := by
  have hcross : a.sum (fun i => s.sum (fun y => 2 * g y * r i y)) = 0 := by
    rw [sum_comm]
    simp only [<- mul_sum, hr, mul_zero, sum_const_zero]
  calc
    _ = a.sum (fun i => s.sum (fun y =>
        (g y) ^ 2 + 2 * g y * r i y + (r i y) ^ 2)) := by
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro y hy
      rw [hf i hi y]
      ring1
    _ = _ := by
      simp only [sum_add_distrib]
      rw [sum_const, nsmul_eq_mul, hcross, add_zero]

/-- The signed complete-coordinate identity gives the maximum, rather than
the sum, of the old centered gap and the new coordinate gap. -/
theorem kernelBilinear_complete_coordinate_gap (s : Finset J) (a : Finset I)
    [DecidableEq I] (K : J -> J -> Real) (f : I -> J -> Real)
    (g : J -> Real) (r : I -> J -> Real) (c center variance : Real)
    (ha : 2 <= a.card)
    (hf : forall i, Membership.mem a i -> forall y, f i y = g y + r i y)
    (hr : forall y, a.sum (fun i => r i y) = 0)
    (hgap : abs (kernelBilinear s K g g - center) <= c * variance)
    (hrows : forall i, Membership.mem a i ->
      abs (kernelBilinear s K (r i) (r i)) <= s.sum (fun y => (r i y) ^ 2))
    (hcoef : 1 / ((a.card : Real) - 1) <= c) :
    abs (a.sum (fun i => (a.erase i).sum
        (fun j => kernelBilinear s K (f i) (f j))) / ((a.card : Real) - 1) -
      (a.card : Real) * center) <=
      c * ((a.card : Real) * variance +
        a.sum (fun i => s.sum (fun y => (r i y) ^ 2))) := by
  let m : Real := (a.card : Real)
  let B : Real := a.sum (fun i => kernelBilinear s K (r i) (r i))
  let E : Real := a.sum (fun i => s.sum (fun y => (r i y) ^ 2))
  have hm : 2 <= m := by
    dsimp only [m]
    exact_mod_cast ha
  have hm0 : 0 <= m := by linarith only [hm]
  have hm1 : 0 < m - 1 := by linarith only [hm]
  have hE : 0 <= E := sum_nonneg (fun i _ => sum_nonneg (fun y _ => sq_nonneg _))
  have hB : abs B <= E := by
    calc
      _ <= a.sum (fun i => abs (kernelBilinear s K (r i) (r i))) :=
        abs_sum_le_sum_abs _ _
      _ <= E := sum_le_sum hrows
  have hdiv : abs (B / (m - 1)) <= c * E := by
    calc
      _ = abs B / (m - 1) := by rw [abs_div, abs_of_pos hm1]
      _ <= E / (m - 1) := div_le_div_of_nonneg_right hB (le_of_lt hm1)
      _ = (1 / (m - 1)) * E := by ring1
      _ <= c * E := mul_le_mul_of_nonneg_right hcoef hE
  have hmain : abs (m * (kernelBilinear s K g g - center)) <=
      m * (c * variance) := by
    rw [abs_mul, abs_of_nonneg hm0]
    exact mul_le_mul_of_nonneg_left hgap hm0
  have hidentity :
      a.sum (fun i => (a.erase i).sum
        (fun j => kernelBilinear s K (f i) (f j))) / (m - 1) - m * center =
      m * (kernelBilinear s K g g - center) - B / (m - 1) := by
    rw [kernelBilinear_complete_coordinate s a K f g r hf hr]
    change (m * (m - 1) * kernelBilinear s K g g - B) / (m - 1) -
      m * center = m * (kernelBilinear s K g g - center) - B / (m - 1)
    field_simp [ne_of_gt hm1]
    ring1
  change abs (_ / (m - 1) - m * center) <= c * (m * variance + E)
  rw [hidentity]
  apply abs_le.mpr
  constructor
  case left =>
    nlinarith only [(abs_le.mp hmain).1, (abs_le.mp hdiv).2]
  case right =>
    nlinarith only [(abs_le.mp hmain).2, (abs_le.mp hdiv).1]


/-- Centered energy is a sum of squares on the exact finite support. -/
theorem sum_sq_sub_sq_sum_div_card_nonneg (s : Finset J) (f : J -> Real)
    (hs : 0 < s.card) :
    0 <= s.sum (fun y => (f y) ^ 2) - (s.sum f) ^ 2 / (s.card : Real) := by
  have hn : Not ((s.card : Real) = 0) := by exact_mod_cast Nat.ne_of_gt hs
  let b : Real := s.sum f / (s.card : Real)
  have hsplit : s.sum (fun y => (f y - b) ^ 2) =
      s.sum (fun y => (f y) ^ 2) - (s.sum f) ^ 2 / (s.card : Real) := by
    calc
      _ = s.sum (fun y => (f y) ^ 2 - (2 * b) * f y + b ^ 2) := by
        apply sum_congr rfl
        intro y hy
        ring1
      _ = _ := by
        simp only [sum_add_distrib, sum_sub_distrib, <- mul_sum, sum_const,
          nsmul_eq_mul]
        dsimp only [b]
        field_simp
        ring1
  rw [<- hsplit]
  exact sum_nonneg (fun y _ => sq_nonneg _)

/-- A centered gap at most one also controls the full quadratic form. -/
theorem kernelBilinear_abs_le_energy_of_fifth_gap (s : Finset J)
    (K : J -> J -> Real) (hs : 0 < s.card)
    (hgap : forall f : J -> Real,
      abs (kernelBilinear s K f f - (s.sum f) ^ 2 / (s.card : Real)) <=
        (1 / 5 : Real) *
          (s.sum (fun y => (f y) ^ 2) - (s.sum f) ^ 2 / (s.card : Real)))
    (f : J -> Real) :
    abs (kernelBilinear s K f f) <= s.sum (fun y => (f y) ^ 2) := by
  have hv := sum_sq_sub_sq_sum_div_card_nonneg s f hs
  have hm : 0 <= (s.sum f) ^ 2 / (s.card : Real) :=
    div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  have h := abs_le.mp (hgap f)
  apply abs_le.mpr
  constructor
  case left => nlinarith only [h.1, hv, hm]
  case right => nlinarith only [h.2, hv]

/-- Mean and energy normalization for the complete coordinate. -/
theorem sum_complete_coordinate (s : Finset J) (a : Finset I)
    (f : I -> J -> Real) (g : J -> Real) (r : I -> J -> Real)
    (hf : forall i, Membership.mem a i -> forall y, f i y = g y + r i y)
    (hr : forall y, a.sum (fun i => r i y) = 0) :
    a.sum (fun i => s.sum (f i)) = (a.card : Real) * s.sum g := by
  have hrow (y : J) : a.sum (fun i => f i y) = (a.card : Real) * g y := by
    calc
      _ = a.sum (fun i => g y + r i y) := sum_congr rfl (fun i hi => hf i hi y)
      _ = _ := by rw [sum_add_distrib, hr, sum_const, nsmul_eq_mul, add_zero]
  rw [sum_comm]
  simp_rw [hrow]
  exact (mul_sum _ _ _).symm

/-- Adding an arbitrary complete-graph coordinate with at least six classes
preserves the centered one-fifth spectral gap. -/
theorem kernelBilinear_complete_coordinate_fifth_gap (s : Finset J) (a : Finset I)
    [DecidableEq I] (K : J -> J -> Real) (ha : 6 <= a.card) (hs : 0 < s.card)
    (hgap : forall h : J -> Real,
      abs (kernelBilinear s K h h - (s.sum h) ^ 2 / (s.card : Real)) <=
        (1 / 5 : Real) *
          (s.sum (fun y => (h y) ^ 2) - (s.sum h) ^ 2 / (s.card : Real)))
    (f : I -> J -> Real) :
    abs (a.sum (fun i => (a.erase i).sum
        (fun j => kernelBilinear s K (f i) (f j))) / ((a.card : Real) - 1) -
      (a.sum (fun i => s.sum (f i))) ^ 2 /
        ((a.card : Real) * (s.card : Real))) <=
    (1 / 5 : Real) * (a.sum (fun i => s.sum (fun y => (f i y) ^ 2)) -
      (a.sum (fun i => s.sum (f i))) ^ 2 /
        ((a.card : Real) * (s.card : Real))) := by
  let m : Real := (a.card : Real)
  let N : Real := (s.card : Real)
  let g : J -> Real := fun y => a.sum (fun i => f i y) / m
  let r : I -> J -> Real := fun i y => f i y - g y
  let center : Real := (s.sum g) ^ 2 / N
  have hm : 6 <= m := by
    dsimp only [m]
    exact_mod_cast ha
  have hmne : Not (m = 0) := by linarith only [hm]
  have hN : Not (N = 0) := by
    dsimp only [N]
    exact_mod_cast Nat.ne_of_gt hs
  have hf : forall i, Membership.mem a i -> forall y, f i y = g y + r i y := by
    intro i hi y
    dsimp only [r]
    ring1
  have hr : forall y, a.sum (fun i => r i y) = 0 := by
    intro y
    exact sum_centered_rows a f (lt_of_lt_of_le (by decide : 0 < 6) ha) y
  have hcoef : 1 / (m - 1) <= (1 / 5 : Real) :=
    div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith only [hm])
  have htotal := sum_complete_coordinate s a f g r hf hr
  have henergy := sum_sq_complete_coordinate s a f g r hf hr
  have hcenter : (a.sum (fun i => s.sum (f i))) ^ 2 / (m * N) = m * center := by
    rw [htotal]
    change (m * s.sum g) ^ 2 / (m * N) = m * ((s.sum g) ^ 2 / N)
    field_simp [hmne, hN]
  have hvariance :
      a.sum (fun i => s.sum (fun y => (f i y) ^ 2)) -
        (a.sum (fun i => s.sum (f i))) ^ 2 / (m * N) =
      m * (s.sum (fun y => (g y) ^ 2) - center) +
        a.sum (fun i => s.sum (fun y => (r i y) ^ 2)) := by
    rw [hcenter, henergy]
    change m * _ + _ - m * center = m * (_ - center) + _
    ring1
  change abs (_ / (m - 1) - _ / (m * N)) <= (1 / 5 : Real) * (_ - _ / (m * N))
  rw [hvariance, hcenter]
  apply kernelBilinear_complete_coordinate_gap s a K f g r (1 / 5) center
    (s.sum (fun y => (g y) ^ 2) - center) (Nat.le_trans (by decide) ha) hf hr (hgap g)
  case hrows =>
    intro i hi
    exact kernelBilinear_abs_le_energy_of_fifth_gap s K hs hgap (r i)
  case hcoef => exact hcoef

end Finset
