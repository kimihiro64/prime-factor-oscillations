/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.Analysis.MeanInequalities.CompleteCoordinateGap

/-! # Complete-product centered gaps and the binary parity mode

An algebraically generated product of normalized complete graphs, with every
factor of size at least six, has a centered one-fifth quadratic gap. The binary
extension keeps both constant and parity modes, with the same residual bound.
No analytic estimate is stored in the inductive construction predicate.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace Finset

variable {I J : Type*} [DecidableEq I]

def completeCoordinateKernel (a : Finset I) (K : J -> J -> Real)
    (x y : Prod I J) : Real :=
  if x.1 = y.1 then 0 else K x.2 y.2 / ((a.card : Real) - 1)

theorem kernelBilinear_product_complete (a : Finset I) (s : Finset J)
    (K : J -> J -> Real) (f g : Prod I J -> Real) :
    kernelBilinear (a.product s) (completeCoordinateKernel a K) f g =
      a.sum (fun i => (a.erase i).sum (fun j =>
        kernelBilinear s K (fun y => f (i, y)) (fun y => g (j, y)))) /
          ((a.card : Real) - 1) := by
  have hp (h : Prod I J -> Real) :
      (a.product s).sum h = a.sum (fun i => s.sum (fun y => h (i, y))) :=
    Finset.sum_product a s h
  have hcell (i j : I) :
      s.sum (fun x => s.sum (fun y =>
        completeCoordinateKernel a K (i, x) (j, y) * f (i, x) * g (j, y))) =
      (if i = j then 0 else
        kernelBilinear s K (fun x => f (i, x)) (fun y => g (j, y))) /
        ((a.card : Real) - 1) := by
    by_cases h : i = j
    case pos => simp only [completeCoordinateKernel, h, ite_true, zero_mul,
      sum_const_zero, zero_div]
    case neg =>
      simp only [completeCoordinateKernel, h, ite_false]
      unfold kernelBilinear
      simp only [div_eq_mul_inv]
      rw [sum_mul]
      apply sum_congr rfl
      intro x hx
      rw [sum_mul]
      apply sum_congr rfl
      intro y hy
      ring1
  have hoff (i : I) (hi : Membership.mem a i) :
      a.sum (fun j => if i = j then 0 else
        kernelBilinear s K (fun x => f (i, x)) (fun y => g (j, y))) =
      (a.erase i).sum (fun j =>
        kernelBilinear s K (fun x => f (i, x)) (fun y => g (j, y))) := by
    have heq := sum_erase_eq_sub
      (f := fun j => if i = j then 0 else
        kernelBilinear s K (fun x => f (i, x)) (fun y => g (j, y))) hi
    simp only [ite_true, sub_zero] at heq
    rw [<- heq]
    apply sum_congr rfl
    intro j hj
    rw [ite_eq_right (ne_of_mem_erase hj).symm]
  calc
    _ = a.sum (fun i => a.sum (fun j => s.sum (fun x => s.sum (fun y =>
        completeCoordinateKernel a K (i, x) (j, y) * f (i, x) * g (j, y))))) := by
      unfold kernelBilinear
      simp only [hp]
      apply sum_congr rfl
      intro i hi
      exact sum_comm
    _ = _ := by
      simp_rw [hcell, div_eq_mul_inv]
      rw [sum_mul]
      apply sum_congr rfl
      intro i hi
      rw [<- sum_mul, hoff i hi]

theorem kernelBilinear_product_complete_fifth_gap (a : Finset I) (s : Finset J)
    (K : J -> J -> Real) (ha : 6 <= a.card) (hs : 0 < s.card)
    (hgap : forall h : J -> Real,
      abs (kernelBilinear s K h h - (s.sum h) ^ 2 / (s.card : Real)) <=
        (1 / 5 : Real) *
          (s.sum (fun y => (h y) ^ 2) - (s.sum h) ^ 2 / (s.card : Real)))
    (f : Prod I J -> Real) :
    abs (kernelBilinear (a.product s) (completeCoordinateKernel a K) f f -
      ((a.product s).sum f) ^ 2 / ((a.product s).card : Real)) <=
      (1 / 5 : Real) * ((a.product s).sum (fun x => (f x) ^ 2) -
        ((a.product s).sum f) ^ 2 / ((a.product s).card : Real)) := by
  have hp (h : Prod I J -> Real) :
      (a.product s).sum h = a.sum (fun i => s.sum (fun y => h (i, y))) :=
    Finset.sum_product a s h
  have hc : (a.product s).card = a.card * s.card := Finset.card_product a s
  rw [kernelBilinear_product_complete]
  simpa only [hp, hc, Nat.cast_mul] using
    kernelBilinear_complete_coordinate_fifth_gap s a K ha hs hgap
      (fun i y => f (i, y))


universe u

/-- Algebraic construction of finite products of normalized complete graphs.
The constructor carries no analytic estimate. -/
inductive IsLargeCompleteProduct :
    {J : Type u} -> Finset J -> (J -> J -> Real) -> Prop
  | singleton {J : Type u} (x : J) :
      IsLargeCompleteProduct (Singleton.singleton x) (fun _ _ => 1)
  | coordinate {I J : Type u} [DecidableEq I] (a : Finset I) (s : Finset J)
      (K : J -> J -> Real) (ha : 6 <= a.card) (h : IsLargeCompleteProduct s K) :
      IsLargeCompleteProduct (a.product s) (completeCoordinateKernel a K)

theorem IsLargeCompleteProduct.card_pos {J : Type u} {s : Finset J}
    {K : J -> J -> Real} (h : IsLargeCompleteProduct s K) : 0 < s.card := by
  induction h with
  | singleton x => simp only [card_singleton]; decide
  | coordinate a s K ha h ih =>
    have hc : (a.product s).card = a.card * s.card := Finset.card_product a s
    rw [hc]
    exact Nat.mul_pos (lt_of_lt_of_le (by decide : 0 < 6) ha) ih

/-- Every finite product, of any arity and with all sizes at least six,
has centered normalized spectral gap at most one fifth. -/
theorem IsLargeCompleteProduct.fifth_gap {J : Type u} {s : Finset J}
    {K : J -> J -> Real} (h : IsLargeCompleteProduct s K) (f : J -> Real) :
    abs (kernelBilinear s K f f - (s.sum f) ^ 2 / (s.card : Real)) <=
      (1 / 5 : Real) *
        (s.sum (fun y => (f y) ^ 2) - (s.sum f) ^ 2 / (s.card : Real)) := by
  induction h with
  | singleton x => simp only [kernelBilinear, sum_singleton, card_singleton,
      Nat.cast_one, div_one, one_mul, pow_two, sub_self, abs_zero, mul_zero, le_refl]
  | coordinate a s K ha h ih =>
    exact kernelBilinear_product_complete_fifth_gap a s K ha h.card_pos ih f


/-- The binary factor retains its negative mode. The two leading energies
are the total mean and the difference between the two row means. -/
theorem IsLargeCompleteProduct.parity_gap {J : Type u} {s : Finset J}
    {K : J -> J -> Real} (h : IsLargeCompleteProduct s K) (f0 f1 : J -> Real) :
    abs (kernelBilinear s K f0 f1 + kernelBilinear s K f1 f0 -
      ((s.sum f0 + s.sum f1) ^ 2 - (s.sum f0 - s.sum f1) ^ 2) /
        (2 * (s.card : Real))) <=
      (1 / 5 : Real) * (s.sum (fun y => (f0 y) ^ 2) + s.sum (fun y => (f1 y) ^ 2) -
        ((s.sum f0 + s.sum f1) ^ 2 + (s.sum f0 - s.sum f1) ^ 2) /
          (2 * (s.card : Real))) := by
  let g : J -> Real := fun y => (f0 y + f1 y) / 2
  let r : J -> Real := fun y => (f0 y - f1 y) / 2
  have hf0 : f0 = fun y => g y + r y := by
    funext y
    dsimp only [g, r]
    ring1
  have hf1 : f1 = fun y => g y + (-1) * r y := by
    funext y
    dsimp only [g, r]
    ring1
  have hQ : kernelBilinear s K f0 f1 + kernelBilinear s K f1 f0 =
      2 * (kernelBilinear s K g g - kernelBilinear s K r r) := by
    rw [hf0, hf1]
    simp only [kernelBilinear_add_left, kernelBilinear_add_right,
      kernelBilinear_const_mul_left, kernelBilinear_const_mul_right]
    ring1
  have hE : s.sum (fun y => (f0 y) ^ 2) + s.sum (fun y => (f1 y) ^ 2) =
      2 * (s.sum (fun y => (g y) ^ 2) + s.sum (fun y => (r y) ^ 2)) := by
    calc
      _ = s.sum (fun y => (f0 y) ^ 2 + (f1 y) ^ 2) := (sum_add_distrib).symm
      _ = s.sum (fun y => 2 * ((g y) ^ 2 + (r y) ^ 2)) := by
        apply sum_congr rfl
        intro y hy
        dsimp only [g, r]
        ring1
      _ = _ := by rw [<- mul_sum, sum_add_distrib]
  have hSg : s.sum g = (s.sum f0 + s.sum f1) / 2 := by
    dsimp only [g]
    simp only [div_eq_mul_inv, add_mul, sum_add_distrib, <- sum_mul]
  have hSr : s.sum r = (s.sum f0 - s.sum f1) / 2 := by
    dsimp only [r]
    simp only [div_eq_mul_inv, sub_mul, sum_sub_distrib, <- sum_mul]
  have hn : Not ((s.card : Real) = 0) := by
    exact_mod_cast Nat.ne_of_gt h.card_pos
  have hcenter :
      ((s.sum f0 + s.sum f1) ^ 2 - (s.sum f0 - s.sum f1) ^ 2) /
        (2 * (s.card : Real)) =
      2 * ((s.sum g) ^ 2 / (s.card : Real) - (s.sum r) ^ 2 / (s.card : Real)) := by
    rw [hSg, hSr]
    field_simp
  have hmass :
      ((s.sum f0 + s.sum f1) ^ 2 + (s.sum f0 - s.sum f1) ^ 2) /
        (2 * (s.card : Real)) =
      2 * ((s.sum g) ^ 2 / (s.card : Real) + (s.sum r) ^ 2 / (s.card : Real)) := by
    rw [hSg, hSr]
    field_simp
  have hg := abs_le.mp (h.fifth_gap g)
  have hr := abs_le.mp (h.fifth_gap r)
  rw [hQ, hE, hcenter, hmass]
  apply abs_le.mpr
  constructor
  case left => nlinarith only [hg.1, hr.2]
  case right => nlinarith only [hg.2, hr.1]

end Finset
