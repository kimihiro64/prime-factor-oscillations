/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.Analysis.MeanInequalities.CompleteProductGap

/-! # Zero-one complete products with explicit density

The raw kernel is its row-normalized kernel multiplied by its degree.
The binary extension keeps both mean modes in the counting normalization
required by the uniform signed finite-fibre comparison.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace Finset

universe u

def rawCompleteCoordinateKernel {I J : Type*} [DecidableEq I]
    (K : J -> J -> Real) (x y : Prod I J) : Real :=
  if x.1 = y.1 then 0 else K x.2 y.2

/-- Raw zero-one product kernels, with the exact uniform row density. -/
inductive IsRawCompleteProduct :
    {J : Type u} -> Finset J -> (J -> J -> Real) -> Real -> Prop
  | singleton {J : Type u} (x : J) :
      IsRawCompleteProduct (Singleton.singleton x) (fun _ _ => 1) 1
  | coordinate {I J : Type u} [DecidableEq I] (a : Finset I) (s : Finset J)
      (K : J -> J -> Real) (D : Real) (ha : 6 <= a.card)
      (h : IsRawCompleteProduct s K D) :
      IsRawCompleteProduct (a.product s) (rawCompleteCoordinateKernel K)
        (((a.card : Real) - 1) / (a.card : Real) * D)

theorem IsRawCompleteProduct.normalized_witness {J : Type u} {s : Finset J}
    {K : J -> J -> Real} {D : Real} (h : IsRawCompleteProduct s K D) :
    exists P : J -> J -> Real,
      IsLargeCompleteProduct s P /\ 0 < D /\ D <= 1 /\
        (forall x, Membership.mem s x -> forall y, Membership.mem s y ->
          K x y = ((s.card : Real) * D) * P x y) := by
  induction h with
  | singleton x =>
    refine Exists.intro (fun _ _ => 1) (And.intro (IsLargeCompleteProduct.singleton x)
      (And.intro (by linarith) (And.intro (by linarith) ?_)))
    intro y hy z hz
    simp only [card_singleton, Nat.cast_one, mul_one]
  | coordinate a s K D ha h ih =>
    choose P hP hD hOne hScale using ih
    let m : Real := (a.card : Real)
    have hm : 6 <= m := by
      dsimp only [m]
      exact_mod_cast ha
    have hm0 : 0 < m := by linarith only [hm]
    have hm1 : 0 < m - 1 := by linarith only [hm]
    have hq0 : 0 < (m - 1) / m := div_pos hm1 hm0
    have hq1 : (m - 1) / m <= 1 := by
      calc
        _ <= m / m := div_le_div_of_nonneg_right (by linarith) (le_of_lt hm0)
        _ = 1 := div_self (ne_of_gt hm0)
    have hnew0 : 0 < (m - 1) / m * D := mul_pos hq0 hD
    have hnew1 : (m - 1) / m * D <= 1 := by
      simpa only [mul_one] using mul_le_mul hq1 hOne (le_of_lt hD) (by linarith)
    refine Exists.intro (completeCoordinateKernel a P)
      (And.intro (IsLargeCompleteProduct.coordinate a s P ha hP)
        (And.intro hnew0 (And.intro hnew1 ?_)))
    intro x hx y hy
    have hxS := (mem_product.mp hx).2
    have hyS := (mem_product.mp hy).2
    have hc : ((a.product s).card : Real) = (a.card : Real) * (s.card : Real) := by
      exact_mod_cast Finset.card_product a s
    by_cases hxy : x.1 = y.1
    case pos =>
      simp only [rawCompleteCoordinateKernel, completeCoordinateKernel,
        hxy, ite_true, mul_zero]
    case neg =>
      simp only [rawCompleteCoordinateKernel, completeCoordinateKernel, hxy, ite_false]
      rw [hScale x.2 hxS y.2 hyS, hc]
      change ((s.card : Real) * D) * P x.2 y.2 =
        (m * (s.card : Real) * ((m - 1) / m * D)) * (P x.2 y.2 / (m - 1))
      field_simp [ne_of_gt hm0, ne_of_gt hm1]

theorem IsRawCompleteProduct.zero_or_one {J : Type u} {s : Finset J}
    {K : J -> J -> Real} {D : Real} (h : IsRawCompleteProduct s K D) :
    forall x, Membership.mem s x -> forall y, Membership.mem s y ->
      Or (K x y = 0) (K x y = 1) := by
  induction h with
  | singleton x =>
    intro y hy z hz
    exact Or.inr rfl
  | coordinate a s K D ha h ih =>
    intro x hx y hy
    by_cases hxy : x.1 = y.1
    case pos =>
      exact Or.inl (by simp only [rawCompleteCoordinateKernel, hxy, ite_true])
    case neg =>
      simpa only [rawCompleteCoordinateKernel, hxy, ite_false] using
        ih x.2 (mem_product.mp hx).2 y.2 (mem_product.mp hy).2

private theorem kernelBilinear_eq_scaled {J : Type*} (s : Finset J)
    (K P : J -> J -> Real) (c : Real)
    (hscale : forall x, Membership.mem s x -> forall y, Membership.mem s y ->
      K x y = c * P x y) (f b : J -> Real) :
    kernelBilinear s K f b = c * kernelBilinear s P f b := by
  unfold kernelBilinear
  rw [mul_sum]
  apply sum_congr rfl
  intro x hx
  rw [mul_sum]
  apply sum_congr rfl
  intro y hy
  rw [hscale x hx y hy]
  ring1

/-- Exact density normalization of the two leading binary modes. -/
theorem IsRawCompleteProduct.parity_gap {J : Type u} {s : Finset J}
    {K : J -> J -> Real} {D : Real} (h : IsRawCompleteProduct s K D)
    (f0 f1 : J -> Real) :
    abs (kernelBilinear s K f0 f1 + kernelBilinear s K f1 f0 -
      D / 2 * ((s.sum f0 + s.sum f1) ^ 2 - (s.sum f0 - s.sum f1) ^ 2)) <=
      (D / 2) / 5 * (2 * (s.card : Real) *
        (s.sum (fun y => (f0 y) ^ 2) + s.sum (fun y => (f1 y) ^ 2)) -
        (s.sum f0 + s.sum f1) ^ 2 - (s.sum f0 - s.sum f1) ^ 2) := by
  choose P hP hD hOne hScale using h.normalized_witness
  let N : Real := (s.card : Real)
  let A : Real := (s.sum f0 + s.sum f1) ^ 2 - (s.sum f0 - s.sum f1) ^ 2
  let B : Real := (s.sum f0 + s.sum f1) ^ 2 + (s.sum f0 - s.sum f1) ^ 2
  let E : Real := s.sum (fun y => (f0 y) ^ 2) + s.sum (fun y => (f1 y) ^ 2)
  let Q : Real := kernelBilinear s P f0 f1 + kernelBilinear s P f1 f0
  have hn : Not (N = 0) := by
    dsimp only [N]
    exact_mod_cast Nat.ne_of_gt hP.card_pos
  have hc : 0 <= N * D := mul_nonneg (Nat.cast_nonneg _) (le_of_lt hD)
  have hQ : kernelBilinear s K f0 f1 + kernelBilinear s K f1 f0 = (N * D) * Q := by
    rw [kernelBilinear_eq_scaled s K P (N * D) hScale f0 f1,
      kernelBilinear_eq_scaled s K P (N * D) hScale f1 f0]
    dsimp only [Q]
    ring1
  have hm := mul_le_mul_of_nonneg_left (hP.parity_gap f0 f1) hc
  have hleft : abs ((N * D) * Q - D / 2 * A) =
      (N * D) * abs (Q - A / (2 * N)) := by
    calc
      _ = abs ((N * D) * (Q - A / (2 * N))) := by
        congr 1
        field_simp [hn]
      _ = _ := by rw [abs_mul, abs_of_nonneg hc]
  have hright : (N * D) * ((1 / 5 : Real) * (E - B / (2 * N))) =
      (D / 2) / 5 * (2 * N * E - B) := by
    field_simp [hn]
  change abs (_ - D / 2 * A) <= (D / 2) / 5 *
    (2 * N * E - (s.sum f0 + s.sum f1) ^ 2 - (s.sum f0 - s.sum f1) ^ 2)
  have hsum : 2 * N * E - (s.sum f0 + s.sum f1) ^ 2 -
      (s.sum f0 - s.sum f1) ^ 2 = 2 * N * E - B := by
    dsimp only [B]
    ring1
  rw [hsum, hQ, hleft, <- hright]
  exact hm


def binaryProductSupport {J : Type*} (s : Finset J) : Finset (Prod Bool J) :=
  @Finset.product Bool J (Insert.insert false (Singleton.singleton true)) s

def binaryProductSign {J : Type*} (x : Prod Bool J) : Real :=
  if x.1 then -1 else 1

/-- The full raw binary-product model, in exactly the counting normalization
accepted by the signed finite-fibre sampling theorem. -/
theorem IsRawCompleteProduct.binary_model_gap {J : Type u} {s : Finset J}
    {K : J -> J -> Real} {D : Real} (h : IsRawCompleteProduct s K D)
    (f : Prod Bool J -> Real) :
    abs (kernelBilinear (binaryProductSupport s) (rawCompleteCoordinateKernel K) f f -
      D / 2 * (((binaryProductSupport s).sum f) ^ 2 -
        ((binaryProductSupport s).sum (fun x => binaryProductSign x * f x)) ^ 2)) <=
      (D / 2) / 5 *
        (((binaryProductSupport s).card : Real) *
          (binaryProductSupport s).sum (fun x => (f x) ^ 2) -
        ((binaryProductSupport s).sum f) ^ 2 -
        ((binaryProductSupport s).sum (fun x => binaryProductSign x * f x)) ^ 2) := by
  let B : Finset Bool := Insert.insert false (Singleton.singleton true)
  have hB : B.card = 2 := by decide
  have hf : Not (Membership.mem (Singleton.singleton true : Finset Bool) false) := by decide
  have hden : (B.card : Real) - 1 = 1 := by
    rw [hB]
    ring1
  have hsum (H : Prod Bool J -> Real) :
      (binaryProductSupport s).sum H =
        s.sum (fun y => H (false, y)) + s.sum (fun y => H (true, y)) := by
    have hp : (B.product s).sum H = B.sum (fun i => s.sum (fun y => H (i, y))) :=
      Finset.sum_product B s H
    change (B.product s).sum H = _
    rw [hp]
    simp only [B, sum_insert hf, sum_singleton]
  have hcard : (binaryProductSupport s).card = 2 * s.card := by
    have hc : (B.product s).card = B.card * s.card := Finset.card_product B s
    change (B.product s).card = _
    rw [hc, hB]
  have hsign : (binaryProductSupport s).sum (fun x => binaryProductSign x * f x) =
      s.sum (fun y => f (false, y)) - s.sum (fun y => f (true, y)) := by
    rw [hsum]
    simp [binaryProductSign, sub_eq_add_neg]
  have hkernel : rawCompleteCoordinateKernel K = completeCoordinateKernel B K := by
    funext x y
    simp only [rawCompleteCoordinateKernel, completeCoordinateKernel, hden, div_one]
  have hquad :
      kernelBilinear (binaryProductSupport s) (rawCompleteCoordinateKernel K) f f =
        kernelBilinear s K (fun y => f (false, y)) (fun y => f (true, y)) +
          kernelBilinear s K (fun y => f (true, y)) (fun y => f (false, y)) := by
    change kernelBilinear (B.product s) (rawCompleteCoordinateKernel K) f f = _
    rw [hkernel, kernelBilinear_product_complete, hden, div_one]
    simp [B]
    ring1
  rw [hsign]
  simpa only [hsum, hquad, hcard, Nat.cast_mul, Nat.cast_ofNat] using
    h.parity_gap (fun y => f (false, y)) (fun y => f (true, y))

end Finset
