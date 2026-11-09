/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import PrimeFactorOscillations.Mathlib.Analysis.MeanInequalities.CompleteCoordinateGap

/-! # Signed kernel restriction with sparse exceptions

The full restriction packet keeps both cross orientations and its exceptional
self interaction. Sparse support controls this packet and both mean-square
shifts uniformly over every real test function. The principal kernel is not
replaced by an unsigned envelope.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace Finset

variable {I : Type*}

def kernelRect (s t : Finset I) (K : I -> I -> Real) (f b : I -> Real) : Real :=
  s.sum (fun i => t.sum (fun j => K i j * f i * b j))

theorem abs_kernelRect_le (s t : Finset I) (K : I -> I -> Real) (f b : I -> Real)
    (hK : forall i, Membership.mem s i -> forall j, Membership.mem t j ->
      abs (K i j) <= 1) :
    abs (kernelRect s t K f b) <= s.sum (fun i => abs (f i)) *
      t.sum (fun j => abs (b j)) := by
  unfold kernelRect
  calc
    _ <= s.sum (fun i => abs (t.sum (fun j => K i j * f i * b j))) :=
      abs_sum_le_sum_abs _ _
    _ <= s.sum (fun i => t.sum (fun j => abs (K i j * f i * b j))) := by
      apply sum_le_sum
      intro i hi
      exact abs_sum_le_sum_abs _ _
    _ <= s.sum (fun i => t.sum (fun j => abs (f i) * abs (b j))) := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      rw [abs_mul, abs_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hK i hi j hj) (abs_nonneg (f i)))
        (abs_nonneg (b j))
    _ = _ := by rw [sum_mul_sum]

theorem sum_abs_subset_cross_le (s a : Finset I) (ha : forall {i}, Membership.mem a i -> Membership.mem s i)
    (f : I -> Real) (tau : Real) (htau : 0 <= tau)
    (hcount : (a.card : Real) <= tau ^ 2 * (s.card : Real)) :
    And
      (a.sum (fun i => abs (f i)) * s.sum (fun i => abs (f i)) <=
        tau * ((s.card : Real) * s.sum (fun i => (f i) ^ 2)))
      ((a.sum (fun i => abs (f i))) ^ 2 <=
        tau ^ 2 * ((s.card : Real) * s.sum (fun i => (f i) ^ 2))) := by
  let L := s.sum (fun i => abs (f i))
  let R := a.sum (fun i => abs (f i))
  let E := s.sum (fun i => (f i) ^ 2)
  let W := (s.card : Real) * E
  have hL : 0 <= L := sum_nonneg (fun i _ => abs_nonneg _)
  have hR : 0 <= R := sum_nonneg (fun i _ => abs_nonneg _)
  have hE : 0 <= E := sum_nonneg (fun i _ => sq_nonneg _)
  have hW : 0 <= W := mul_nonneg (Nat.cast_nonneg _) hE
  have hcsS := sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : Real))
    (fun i => abs (f i))
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one, sq_abs] at hcsS
  have hcsA := sum_mul_sq_le_sq_mul_sq a (fun _ => (1 : Real))
    (fun i => abs (f i))
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one, sq_abs] at hcsA
  have heSub : a.sum (fun i => (f i) ^ 2) <= E :=
    sum_le_sum_of_subset_of_nonneg @ha (fun i _ _ => sq_nonneg _)
  have hR2 : R ^ 2 <= tau ^ 2 * W := by
    calc
      _ <= (a.card : Real) * a.sum (fun i => (f i) ^ 2) := hcsA
      _ <= (a.card : Real) * E :=
        mul_le_mul_of_nonneg_left heSub (Nat.cast_nonneg _)
      _ <= (tau ^ 2 * (s.card : Real)) * E :=
        mul_le_mul_of_nonneg_right hcount hE
      _ = _ := by dsimp only [W]; ring1
  have hprod : (R * L) ^ 2 <= (tau * W) ^ 2 := by
    calc
      _ = R ^ 2 * L ^ 2 := by ring1
      _ <= (tau ^ 2 * W) * W :=
        mul_le_mul hR2 hcsS (sq_nonneg L) (mul_nonneg (sq_nonneg tau) hW)
      _ = _ := by ring1
  have hcross : R * L <= tau * W := by
    nlinarith only [hprod, mul_nonneg hR hL, mul_nonneg htau hW]
  exact And.intro hcross hR2

variable [DecidableEq I]

/-- Both cross orientations and the complete exceptional diagonal are retained. -/
theorem abs_kernelBilinear_sub_restrict_le (s t : Finset I) (ht : forall {i}, Membership.mem t i -> Membership.mem s i)
    (K : I -> I -> Real) (f : I -> Real) (tau : Real) (htau : 0 <= tau)
    (hcount : ((s \ t).card : Real) <= tau ^ 2 * (s.card : Real))
    (hK : forall i, Membership.mem s i -> forall j, Membership.mem s j ->
      abs (K i j) <= 1) :
    abs (kernelBilinear s K f f - kernelBilinear t K f f) <=
      (2 * tau + tau ^ 2) * ((s.card : Real) * s.sum (fun i => (f i) ^ 2)) := by
  let a := s \ t
  let L := s.sum (fun i => abs (f i))
  let R := a.sum (fun i => abs (f i))
  let W := (s.card : Real) * s.sum (fun i => (f i) ^ 2)
  have ha : forall {i}, Membership.mem a i -> Membership.mem s i := by
    intro i hi
    exact (mem_sdiff.mp hi).1
  have hdis : Disjoint t a := by
    apply disjoint_left.mpr
    intro i hi hia
    exact (mem_sdiff.mp hia).2 hi
  have hunion : Union.union t a = s := union_sdiff_of_subset @ht
  have hsum (H : I -> Real) : s.sum H = t.sum H + a.sum H := by
    rw [<- hunion, sum_union hdis]
  have hpacket : kernelBilinear s K f f - kernelBilinear t K f f =
      kernelRect t a K f f + kernelRect a t K f f + kernelRect a a K f f := by
    unfold kernelBilinear kernelRect
    rw [hsum]
    simp_rw [hsum]
    simp only [sum_add_distrib]
    ring1
  have hT : t.sum (fun i => abs (f i)) <= L :=
    sum_le_sum_of_subset_of_nonneg @ht (fun i _ _ => abs_nonneg _)
  have hR : 0 <= R := sum_nonneg (fun i _ => abs_nonneg _)
  have h1 : abs (kernelRect t a K f f) <= R * L := by
    calc
      _ <= t.sum (fun i => abs (f i)) * R :=
        abs_kernelRect_le t a K f f (fun i hi j hj => hK i (ht hi) j (ha hj))
      _ <= L * R := mul_le_mul_of_nonneg_right hT hR
      _ = _ := mul_comm _ _
  have h2 : abs (kernelRect a t K f f) <= R * L := by
    calc
      _ <= R * t.sum (fun i => abs (f i)) :=
        abs_kernelRect_le a t K f f (fun i hi j hj => hK i (ha hi) j (ht hj))
      _ <= R * L := mul_le_mul_of_nonneg_left hT hR
  have h3 : abs (kernelRect a a K f f) <= R ^ 2 := by
    simpa only [pow_two] using
      abs_kernelRect_le a a K f f (fun i hi j hj => hK i (ha hi) j (ha hj))
  have hc := sum_abs_subset_cross_le s a @ha f tau htau hcount
  rw [hpacket]
  apply abs_le.mpr
  constructor
  case left =>
    nlinarith only [(abs_le.mp h1).1, (abs_le.mp h2).1, (abs_le.mp h3).1, hc.1, hc.2]
  case right =>
    nlinarith only [(abs_le.mp h1).2, (abs_le.mp h2).2, (abs_le.mp h3).2, hc.1, hc.2]

theorem abs_sum_sq_sub_restrict_le (s t : Finset I) (ht : forall {i}, Membership.mem t i -> Membership.mem s i)
    (f : I -> Real) (tau : Real) (htau : 0 <= tau)
    (hcount : ((s \ t).card : Real) <= tau ^ 2 * (s.card : Real)) :
    abs ((s.sum f) ^ 2 - (t.sum f) ^ 2) <=
      2 * tau * ((s.card : Real) * s.sum (fun i => (f i) ^ 2)) := by
  let a := s \ t
  let L := s.sum (fun i => abs (f i))
  let R := a.sum (fun i => abs (f i))
  let W := (s.card : Real) * s.sum (fun i => (f i) ^ 2)
  have ha : forall {i}, Membership.mem a i -> Membership.mem s i := by
    intro i hi
    exact (mem_sdiff.mp hi).1
  have hd : Disjoint t a := by
    apply disjoint_left.mpr
    intro i hi hia
    exact (mem_sdiff.mp hia).2 hi
  have hsum : s.sum f = t.sum f + a.sum f := by
    rw [<- union_sdiff_of_subset @ht, sum_union hd]
  have hs : abs (s.sum f) <= L := abs_sum_le_sum_abs _ _
  have hT : abs (t.sum f) <= L := by
    exact le_trans (abs_sum_le_sum_abs _ _)
      (sum_le_sum_of_subset_of_nonneg @ht (fun i _ _ => abs_nonneg _))
  have hdiff : abs (s.sum f - t.sum f) <= R := by
    rw [hsum]
    simpa only [add_sub_cancel_left] using abs_sum_le_sum_abs f a
  have hplus : abs (s.sum f + t.sum f) <= 2 * L := by
    apply abs_le.mpr
    constructor
    case left => linarith only [(abs_le.mp hs).1, (abs_le.mp hT).1]
    case right => linarith only [(abs_le.mp hs).2, (abs_le.mp hT).2]
  have hR : 0 <= R := sum_nonneg (fun i _ => abs_nonneg _)
  have hc := (sum_abs_subset_cross_le s a @ha f tau htau hcount).1
  calc
    _ = abs ((s.sum f - t.sum f) * (s.sum f + t.sum f)) := by
      congr 1
      ring1
    _ = abs (s.sum f - t.sum f) * abs (s.sum f + t.sum f) := abs_mul _ _
    _ <= R * (2 * L) := mul_le_mul hdiff hplus (abs_nonneg _) hR
    _ = 2 * (R * L) := by ring1
    _ <= 2 * (tau * W) := mul_le_mul_of_nonneg_left hc (by linarith)
    _ = _ := by ring1

end Finset
