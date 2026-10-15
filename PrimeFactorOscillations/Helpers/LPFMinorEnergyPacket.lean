/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFDivisorAverage
import PrimeFactorOscillations.Helpers.LPFMinorWeightedPacket

/-!
# Joint Type II coefficient-energy estimate

The actual product-window intersection and all diagonal pairs are retained.
Uniform row and column residue estimates bound the paired kernel against the
inner coefficient second moment, instead of a pointwise coefficient maximum.
Supplying an explicit averaged Vaughan coefficient bound and its full dyadic
consumer remains separate; this module asserts no numerical entry threshold.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem lpf_finite_schur_energy_bound (T : Finset Nat)
    (w : Nat -> Real) (F : Nat -> Nat -> Real) (G : Real)
    (hF : forall n, Membership.mem T n -> forall m, Membership.mem T m -> 0 <= F n m)
    (hRow : forall n, Membership.mem T n -> Finset.sum T (F n) <= G)
    (hCol : forall m, Membership.mem T m -> Finset.sum T (fun n => F n m) <= G) :
    Finset.sum T (fun n => Finset.sum T (fun m => w n * w m * F n m)) <=
      G * Finset.sum T (fun n => w n ^ 2) := by
  have hPoint (n : Nat) (hn : Membership.mem T n) (m : Nat) (hm : Membership.mem T m) :
      2 * (w n * w m * F n m) <= (w n ^ 2 + w m ^ 2) * F n m := by
    have hAM : 2 * (w n * w m) <= w n ^ 2 + w m ^ 2 := by
      nlinarith only [sq_nonneg (w n - w m)]
    have h := mul_le_mul_of_nonneg_right hAM (hF n hn m hm)
    nlinarith only [h]
  have hFirst : Finset.sum T (fun n => Finset.sum T (fun m => w n ^ 2 * F n m)) =
      Finset.sum T (fun n => w n ^ 2 * Finset.sum T (F n)) := by
    simp_rw [Finset.mul_sum]
  have hSecond : Finset.sum T (fun n => Finset.sum T (fun m => w m ^ 2 * F n m)) =
      Finset.sum T (fun m => w m ^ 2 * Finset.sum T (fun n => F n m)) := by
    rw [Finset.sum_comm]
    simp_rw [Finset.mul_sum]
  have hDouble :
      2 * Finset.sum T (fun n => Finset.sum T (fun m => w n * w m * F n m)) <=
        2 * (G * Finset.sum T (fun n => w n ^ 2)) := by
    calc
      _ = Finset.sum T (fun n => Finset.sum T (fun m => 2 * (w n * w m * F n m))) := by
        simp_rw [Finset.mul_sum]
      _ <= Finset.sum T (fun n => Finset.sum T (fun m => (w n ^ 2 + w m ^ 2) * F n m)) := by
        apply Finset.sum_le_sum
        intro n hn
        apply Finset.sum_le_sum
        intro m hm
        exact hPoint n hn m hm
      _ = Finset.sum T (fun n => Finset.sum T (fun m => w n ^ 2 * F n m)) +
          Finset.sum T (fun n => Finset.sum T (fun m => w m ^ 2 * F n m)) := by
        simp_rw [add_mul, Finset.sum_add_distrib]
      _ = Finset.sum T (fun n => w n ^ 2 * Finset.sum T (F n)) +
          Finset.sum T (fun m => w m ^ 2 * Finset.sum T (fun n => F n m)) := by
        rw [hFirst, hSecond]
      _ <= Finset.sum T (fun n => w n ^ 2 * G) +
          Finset.sum T (fun m => w m ^ 2 * G) := by
        apply add_le_add
        . apply Finset.sum_le_sum
          intro n hn
          exact mul_le_mul_of_nonneg_left (hRow n hn) (sq_nonneg _)
        . apply Finset.sum_le_sum
          intro m hm
          exact mul_le_mul_of_nonneg_left (hCol m hm) (sq_nonneg _)
      _ = _ := by simp_rw [<- Finset.sum_mul]; ring
  linarith only [hDouble]

theorem lpf_unit_difference_allowance_row_bound {q : Nat} [NeZero q]
    (a : Units (ZMod q)) (c : ZMod q) (C D : Nat) (L : Real) (hL : 0 <= L) :
    Finset.sum (Finset.Ioc C D) (fun n =>
      lpfMinorResidueAllowance q L (((a : ZMod q) * (c - (n : ZMod q))).val)) <=
        (((D - C) / q + 1 : Nat) : Real) *
          (L + 2 * (q : Real) * (1 + Real.log (q : Real))) := by
  let F : ZMod q -> Real := fun r => lpfMinorResidueAllowance q L r.val
  have hF : forall r, 0 <= F r := fun r => lpfMinorResidueAllowance_nonneg q r.val L hL
  have hAll : Finset.sum Finset.univ F <= L + 2 * (q : Real) * (1 + Real.log (q : Real)) := by
    rw [<- lpf_natural_residue_sum F]
    calc
      _ = Finset.sum (Finset.range q) (lpfMinorResidueAllowance q L) := by
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [F]
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hj)]
      _ <= _ := lpfMinorResidueAllowance_period_bound q (Nat.pos_of_ne_zero (NeZero.ne q)) L
  exact (lpf_unit_difference_interval_sum_bound a c C D F hF).trans
    (mul_le_mul_of_nonneg_left hAll (by positivity))

theorem lpf_typeII_energy_packet_bound {N q : Nat} [NeZero N] [NeZero q]
    (k a : Int) (u : Units (ZMod q)) (hU : (a : ZMod q) = (u : ZMod q))
    (beta : Real) (A B C D s L : Nat) (outer inner : Nat -> Complex) (A2 B2 : Real)
    (hAlpha : (k : Real) / (N : Real) = (a : Real) / (q : Real) + beta)
    (hBeta : abs beta * ((D - C : Nat) : Real) <= 1 / (4 * (q : Real)))
    (hA : Finset.sum (Finset.Ioc A B) (fun m => norm (outer m) ^ 2) <= A2)
    (hB : Finset.sum (Finset.Ioc C D) (fun n => norm (inner n) ^ 2) <= B2) :
    norm (Finset.sum (Finset.Ioc A B) (fun m => outer m *
      Finset.sum (Finset.Ioc C D) (fun n => inner n * lpfBilinearFrequencyWindowPhase N s L k m n))) ^ 2 <=
        A2 * B2 * (((D - C) / q + 1 : Nat) : Real) *
          (((B - A : Nat) : Real) + 2 * (q : Real) * (1 + Real.log (q : Real))) := by
  let S := Finset.Ioc A B
  let T := Finset.Ioc C D
  let K : Nat -> Nat -> Complex := fun n1 n2 =>
    Finset.sum (Finset.Ioc (max (max A (s / n1)) (s / n2))
      (min (min B ((s + L) / n1)) ((s + L) / n2))) (fun m =>
        ZMod.stdAddChar (N := N)
          ((k : ZMod N) * (m : ZMod N) * ((n1 : ZMod N) - (n2 : ZMod N))))
  let F : Nat -> Nat -> Real := fun n1 n2 => lpfMinorResidueAllowance q ((B - A : Nat) : Real)
    (((u : ZMod q) * ((n1 : ZMod q) - (n2 : ZMod q))).val)
  let G : Real := (((D - C) / q + 1 : Nat) : Real) *
    (((B - A : Nat) : Real) + 2 * (q : Real) * (1 + Real.log (q : Real)))
  let pair : Nat -> Nat -> Complex := fun n1 n2 => (inner n1 * star (inner n2)) * K n1 n2
  let E : Real := (Finset.sum T (fun n1 => Finset.sum T (pair n1))).re
  have hT : forall n, Membership.mem T n -> 0 < n := by
    intro n hn
    have h := Finset.mem_Ioc.mp hn
    omega
  have hCauchy := lpf_bilinear_frequency_cauchy_packet (N := N) k A B s L T hT outer inner
  change norm (Finset.sum S (fun m => outer m *
    Finset.sum T (fun n => inner n * lpfBilinearFrequencyWindowPhase N s L k m n))) ^ 2 <=
      Finset.sum S (fun m => norm (outer m) ^ 2) * E at hCauchy
  have hPoint : forall n1, Membership.mem T n1 -> forall n2, Membership.mem T n2 ->
      norm (K n1 n2) <= F n1 n2 := by
    intro n1 hn1 n2 hn2
    exact lpf_bilinear_window_minor_point_bound k a u hU beta A B C D s L n1 n2 hn1 hn2 hAlpha hBeta
  have hTerm : forall n1, Membership.mem T n1 -> forall n2, Membership.mem T n2 ->
      norm (pair n1 n2) <= norm (inner n1) * norm (inner n2) * F n1 n2 := by
    intro n1 hn1 n2 hn2
    change norm ((inner n1 * star (inner n2)) * K n1 n2) <=
      norm (inner n1) * norm (inner n2) * F n1 n2
    rw [norm_mul, norm_mul, norm_star]
    exact mul_le_mul_of_nonneg_left (hPoint n1 hn1 n2 hn2) (by positivity)
  have hEnergy : E <= Finset.sum T (fun n1 => Finset.sum T (fun n2 =>
      norm (inner n1) * norm (inner n2) * F n1 n2)) := by
    calc
      E <= norm (Finset.sum T (fun n1 => Finset.sum T (pair n1))) := Complex.re_le_norm _
      _ <= Finset.sum T (fun n1 => norm (Finset.sum T (pair n1))) := norm_sum_le T _
      _ <= Finset.sum T (fun n1 => Finset.sum T (fun n2 => norm (pair n1 n2))) := by
        apply Finset.sum_le_sum
        intro n1 hn1
        exact norm_sum_le T _
      _ <= _ := by
        apply Finset.sum_le_sum
        intro n1 hn1
        apply Finset.sum_le_sum
        intro n2 hn2
        exact hTerm n1 hn1 n2 hn2
  have hF : forall n1, Membership.mem T n1 -> forall n2, Membership.mem T n2 -> 0 <= F n1 n2 := by
    intro n1 hn1 n2 hn2
    exact lpfMinorResidueAllowance_nonneg q _ _ (Nat.cast_nonneg _)
  have hRow : forall n1, Membership.mem T n1 -> Finset.sum T (F n1) <= G := by
    intro n1 hn1
    exact lpf_unit_difference_allowance_row_bound u (n1 : ZMod q) C D
      ((B - A : Nat) : Real) (Nat.cast_nonneg _)
  have hCol : forall n2, Membership.mem T n2 -> Finset.sum T (fun n1 => F n1 n2) <= G := by
    intro n2 hn2
    have h := lpf_unit_difference_allowance_row_bound (-u) (n2 : ZMod q) C D
      ((B - A : Nat) : Real) (Nat.cast_nonneg _)
    change Finset.sum T (fun n1 => lpfMinorResidueAllowance q ((B - A : Nat) : Real)
      ((-(u : ZMod q)) * ((n2 : ZMod q) - (n1 : ZMod q))).val) <= G at h
    have hEq (n1 : Nat) : (-(u : ZMod q)) * ((n2 : ZMod q) - (n1 : ZMod q)) =
        (u : ZMod q) * ((n1 : ZMod q) - (n2 : ZMod q)) := by ring
    simpa only [hEq] using h
  have hSchur := lpf_finite_schur_energy_bound T (fun n => norm (inner n)) F G hF hRow hCol
  have hLog : 0 <= Real.log (q : Real) :=
    Real.log_nonneg (by exact_mod_cast (show 1 <= q by exact Nat.succ_le_of_lt (NeZero.pos q)))
  have hG : 0 <= G := by dsimp [G]; positivity
  have hB2 : 0 <= B2 :=
    (Finset.sum_nonneg (fun n hn => sq_nonneg (norm (inner n)))).trans hB
  have hE : E <= G * B2 := (hEnergy.trans hSchur).trans (mul_le_mul_of_nonneg_left hB hG)
  have hOuterNonneg : 0 <= Finset.sum S (fun m => norm (outer m) ^ 2) := by positivity
  have hFinal := (hCauchy.trans (mul_le_mul_of_nonneg_left hE hOuterNonneg)).trans
    (mul_le_mul_of_nonneg_right hA (mul_nonneg hG hB2))
  calc
    _ <= A2 * (G * B2) := hFinal
    _ = _ := by dsimp [G]; ring

theorem lpf_typeII_actual_energy_packet_bound {N q : Nat} [NeZero N] [NeZero q]
    (k a : Int) (u : Units (ZMod q)) (hU : (a : ZMod q) = (u : ZMod q))
    (beta : Real) (U V A B C D s L H : Nat)
    (hB : B <= H) (hD : D <= H) (hH : 1 <= H)
    (hAlpha : (k : Real) / (N : Real) = (a : Real) / (q : Real) + beta)
    (hBeta : abs beta * ((D - C : Nat) : Real) <= 1 / (4 * (q : Real))) :
    norm (Finset.sum (Finset.Ioc A B) (fun m =>
      ((ArithmeticFunction.vonMangoldt m - lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U m : Real) : Complex) *
        Finset.sum (Finset.Ioc C D) (fun n => ((lpfVaughanB V n : Real) : Complex) *
          lpfBilinearFrequencyWindowPhase N s L k m n))) ^ 2 <=
      ((B - A : Nat) : Real) * (D : Real) * Real.log (H : Real) ^ 2 *
        (1 + Real.log (H : Real)) ^ 3 * (((D - C) / q + 1 : Nat) : Real) *
          (((B - A : Nat) : Real) + 2 * (q : Real) * (1 + Real.log (q : Real))) := by
  have hOuter := lpfVaughanHighLambda_square_sum_le U A B H hB hH
  have hInner := lpfVaughanB_square_sum_height_bound V C D H hD hH
  have h := lpf_typeII_energy_packet_bound (N := N) (q := q) k a u hU beta A B C D s L
    (fun m => ((ArithmeticFunction.vonMangoldt m - lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U m : Real) : Complex))
    (fun n => ((lpfVaughanB V n : Real) : Complex))
    (((B - A : Nat) : Real) * Real.log (H : Real) ^ 2)
    ((D : Real) * (1 + Real.log (H : Real)) ^ 3) hAlpha hBeta hOuter hInner
  convert h using 1 <;> ring

end PrimeFactorOscillations.LPF
