/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairMoments
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairProduct


/-!
# Uniform energy of coherent quadratic-pair packets

The exact conditional-count moment is multiplied across finite fields.
Its cubic Mertens normalization is positive, differs from one by at most
20/q^2, and has finite natural-cutoff tails between exp(-40/N) and
exp(40/N). All constants are uniform in the nonzero local shifts.
The integer CRT and short-interval recurrence transfer is not asserted.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace FiniteField.QuadraticPairEnergy

def moment (q d : Real) : Real := 1 + (3 * q + d) / (q * (q - d))

def correction (q d : Real) : Real := moment q d * (1 - 1 / q) ^ 3

theorem correction_pos (q d : Real)
    (hq : 16 <= q) (hd1 : 1 <= d) (hd5 : d <= 5) :
    0 < correction q d := by
  have hq0 : 0 < q := by linarith
  have hqd : 0 < q - d := by linarith
  have hm : 0 < moment q d := by
    unfold moment
    have hr := div_pos (show 0 < 3 * q + d by linarith) (mul_pos hq0 hqd)
    linarith
  have hh : 1 - 1 / q = (q - 1) / q := by
    field_simp [ne_of_gt hq0] <;> ring
  unfold correction
  rw [hh]
  exact mul_pos hm (pow_pos (div_pos (by linarith) hq0) 3)

theorem correction_error (q d : Real)
    (hq : 16 <= q) (hd1 : 1 <= d) (hd5 : d <= 5) :
    |correction q d - 1| <= 20 / q ^ 2 := by
  have hq0 : 0 < q := by linarith
  have hqd : 0 < q - d := by linarith
  have hden : 0 < q ^ 4 * (q - d) := mul_pos (pow_pos hq0 4) hqd
  let R : Real :=
    (4 * d - 6) * q ^ 3 + (8 - 6 * d) * q ^ 2 + (4 * d - 3) * q - d
  have hidentity : correction q d - 1 = R / (q ^ 4 * (q - d)) := by
    unfold correction moment R
    generalize hz : q - d = z
    have hz0 : Not (z = 0) := by rw [<- hz]; exact ne_of_gt hqd
    field_simp [ne_of_gt hq0, hz0] <;> rw [<- hz] <;> ring
  have hlow : 0 <= R + 2 * q ^ 2 * (q - d) := by
    have h1 : 0 <= 4 * (d - 1) * q ^ 2 * (q - 2) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith))
        (sq_nonneg q)) (by linarith)
    have h2 : 0 <= (d - 1) * (4 * q - 1) :=
      mul_nonneg (by linarith) (by linarith)
    dsimp [R]
    nlinarith only [h1, h2, hq]
  have hhigh : 0 <= 20 * q ^ 2 * (q - d) - R := by
    have h1 : 0 <= 6 * q ^ 2 * (q - 16) :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg q)) (by linarith)
    have h2 : 0 <= 18 * q * (q - 1) :=
      mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hq0)) (by linarith)
    have h3 : 0 <= 4 * q ^ 3 + 14 * q ^ 2 + 4 * q - 1 := by
      nlinarith only [pow_nonneg (le_of_lt hq0) 3, sq_nonneg q, hq]
    have h4 := mul_nonneg (show 0 <= 5 - d by linarith) h3
    dsimp [R]
    nlinarith only [h1, h2, h4, hq]
  have hn : 0 <= q ^ 2 * (q - d) :=
    mul_nonneg (sq_nonneg q) (le_of_lt hqd)
  have habs : |R| <= 20 * q ^ 2 * (q - d) :=
    abs_le.mpr (And.intro (by linarith only [hlow, hn]) (by linarith only [hhigh]))
  rw [hidentity, abs_div, abs_of_pos hden]
  calc
    _ <= (20 * q ^ 2 * (q - d)) / (q ^ 4 * (q - d)) :=
      div_le_div_of_nonneg_right habs (le_of_lt hden)
    _ = _ := by
      field_simp [ne_of_gt hq0, ne_of_gt hqd] <;> ring


theorem energy_product_bounds
    (N M : Nat) (hN : 16 <= N) (hNM : N <= M)
    (T : Finset Nat) (hT : T <= Finset.Ico (N + 1) (M + 1))
    (d : Nat -> Real)
    (hd : forall n, Membership.mem T n -> 1 <= d n /\ d n <= 5) :
    Real.exp (-(40 / (N : Real))) <=
        T.prod (fun n => correction (n : Real) (d n)) /\
      T.prod (fun n => correction (n : Real) (d n)) <=
        Real.exp (40 / (N : Real)) := by
  have hp (n : Nat) (hn : Membership.mem T n) : 16 <= (n : Real) := by
    have hi := (Finset.mem_Ico.mp (hT hn)).1
    have hh : 16 <= n := le_trans (le_trans hN (Nat.le_succ N)) hi
    exact_mod_cast hh
  have hb (n : Nat) (hn : Membership.mem T n) :
      |correction (n : Real) (d n) - 1| <= 20 / (n : Real) ^ 2 :=
    correction_error (n : Real) (d n) (hp n hn) (hd n hn).1 (hd n hn).2
  have hs (n : Nat) (hn : Membership.mem T n) :
      (20 : Real) / (n : Real) ^ 2 <= 1 / 2 := by
    have hsq : (256 : Real) <= (n : Real) ^ 2 := by
      nlinarith only [hp n hn, sq_nonneg ((n : Real) - 16)]
    calc
      _ <= (20 : Real) / 256 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsq
      _ <= _ := by norm_num
  have hl := QuadraticPairEuler.log_product_tail_bound N M (le_trans (by norm_num) hN) hNM
    T hT (fun n => correction (n : Real) (d n)) 20 (by norm_num) hb hs
  have hl' :
      |Real.log (T.prod (fun n => correction (n : Real) (d n)))| <=
        40 / (N : Real) := by
    convert hl using 1 <;> norm_num
  have hpos : 0 < T.prod (fun n => correction (n : Real) (d n)) :=
    Finset.prod_pos (fun n hn =>
      correction_pos (n : Real) (d n) (hp n hn) (hd n hn).1 (hd n hn).2)
  exact QuadraticPairEuler.product_bounds_of_log_bound _ _ hpos hl'


theorem product_space_square_sum
    {I : Type*} [Fintype I] [DecidableEq I]
    (K : I -> Type*) [forall i, Fintype (K i)]
    (v : (i : I) -> K i -> Real) :
    (Finset.univ.sum fun x : (i : I) -> K i =>
      (Finset.univ.prod fun i : I => v i (x i)) ^ 2) =
      Finset.univ.prod (fun i : I => Finset.univ.sum (fun c : K i => (v i c) ^ 2)) := by
  classical
  simp_rw [<- Finset.prod_pow]
  exact (Fintype.prod_sum (fun i c => (v i c) ^ 2)).symm

theorem product_space_energy
    {I : Type*} [Fintype I] [DecidableEq I]
    (K : I -> Type*) [forall i, Fintype (K i)]
    (v : (i : I) -> K i -> Real) :
    (Finset.univ.prod fun i : I => 1 / (Fintype.card (K i) : Real)) *
      (Finset.univ.sum fun x : (i : I) -> K i =>
        (Finset.univ.prod fun i : I => v i (x i)) ^ 2) =
      Finset.univ.prod (fun i : I =>
        (1 / (Fintype.card (K i) : Real)) *
          (Finset.univ.sum fun c : K i => (v i c) ^ 2)) := by
  rw [product_space_square_sum K v, Finset.prod_mul_distrib]


theorem normalized_packet_energy
    {I : Type*} [Fintype I] [DecidableEq I]
    (K : I -> Type*) [forall i, Field (K i)] [forall i, Fintype (K i)]
    [forall i, DecidableEq (K i)]
    (h : (i : I) -> K i)
    (hodd : forall i, Not (ringChar (K i) = 2))
    (hzero : forall i, Not (h i = 0))
    (hcard : forall i, 16 <= (Fintype.card (K i) : Real)) :
    (Finset.univ.prod fun i : I => 1 / (Fintype.card (K i) : Real)) *
      (Finset.univ.sum fun x : (i : I) -> K i =>
        (Finset.univ.prod fun i : I =>
          QuadraticPairEuler.normalizedPairCount (x i) (h i)) ^ 2) =
      Finset.univ.prod (fun i : I =>
        moment (Fintype.card (K i) : Real) (quadraticPairOffset (h i) : Real)) := by
  rw [product_space_energy K
    (fun i c => QuadraticPairEuler.normalizedPairCount c (h i))]
  apply Finset.prod_congr rfl
  intro i _
  exact normalizedPairCount_second_moment_large (hodd i) (h i) (hzero i) (hcard i)

theorem normalized_packet_compensated
    {I : Type*} [Fintype I] [DecidableEq I]
    (K : I -> Type*) [forall i, Field (K i)] [forall i, Fintype (K i)]
    [forall i, DecidableEq (K i)]
    (h : (i : I) -> K i)
    (hodd : forall i, Not (ringChar (K i) = 2))
    (hzero : forall i, Not (h i = 0))
    (hcard : forall i, 16 <= (Fintype.card (K i) : Real)) :
    ((Finset.univ.prod fun i : I => 1 / (Fintype.card (K i) : Real)) *
      (Finset.univ.sum fun x : (i : I) -> K i =>
        (Finset.univ.prod fun i : I =>
          QuadraticPairEuler.normalizedPairCount (x i) (h i)) ^ 2)) *
      (Finset.univ.prod fun i : I => (1 - 1 / (Fintype.card (K i) : Real)) ^ 3) =
      Finset.univ.prod (fun i : I =>
        correction (Fintype.card (K i) : Real) (quadraticPairOffset (h i) : Real)) := by
  rw [normalized_packet_energy K h hodd hzero hcard, <- Finset.prod_mul_distrib]
  rfl

end FiniteField.QuadraticPairEnergy
