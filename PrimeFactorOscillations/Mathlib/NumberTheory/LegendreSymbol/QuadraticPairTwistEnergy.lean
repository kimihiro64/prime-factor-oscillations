/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairTwistAverage


/-!
# Near-minimal energy of positive quadratic-twist packets

The trace-free actual-count law has finite product-space mean one and
energy within 1 + 5/q^2 of every mean-one competitor with the same two
forbidden constants. Its ratio to the flat support energy is between
one and 1 + 5/q^2; finite natural-cutoff product tails are at most
exp(10/N), uniformly in the fields and nonzero shifts.
No Hasse, RH or integer short-window estimate is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace FiniteField

theorem two_omitted_points_energy_lower
    {I : Type*} [Fintype I] [DecidableEq I]
    (a b : I) (hab : Not (a = b)) (w : I -> Real)
    (hwa : w a = 0) (hwb : w b = 0)
    (hq : 3 <= (Fintype.card I : Real))
    (hmean : (1 / (Fintype.card I : Real)) * (Finset.univ.sum w) = 1) :
    (Fintype.card I : Real) / ((Fintype.card I : Real) - 2) <=
      (1 / (Fintype.card I : Real)) *
        (Finset.univ.sum fun c : I => (w c) ^ 2) := by
  classical
  let q : Real := Fintype.card I
  let k : Real := q / (q - 2)
  let r : I -> Real := fun c =>
    if c = a then 0 else if c = b then 0 else (w c - k) ^ 2
  have hq0 : 0 < q := by dsimp [q]; linarith only [hq]
  have hq2 : 0 < q - 2 := by dsimp [q]; linarith only [hq]
  have hsum : Finset.univ.sum w = q := by
    calc
      _ = q * ((1 / q) * Finset.univ.sum w) := by
        field_simp [ne_of_gt hq0]
      _ = q := by rw [hmean, mul_one]
  have hp (c : I) :
      r c = (w c) ^ 2 - (2 * k) * w c + k ^ 2 -
        (if c = a then k ^ 2 else 0) - (if c = b then k ^ 2 else 0) := by
    by_cases ha : c = a
    . subst c
      simp only [r, ite_true, if_neg hab, hwa]
      ring
    . by_cases hb : c = b
      . subst c
        simp only [r, if_neg (Ne.symm hab), ite_true, hwb]
        ring
      . simp only [r, if_neg ha, if_neg hb]
        ring
  have hs :
      Finset.univ.sum r =
        (Finset.univ.sum fun c : I => (w c) ^ 2) -
          (2 * k) * (Finset.univ.sum w) + (q - 2) * k ^ 2 := by
    simp_rw [hp]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, <- Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp
    ring
  have hr : 0 <= Finset.univ.sum r := by
    apply Finset.sum_nonneg
    intro c _
    change 0 <= (if c = a then (0 : Real) else if c = b then 0 else (w c - k) ^ 2)
    split_ifs
    . exact le_rfl
    . exact le_rfl
    . exact sq_nonneg _
  have he :
      (1 / q) * (Finset.univ.sum fun c : I => (w c) ^ 2) - q / (q - 2) =
        (1 / q) * Finset.univ.sum r := by
    rw [hs, hsum]
    change (1 / q) * (Finset.univ.sum fun c : I => (w c) ^ 2) - q / (q - 2) =
      (1 / q) * ((Finset.univ.sum fun c : I => (w c) ^ 2) -
        (2 * (q / (q - 2))) * q + (q - 2) * (q / (q - 2)) ^ 2)
    generalize hz : q - 2 = z
    have hz0 : Not (z = 0) := by rw [<- hz]; exact ne_of_gt hq2
    field_simp [ne_of_gt hq0, hz0] <;> rw [<- hz] <;> ring
  have hn := mul_nonneg (one_div_nonneg.mpr (le_of_lt hq0)) hr
  change q / (q - 2) <= _
  linarith only [he, hn]


namespace QuadraticPairTwistEnergy

def moment (q epsilon : Real) : Real :=
  1 + 2 / (q - 3) - 2 * (1 + epsilon) / (q * (q - 3) ^ 2)

def flatCorrection (q epsilon : Real) : Real := moment q epsilon * (1 - 2 / q)

theorem flatCorrection_bounds (q epsilon : Real)
    (hq : 5 <= q) (he0 : -1 <= epsilon) (he1 : epsilon <= 1) :
    1 <= flatCorrection q epsilon /\ flatCorrection q epsilon <= 1 + 5 / q ^ 2 := by
  have hq0 : 0 < q := by linarith only [hq]
  have hq3 : 0 < q - 3 := by linarith only [hq]
  have hden : 0 < q ^ 2 * (q - 3) ^ 2 := mul_pos (pow_pos hq0 2) (pow_pos hq3 2)
  let R : Real := 2 * q * (q - 3) - 2 * (1 + epsilon) * (q - 2)
  have hid : flatCorrection q epsilon - 1 = R / (q ^ 2 * (q - 3) ^ 2) := by
    unfold flatCorrection moment R
    generalize hz : q - 3 = z
    have hz0 : Not (z = 0) := by rw [<- hz]; exact ne_of_gt hq3
    field_simp [ne_of_gt hq0, hz0] <;> rw [<- hz] <;> ring
  have hR0 : 0 <= R := by
    have h1 : 0 <= 2 * (q - 1) * (q - 4) :=
      mul_nonneg (mul_nonneg (by norm_num) (by linarith only [hq])) (by linarith only [hq])
    have h2 : 0 <= 2 * (1 - epsilon) * (q - 2) :=
      mul_nonneg (mul_nonneg (by norm_num) (by linarith only [he1]))
        (by linarith only [hq])
    dsimp [R]
    nlinarith only [h1, h2]
  have hRup : R <= 2 * q * (q - 3) := by
    have hp := mul_nonneg (show 0 <= 1 + epsilon by linarith only [he0])
      (show 0 <= q - 2 by linarith only [hq])
    dsimp [R]
    nlinarith only [hp]
  have hlo : 0 <= flatCorrection q epsilon - 1 := by
    rw [hid]
    exact div_nonneg hR0 (le_of_lt hden)
  have hratio : (2 : Real) / (q * (q - 3)) <= 5 / q ^ 2 := by
    have hp : 0 <= q ^ 2 * (q - 3) :=
      mul_nonneg (sq_nonneg q) (le_of_lt hq3)
    calc
      _ = (2 * q) / (q ^ 2 * (q - 3)) := by
        field_simp [ne_of_gt hq0, ne_of_gt hq3] <;> ring
      _ <= (5 * (q - 3)) / (q ^ 2 * (q - 3)) :=
        div_le_div_of_nonneg_right (by linarith only [hq]) hp
      _ = _ := by field_simp [ne_of_gt hq0, ne_of_gt hq3] <;> ring
  have hhi : flatCorrection q epsilon - 1 <= 5 / q ^ 2 := by
    rw [hid]
    calc
      _ <= (2 * q * (q - 3)) / (q ^ 2 * (q - 3) ^ 2) :=
        div_le_div_of_nonneg_right hRup (le_of_lt hden)
      _ = 2 / (q * (q - 3)) := by
        field_simp [ne_of_gt hq0, ne_of_gt hq3] <;> ring
      _ <= _ := hratio
  exact And.intro (by linarith only [hlo]) (by linarith only [hhi])


theorem flatCorrection_product_bounds
    (N M : Nat) (hN : 4 <= N) (hNM : N <= M)
    (T : Finset Nat) (hT : T <= Finset.Ico (N + 1) (M + 1))
    (epsilon : Nat -> Real)
    (he : forall n, Membership.mem T n -> -1 <= epsilon n /\ epsilon n <= 1) :
    1 <= T.prod (fun n => flatCorrection (n : Real) (epsilon n)) /\
      T.prod (fun n => flatCorrection (n : Real) (epsilon n)) <=
        Real.exp (10 / (N : Real)) := by
  have hp (n : Nat) (hn : Membership.mem T n) : 5 <= (n : Real) := by
    have hi := (Finset.mem_Ico.mp (hT hn)).1
    have hh : 5 <= n := le_trans (Nat.succ_le_succ hN) hi
    exact_mod_cast hh
  have hb (n : Nat) (hn : Membership.mem T n) :
      |flatCorrection (n : Real) (epsilon n) - 1| <= 5 / (n : Real) ^ 2 := by
    have h := flatCorrection_bounds (n : Real) (epsilon n)
      (hp n hn) (he n hn).1 (he n hn).2
    rw [abs_of_nonneg (sub_nonneg.mpr h.1)]
    linarith only [h.2]
  have hs (n : Nat) (hn : Membership.mem T n) :
      (5 : Real) / (n : Real) ^ 2 <= 1 / 2 := by
    have hsq : (25 : Real) <= (n : Real) ^ 2 := by
      nlinarith only [hp n hn, sq_nonneg ((n : Real) - 5)]
    calc
      _ <= (5 : Real) / 25 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsq
      _ <= _ := by norm_num
  have hl := QuadraticPairEuler.log_product_tail_bound N M
    (le_trans (by norm_num) hN) hNM T hT
    (fun n => flatCorrection (n : Real) (epsilon n)) 5 (by norm_num) hb hs
  have hlow_aux : forall S : Finset Nat,
      (forall n, Membership.mem S n -> 1 <= flatCorrection (n : Real) (epsilon n)) ->
        1 <= S.prod (fun n => flatCorrection (n : Real) (epsilon n)) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      simp
    | @insert n S hn ih =>
      intro hc
      rw [Finset.prod_insert hn]
      have hn1 := hc n (Finset.mem_insert_self n S)
      have hs1 := ih (fun m hm => hc m (Finset.mem_insert_of_mem hm))
      have hm := mul_nonneg (sub_nonneg.mpr hn1) (sub_nonneg.mpr hs1)
      nlinarith only [hn1, hs1, hm]
  have hlow : 1 <= T.prod (fun n => flatCorrection (n : Real) (epsilon n)) :=
    hlow_aux T (fun n hn => (flatCorrection_bounds (n : Real) (epsilon n)
      (hp n hn) (he n hn).1 (he n hn).2).1)
  have hpos : 0 < T.prod (fun n => flatCorrection (n : Real) (epsilon n)) :=
    lt_of_lt_of_le (by norm_num) hlow
  have hl' :
      |Real.log (T.prod (fun n => flatCorrection (n : Real) (epsilon n)))| <=
        10 / (N : Real) := by
    convert hl using 1 <;> norm_num
  exact And.intro hlow (QuadraticPairEuler.product_bounds_of_log_bound _ _ hpos hl').2


theorem traceFree_packet_mean_one
    {I : Type*} [Fintype I] [DecidableEq I]
    (K : I -> Type*) [forall i, Field (K i)] [forall i, Fintype (K i)]
    [forall i, DecidableEq (K i)]
    (h : (i : I) -> K i)
    (hodd : forall i, Not (ringChar (K i) = 2))
    (hzero : forall i, Not (h i = 0))
    (hcard : forall i, 5 <= (Fintype.card (K i) : Real)) :
    (Finset.univ.prod fun i : I => 1 / (Fintype.card (K i) : Real)) *
      (Finset.univ.sum fun x : (i : I) -> K i =>
        Finset.univ.prod (fun i : I => traceFreePairWeight (x i) (h i))) = 1 := by
  rw [<- Fintype.prod_sum (fun i c => traceFreePairWeight c (h i))]
  rw [<- Finset.prod_mul_distrib]
  have hp (i : I) :
      (1 / (Fintype.card (K i) : Real)) *
        (Finset.univ.sum fun c : K i => traceFreePairWeight c (h i)) = 1 :=
    traceFreePairWeight_mean_one (hodd i) (h i) (hzero i) (hcard i)
  simp_rw [hp]
  simp

theorem traceFree_packet_energy
    {I : Type*} [Fintype I] [DecidableEq I]
    (K : I -> Type*) [forall i, Field (K i)] [forall i, Fintype (K i)]
    [forall i, DecidableEq (K i)]
    (h : (i : I) -> K i)
    (hodd : forall i, Not (ringChar (K i) = 2))
    (hzero : forall i, Not (h i = 0))
    (hcard : forall i, 5 <= (Fintype.card (K i) : Real)) :
    (Finset.univ.prod fun i : I => 1 / (Fintype.card (K i) : Real)) *
      (Finset.univ.sum fun x : (i : I) -> K i =>
        (Finset.univ.prod fun i : I => traceFreePairWeight (x i) (h i)) ^ 2) =
      Finset.univ.prod (fun i : I =>
        moment (Fintype.card (K i) : Real) ((quadraticChar (K i)) (-1) : Real)) := by
  rw [QuadraticPairEnergy.product_space_energy K
    (fun i c => traceFreePairWeight c (h i))]
  apply Finset.prod_congr rfl
  intro i _
  exact traceFreePairWeight_second_moment (hodd i) (h i) (hzero i) (hcard i)

theorem traceFree_packet_flat_compensated
    {I : Type*} [Fintype I] [DecidableEq I]
    (K : I -> Type*) [forall i, Field (K i)] [forall i, Fintype (K i)]
    [forall i, DecidableEq (K i)]
    (h : (i : I) -> K i)
    (hodd : forall i, Not (ringChar (K i) = 2))
    (hzero : forall i, Not (h i = 0))
    (hcard : forall i, 5 <= (Fintype.card (K i) : Real)) :
    ((Finset.univ.prod fun i : I => 1 / (Fintype.card (K i) : Real)) *
      (Finset.univ.sum fun x : (i : I) -> K i =>
        (Finset.univ.prod fun i : I => traceFreePairWeight (x i) (h i)) ^ 2)) *
      (Finset.univ.prod fun i : I => 1 - 2 / (Fintype.card (K i) : Real)) =
      Finset.univ.prod (fun i : I =>
        flatCorrection (Fintype.card (K i) : Real) ((quadraticChar (K i)) (-1) : Real)) := by
  rw [traceFree_packet_energy K h hodd hzero hcard, <- Finset.prod_mul_distrib]
  rfl

theorem traceFreePairWeight_near_minimal
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : Not (ringChar F = 2)) (h : F) (hh : Not (h = 0))
    (hq : 5 <= (Fintype.card F : Real))
    (w : F -> Real) (hw0 : w 0 = 0) (hwn : w (-h) = 0)
    (hwmean : (1 / (Fintype.card F : Real)) * (Finset.univ.sum w) = 1) :
    (1 / (Fintype.card F : Real)) *
      (Finset.univ.sum fun c : F => (traceFreePairWeight c h) ^ 2) <=
      (1 + 5 / (Fintype.card F : Real) ^ 2) *
        ((1 / (Fintype.card F : Real)) * (Finset.univ.sum fun c : F => (w c) ^ 2)) := by
  let q : Real := Fintype.card F
  let epsilon : Real := (quadraticChar F) (-1)
  let Enew : Real := (1 / q) * (Finset.univ.sum fun c : F => (traceFreePairWeight c h) ^ 2)
  let Eold : Real := (1 / q) * (Finset.univ.sum fun c : F => (w c) ^ 2)
  have hq0 : 0 < q := by dsimp [q]; linarith only [hq]
  have hq2 : 0 < q - 2 := by dsimp [q]; linarith only [hq]
  have he : -1 <= epsilon /\ epsilon <= 1 := by
    change -1 <= ((quadraticChar F) (-1) : Real) /\
      ((quadraticChar F) (-1) : Real) <= 1
    rcases QuadraticPairEuler.quadraticChar_real_signs (-1 : F)
      (neg_ne_zero.mpr one_ne_zero) with he | he <;>
      rw [he] <;> constructor <;> norm_num
  have hEv : Enew = moment q epsilon :=
    traceFreePairWeight_second_moment hF h hh hq
  have hmin : q / (q - 2) <= Eold :=
    two_omitted_points_energy_lower (0 : F) (-h)
      (Ne.symm (neg_ne_zero.mpr hh)) w hw0 hwn (by linarith only [hq]) hwmean
  have hC : Enew * (1 - 2 / q) <= 1 + 5 / q ^ 2 := by
    rw [hEv]
    exact (flatCorrection_bounds q epsilon hq he.1 he.2).2
  have hk : 0 <= q / (q - 2) := div_nonneg (le_of_lt hq0) (le_of_lt hq2)
  have hcancel : (1 - 2 / q) * (q / (q - 2)) = 1 := by
    generalize hz : q - 2 = z
    have hz0 : Not (z = 0) := by rw [<- hz]; exact ne_of_gt hq2
    field_simp [ne_of_gt hq0, hz0] <;> rw [<- hz] <;> ring
  have hm := mul_le_mul_of_nonneg_right hC hk
  have hupper : Enew <= (1 + 5 / q ^ 2) * (q / (q - 2)) := by
    simpa only [mul_assoc, hcancel, mul_one] using hm
  have hB : 0 <= 1 + 5 / q ^ 2 := by
    have hp : (0 : Real) <= 5 / q ^ 2 := div_nonneg (by norm_num) (sq_nonneg q)
    linarith only [hp]
  exact hupper.trans (mul_le_mul_of_nonneg_left hmin hB)


end QuadraticPairTwistEnergy

theorem two_omitted_points_floor_attained
    {I : Type*} [Fintype I] [DecidableEq I]
    (a b : I) (hab : Not (a = b)) (hq : 3 <= (Fintype.card I : Real)) :
    let q : Real := Fintype.card I
    let w : I -> Real := fun c =>
      if c = a then 0 else if c = b then 0 else q / (q - 2)
    ((1 / q) * (Finset.univ.sum w) = 1) /\
      ((1 / q) * (Finset.univ.sum fun c : I => (w c) ^ 2) = q / (q - 2)) := by
  classical
  let q : Real := Fintype.card I
  let k : Real := q / (q - 2)
  let w : I -> Real := fun c => if c = a then 0 else if c = b then 0 else k
  change ((1 / q) * (Finset.univ.sum w) = 1) /\
    ((1 / q) * (Finset.univ.sum fun c : I => (w c) ^ 2) = q / (q - 2))
  have hq0 : 0 < q := by dsimp [q]; linarith only [hq]
  have hq2 : 0 < q - 2 := by dsimp [q]; linarith only [hq]
  have hp (c : I) :
      w c = k - (if c = a then k else 0) - (if c = b then k else 0) := by
    by_cases ha : c = a
    . subst c
      simp only [w, ite_true, if_neg hab]
      ring
    . by_cases hb : c = b
      . subst c
        simp only [w, if_neg (Ne.symm hab), ite_true]
        ring
      . simp only [w, if_neg ha, if_neg hb]
        ring
  have hp2 (c : I) :
      (w c) ^ 2 = k ^ 2 -
        (if c = a then k ^ 2 else 0) - (if c = b then k ^ 2 else 0) := by
    by_cases ha : c = a
    . subst c
      simp only [w, ite_true, if_neg hab]
      ring
    . by_cases hb : c = b
      . subst c
        simp only [w, if_neg (Ne.symm hab), ite_true]
        ring
      . simp only [w, if_neg ha, if_neg hb]
        ring
  have hs : Finset.univ.sum w = (q - 2) * k := by
    simp_rw [hp]
    simp only [Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    simp
    ring
  have hs2 : (Finset.univ.sum fun c : I => (w c) ^ 2) = (q - 2) * k ^ 2 := by
    simp_rw [hp2]
    simp only [Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    simp
    ring
  constructor
  . rw [hs]
    change (1 / q) * ((q - 2) * (q / (q - 2))) = 1
    field_simp [ne_of_gt hq0, ne_of_gt hq2]
  . rw [hs2]
    change (1 / q) * ((q - 2) * (q / (q - 2)) ^ 2) = q / (q - 2)
    generalize hz : q - 2 = z
    have hz0 : Not (z = 0) := by rw [<- hz]; exact ne_of_gt hq2
    field_simp [ne_of_gt hq0, hz0] <;> ring

end FiniteField
