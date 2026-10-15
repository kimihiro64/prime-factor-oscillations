/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFIntervalGeometric

/-!
# Geometric cancellation on the paired minor-arc product windows

A rational root may be perturbed by at most 1/(4*q); its nonzero
residue-distance bound still gives geometric cancellation q/k.
Positive and negative residues are retained. The exact intersection
of two product windows is one interval, without extending its support.
These are ingredients of the coupled Type II bound, which remains open.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem lpf_unit_phase_perturbation (r : Complex) (hr : norm r = 1) (x : Real) :
    norm (r * Complex.exp (Complex.I * (x : Complex)) - r) <= abs x := by
  have hFactor : r * Complex.exp (Complex.I * (x : Complex)) - r =
      r * (Complex.exp (Complex.I * (x : Complex)) - 1) := by ring
  rw [hFactor, norm_mul, hr, one_mul]
  simpa only [Real.norm_eq_abs] using Real.norm_exp_I_mul_ofReal_sub_one_le (x := x)

theorem lpf_perturbed_phase_distance (q k : Nat) (hq : 0 < q) (hk : 1 <= k)
    (r : Complex) (hr : norm r = 1)
    (hBase : 4 * (k : Real) / (q : Real) <= norm (1 - r))
    (beta : Real) (hBeta : abs beta <= 1 / (4 * (q : Real))) :
    2 * (k : Real) / (q : Real) <=
      norm (1 - r * Complex.exp (Complex.I * ((2 * Real.pi * beta : Real) : Complex))) := by
  have hqR : (0 : Real) < (q : Real) := Nat.cast_pos.mpr hq
  have hkR : (1 : Real) <= (k : Real) := by exact_mod_cast hk
  let z := r * Complex.exp (Complex.I * ((2 * Real.pi * beta : Real) : Complex))
  have hPerturb := lpf_unit_phase_perturbation r hr (2 * Real.pi * beta)
  have hAbs : abs (2 * Real.pi * beta) = 2 * Real.pi * abs beta := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 <= 2 * Real.pi)]
  rw [hAbs] at hPerturb
  have hError : norm (z - r) <= 2 / (q : Real) := by
    apply hPerturb.trans
    calc
      2 * Real.pi * abs beta <= 2 * Real.pi * (1 / (4 * (q : Real))) :=
        mul_le_mul_of_nonneg_left hBeta (by positivity)
      _ <= 2 * 4 * (1 / (4 * (q : Real))) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.pi_lt_four]) (by positivity)
      _ = _ := by field_simp
  have hTriangle : norm (1 - r) <= norm (1 - z) + norm (z - r) := by
    have hEq : (1 : Complex) - r = (1 - z) + (z - r) := by ring
    rw [hEq]
    exact norm_add_le _ _
  have hScale : 2 / (q : Real) <= 2 * (k : Real) / (q : Real) := by
    apply div_le_div_of_nonneg_right _ hqR.le
    linarith
  change 2 * (k : Real) / (q : Real) <= norm (1 - z)
  have hFour : 4 * (k : Real) / (q : Real) =
      2 * (2 * (k : Real) / (q : Real)) := by ring
  rw [hFour] at hBase
  linarith

theorem lpf_perturbed_geometric_sum_bound (q k L : Nat) (hq : 0 < q) (hk : 1 <= k)
    (r : Complex) (hr : norm r = 1)
    (hBase : 4 * (k : Real) / (q : Real) <= norm (1 - r))
    (beta : Real) (hBeta : abs beta <= 1 / (4 * (q : Real))) :
    norm (Finset.sum (Finset.range L) (fun j =>
      (r * Complex.exp (Complex.I * ((2 * Real.pi * beta : Real) : Complex))) ^ j)) <=
        (q : Real) / (k : Real) := by
  let z := r * Complex.exp (Complex.I * ((2 * Real.pi * beta : Real) : Complex))
  have hz : norm z = 1 := by
    dsimp [z]
    rw [norm_mul, hr, one_mul, Complex.norm_exp]
    simp
  have hDistance := lpf_perturbed_phase_distance q k hq hk r hr hBase beta hBeta
  have hScaled := lpf_unit_geometric_sum_scaled_bound z hz L
  have hPair := (mul_le_mul_of_nonneg_right hDistance
    (norm_nonneg (Finset.sum (Finset.range L) (fun j => z ^ j)))).trans hScaled
  have hqR : (0 : Real) < (q : Real) := Nat.cast_pos.mpr hq
  have hkR : (0 : Real) < (k : Real) := Nat.cast_pos.mpr (by omega : 0 < k)
  have hMul := mul_le_mul_of_nonneg_right hPair hqR.le
  have hCancel : (2 * (k : Real) / (q : Real)) *
      norm (Finset.sum (Finset.range L) (fun j => z ^ j)) * (q : Real) =
        2 * (k : Real) * norm (Finset.sum (Finset.range L) (fun j => z ^ j)) := by
    field_simp
  rw [hCancel] at hMul
  have hBound : norm (Finset.sum (Finset.range L) (fun j => z ^ j)) * (k : Real) <= (q : Real) := by
    nlinarith only [hMul]
  have hDiv := div_le_div_of_nonneg_right hBound hkR.le
  have hCancelK : (norm (Finset.sum (Finset.range L) (fun j => z ^ j)) * (k : Real)) /
      (k : Real) = norm (Finset.sum (Finset.range L) (fun j => z ^ j)) := by field_simp
  rw [hCancelK] at hDiv
  exact hDiv

theorem lpf_product_window_pair_intersection (A B s L n1 n2 : Nat)
    (hn1 : 0 < n1) (hn2 : 0 < n2) :
    (Finset.Ioc A B).filter (fun m => And (And (s < m * n1) (m * n1 <= s + L))
      (And (s < m * n2) (m * n2 <= s + L))) =
        Finset.Ioc (max (max A (s / n1)) (s / n2))
          (min (min B ((s + L) / n1)) ((s + L) / n2)) := by
  classical
  apply Finset.ext
  intro m
  have hLower1 : s / n1 < m <-> s < m * n1 := Nat.div_lt_iff_lt_mul hn1
  have hLower2 : s / n2 < m <-> s < m * n2 := Nat.div_lt_iff_lt_mul hn2
  have hUpper1 : m <= (s + L) / n1 <-> m * n1 <= s + L := Nat.le_div_iff_mul_le hn1
  have hUpper2 : m <= (s + L) / n2 <-> m * n2 <= s + L := Nat.le_div_iff_mul_le hn2
  simp only [Finset.mem_filter, Finset.mem_Ioc, max_lt_iff, le_min_iff, hLower1, hLower2,
    hUpper1, hUpper2]
  constructor
  . intro h
    exact And.intro (And.intro (And.intro h.1.1 h.2.1.1) h.2.2.1)
      (And.intro (And.intro h.1.2 h.2.1.2) h.2.2.2)
  . intro h
    exact And.intro (And.intro h.1.1.1 h.2.1.1)
      (And.intro (And.intro h.1.1.2 h.2.1.2) (And.intro h.1.2 h.2.2))

theorem lpf_positive_rational_geometric_bound {q : Nat} [NeZero q]
    (k L : Nat) (hk : 1 <= k) (hHalf : 2 * k <= q)
    (beta : Real) (hBeta : abs beta <= 1 / (4 * (q : Real))) :
    norm (Finset.sum (Finset.range L) (fun j =>
      (ZMod.stdAddChar (N := q) (k : ZMod q) *
        Complex.exp (Complex.I * ((2 * Real.pi * beta : Real) : Complex))) ^ j)) <=
          (q : Real) / (k : Real) := by
  apply lpf_perturbed_geometric_sum_bound q k L
    (Nat.pos_of_ne_zero (NeZero.ne q)) hk
  . rw [ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  . exact lpf_root_distance_lower_bound (N := q) k hHalf
  . exact hBeta

theorem lpf_negative_rational_geometric_bound {q : Nat} [NeZero q]
    (k L : Nat) (hk : 1 <= k) (hHalf : 2 * k <= q)
    (beta : Real) (hBeta : abs beta <= 1 / (4 * (q : Real))) :
    norm (Finset.sum (Finset.range L) (fun j =>
      (ZMod.stdAddChar (N := q) (-(k : ZMod q)) *
        Complex.exp (Complex.I * ((2 * Real.pi * beta : Real) : Complex))) ^ j)) <=
          (q : Real) / (k : Real) := by
  apply lpf_perturbed_geometric_sum_bound q k L
    (Nat.pos_of_ne_zero (NeZero.ne q)) hk
  . rw [ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  . rw [lpf_stdAddChar_neg_star]
    have hEq : (1 : Complex) - star (ZMod.stdAddChar (N := q) (k : ZMod q)) =
        star (1 - ZMod.stdAddChar (N := q) (k : ZMod q)) := by
      rw [star_sub, star_one]
    rw [hEq, norm_star]
    exact lpf_root_distance_lower_bound (N := q) k hHalf
  . exact hBeta

theorem lpf_Ioc_power_sum (z : Complex) (A B : Nat) :
    Finset.sum (Finset.Ioc A B) (fun m => z ^ m) =
      z ^ (A + 1) * Finset.sum (Finset.range (B - A)) (fun j => z ^ j) := by
  have hMap : Finset.sum (Finset.range (B - A)) (fun j => z ^ (A + 1 + j)) =
      Finset.sum (Finset.Ioc A B) (fun m => z ^ m) := by
    apply Finset.sum_bij (fun j _ => A + 1 + j)
    . intro j hj
      apply Finset.mem_Ioc.mpr
      have h := Finset.mem_range.mp hj
      omega
    . intro j hj k hk hEq
      exact Nat.add_left_cancel hEq
    . intro m hm
      have h := Finset.mem_Ioc.mp hm
      refine Exists.intro (m - A - 1) (Exists.intro ?_ ?_)
      . apply Finset.mem_range.mpr
        omega
      . omega
    . intro j hj
      rfl
  rw [<- hMap, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact pow_add z (A + 1) j

theorem norm_lpf_unit_Ioc_power_sum_le_length (z : Complex) (hz : norm z = 1) (A B : Nat) :
    norm (Finset.sum (Finset.Ioc A B) (fun m => z ^ m)) <= ((B - A : Nat) : Real) := by
  have h := norm_sum_le (Finset.Ioc A B) (fun m => z ^ m)
  simpa only [norm_pow, hz, one_pow, Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul,
    mul_one] using h

theorem lpf_perturbed_Ioc_geometric_bound (q k A B : Nat) (hq : 0 < q) (hk : 1 <= k)
    (r : Complex) (hr : norm r = 1)
    (hBase : 4 * (k : Real) / (q : Real) <= norm (1 - r))
    (beta : Real) (hBeta : abs beta <= 1 / (4 * (q : Real))) :
    norm (Finset.sum (Finset.Ioc A B) (fun m =>
      (r * Complex.exp (Complex.I * ((2 * Real.pi * beta : Real) : Complex))) ^ m)) <=
        min ((B - A : Nat) : Real) ((q : Real) / (k : Real)) := by
  let z := r * Complex.exp (Complex.I * ((2 * Real.pi * beta : Real) : Complex))
  have hz : norm z = 1 := by
    dsimp [z]
    rw [norm_mul, hr, one_mul, Complex.norm_exp]
    simp
  apply le_min
  . exact norm_lpf_unit_Ioc_power_sum_le_length z hz A B
  . change norm (Finset.sum (Finset.Ioc A B) (fun m => z ^ m)) <= _
    rw [lpf_Ioc_power_sum, norm_mul, norm_pow, hz, one_pow, one_mul]
    exact lpf_perturbed_geometric_sum_bound q k (B - A) hq hk r hr hBase beta hBeta

theorem lpf_residue_root_distance {q : Nat} [NeZero q] (j : Nat) (hj : j < q) :
    4 * ((min j (q - j) : Nat) : Real) / (q : Real) <=
      norm (1 - ZMod.stdAddChar (N := q) (j : ZMod q)) := by
  by_cases hHalf : 2 * j <= q
  . rw [min_eq_left (by omega : j <= q - j)]
    exact lpf_root_distance_lower_bound (N := q) j hHalf
  . rw [min_eq_right (by omega : q - j <= j)]
    have hEq : (j : ZMod q) = -((q - j : Nat) : ZMod q) := by
      rw [Nat.cast_sub hj.le]
      simp
    rw [hEq, lpf_stdAddChar_neg_star]
    have hStar : (1 : Complex) - star (ZMod.stdAddChar (N := q) ((q - j : Nat) : ZMod q)) =
        star (1 - ZMod.stdAddChar (N := q) ((q - j : Nat) : ZMod q)) := by
      rw [star_sub, star_one]
    rw [hStar, norm_star]
    exact lpf_root_distance_lower_bound (N := q) (q - j) (by omega)

theorem lpf_perturbed_residue_Ioc_bound {q : Nat} [NeZero q] (j A B : Nat)
    (hj0 : 0 < j) (hj : j < q) (beta : Real)
    (hBeta : abs beta <= 1 / (4 * (q : Real))) :
    norm (Finset.sum (Finset.Ioc A B) (fun m =>
      (ZMod.stdAddChar (N := q) (j : ZMod q) *
        Complex.exp (Complex.I * ((2 * Real.pi * beta : Real) : Complex))) ^ m)) <=
          min ((B - A : Nat) : Real) ((q : Real) / ((min j (q - j) : Nat) : Real)) := by
  apply lpf_perturbed_Ioc_geometric_bound q (min j (q - j)) A B
    (Nat.pos_of_ne_zero (NeZero.ne q)) (by omega)
  . rw [ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  . exact lpf_residue_root_distance j hj
  . exact hBeta

theorem lpf_real_phase_nat_power (x : Real) (m : Nat) :
    Complex.exp (Complex.I * ((x * (m : Real) : Real) : Complex)) =
      Complex.exp (Complex.I * (x : Complex)) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hAngle : Complex.I * ((x * ((m + 1 : Nat) : Real) : Real) : Complex) =
        Complex.I * ((x * (m : Real) : Real) : Complex) + Complex.I * (x : Complex) := by
      push_cast
      ring
    rw [hAngle, Complex.exp_add, ih, pow_succ]

theorem lpf_minor_character_frequency {q : Nat} [NeZero q] (a d : Int) (beta : Real) :
    ZMod.stdAddChar (N := q) ((a * d : Int) : ZMod q) *
      Complex.exp (Complex.I * ((2 * Real.pi * beta * (d : Real) : Real) : Complex)) =
        Complex.exp (Complex.I * ((2 * Real.pi * ((a : Real) / (q : Real) + beta) *
          (d : Real) : Real) : Complex)) := by
  rw [ZMod.stdAddChar_coe, <- Complex.exp_add]
  congr 1
  push_cast
  ring

theorem lpf_minor_rational_phase_factor {q : Nat} [NeZero q] (a d : Int) (beta : Real) (m : Nat) :
    Complex.exp (Complex.I * ((2 * Real.pi * ((a : Real) / (q : Real) + beta) *
      (d : Real) * (m : Real) : Real) : Complex)) =
        (ZMod.stdAddChar (N := q) ((a * d : Int) : ZMod q) *
          Complex.exp (Complex.I * ((2 * Real.pi * beta * (d : Real) : Real) : Complex))) ^ m := by
  rw [lpf_real_phase_nat_power, <- lpf_minor_character_frequency]

theorem lpf_grid_pair_phase_rational {N q : Nat} [NeZero N] [NeZero q]
    (k a d : Int) (beta : Real) (m : Nat)
    (hAlpha : (k : Real) / (N : Real) = (a : Real) / (q : Real) + beta) :
    ZMod.stdAddChar (N := N) ((k : ZMod N) * (m : ZMod N) * (d : ZMod N)) =
      (ZMod.stdAddChar (N := q) ((a * d : Int) : ZMod q) *
        Complex.exp (Complex.I * ((2 * Real.pi * beta * (d : Real) : Real) : Complex))) ^ m := by
  have hCast : (k : ZMod N) * (m : ZMod N) * (d : ZMod N) =
      ((k * (m : Int) * d : Int) : ZMod N) := by push_cast; ring
  rw [hCast, ZMod.stdAddChar_coe]
  have hAngle : 2 * Real.pi * Complex.I * ((k * (m : Int) * d : Int) : Complex) / (N : Complex) =
      Complex.I * ((2 * Real.pi * ((k : Real) / (N : Real)) * (d : Real) * (m : Real) : Real) : Complex) := by
    push_cast
    ring
  rw [hAngle, hAlpha]
  exact lpf_minor_rational_phase_factor a d beta m

theorem lpf_grid_pair_interval_minor_bound {N q : Nat} [NeZero N] [NeZero q]
    (k a d : Int) (beta : Real) (A B : Nat)
    (hAlpha : (k : Real) / (N : Real) = (a : Real) / (q : Real) + beta)
    (hResidue : 0 < (((a * d : Int) : ZMod q).val))
    (hBeta : abs (beta * (d : Real)) <= 1 / (4 * (q : Real))) :
    norm (Finset.sum (Finset.Ioc A B) (fun m =>
      ZMod.stdAddChar (N := N) ((k : ZMod N) * (m : ZMod N) * (d : ZMod N)))) <=
        min ((B - A : Nat) : Real)
          ((q : Real) / ((min (((a * d : Int) : ZMod q).val)
            (q - (((a * d : Int) : ZMod q).val)) : Nat) : Real)) := by
  have hPhase : Finset.sum (Finset.Ioc A B) (fun m =>
      ZMod.stdAddChar (N := N) ((k : ZMod N) * (m : ZMod N) * (d : ZMod N))) =
        Finset.sum (Finset.Ioc A B) (fun m =>
          (ZMod.stdAddChar (N := q) (((((a * d : Int) : ZMod q).val) : Nat) : ZMod q) *
            Complex.exp (Complex.I * ((2 * Real.pi * (beta * (d : Real)) : Real) : Complex))) ^ m) := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [ZMod.natCast_zmod_val, lpf_grid_pair_phase_rational k a d beta m hAlpha]
    congr 2
    congr 1
    push_cast
    ring
  rw [hPhase]
  exact lpf_perturbed_residue_Ioc_bound (((a * d : Int) : ZMod q).val) A B hResidue
    (ZMod.val_lt _) (beta * (d : Real)) hBeta

theorem lpf_minor_beta_difference_bound (q M P D : Nat) (hq : 0 < q) (hM : 0 < M)
    (beta : Real) (d : Int)
    (hBeta : abs beta <= (P : Real) / ((q : Real) * (M : Real)))
    (hD : abs (d : Real) <= (D : Real)) (hRange : 4 * P * D <= M) :
    abs (beta * (d : Real)) <= 1 / (4 * (q : Real)) := by
  have hqR : (0 : Real) < (q : Real) := Nat.cast_pos.mpr hq
  have hMR : (0 : Real) < (M : Real) := Nat.cast_pos.mpr hM
  have hRangeR : 4 * (P : Real) * (D : Real) <= (M : Real) := by exact_mod_cast hRange
  rw [abs_mul]
  have hPair : abs beta * abs (d : Real) <=
      ((P : Real) / ((q : Real) * (M : Real))) * (D : Real) :=
    mul_le_mul hBeta hD (abs_nonneg _) (by positivity)
  apply hPair.trans
  apply (mul_le_mul_iff_of_pos_right (by positivity : 0 < 4 * (q : Real) * (M : Real))).mp
  have hLeft : (((P : Real) / ((q : Real) * (M : Real))) * (D : Real)) *
      (4 * (q : Real) * (M : Real)) = 4 * (P : Real) * (D : Real) := by field_simp
  have hRight : (1 / (4 * (q : Real))) * (4 * (q : Real) * (M : Real)) = (M : Real) := by
    field_simp
  rw [hLeft, hRight]
  exact hRangeR

theorem norm_lpf_grid_pair_interval_le_length {N : Nat} [NeZero N]
    (k d : Int) (A B : Nat) :
    norm (Finset.sum (Finset.Ioc A B) (fun m =>
      ZMod.stdAddChar (N := N) ((k : ZMod N) * (m : ZMod N) * (d : ZMod N)))) <=
        ((B - A : Nat) : Real) := by
  have h := norm_sum_le (Finset.Ioc A B) (fun m =>
    ZMod.stdAddChar (N := N) ((k : ZMod N) * (m : ZMod N) * (d : ZMod N)))
  simpa only [ZMod.stdAddChar_apply, Circle.norm_coe, Finset.sum_const, Nat.card_Ioc,
    nsmul_eq_mul, mul_one] using h

end PrimeFactorOscillations.LPF
