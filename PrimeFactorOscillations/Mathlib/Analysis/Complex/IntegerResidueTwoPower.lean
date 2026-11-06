/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Mathlib.Analysis.Complex.IntegerResiduePanel

/-!
# Exact degree-budget optimization with two compensation powers

The consecutive pair K-1,K maximizes the full unrestricted panel spacing.
All reference coordinates and the shared target are retained.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace Complex

def twoPowerBudgetRadius (K : Nat) (z : Complex) : Real :=
  min 1 ((K : Real) * ((K : Real) - 1) ^ 2 / norm (z + (K : Complex) - 1))

private theorem two_pair_max (d e : Nat) (hde : d <= e) :
    ({d, e} : Finset Nat).max' (by simp) = e := by
  apply (Finset.max'_eq_iff _ _ _).2
  refine And.intro (by simp) ?_
  intro b hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with h | h
  . rw [h]
    exact hde
  . exact h.le

theorem residuePanelPeriod_pair (d e : Nat) :
    residuePanelPeriod ({d, e} : Finset Nat) = Nat.lcm d e := by
  simp [residuePanelPeriod, Finset.lcm_insert]
  rfl

theorem residuePanelRadius_pair (d e : Nat) (hde : d <= e) (z : Complex) :
    residuePanelRadius ({d, e} : Finset Nat) (by simp) z =
      min 1 ((Nat.lcm d e : Real) * ((e : Real) - 1) /
        norm (z + (e : Complex) - 1)) := by
  simp only [residuePanelRadius, two_pair_max d e hde, residuePanelPeriod_pair]

theorem twoPowerPeriod_le_budget (K d e : Nat) (hK : 3 <= K)
    (hd : 2 <= d) (hde : d <= e) (heK : e <= K) :
    (Nat.lcm d e : Real) <= (K : Real) * ((K : Real) - 1) := by
  have hKR : (3 : Real) <= K := by exact_mod_cast hK
  have hdR : (2 : Real) <= d := by exact_mod_cast hd
  have heR : (2 : Real) <= e := by exact_mod_cast (hd.trans hde)
  have heKR : (e : Real) <= K := by exact_mod_cast heK
  by_cases hEq : d = e
  . subst e
    simp only [Nat.lcm_self]
    nlinarith [sq_nonneg ((K : Real) - 2)]
  . have hdK : d + 1 <= K := by omega
    have hdKR : (d : Real) <= (K : Real) - 1 := by
      have ht : (d : Real) + 1 <= K := by exact_mod_cast hdK
      linarith
    have hL : (Nat.lcm d e : Real) <= (d : Real) * (e : Real) := by
      exact_mod_cast (Nat.lcm_le_mul (by omega : 0 < d) (by omega : 0 < e))
    calc
      (Nat.lcm d e : Real) <= (d : Real) * (e : Real) := hL
      _ <= ((K : Real) - 1) * (K : Real) :=
        mul_le_mul hdKR heKR (by linarith) (by linarith)
      _ = (K : Real) * ((K : Real) - 1) := by ring

theorem residuePanelRadius_pair_le_budget (K d e : Nat) (hK : 3 <= K)
    (hd : 2 <= d) (hde : d <= e) (heK : e <= K)
    (z : Complex) (hRe : 0 <= z.re) (hH : 2 <= abs z.im) :
    residuePanelRadius ({d, e} : Finset Nat) (by simp) z <= twoPowerBudgetRadius K z := by
  rw [residuePanelRadius_pair d e hde z]
  unfold twoPowerBudgetRadius
  apply min_le_min le_rfl
  have hKR : (3 : Real) <= K := by exact_mod_cast hK
  have he : 2 <= e := hd.trans hde
  have heR : (2 : Real) <= e := by exact_mod_cast he
  have hL := twoPowerPeriod_le_budget K d e hK hd hde heK
  have hF := residueReferenceFraction_mono e K he heK z hRe hH
  have hF0 : 0 <= ((e : Real) - 1) / norm (z + (e : Complex) - 1) :=
    div_nonneg (by linarith) (norm_nonneg _)
  calc
    (Nat.lcm d e : Real) * ((e : Real) - 1) / norm (z + (e : Complex) - 1) =
        (Nat.lcm d e : Real) * (((e : Real) - 1) / norm (z + (e : Complex) - 1)) := by ring
    _ <= (K : Real) * ((K : Real) - 1) *
        (((e : Real) - 1) / norm (z + (e : Complex) - 1)) :=
      mul_le_mul_of_nonneg_right hL hF0
    _ <= (K : Real) * ((K : Real) - 1) *
        (((K : Real) - 1) / norm (z + (K : Complex) - 1)) :=
      mul_le_mul_of_nonneg_left hF (mul_nonneg (by linarith) (by linarith))
    _ = (K : Real) * ((K : Real) - 1) ^ 2 / norm (z + (K : Complex) - 1) := by ring

theorem residuePanelRadius_consecutive (K : Nat) (hK : 3 <= K) (z : Complex) :
    residuePanelRadius ({K - 1, K} : Finset Nat) (by simp) z =
      twoPowerBudgetRadius K z := by
  have hCop : Nat.Coprime (K - 1) K := by
    change Nat.gcd (K - 1) K = 1
    calc
      Nat.gcd (K - 1) K = Nat.gcd (K - 1) (1 + (K - 1)) := by congr 1; omega
      _ = Nat.gcd (K - 1) 1 := Nat.gcd_add_self_right (K - 1) 1
      _ = 1 := by simp
  rw [residuePanelRadius_pair (K - 1) K (by omega) z, hCop.lcm_eq_mul]
  simp only [Nat.cast_mul, Nat.cast_sub (by omega : 1 <= K), Nat.cast_one]
  unfold twoPowerBudgetRadius
  congr 2
  ring

private theorem two_budget_den_pos (K : Nat) (z : Complex) (hH : 2 <= abs z.im) :
    0 < norm (z + (K : Complex) - 1) := by
  have h := Complex.abs_im_le_norm (z + (K : Complex) - 1)
  simp at h
  linarith

theorem twoPowerBudgetRadius_unit_iff (K : Nat) (z : Complex) (hH : 2 <= abs z.im) :
    1 <= twoPowerBudgetRadius K z <->
      norm (z + (K : Complex) - 1) <= (K : Real) * ((K : Real) - 1) ^ 2 := by
  let S := (K : Real) * ((K : Real) - 1) ^ 2 / norm (z + (K : Complex) - 1)
  have hDen := two_budget_den_pos K z hH
  have he : S * norm (z + (K : Complex) - 1) = (K : Real) * ((K : Real) - 1) ^ 2 := by
    dsimp [S]
    field_simp
  constructor
  . intro h
    have hS : 1 <= S := h.trans (min_le_right 1 S)
    have hm := mul_le_mul_of_nonneg_right hS hDen.le
    simpa only [one_mul, he] using hm
  . intro h
    have hS : 1 <= S := le_of_mul_le_mul_right (by rw [one_mul, he]; exact h) hDen
    exact le_min le_rfl hS

theorem twoPowerBudget_unit_iff (K : Nat) (hK : 3 <= K) (z : Complex)
    (hRe : 0 <= z.re) (hH : 2 <= abs z.im) :
    (Exists (fun d : Nat => Exists (fun e : Nat =>
      And (And (2 <= d) (And (d <= e) (e <= K)))
        (1 <= residuePanelRadius ({d, e} : Finset Nat) (by simp) z)))) <->
      norm (z + (K : Complex) - 1) <= (K : Real) * ((K : Real) - 1) ^ 2 := by
  constructor
  . intro h
    choose d e hp using h
    have hB := residuePanelRadius_pair_le_budget K d e hK hp.1.1 hp.1.2.1 hp.1.2.2 z hRe hH
    exact (twoPowerBudgetRadius_unit_iff K z hH).1 (hp.2.trans hB)
  . intro h
    refine Exists.intro (K - 1) (Exists.intro K (And.intro ?_ ?_))
    . exact And.intro (by omega) (And.intro (by omega) le_rfl)
    . rw [residuePanelRadius_consecutive K hK z]
      exact (twoPowerBudgetRadius_unit_iff K z hH).2 h

theorem twoPowerBudget_height_necessary (K : Nat) (hK : 3 <= K)
    (z : Complex) (hH : 2 <= abs z.im) (hUnit : 1 <= twoPowerBudgetRadius K z) :
    abs z.im < (K : Real) ^ 3 := by
  have hDisk := (twoPowerBudgetRadius_unit_iff K z hH).1 hUnit
  have hIm := Complex.abs_im_le_norm (z + (K : Complex) - 1)
  simp at hIm
  have hKR : (3 : Real) <= K := by exact_mod_cast hK
  have hp : 0 < (K : Real) * (2 * (K : Real) - 1) :=
    mul_pos (by linarith) (by linarith)
  nlinarith

theorem twoPowerBudget_height_sufficient (K : Nat) (hK : 3 <= K)
    (z : Complex) (hRe : And (0 <= z.re) (z.re <= 1)) (hH : 2 <= abs z.im)
    (hCube : abs z.im <= ((K : Real) - 1) ^ 3) :
    1 <= twoPowerBudgetRadius K z := by
  apply (twoPowerBudgetRadius_unit_iff K z hH).2
  let T := norm (z + (K : Complex) - 1)
  let H := abs z.im
  have hKR : (3 : Real) <= K := by exact_mod_cast hK
  have hK0 : (0 : Real) <= K := by positivity
  have hH0 : 0 <= H := abs_nonneg _
  have hT0 : 0 <= T := norm_nonneg _
  have hs : T ^ 2 = (z.re + (K : Real) - 1) ^ 2 + z.im ^ 2 := by
    dsimp [T]
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hx0 : 0 <= z.re + (K : Real) - 1 := by linarith [hRe.1]
  have hxK : z.re + (K : Real) - 1 <= K := by linarith [hRe.2]
  have hHs : H ^ 2 = z.im ^ 2 := sq_abs _
  have hSq : T ^ 2 <= (K : Real) ^ 2 + H ^ 2 := by nlinarith only [hs, hx0, hxK, hHs, hK0]
  have hL1 : T <= (K : Real) + H := by
    nlinarith [mul_nonneg hK0 hH0]
  have hSmall : (K : Real) <= ((K : Real) - 1) ^ 2 := by
    nlinarith [sq_nonneg ((K : Real) - 2)]
  change T <= (K : Real) * ((K : Real) - 1) ^ 2
  change H <= ((K : Real) - 1) ^ 3 at hCube
  nlinarith

theorem twoPowerBudget_cube_root_lower (K : Nat) (hK : 3 <= K)
    (z : Complex) (hH : 2 <= abs z.im) (r : Real) (hr0 : 0 <= r)
    (hrCube : r ^ 3 = abs z.im) (hUnit : 1 <= twoPowerBudgetRadius K z) :
    r < (K : Real) := by
  have hBound := twoPowerBudget_height_necessary K hK z hH hUnit
  by_contra h
  have hKr : (K : Real) <= r := le_of_not_gt h
  have hSum : 0 <= r ^ 2 + r * (K : Real) + (K : Real) ^ 2 := by positivity
  have hp := mul_nonneg (sub_nonneg.mpr hKr) hSum
  nlinarith

theorem twoPowerBudget_ceil_cube_root (z : Complex)
    (hRe : And (0 <= z.re) (z.re <= 1)) (hH : 2 <= abs z.im)
    (r : Real) (hr0 : 0 <= r) (hrCube : r ^ 3 = abs z.im) :
    And (3 <= Nat.ceil r + 1)
      (1 <= twoPowerBudgetRadius (Nat.ceil r + 1) z) := by
  let n : Nat := Nat.ceil r
  have hrn : r <= (n : Real) := Nat.le_ceil r
  have hn2 : 2 <= n := by
    by_contra h
    have hn1 : n <= 1 := by omega
    have hnR : (n : Real) <= 1 := by exact_mod_cast hn1
    have hr1 : r <= 1 := hrn.trans hnR
    have hSum : 0 <= 1 + r + r ^ 2 := by positivity
    have hp := mul_nonneg (sub_nonneg.mpr hr1) hSum
    nlinarith
  have hSum : 0 <= (n : Real) ^ 2 + (n : Real) * r + r ^ 2 := by positivity
  have hp := mul_nonneg (sub_nonneg.mpr hrn) hSum
  have hCube : abs z.im <= (n : Real) ^ 3 := by nlinarith
  have hK : 3 <= n + 1 := by omega
  refine And.intro hK ?_
  apply twoPowerBudget_height_sufficient (n + 1) hK z hRe hH
  simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hCube

theorem twoPowerBudget_cube_root_degree (z : Complex)
    (hRe : And (0 <= z.re) (z.re <= 1)) (hH : 2 <= abs z.im)
    (r : Real) (hr0 : 0 <= r) (hrCube : r ^ 3 = abs z.im) :
    Exists (fun K : Nat => And (3 <= K) (And (1 <= twoPowerBudgetRadius K z)
      (And (r < (K : Real)) ((K : Real) < r + 2)))) := by
  let K : Nat := Nat.ceil r + 1
  have h := twoPowerBudget_ceil_cube_root z hRe hH r hr0 hrCube
  refine Exists.intro K (And.intro h.1 (And.intro h.2 (And.intro ?_ ?_)))
  . exact twoPowerBudget_cube_root_lower K h.1 z hH r hr0 hrCube h.2
  . have hc := Nat.ceil_lt_add_one hr0
    have hK : (K : Real) = (Nat.ceil r : Real) + 1 := by simp only [K, Nat.cast_add, Nat.cast_one]
    linarith

end Complex

end
