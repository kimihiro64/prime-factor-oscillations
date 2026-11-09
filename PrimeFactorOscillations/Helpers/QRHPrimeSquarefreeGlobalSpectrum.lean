/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.QRHArtinDensity
import PrimeFactorOscillations.Helpers.QRHPrimeSquarefreeSpectrum

/-! # The global signed spectral estimate for squarefree prime differences

The positive unconditional Euler-product density replaces the finite density
in the complete signed comparison. Both principal means and the entire
residual remain in the estimate, uniformly over every real prime mask.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
open Filter
open scoped Classical
namespace PrimeFactorOscillations.QRH

private theorem mean_square_le_energy (S : Finset Nat) (f : Nat -> Real)
    (hn : (0 : Real) < S.card) :
    (S.sum f / (S.card : Real)) ^ 2 <=
      S.sum (fun p => (f p) ^ 2) / (S.card : Real) := by
  have hCS : (S.sum f) ^ 2 <=
      (S.card : Real) * S.sum (fun p => (f p) ^ 2) := by
    simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using
      Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : Real)) f
  calc
    _ = (S.sum f) ^ 2 / (S.card : Real) ^ 2 := div_pow _ _ _
    _ <= ((S.card : Real) * S.sum (fun p => (f p) ^ 2)) / (S.card : Real) ^ 2 :=
      div_le_div_of_nonneg_right hCS (sq_nonneg _)
    _ = _ := by field_simp [hn.ne']

private theorem signed_density_replacement (Q D A a b e eta : Real)
    (hDA : A <= D) (ha : a ^ 2 <= e) (hb : b ^ 2 <= e)
    (hFinite : abs (Q - D * (a ^ 2 - b ^ 2)) <=
      D / 5 * (e - a ^ 2 - b ^ 2) + eta * e) :
    abs (Q - A * (a ^ 2 - b ^ 2)) <=
      A / 5 * (e - a ^ 2 - b ^ 2) + ((6 / 5 : Real) * (D - A) + eta) * e := by
  have hContrast : abs (a ^ 2 - b ^ 2) <= e := by
    apply abs_le.mpr
    exact And.intro
      (by nlinarith only [ha, hb, sq_nonneg a, sq_nonneg b])
      (by nlinarith only [ha, hb, sq_nonneg a, sq_nonneg b])
  have hTail : abs ((D - A) * (a ^ 2 - b ^ 2)) <= (D - A) * e := by
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hDA)]
    exact mul_le_mul_of_nonneg_left hContrast (sub_nonneg.mpr hDA)
  have hTriangle : abs (Q - A * (a ^ 2 - b ^ 2)) <=
      abs (Q - D * (a ^ 2 - b ^ 2)) + abs ((D - A) * (a ^ 2 - b ^ 2)) := by
    calc
      _ = abs ((Q - D * (a ^ 2 - b ^ 2)) + (D - A) * (a ^ 2 - b ^ 2)) := by
        congr 1
        ring1
      _ <= _ := abs_add_le _ _
  have hCorrection := mul_nonneg (sub_nonneg.mpr hDA)
    (add_nonneg (sq_nonneg a) (sq_nonneg b))
  nlinarith only [hFinite, hTail, hTriangle, hCorrection]

/-- The full signed spectral estimate at the positive infinite Euler-product density. -/
theorem eventually_prime_squarefree_spectral_gap {eps : Real} (heps : 0 < eps) :
    Filter.Eventually (fun X : Nat => forall f : Nat -> Real,
      let A := artinPrimeSquareConstant
      let n := ((oddPrimeVertices X).card : Real)
      let a := (oddPrimeVertices X).sum f / n
      let b := (oddPrimeVertices X).sum (fun p => primeResidueSign p * f p) / n
      let e := (oddPrimeVertices X).sum (fun p => (f p) ^ 2) / n
      abs (Finset.kernelBilinear (oddPrimeVertices X)
        primeSquarefreeDifferenceKernel f f / n ^ 2 - A * (a ^ 2 - b ^ 2)) <=
        A / 5 * (e - a ^ 2 - b ^ 2) + eps * e) atTop := by
  classical
  let A := artinPrimeSquareConstant
  let budget : Nat -> Real := fun R =>
    (6 / 5 : Real) * (primeSquareCutoffDensity R - A) + 1 / (R : Real)
  have hc : Tendsto (fun _ : Nat => A) atTop (nhds A) := tendsto_const_nhds
  have hD : Tendsto primeSquareCutoffDensity atTop (nhds A) :=
    tendsto_primeSquareCutoffDensity
  have hDelta : Tendsto (fun R : Nat => primeSquareCutoffDensity R - A)
      atTop (nhds (0 : Real)) := by
    simpa only [sub_self] using hD.sub hc
  have hInv : Tendsto (fun R : Nat => 1 / (R : Real)) atTop (nhds (0 : Real)) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun R : Nat => (R : Real)) atTop atTop)
  have hBudget : Tendsto budget atTop (nhds (0 : Real)) := by
    simpa only [budget, mul_zero, add_zero] using
      (hDelta.const_mul (6 / 5 : Real)).add hInv
  have hHalf : (0 : Real) < eps / 2 := by linarith
  have hChoice := (hBudget.eventually (gt_mem_nhds hHalf)).and
    (eventually_ge_atTop (2 : Nat))
  choose R hR using hChoice.exists
  have hFinite := eventually_prime_squarefree_spectral_gap_at_cutoff R hR.2
    (eps := eps / 2) hHalf
  filter_upwards [eventually_ge_atTop (3 : Nat), hFinite] with X hX hF
  intro f
  let S := oddPrimeVertices X
  let n : Real := (S.card : Real)
  let a := S.sum f / n
  let b := S.sum (fun p => primeResidueSign p * f p) / n
  let e := S.sum (fun p => (f p) ^ 2) / n
  let Q := Finset.kernelBilinear S primeSquarefreeDifferenceKernel f f / n ^ 2
  let D := primeSquareCutoffDensity R
  have hn : 0 < n := by
    apply Nat.cast_pos.mpr
    apply Finset.card_pos.mpr
    refine Exists.intro 3 ?_
    change Membership.mem ((Nat.primesBelow (X + 1)).erase 2) 3
    exact Finset.mem_erase.mpr (And.intro (by decide)
      (Nat.mem_primesBelow.mpr (And.intro (by omega) Nat.prime_three)))
  have ha : a ^ 2 <= e := mean_square_le_energy S f hn
  have hSign (p : Nat) : (primeResidueSign p) ^ 2 = 1 := by
    simp only [primeResidueSign]
    split_ifs <;> norm_num
  have hEnergy : S.sum (fun p => (primeResidueSign p * f p) ^ 2) =
      S.sum (fun p => (f p) ^ 2) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [mul_pow, hSign, one_mul]
  have hb : b ^ 2 <= e := by
    have h := mean_square_le_energy S (fun p => primeResidueSign p * f p) hn
    rw [hEnergy] at h
    exact h
  have hf := hF f
  change abs (Q - D * (a ^ 2 - b ^ 2)) <=
    D / 5 * (e - a ^ 2 - b ^ 2) + (1 / (R : Real) + eps / 2) * e at hf
  have hTransfer := signed_density_replacement Q D A a b e
    (1 / (R : Real) + eps / 2) (artinPrimeSquareConstant_le_cutoff_density R) ha hb hf
  have hAllowance : (6 / 5 : Real) * (D - A) + (1 / (R : Real) + eps / 2) <= eps := by
    have hSmall := hR.1
    change (6 / 5 : Real) * (D - A) + 1 / (R : Real) < eps / 2 at hSmall
    linarith
  have hWeighted := mul_le_mul_of_nonneg_right hAllowance ((sq_nonneg a).trans ha)
  change abs (Q - A * (a ^ 2 - b ^ 2)) <= A / 5 * (e - a ^ 2 - b ^ 2) + eps * e
  linarith only [hTransfer, hWeighted]

end PrimeFactorOscillations.QRH
