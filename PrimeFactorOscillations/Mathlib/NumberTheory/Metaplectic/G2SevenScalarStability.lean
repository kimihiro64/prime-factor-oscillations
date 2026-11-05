/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.G2SevenPaleyStability

/-!
# The scalar region of the unrestricted sevenfold stability problem

This is a two-moment envelope, not the unrestricted sharp theorem.
It controls the complete range 1 < M <= 1 + 2 * sqrt 2. The remaining
high-maximum region must use additional cyclic correlations.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace Metaplectic.G2Seven.Scalar

private theorem square_expansion (f : Fin 7 -> Real) (M : Real)
    (hmean : Finset.univ.sum f = 7)
    (hsquare : Finset.univ.sum (fun i => f i ^ 2) = 49) :
    Finset.univ.sum (fun i => (M - f i) * ((M - 1) * f i - (M - 7)) ^ 2) =
      (M - 1) * ((M - 1) * (343 - Finset.univ.sum (fun i => f i ^ 3)) -
        42 * M * (7 - M)) := by
  calc
    _ = Finset.univ.sum (fun i =>
        -(M - 1) ^ 2 * f i ^ 3 +
        (M * (M - 1) ^ 2 + 2 * (M - 1) * (M - 7)) * f i ^ 2 +
        (-2 * M * (M - 1) * (M - 7) - (M - 7) ^ 2) * f i +
        M * (M - 7) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, <- Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        hmean, hsquare]
      norm_num
      ring

/-- The complete third-moment envelope retains its exact signed square residual. -/
theorem cubic_envelope (f : Fin 7 -> Real) (M : Real)
    (hmean : Finset.univ.sum f = 7)
    (hsquare : Finset.univ.sum (fun i => f i ^ 2) = 49)
    (hupper : forall i : Fin 7, f i <= M) (hM : 1 < M) :
    42 * M * (7 - M) <=
      (M - 1) * (343 - Finset.univ.sum (fun i => f i ^ 3)) := by
  have hsum : 0 <= Finset.univ.sum
      (fun i => (M - f i) * ((M - 1) * f i - (M - 7)) ^ 2) := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (sub_nonneg.mpr (hupper i)) (sq_nonneg _)
  rw [square_expansion f M hmean hsquare] at hsum
  by_contra h
  have hneg : (M - 1) * (343 - Finset.univ.sum (fun i => f i ^ 3)) -
      42 * M * (7 - M) < 0 := by linarith
  have hp := mul_neg_of_pos_of_neg (sub_pos.mpr hM) hneg
  linarith only [hsum, hp]

/-- The proposed sharp constant is proved on the entire scalar low-maximum region. -/
theorem low_peak_stability (f : Fin 7 -> Real) (M t : Real)
    (hmean : Finset.univ.sum f = 7)
    (hsquare : Finset.univ.sum (fun i => f i ^ 2) = 49)
    (hupper : forall i : Fin 7, f i <= M) (hM : 1 < M)
    (ht : 0 < t) (ht2 : t ^ 2 = 1 / 2) (hcut : M <= 1 + 4 * t) :
    (6 + 3 * t) * (7 - M) <=
      (343 - Finset.univ.sum (fun i => f i ^ 3)) / 7 := by
  have hb := Paley.half_root_bounds t ht ht2
  have hM7 : M <= 7 := by linarith [hb.2]
  have hslack : 0 <= 21 * t * (7 - M) * (1 + 4 * t - M) := by positivity
  have he : 42 * M * (7 - M) - 7 * (6 + 3 * t) * (M - 1) * (7 - M) =
      21 * t * (7 - M) * (1 + 4 * t - M) := by
    ring_nf
    simp only [ht2]
    ring
  have henvelope := cubic_envelope f M hmean hsquare hupper hM
  have htotal : 0 <= (M - 1) *
      (343 - Finset.univ.sum (fun i => f i ^ 3) - 7 * (6 + 3 * t) * (7 - M)) := by
    nlinarith only [henvelope, hslack, he]
  by_contra h
  have hneg : 343 - Finset.univ.sum (fun i => f i ^ 3) -
      7 * (6 + 3 * t) * (7 - M) < 0 := by linarith
  have hp := mul_neg_of_pos_of_neg (sub_pos.mpr hM) hneg
  linarith only [htotal, hp]

noncomputable def twoPeak (v : Real) (i : Fin 7) : Real :=
  if i.val < 2 then 1 + v else 1 - 2 * v / 5

/-- The exact two-moment obstruction is not an obstruction to cyclic correlations. -/
theorem scalar_constraints_insufficient (t v : Real) (ht : 0 < t)
    (ht2 : t ^ 2 = 1 / 2) (hv : 0 < v) (hv2 : v ^ 2 = 15) :
    Finset.univ.sum (twoPeak v) = 7 /\
    Finset.univ.sum (fun i => twoPeak v i ^ 2) = 49 /\
    (forall i : Fin 7, twoPeak v i <= 1 + v) /\
    (343 - Finset.univ.sum (fun i => twoPeak v i ^ 3)) / 7 <
      (6 + 3 * t) * (7 - (1 + v)) /\
    Finset.univ.sum (fun i : Fin 7 => twoPeak v i * twoPeak v (i + 1)) = 98 / 5 := by
  have hv3 : v ^ 3 = 15 * v := by
    calc
      v ^ 3 = v * v ^ 2 := by ring
      _ = 15 * v := by rw [hv2]; ring
  have hmean : Finset.univ.sum (twoPeak v) = 7 := by
    norm_num [twoPeak, Fin.sum_univ_succ]
    ring
  have hsquare : Finset.univ.sum (fun i => twoPeak v i ^ 2) = 49 := by
    norm_num [twoPeak, Fin.sum_univ_succ]
    nlinarith only [hv2]
  have hupper (i : Fin 7) : twoPeak v i <= 1 + v := by
    unfold twoPeak
    split_ifs <;> linarith
  have hcube : Finset.univ.sum (fun i => twoPeak v i ^ 3) = 133 + 126 * v / 5 := by
    norm_num [twoPeak, Fin.sum_univ_succ]
    ring_nf
    simp only [hv2, hv3]
    ring
  have hv6 : v < 6 := by nlinarith [sq_nonneg (v - 6)]
  have hgap : 0 < 3 * t - 2 * v / 5 := by
    by_contra h
    have hle : 3 * t <= 2 * v / 5 := by linarith
    have hm := mul_nonneg (sub_nonneg.mpr hle)
      (show 0 <= 2 * v / 5 + 3 * t by positivity)
    nlinarith only [hm, ht2, hv2]
  have hprod := mul_pos (sub_pos.mpr hv6) hgap
  have hbad : (343 - Finset.univ.sum (fun i => twoPeak v i ^ 3)) / 7 <
      (6 + 3 * t) * (7 - (1 + v)) := by
    rw [hcube]
    nlinarith only [hprod, hv2]
  have hcorr : Finset.univ.sum
      (fun i : Fin 7 => twoPeak v i * twoPeak v (i + 1)) = 98 / 5 := by
    norm_num [twoPeak, Fin.sum_univ_succ]
    nlinarith only [hv2]
  exact And.intro hmean (And.intro hsquare (And.intro hupper (And.intro hbad hcorr)))

end Metaplectic.G2Seven.Scalar
