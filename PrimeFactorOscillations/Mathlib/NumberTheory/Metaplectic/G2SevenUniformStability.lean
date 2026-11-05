/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.G2SevenUniformCertificateColumns

/-!
# Uniform constant-eight cyclic stability

The exact signed certificate proves the global normalized stability inequality
under unit mass, peak dominance and all three cyclic correlation equations.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace Metaplectic.G2Seven.Uniform

open Certificate

private theorem empty_sum (f : Fin 0 -> Real) :
    Finset.univ.sum f = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact Fin.elim0 i

private theorem coordinate_vector (y : Fin 6 -> Real) :
    y = ![y 0, y 1, y 2, y 3, y 4, y 5] := by
  funext i
  fin_cases i <;> rfl

private noncomputable def deficit (y : Fin 6 -> Real) : Real :=
  7 * (1 - Finset.univ.sum (fun i : Fin 7 => coordinates y i ^ 3)) -
    8 * (1 - mass y)

private theorem target_expansion (y : Fin 6 -> Real) :
    (704643072 : Real) * deficit y =
      Finset.univ.sum (fun i : Fin 80 => (targetCoefficient i : Real) * orbitBasis y i) := by
  change (704643072 : Real) *
      (7 * (1 - Finset.univ.sum (fun i : Fin 7 => coordinates y i ^ 3)) -
        8 * (1 - mass y)) =
    Finset.univ.sum (fun i : Fin 80 => (targetCoefficient i : Real) * orbitBasis y i)
  rw [coordinate_vector y]
  generalize y 0 = a
  generalize y 1 = b
  generalize y 2 = c
  generalize y 3 = d
  generalize y 4 = e
  generalize y 5 = f
  simp only [Fin.sum_univ_succ, empty_sum, add_zero]
  change (704643072 : Real) * (7 * (1 - (((1 - a - b - c - d - e - f)) ^ 3 + ((a) ^ 3 + ((b) ^ 3 + ((c) ^ 3 + ((d) ^ 3 + ((e) ^ 3 + ((f) ^ 3)))))))) - 8 * (1 - (1 - a - b - c - d - e - f))) =
    ((0 : Int) : Real) * (1) + (((9160359936 : Int) : Real) * (a + b + c + d + e + f) + (((-14797504512 : Int) : Real) * (a * a + b * b + c * c + d * d + e * e + f * f) + (((-29595009024 : Int) : Real) * (a * b + a * d + b * d + c * e + c * f + e * f) + (((-29595009024 : Int) : Real) * (a * c + a * e + b * c + b * f + d * e + d * f) + (((-29595009024 : Int) : Real) * (a * f + b * e + c * d) + (((0 : Int) : Real) * (a * a * a + b * b * b + c * c * c + d * d * d + e * e * e + f * f * f) + (((14797504512 : Int) : Real) * (a * a * b + a * d * d + b * b * d + c * c * f + c * e * e + e * f * f) + (((14797504512 : Int) : Real) * (a * a * c + a * e * e + b * b * f + b * c * c + d * d * e + d * f * f) + (((14797504512 : Int) : Real) * (a * a * d + a * b * b + b * d * d + c * c * e + c * f * f + e * e * f) + (((14797504512 : Int) : Real) * (a * a * e + a * c * c + b * b * c + b * f * f + d * d * f + d * e * e) + (((14797504512 : Int) : Real) * (a * a * f + a * f * f + b * b * e + b * e * e + c * c * d + c * d * d) + (((29595009024 : Int) : Real) * (a * b * c + a * c * e + a * d * e + b * c * f + b * d * f + d * e * f) + (((29595009024 : Int) : Real) * (a * b * d + c * e * f) + (((29595009024 : Int) : Real) * (a * b * e + a * c * f + a * d * f + b * c * d + b * e * f + c * d * e) + (((29595009024 : Int) : Real) * (a * b * f + a * c * d + a * e * f + b * c * e + b * d * e + c * d * f) + (((0 : Int) : Real) * (a * a * a * a + b * b * b * b + c * c * c * c + d * d * d * d + e * e * e * e + f * f * f * f) + (((0 : Int) : Real) * (a * a * a * b + a * d * d * d + b * b * b * d + c * c * c * f + c * e * e * e + e * f * f * f) + (((0 : Int) : Real) * (a * a * a * c + a * e * e * e + b * b * b * f + b * c * c * c + d * d * d * e + d * f * f * f) + (((0 : Int) : Real) * (a * a * a * d + a * b * b * b + b * d * d * d + c * c * c * e + c * f * f * f + e * e * e * f) + (((0 : Int) : Real) * (a * a * a * e + a * c * c * c + b * b * b * c + b * f * f * f + d * d * d * f + d * e * e * e) + (((0 : Int) : Real) * (a * a * a * f + a * f * f * f + b * b * b * e + b * e * e * e + c * c * c * d + c * d * d * d) + (((0 : Int) : Real) * (a * a * b * b + a * a * d * d + b * b * d * d + c * c * e * e + c * c * f * f + e * e * f * f) + (((0 : Int) : Real) * (a * a * b * c + a * c * e * e + a * d * d * e + b * b * d * f + b * c * c * f + d * e * f * f) + (((0 : Int) : Real) * (a * a * b * d + a * b * b * d + a * b * d * d + c * c * e * f + c * e * e * f + c * e * f * f) + (((0 : Int) : Real) * (a * a * b * e + a * c * c * f + a * d * d * f + b * b * c * d + b * e * f * f + c * d * e * e) + (((0 : Int) : Real) * (a * a * b * f + a * c * d * d + a * e * f * f + b * b * d * e + b * c * e * e + c * c * d * f) + (((0 : Int) : Real) * (a * a * c * c + a * a * e * e + b * b * c * c + b * b * f * f + d * d * e * e + d * d * f * f) + (((0 : Int) : Real) * (a * a * c * d + a * b * b * f + a * e * e * f + b * c * c * e + b * d * d * e + c * d * f * f) + (((0 : Int) : Real) * (a * a * c * e + a * b * c * c + a * d * e * e + b * b * c * f + b * d * f * f + d * d * e * f) + (((0 : Int) : Real) * (a * a * c * f + a * b * e * e + a * d * f * f + b * b * e * f + b * c * c * d + c * d * d * e) + (((0 : Int) : Real) * (a * a * d * e + a * b * b * c + a * c * c * e + b * c * f * f + b * d * d * f + d * e * e * f) + (((0 : Int) : Real) * (a * a * d * f + a * b * b * e + a * c * f * f + b * c * d * d + b * e * e * f + c * c * d * e) + (((0 : Int) : Real) * (a * a * e * f + a * b * f * f + a * c * c * d + b * b * c * e + b * d * e * e + c * d * d * f) + (((0 : Int) : Real) * (a * a * f * f + b * b * e * e + c * c * d * d) + (((0 : Int) : Real) * (a * b * c * d + a * b * d * e + a * b * d * f + a * c * e * f + b * c * e * f + c * d * e * f) + (((0 : Int) : Real) * (a * b * c * e + a * b * c * f + a * c * d * e + a * d * e * f + b * c * d * f + b * d * e * f) + (((0 : Int) : Real) * (a * b * e * f + a * c * d * f + b * c * d * e) + (((0 : Int) : Real) * (a * a * a * a * a + b * b * b * b * b + c * c * c * c * c + d * d * d * d * d + e * e * e * e * e + f * f * f * f * f) + (((0 : Int) : Real) * (a * a * a * a * b + a * d * d * d * d + b * b * b * b * d + c * c * c * c * f + c * e * e * e * e + e * f * f * f * f) + (((0 : Int) : Real) * (a * a * a * a * c + a * e * e * e * e + b * b * b * b * f + b * c * c * c * c + d * d * d * d * e + d * f * f * f * f) + (((0 : Int) : Real) * (a * a * a * a * d + a * b * b * b * b + b * d * d * d * d + c * c * c * c * e + c * f * f * f * f + e * e * e * e * f) + (((0 : Int) : Real) * (a * a * a * a * e + a * c * c * c * c + b * b * b * b * c + b * f * f * f * f + d * d * d * d * f + d * e * e * e * e) + (((0 : Int) : Real) * (a * a * a * a * f + a * f * f * f * f + b * b * b * b * e + b * e * e * e * e + c * c * c * c * d + c * d * d * d * d) + (((0 : Int) : Real) * (a * a * a * b * b + a * a * d * d * d + b * b * b * d * d + c * c * c * f * f + c * c * e * e * e + e * e * f * f * f) + (((0 : Int) : Real) * (a * a * a * b * c + a * c * e * e * e + a * d * d * d * e + b * b * b * d * f + b * c * c * c * f + d * e * f * f * f) + (((0 : Int) : Real) * (a * a * a * b * d + a * b * b * b * d + a * b * d * d * d + c * c * c * e * f + c * e * e * e * f + c * e * f * f * f) + (((0 : Int) : Real) * (a * a * a * b * e + a * c * c * c * f + a * d * d * d * f + b * b * b * c * d + b * e * f * f * f + c * d * e * e * e) + (((0 : Int) : Real) * (a * a * a * b * f + a * c * d * d * d + a * e * f * f * f + b * b * b * d * e + b * c * e * e * e + c * c * c * d * f) + (((0 : Int) : Real) * (a * a * a * c * c + a * a * e * e * e + b * b * b * f * f + b * b * c * c * c + d * d * d * e * e + d * d * f * f * f) + (((0 : Int) : Real) * (a * a * a * c * d + a * b * b * b * f + a * e * e * e * f + b * c * c * c * e + b * d * d * d * e + c * d * f * f * f) + (((0 : Int) : Real) * (a * a * a * c * e + a * b * c * c * c + a * d * e * e * e + b * b * b * c * f + b * d * f * f * f + d * d * d * e * f) + (((0 : Int) : Real) * (a * a * a * c * f + a * b * e * e * e + a * d * f * f * f + b * b * b * e * f + b * c * c * c * d + c * d * d * d * e) + (((0 : Int) : Real) * (a * a * a * d * d + a * a * b * b * b + b * b * d * d * d + c * c * c * e * e + c * c * f * f * f + e * e * e * f * f) + (((0 : Int) : Real) * (a * a * a * d * e + a * b * b * b * c + a * c * c * c * e + b * c * f * f * f + b * d * d * d * f + d * e * e * e * f) + (((0 : Int) : Real) * (a * a * a * d * f + a * b * b * b * e + a * c * f * f * f + b * c * d * d * d + b * e * e * e * f + c * c * c * d * e) + (((0 : Int) : Real) * (a * a * a * e * e + a * a * c * c * c + b * b * b * c * c + b * b * f * f * f + d * d * d * f * f + d * d * e * e * e) + (((0 : Int) : Real) * (a * a * a * e * f + a * b * f * f * f + a * c * c * c * d + b * b * b * c * e + b * d * e * e * e + c * d * d * d * f) + (((0 : Int) : Real) * (a * a * a * f * f + a * a * f * f * f + b * b * b * e * e + b * b * e * e * e + c * c * c * d * d + c * c * d * d * d) + (((0 : Int) : Real) * (a * a * b * b * c + a * a * d * d * e + a * c * c * e * e + b * b * d * d * f + b * c * c * f * f + d * e * e * f * f) + (((0 : Int) : Real) * (a * a * b * b * d + a * a * b * d * d + a * b * b * d * d + c * c * e * e * f + c * c * e * f * f + c * e * e * f * f) + (((0 : Int) : Real) * (a * a * b * b * e + a * a * d * d * f + a * c * c * f * f + b * b * c * d * d + b * e * e * f * f + c * c * d * e * e) + (((0 : Int) : Real) * (a * a * b * b * f + a * a * c * d * d + a * e * e * f * f + b * b * d * d * e + b * c * c * e * e + c * c * d * f * f) + (((0 : Int) : Real) * (a * a * b * c * c + a * a * c * e * e + a * d * d * e * e + b * b * c * c * f + b * b * d * f * f + d * d * e * f * f) + (((0 : Int) : Real) * (a * a * b * c * d + a * b * b * d * f + a * b * d * d * e + a * c * e * e * f + b * c * c * e * f + c * d * e * f * f) + (((0 : Int) : Real) * (a * a * b * c * e + a * b * c * c * f + a * c * d * e * e + a * d * d * e * f + b * b * c * d * f + b * d * e * f * f) + (((0 : Int) : Real) * (a * a * b * c * f + a * b * c * e * e + a * c * d * d * e + a * d * e * f * f + b * b * d * e * f + b * c * c * d * f) + (((0 : Int) : Real) * (a * a * b * d * e + a * b * b * c * d + a * b * d * d * f + a * c * c * e * f + b * c * e * f * f + c * d * e * e * f) + (((0 : Int) : Real) * (a * a * b * d * f + a * b * b * d * e + a * b * c * d * d + a * c * e * f * f + b * c * e * e * f + c * c * d * e * f) + (((0 : Int) : Real) * (a * a * b * e * e + a * a * c * c * f + a * d * d * f * f + b * b * c * c * d + b * b * e * f * f + c * d * d * e * e) + (((0 : Int) : Real) * (a * a * b * e * f + a * b * e * f * f + a * c * c * d * f + a * c * d * d * f + b * b * c * d * e + b * c * d * e * e) + (((0 : Int) : Real) * (a * a * b * f * f + a * a * e * f * f + a * c * c * d * d + b * b * c * e * e + b * b * d * e * e + c * c * d * d * f) + (((0 : Int) : Real) * (a * a * c * c * d + a * a * e * e * f + a * b * b * f * f + b * b * c * c * e + b * d * d * e * e + c * d * d * f * f) + (((0 : Int) : Real) * (a * a * c * c * e + a * a * d * e * e + a * b * b * c * c + b * b * c * f * f + b * d * d * f * f + d * d * e * e * f) + (((0 : Int) : Real) * (a * a * c * d * e + a * b * b * c * f + a * b * c * c * e + a * d * e * e * f + b * c * d * f * f + b * d * d * e * f) + (((0 : Int) : Real) * (a * a * c * d * f + a * b * b * e * f + a * b * e * e * f + a * c * d * f * f + b * c * c * d * e + b * c * d * d * e) + (((0 : Int) : Real) * (a * a * c * e * f + a * b * c * c * d + a * b * d * e * e + a * b * d * f * f + b * b * c * e * f + c * d * d * e * f) + (((0 : Int) : Real) * (a * a * c * f * f + a * a * d * f * f + a * b * b * e * e + b * b * e * e * f + b * c * c * d * d + c * c * d * d * e) + (((0 : Int) : Real) * (a * a * d * e * f + a * b * b * c * e + a * b * c * f * f + a * c * c * d * e + b * c * d * d * f + b * d * e * e * f) + (((0 : Int) : Real) * (a * b * c * d * e + a * b * c * d * f + a * b * c * e * f + a * b * d * e * f + a * c * d * e * f + b * c * d * e * f))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  ring

private theorem sum_exchange (w : Fin 79 -> Real) (a : Fin 79 -> Fin 80 -> Real)
    (b : Fin 80 -> Real) :
    Finset.univ.sum (fun j : Fin 79 =>
      w j * Finset.univ.sum (fun i : Fin 80 => a j i * b i)) =
    Finset.univ.sum (fun i : Fin 80 =>
      Finset.univ.sum (fun j : Fin 79 => w j * a j i) * b i) := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem total_identity (y : Fin 6 -> Real) :
    Finset.univ.sum (fun j : Fin 79 => (weight j : Real) * column y j) =
      (235085993889816576311765157984666540141133198301913457943358475317247902439921993661067807749666424264260927667883927091335909688994404895309820964205336194930112189539966351061350109487655497889568133638423693602817269237986224255472418058079447631305597778557451191586072416032 : Real) * ((704643072 : Real) * deficit y) := by
  have hr (i : Fin 80) :
      Finset.univ.sum (fun j : Fin 79 => (weight j : Real) * (coefficient j i : Real)) =
        (235085993889816576311765157984666540141133198301913457943358475317247902439921993661067807749666424264260927667883927091335909688994404895309820964205336194930112189539966351061350109487655497889568133638423693602817269237986224255472418058079447631305597778557451191586072416032 : Real) * (targetCoefficient i : Real) := by
    exact_mod_cast coefficient_identity i
  simp_rw [column_expansion]
  rw [sum_exchange]
  simp_rw [hr]
  calc
    _ = (235085993889816576311765157984666540141133198301913457943358475317247902439921993661067807749666424264260927667883927091335909688994404895309820964205336194930112189539966351061350109487655497889568133638423693602817269237986224255472418058079447631305597778557451191586072416032 : Real) *
        Finset.univ.sum (fun i : Fin 80 => (targetCoefficient i : Real) * orbitBasis y i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [target_expansion]

private theorem positive_column (y : Fin 6 -> Real)
    (hmax : forall i : Fin 6, y i <= mass y)
    (hlower : 2 <= 7 * mass y) (hupper : mass y <= 1)
    (j : Fin 79) (hj : j.val < 39) : 0 <= column y j := by
  have hg (u : Fin 6) : 0 <= mass (permute y u) - permute y u 0 :=
    sub_nonneg.mpr (upper_permute y hmax u 0)
  have hu (u : Fin 6) : 0 <= 1 - mass (permute y u) := by
    rw [mass_permute]
    linarith
  have hl (u : Fin 6) : 0 <= 7 * mass (permute y u) - 2 := by
    rw [mass_permute]
    linarith
  have hs0 (k : Fin 79) : 0 <= Finset.univ.sum (fun u : Fin 6 =>
      (mass (permute y u) - permute y u 0) * (quadratic (permute y u) k) ^ 2) := by
    exact Finset.sum_nonneg (fun u _ => mul_nonneg (hg u) (sq_nonneg _))
  have hs1 (k : Fin 79) : 0 <= Finset.univ.sum (fun u : Fin 6 =>
      (1 - mass (permute y u)) * (quadratic (permute y u) k) ^ 2) := by
    exact Finset.sum_nonneg (fun u _ => mul_nonneg (hu u) (sq_nonneg _))
  have hs2 (k : Fin 79) : 0 <= Finset.univ.sum (fun u : Fin 6 =>
      (7 * mass (permute y u) - 2) * (quadratic (permute y u) k) ^ 2) := by
    exact Finset.sum_nonneg (fun u _ => mul_nonneg (hl u) (sq_nonneg _))
  have h0 := sub_nonneg.mpr (hmax 0)
  have h1 := sub_nonneg.mpr (hmax 1)
  have h2 := sub_nonneg.mpr (hmax 2)
  have h3 := sub_nonneg.mpr (hmax 3)
  have h4 := sub_nonneg.mpr (hmax 4)
  have h5 := sub_nonneg.mpr (hmax 5)
  have hU := sub_nonneg.mpr hupper
  have hF : 0 <= (704643072 : Real) * (1 - mass y) *
      ((mass y - y 0) * (mass y - y 1) * (mass y - y 3) +
        (mass y - y 2) * (mass y - y 4) * (mass y - y 5)) := by positivity
  fin_cases j <;> norm_num at hj
  all_goals dsimp only [column]
  all_goals first
    | exact mul_nonneg (show (0 : Real) <= 42 by norm_num) (hs0 _)
    | exact mul_nonneg (show (0 : Real) <= 42 by norm_num) (hs1 _)
    | exact mul_nonneg (show (0 : Real) <= 6 by norm_num) (hs2 _)
    | exact hF

private theorem ideal_column_zero (y : Fin 6 -> Real)
    (h1 : correlation y 1 = 0) (h2 : correlation y 2 = 0)
    (h3 : correlation y 3 = 0) (j : Fin 79) (hj : 39 <= j.val) :
    column y j = 0 := by
  have hz := permuted_zero y h1 h2 h3
  fin_cases j <;> norm_num at hj
  all_goals dsimp only [column]
  all_goals simp only [hz, zero_mul, Finset.sum_const_zero, mul_zero]

/-- Uniform cyclic cubic stability, without a restriction to a two-level sector. -/
theorem normalized_stability (y : Fin 6 -> Real)
    (hmax : forall i : Fin 6, y i <= mass y)
    (h1 : correlation y 1 = 0) (h2 : correlation y 2 = 0)
    (h3 : correlation y 3 = 0) :
    8 * (1 - mass y) <=
      7 * (1 - Finset.univ.sum (fun i : Fin 7 => coordinates y i ^ 3)) := by
  have hb := admissible_peak y hmax h1 h2 h3
  have hs : 0 <= Finset.univ.sum (fun j : Fin 79 => (weight j : Real) * column y j) := by
    apply Finset.sum_nonneg
    intro j _
    by_cases hj : j.val < 39
    case pos =>
      have hw : 0 <= (weight j : Real) := by exact_mod_cast positive_weights j hj
      exact mul_nonneg hw (positive_column y hmax hb.1 hb.2 j hj)
    case neg =>
      simpa only [ideal_column_zero y h1 h2 h3 j (Nat.le_of_not_gt hj), mul_zero]
        using (le_refl (0 : Real))
  rw [total_identity] at hs
  have hD : 0 < (235085993889816576311765157984666540141133198301913457943358475317247902439921993661067807749666424264260927667883927091335909688994404895309820964205336194930112189539966351061350109487655497889568133638423693602817269237986224255472418058079447631305597778557451191586072416032 : Real) := by norm_num
  by_contra h
  have hn : deficit y < 0 := by unfold deficit; linarith
  have hinner := mul_neg_of_pos_of_neg (show (0 : Real) < 704643072 by norm_num) hn
  have hbad := mul_neg_of_pos_of_neg hD hinner
  linarith only [hs, hbad]

end Metaplectic.G2Seven.Uniform
