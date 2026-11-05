/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uniform cyclic sevenfold geometry

Real coordinates with unit mass and vanishing nontrivial cyclic correlations.
The peak and automorphism lemmas retain all seven signed coordinates.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace Metaplectic.G2Seven.Uniform

noncomputable def mass (y : Fin 6 -> Real) : Real :=
  1 - y 0 - y 1 - y 2 - y 3 - y 4 - y 5

noncomputable def coordinates (y : Fin 6 -> Real) : Fin 7 -> Real :=
  ![mass y, y 0, y 1, y 2, y 3, y 4, y 5]

noncomputable def correlation (y : Fin 6 -> Real) (h : Fin 7) : Real :=
  Finset.univ.sum (fun i : Fin 7 => coordinates y i * coordinates y (i + h))

noncomputable def permute (y : Fin 6 -> Real) (u : Fin 6) : Fin 6 -> Real :=
  ![![y 0, y 1, y 2, y 3, y 4, y 5],
    ![y 1, y 3, y 5, y 0, y 2, y 4],
    ![y 2, y 5, y 1, y 4, y 0, y 3],
    ![y 3, y 0, y 4, y 1, y 5, y 2],
    ![y 4, y 2, y 0, y 5, y 3, y 1],
    ![y 5, y 4, y 3, y 2, y 1, y 0]] u

private theorem energy_identity (y : Fin 6 -> Real) :
    mass y ^ 2 + Finset.univ.sum (fun i : Fin 6 => y i ^ 2) +
      2 * (correlation y 1 + correlation y 2 + correlation y 3) = 1 := by
  norm_num [correlation, coordinates, mass, Fin.sum_univ_succ]
  ring

private theorem gap_identity (y : Fin 6 -> Real) :
    Finset.univ.sum (fun i : Fin 6 => Finset.univ.sum (fun j : Fin 6 =>
      if i = j then 0 else (mass y - y i) * (mass y - y j))) =
      6 * mass y * (7 * mass y - 2) + 1 -
        (mass y ^ 2 + Finset.univ.sum (fun i : Fin 6 => y i ^ 2)) := by
  norm_num [mass, Fin.sum_univ_succ]
  ring

theorem admissible_peak (y : Fin 6 -> Real)
    (hmax : forall i : Fin 6, y i <= mass y)
    (h1 : correlation y 1 = 0) (h2 : correlation y 2 = 0)
    (h3 : correlation y 3 = 0) :
    2 <= 7 * mass y /\ mass y <= 1 := by
  have he : mass y ^ 2 + Finset.univ.sum (fun i : Fin 6 => y i ^ 2) = 1 := by
    simpa only [h1, h2, h3, add_zero, mul_zero] using energy_identity y
  have hy : 0 <= Finset.univ.sum (fun i : Fin 6 => y i ^ 2) := by
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hm : 0 < mass y := by
    have h0 := hmax 0
    have h1' := hmax 1
    have h2' := hmax 2
    have h3' := hmax 3
    have h4' := hmax 4
    have h5 := hmax 5
    dsimp [mass] at *
    linarith
  have hu : mass y <= 1 := by nlinarith only [he, hy, hm]
  have hc : 0 <= Finset.univ.sum (fun i : Fin 6 =>
      Finset.univ.sum (fun j : Fin 6 =>
        if i = j then 0 else (mass y - y i) * (mass y - y j))) := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    split_ifs
    case pos => exact le_refl 0
    case neg => exact mul_nonneg (sub_nonneg.mpr (hmax i)) (sub_nonneg.mpr (hmax j))
  rw [gap_identity, he] at hc
  have hl : 2 <= 7 * mass y := by
    by_contra h
    have hn : 7 * mass y - 2 < 0 := by linarith
    have hp := mul_neg_of_pos_of_neg (show 0 < 6 * mass y by positivity) hn
    nlinarith only [hp, hc]
  exact And.intro hl hu

theorem mass_permute (y : Fin 6 -> Real) (u : Fin 6) :
    mass (permute y u) = mass y := by
  fin_cases u <;> simp [mass, permute] <;> ring

theorem upper_permute (y : Fin 6 -> Real)
    (hmax : forall i : Fin 6, y i <= mass y) (u i : Fin 6) :
    permute y u i <= mass (permute y u) := by
  rw [mass_permute]
  fin_cases u <;> fin_cases i <;> simp [permute] <;> apply hmax

theorem correlation_permute (y : Fin 6 -> Real) (u : Fin 6) :
    correlation (permute y u) 1 =
      ![correlation y 1, correlation y 2, correlation y 3,
        correlation y 3, correlation y 2, correlation y 1] u := by
  fin_cases u <;>
    norm_num [correlation, coordinates, mass, permute, Fin.sum_univ_succ] <;> ring

theorem permuted_zero (y : Fin 6 -> Real)
    (h1 : correlation y 1 = 0) (h2 : correlation y 2 = 0)
    (h3 : correlation y 3 = 0) (u : Fin 6) :
    correlation (permute y u) 1 = 0 := by
  rw [correlation_permute]
  fin_cases u <;> simp [h1, h2, h3]


end Metaplectic.G2Seven.Uniform
