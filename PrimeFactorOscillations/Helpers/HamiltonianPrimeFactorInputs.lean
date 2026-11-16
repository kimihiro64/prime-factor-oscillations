/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianFactorCutGeometry
import PrimeFactorOscillations.Helpers.HamiltonianPrimeCrossBlock
import PrimeFactorOscillations.Helpers.HamiltonianPrimeCuts

/-! # Actual integer prime-edge inputs to the integral factor theorem -/

set_option autoImplicit false
set_option Elab.async false

open Finset

noncomputable section

namespace PrimeFactorOscillations.LPF

def hamiltonianPrimeFactorEdges (m : Nat) : Finset (Prod (Fin m) (Fin m)) :=
  univ.filter (fun e => Nat.Prime (2 * e.1.val + 2 * e.2.val + 3))

def hamiltonianPrimeFactorScale (m : Nat) : Real :=
  Real.log (2 * m : Nat) / (2 * m : Nat)

def hamiltonianPrimeFactorDegree (m : Nat) : Real :=
  (2 * m : Nat) / Real.log (2 * m : Nat)

theorem hamiltonian_prime_factor_scalars (m : Nat) (hm : 1 <= m) :
    And (0 < hamiltonianPrimeFactorScale m)
      (And (0 < hamiltonianPrimeFactorDegree m)
        (hamiltonianPrimeFactorScale m * hamiltonianPrimeFactorDegree m = 1)) := by
  have hn : 0 < ((2 * m : Nat) : Real) := Nat.cast_pos.mpr (by omega)
  have hl : 0 < Real.log (2 * m : Nat) := Real.log_pos (by
    exact_mod_cast (by omega : 1 < 2 * m))
  unfold hamiltonianPrimeFactorScale hamiltonianPrimeFactorDegree
  refine And.intro (div_pos hl hn) (And.intro (div_pos hn hl) ?_)
  field_simp [ne_of_gt hn, ne_of_gt hl]

theorem hamiltonian_prime_factor_cross_entry (m : Nat) (i j : Fin m) :
    hamiltonianPrimeCrossBlock m i j =
      hamiltonianPrimeFactorScale m *
        (if Membership.mem (hamiltonianPrimeFactorEdges m) (i, j)
          then (1 : Real) else 0) := by
  rw [hamiltonian_prime_cross_formula]
  by_cases hp : Nat.Prime (2 * i.val + 2 * j.val + 3) <;>
    simp [hamiltonianPrimeFactorEdges, hamiltonianPrimeFactorScale, hp]

theorem hamiltonian_prime_factor_adjacency_scale (m : Nat) :
    (hamiltonianUnweightedPrimeMatrix (2 * m)).submatrix
      (hamiltonianParityEquiv m) (hamiltonianParityEquiv m) =
    SMul.smul (hamiltonianPrimeFactorScale m)
      (hamiltonianFactorAdjacency (hamiltonianPrimeFactorEdges m)) := by
  rw [hamiltonian_prime_cross_reindex]
  ext i j
  change bipartiteLift (hamiltonianPrimeCrossBlock m) i j =
    hamiltonianPrimeFactorScale m * hamiltonianFactorAdjacency (hamiltonianPrimeFactorEdges m) i j
  cases i <;> cases j <;>
    simp [bipartiteLift, Matrix.fromBlocks, Matrix.transpose,
      hamiltonianFactorAdjacency, hamiltonianPrimeFactorEdges,
      hamiltonianPrimeFactorScale, hamiltonian_prime_cross_formula,
      Matrix.smul_apply, smul_eq_mul]

theorem hamiltonian_prime_factor_left_degree (m : Nat) (i : Fin m) :
    univ.sum (fun j => hamiltonianPrimeCrossBlock m i j) =
      hamiltonianPrimeFactorScale m *
        (((hamiltonianPrimeFactorEdges m).filter (fun e => e.1 = i)).card : Real) := by
  simp_rw [hamiltonian_prime_factor_cross_entry]
  rw [<- mul_sum, hamiltonian_factor_left_row_count]

theorem hamiltonian_prime_factor_right_degree (m : Nat) (j : Fin m) :
    univ.sum (fun i => hamiltonianPrimeCrossBlock m i j) =
      hamiltonianPrimeFactorScale m *
        (((hamiltonianPrimeFactorEdges m).filter (fun e => e.2 = j)).card : Real) := by
  simp_rw [hamiltonian_prime_factor_cross_entry]
  rw [<- mul_sum, hamiltonian_factor_right_row_count]

theorem hamiltonian_prime_factor_degree_uniform (eps : Real) (heps : 0 < eps) :
    Exists (fun M0 : Nat => And (256 <= M0)
      (forall m : Nat, M0 <= m ->
        And (forall a : Fin m,
          (1 - eps) * hamiltonianPrimeFactorDegree m <=
            (((hamiltonianPrimeFactorEdges m).filter (fun e => e.1 = a)).card : Real) /\
          (((hamiltonianPrimeFactorEdges m).filter (fun e => e.1 = a)).card : Real) <=
            (1 + eps) * hamiltonianPrimeFactorDegree m)
        (forall b : Fin m,
          (1 - eps) * hamiltonianPrimeFactorDegree m <=
            (((hamiltonianPrimeFactorEdges m).filter (fun e => e.2 = b)).card : Real) /\
          (((hamiltonianPrimeFactorEdges m).filter (fun e => e.2 = b)).card : Real) <=
            (1 + eps) * hamiltonianPrimeFactorDegree m))) := by
  choose M0 hM0 hdegree using hamiltonian_prime_cross_degree_uniform eps heps
  refine Exists.intro (max 256 M0) (And.intro (le_max_left _ _) ?_)
  intro m hm
  have hm1 : 1 <= m := by omega
  have hs := hamiltonian_prime_factor_scalars m hm1
  have hconvert (v : Real)
      (hv : abs (hamiltonianPrimeFactorScale m * v - 1) <= eps) :
      (1 - eps) * hamiltonianPrimeFactorDegree m <= v /\
        v <= (1 + eps) * hamiltonianPrimeFactorDegree m := by
    have hlo : 1 - eps <= hamiltonianPrimeFactorScale m * v := by
      linarith only [(abs_le.mp hv).1]
    have hhi : hamiltonianPrimeFactorScale m * v <= 1 + eps := by
      linarith only [(abs_le.mp hv).2]
    have hc : (hamiltonianPrimeFactorScale m * v) *
        hamiltonianPrimeFactorDegree m = v := by
      calc
        _ = (hamiltonianPrimeFactorScale m * hamiltonianPrimeFactorDegree m) * v := by ring
        _ = v := by rw [hs.2.2, one_mul]
    have hL := mul_le_mul_of_nonneg_right hlo (le_of_lt hs.2.1)
    have hU := mul_le_mul_of_nonneg_right hhi (le_of_lt hs.2.1)
    rw [hc] at hL hU
    exact And.intro hL hU
  have hd := hdegree m (by omega : M0 <= m)
  constructor
  . intro a
    apply hconvert
    simpa only [hamiltonian_prime_factor_left_degree] using hd.1 a
  . intro b
    apply hconvert
    simpa only [hamiltonian_prime_factor_right_degree] using hd.2 b

theorem hamiltonian_prime_factor_cut_weight (m : Nat)
    (S T : Finset (Fin m)) :
    hamiltonianCutBoundary (hamiltonianUnweightedPrimeMatrix (2 * m))
      ((S.disjSum T).image (hamiltonianParityEquiv m)) =
      hamiltonianPrimeFactorScale m *
        (((hamiltonianFactorCross (hamiltonianPrimeFactorEdges m) S T).card : Real) +
          ((hamiltonianFactorCross (hamiltonianPrimeFactorEdges m)
            (Compl.compl S) (Compl.compl T)).card : Real)) := by
  rw [hamiltonian_cut_reindex, hamiltonian_prime_factor_adjacency_scale,
    hamiltonian_cut_scalar, hamiltonian_factor_full_boundary]

theorem hamiltonian_prime_factor_cut_uniform :
    Exists (fun M0 : Nat => And (256 <= M0)
      (forall m : Nat, M0 <= m -> forall S T : Finset (Fin m),
        (1 / 5 : Real) * hamiltonianPrimeFactorDegree m *
          min ((S.card : Real) + (T.card : Real))
            (((Compl.compl S).card : Real) + ((Compl.compl T).card : Real)) <=
        ((hamiltonianFactorCross (hamiltonianPrimeFactorEdges m) S T).card : Real) +
          ((hamiltonianFactorCross (hamiltonianPrimeFactorEdges m)
            (Compl.compl S) (Compl.compl T)).card : Real))) := by
  choose M0 hM0 hcut using hamiltonian_prime_cut_weight_uniform
  refine Exists.intro M0 (And.intro hM0 ?_)
  intro m hm S T
  have hs := hamiltonian_prime_factor_scalars m (by omega : 1 <= m)
  have hcard :
      (((S.disjSum T).image (hamiltonianParityEquiv m)).card : Real) =
        (S.card : Real) + (T.card : Real) := by
    rw [card_image_of_injective _ (hamiltonianParityEquiv m).injective,
      card_disjSum, Nat.cast_add]
  have hS : ((Compl.compl S).card : Real) = (m : Real) - (S.card : Real) := by
    rw [card_compl, Nat.cast_sub (card_le_univ S), Fintype.card_fin]
  have hT : ((Compl.compl T).card : Real) = (m : Real) - (T.card : Real) := by
    rw [card_compl, Nat.cast_sub (card_le_univ T), Fintype.card_fin]
  have hcomp : ((2 * m : Nat) : Real) -
      (((S.disjSum T).image (hamiltonianParityEquiv m)).card : Real) =
      ((Compl.compl S).card : Real) + ((Compl.compl T).card : Real) := by
    rw [hcard, hS, hT]
    push_cast
    ring
  have hraw := hcut (2 * m) (by omega) ((S.disjSum T).image (hamiltonianParityEquiv m))
  rw [hamiltonian_prime_factor_cut_weight, hcomp, hcard] at hraw
  have hscaled := mul_le_mul_of_nonneg_left hraw (le_of_lt hs.2.1)
  have hcancel : hamiltonianPrimeFactorDegree m *
      (hamiltonianPrimeFactorScale m *
        (((hamiltonianFactorCross (hamiltonianPrimeFactorEdges m) S T).card : Real) +
          ((hamiltonianFactorCross (hamiltonianPrimeFactorEdges m)
            (Compl.compl S) (Compl.compl T)).card : Real))) =
      ((hamiltonianFactorCross (hamiltonianPrimeFactorEdges m) S T).card : Real) +
          ((hamiltonianFactorCross (hamiltonianPrimeFactorEdges m)
            (Compl.compl S) (Compl.compl T)).card : Real) := by
    calc
      _ = (hamiltonianPrimeFactorScale m * hamiltonianPrimeFactorDegree m) *
        (((hamiltonianFactorCross (hamiltonianPrimeFactorEdges m) S T).card : Real) +
          ((hamiltonianFactorCross (hamiltonianPrimeFactorEdges m)
            (Compl.compl S) (Compl.compl T)).card : Real)) := by ring
      _ = _ := by rw [hs.2.2, one_mul]
  rw [hcancel] at hscaled
  nlinarith only [hscaled]

end PrimeFactorOscillations.LPF
