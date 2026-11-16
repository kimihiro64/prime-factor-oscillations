/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianFactorNormalization
import PrimeFactorOscillations.Helpers.HamiltonianPrimeFactorFamily

/-! # Quantitative normalization of one actual prime-factor family -/

set_option autoImplicit false
set_option Elab.async false

open Finset
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

def hamiltonianPrimeNormalizedFactor (B : Real) (m : Nat)
    (F : Finset (Prod (Fin m) (Fin m))) : Matrix (Fin (2 * m)) (Fin (2 * m)) Real :=
  SMul.smul (1 / (hamiltonianPrimeFactorRank B m : Real))
    (hamiltonianPrimeFactorAdjacency m F)

theorem hamiltonian_prime_factor_full_adjacency (m : Nat) (hm : 1 <= m) :
    SMul.smul (hamiltonianPrimeFactorDegree m) (hamiltonianUnweightedPrimeMatrix (2 * m)) =
      hamiltonianPrimeFactorAdjacency m (hamiltonianPrimeFactorEdges m) := by
  have hs := hamiltonian_prime_factor_scalars m hm
  ext i j
  have hp := congrArg (fun M => M i j) (hamiltonian_prime_factor_physical_scale m)
  change hamiltonianUnweightedPrimeMatrix (2 * m) i j =
    hamiltonianPrimeFactorScale m *
      hamiltonianPrimeFactorAdjacency m (hamiltonianPrimeFactorEdges m) i j at hp
  change hamiltonianPrimeFactorDegree m * hamiltonianUnweightedPrimeMatrix (2 * m) i j =
    hamiltonianPrimeFactorAdjacency m (hamiltonianPrimeFactorEdges m) i j
  rw [hp]
  calc
    _ = (hamiltonianPrimeFactorScale m * hamiltonianPrimeFactorDegree m) *
        hamiltonianPrimeFactorAdjacency m (hamiltonianPrimeFactorEdges m) i j := by ring
    _ = _ := by rw [hs.2.2, one_mul]

theorem hamiltonian_prime_factor_original_norm
    (B : Real) (m : Nat) (hm : 1 <= m)
    (F : Finset (Prod (Fin m) (Fin m))) (h : HamiltonianPrimeFactorPacket B m F) :
    norm (hamiltonianUnweightedPrimeMatrix (2 * m)) <= 1 + hamiltonianPrimeFactorDefect B m := by
  let E := hamiltonianPrimeFactorEdges m
  let d := (1 + hamiltonianPrimeFactorDefect B m) * hamiltonianPrimeFactorDegree m
  have hd : 0 <= d := mul_nonneg (by linarith only [h.defect_positive])
    (by linarith only [h.degree_lower])
  have hemptyLeft : forall a : Fin m,
      (({} : Finset (Prod (Fin m) (Fin m))).filter (fun e => e.1 = a)).card = 0 := by
    intro a
    simp
  have hemptyRight : forall b : Fin m,
      (({} : Finset (Prod (Fin m) (Fin m))).filter (fun e => e.2 = b)).card = 0 := by
    intro b
    simp
  have hnorm := hamiltonian_factor_adjacency_loss E {} 0 d (empty_subset _)
    (by simpa only [Nat.cast_zero, sub_zero] using hd)
    (fun a => (h.original_left_degree a).2) (fun b => (h.original_right_degree b).2)
    hemptyLeft hemptyRight
  have hz : hamiltonianFactorAdjacency ({} : Finset (Prod (Fin m) (Fin m))) = 0 := by
    ext i j
    cases i <;> cases j <;> simp [hamiltonianFactorAdjacency]
  simp only [hz, sub_zero, Nat.cast_zero] at hnorm
  have hphysical :
      norm (hamiltonianPrimeFactorAdjacency m E) = norm (hamiltonianFactorAdjacency E) := by
    exact hamiltonian_reindex_matrix_norm (hamiltonianParityEquiv m).symm _
  have hG : norm (hamiltonianPrimeFactorAdjacency m E) <= d := by
    rw [hphysical]
    exact hnorm
  have hs := hamiltonian_prime_factor_scalars m hm
  rw [hamiltonian_prime_factor_physical_scale, hamiltonian_matrix_real_smul_norm,
    Real.norm_of_nonneg (le_of_lt hs.1)]
  calc
    _ <= hamiltonianPrimeFactorScale m * d :=
      mul_le_mul_of_nonneg_left hG (le_of_lt hs.1)
    _ = (hamiltonianPrimeFactorScale m * hamiltonianPrimeFactorDegree m) *
        (1 + hamiltonianPrimeFactorDefect B m) := by dsimp only [d]; ring
    _ = _ := by rw [hs.2.2, one_mul]

theorem hamiltonian_prime_factor_normalized_rate
    (B : Real) (m : Nat) (hm : 1 <= m)
    (F : Finset (Prod (Fin m) (Fin m))) (h : HamiltonianPrimeFactorPacket B m F) :
    norm (hamiltonianPrimeNormalizedFactor B m F - hamiltonianUnweightedPrimeMatrix (2 * m)) <=
      62 * hamiltonianPrimeFactorDefect B m + 24 / Real.log (2 * m : Nat) := by
  have hD : 0 < hamiltonianPrimeFactorDegree m := by linarith only [h.degree_lower]
  have hepsOne : hamiltonianPrimeFactorDefect B m <= 1 := by
    linarith only [h.defect_small]
  have hf := hamiltonian_factor_floor_bounds (hamiltonianPrimeFactorDegree m)
    (hamiltonianPrimeFactorDefect B m) h.degree_lower
    (le_of_lt h.defect_positive) h.defect_small
  have hloss : norm (SMul.smul (hamiltonianPrimeFactorDegree m)
      (hamiltonianUnweightedPrimeMatrix (2 * m)) - hamiltonianPrimeFactorAdjacency m F) <=
      (1 + hamiltonianPrimeFactorDefect B m) * hamiltonianPrimeFactorDegree m -
        (hamiltonianPrimeFactorRank B m : Real) := by
    rw [hamiltonian_prime_factor_full_adjacency m hm]
    exact h.adjacency_loss
  have hnorm := hamiltonian_factor_normalization_bound
    (hamiltonianUnweightedPrimeMatrix (2 * m)) (hamiltonianPrimeFactorAdjacency m F)
    (hamiltonianPrimeFactorDegree m) (hamiltonianPrimeFactorRank B m : Real)
    (hamiltonianPrimeFactorDefect B m) hD (le_of_lt h.defect_positive) hepsOne
    h.rank_half h.rank_upper hf.2.2.1 (hamiltonian_prime_factor_original_norm B m hm F h) hloss
  have hL : 0 < Real.log (2 * m : Nat) := by linarith only [h.log_large]
  have hDL : Real.log (2 * m : Nat) / 4 <= hamiltonianPrimeFactorDegree m :=
    hamiltonian_logarithmic_degree_lower ((2 * m : Nat) : Real)
      (by exact_mod_cast (by omega : 1 < 2 * m))
  have hinv := hamiltonian_factor_reciprocal_degree (Real.log (2 * m : Nat))
    (hamiltonianPrimeFactorDegree m) hL hDL
  change norm (SMul.smul (1 / (hamiltonianPrimeFactorRank B m : Real))
    (hamiltonianPrimeFactorAdjacency m F) - hamiltonianUnweightedPrimeMatrix (2 * m)) <= _
  have hsix : 6 / hamiltonianPrimeFactorDegree m <= 24 / Real.log (2 * m : Nat) := by
    have hscaled := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : Real) <= 6)
    convert hscaled using 1 <;> ring
  linarith only [hnorm, hsix]

theorem hamiltonian_prime_factor_normalized_single_family :
    Exists (fun B : Real => And (0 < B)
      (Exists (fun M0 : Nat => And (256 <= M0)
        (Exists (fun F : (m : Nat) -> Finset (Prod (Fin m) (Fin m)) =>
          forall m : Nat, M0 <= m ->
            And (HamiltonianPrimeFactorPacket B m (F m))
              (norm (hamiltonianPrimeNormalizedFactor B m (F m) -
                hamiltonianUnweightedPrimeMatrix (2 * m)) <=
                62 * hamiltonianPrimeFactorDefect B m + 24 / Real.log (2 * m : Nat))))))) := by
  choose B hB M0 hM0 F hF using hamiltonian_prime_factor_single_family
  refine Exists.intro B (And.intro hB (Exists.intro M0 (And.intro hM0 (Exists.intro F ?_))))
  intro m hm
  exact And.intro (hF m hm)
    (hamiltonian_prime_factor_normalized_rate B m (by omega : 1 <= m) (F m) (hF m hm))

end PrimeFactorOscillations.LPF
