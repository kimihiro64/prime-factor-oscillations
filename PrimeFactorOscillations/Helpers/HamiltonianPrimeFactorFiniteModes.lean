/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPrimeCrossFiniteModes
import PrimeFactorOscillations.Helpers.HamiltonianPrimeFactorHeadline
import PrimeFactorOscillations.Helpers.HamiltonianRegularFactorKernels

/-! # Uniform bounded finite modes on the actual normalized prime factors -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

theorem hamiltonian_regular_factor_prime_cross_distance
    (m r : Nat) (F : Finset (Prod (Fin m) (Fin m))) :
    norm (hamiltonianRegularFactorCross r F - hamiltonianPrimeCrossBlock m) <=
      norm (hamiltonianRegularNormalizedAdjacency m r F -
        hamiltonianUnweightedPrimeMatrix (2 * m)) := by
  let f : Fin m -> Fin (2 * m) := fun i => hamiltonianParityIndex m (Sum.inl i)
  let g : Fin m -> Fin (2 * m) := fun i => hamiltonianParityIndex m (Sum.inr i)
  have hf : Function.Injective f := by
    intro i j h
    exact Sum.inl.inj ((hamiltonian_parity_index_bijective m).1 h)
  have hg : Function.Injective g := by
    intro i j h
    exact Sum.inr.inj ((hamiltonian_parity_index_bijective m).1 h)
  have hMatrix :
      (hamiltonianRegularNormalizedAdjacency m r F -
        hamiltonianUnweightedPrimeMatrix (2 * m)).submatrix f g =
      hamiltonianRegularFactorCross r F - hamiltonianPrimeCrossBlock m := by
    ext i j
    have hEntry := congrArg (fun M => M (Sum.inl i) (Sum.inr j))
      (hamiltonian_regular_factor_normalized_reindex m r F)
    change hamiltonianRegularNormalizedAdjacency m r F (f i) (g j) =
      hamiltonianRegularFactorCross r F i j at hEntry
    change hamiltonianRegularNormalizedAdjacency m r F (f i) (g j) -
        hamiltonianUnweightedPrimeMatrix (2 * m) (f i) (g j) =
      hamiltonianRegularFactorCross r F i j - hamiltonianPrimeCrossBlock m i j
    rw [hEntry]
    rfl
  have h := hamiltonian_injective_submatrix_norm f g hf hg
    (hamiltonianRegularNormalizedAdjacency m r F - hamiltonianUnweightedPrimeMatrix (2 * m))
  rwa [hMatrix] at h

theorem hamiltonian_prime_factor_finite_modes_terminal
    (B eta : Real) (hB : 0 < B) (hEta : 0 < eta) :
    exists K : Nat, 0 < K /\
      exists M0 : Nat, 256 <= M0 /\
        forall m : Nat, M0 <= m ->
          forall (F : Finset (Prod (Fin m) (Fin m)))
            (P : Matrix (Fin (2 * m)) (Fin (2 * m)) Real),
            HamiltonianPrimeFactorReferencePacket B m F P ->
            exists U : Matrix (Fin m)
              (Sum (lpfRationalCenters (27 * K ^ 4)) (lpfRationalCenters (27 * K ^ 4))) Real,
            exists V : Matrix
              (Sum (lpfRationalCenters (27 * K ^ 4)) (lpfRationalCenters (27 * K ^ 4))) (Fin m) Real,
              norm (hamiltonianRegularFactorCross (hamiltonianPrimeFactorRank B m) F -
                U * V) <= eta /\
              norm U <=
                (Fintype.card (Sum (lpfRationalCenters (27 * K ^ 4))
                  (lpfRationalCenters (27 * K ^ 4))) : Real) + 1 /\
              norm V <=
                (Fintype.card (Sum (lpfRationalCenters (27 * K ^ 4))
                  (lpfRationalCenters (27 * K ^ 4))) : Real) + 1 /\
              norm (centeredKernel
                (hamiltonianRegularFactorCross (hamiltonianPrimeFactorRank B m) F)
                  (1 / (m : Real))) <= (1 / 2 : Real) + eta := by
  have hHalf : 0 < eta / 2 := div_pos hEta (by norm_num)
  choose K hK M1 hM1 hCross using hamiltonian_prime_cross_finite_modes_uniform (eta / 2) hHalf
  choose M2 hM2 hWindow using hamiltonian_prime_factor_spectral_terminal B (eta / 2) hB hHalf
  refine Exists.intro K (And.intro hK (Exists.intro (max M1 M2)
    (And.intro (hM2.trans (le_max_right _ _)) ?_)))
  intro m hm F P hPacket
  have hm1 : M1 <= m := (le_max_left _ _).trans hm
  have hm2 : M2 <= m := (le_max_right _ _).trans hm
  have hPhysical := hWindow m hm2 F P hPacket
  choose U V hApprox hU hV using hCross m hm1
  have hDistance : norm
      (hamiltonianRegularFactorCross (hamiltonianPrimeFactorRank B m) F -
        hamiltonianPrimeCrossBlock m) <= eta / 2 :=
    (hamiltonian_regular_factor_prime_cross_distance m (hamiltonianPrimeFactorRank B m) F).trans
      hPhysical.factor_original
  have hCombined : norm
      (hamiltonianRegularFactorCross (hamiltonianPrimeFactorRank B m) F - U * V) <= eta := by
    have h := norm_sub_le_norm_sub_add_norm_sub
      (hamiltonianRegularFactorCross (hamiltonianPrimeFactorRank B m) F)
        (hamiltonianPrimeCrossBlock m) (U * V)
    linarith only [h, hDistance, hApprox]
  have hGap : norm (centeredKernel
      (hamiltonianRegularFactorCross (hamiltonianPrimeFactorRank B m) F)
        (1 / (m : Real))) <= (1 / 2 : Real) + eta := by
    rw [hamiltonian_regular_factor_centered_norm m _ (by omega) F]
    exact hPhysical.factor_gap.trans (by linarith only [hEta])
  exact Exists.intro U (Exists.intro V
    (And.intro hCombined (And.intro hU (And.intro hV hGap))))

end PrimeFactorOscillations.LPF
