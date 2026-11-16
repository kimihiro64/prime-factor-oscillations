/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianInjectiveMatrixRestriction
import PrimeFactorOscillations.Helpers.HamiltonianPrimeCrossBlock
import PrimeFactorOscillations.Helpers.HamiltonianPrimeRealFiniteModes

/-! # Uniform bounded real Fourier factors for the actual odd/even prime kernel -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

theorem hamiltonian_prime_cross_finite_modes_uniform
    (eta : Real) (hEta : 0 < eta) :
    exists K : Nat, 0 < K /\
      exists M0 : Nat, 1 <= M0 /\
        forall m : Nat, M0 <= m ->
          exists A : Matrix (Fin m)
            (Sum (lpfRationalCenters (27 * K ^ 4)) (lpfRationalCenters (27 * K ^ 4))) Real,
          exists B : Matrix
            (Sum (lpfRationalCenters (27 * K ^ 4)) (lpfRationalCenters (27 * K ^ 4))) (Fin m) Real,
            norm (hamiltonianPrimeCrossBlock m - A * B) <= eta /\
              norm A <=
                (Fintype.card (Sum (lpfRationalCenters (27 * K ^ 4))
                  (lpfRationalCenters (27 * K ^ 4))) : Real) + 1 /\
              norm B <=
                (Fintype.card (Sum (lpfRationalCenters (27 * K ^ 4))
                  (lpfRationalCenters (27 * K ^ 4))) : Real) + 1 := by
  choose K hK N0 hN0 hApprox using
    hamiltonian_prime_real_finite_mode_approximation_uniform eta hEta
  refine Exists.intro K (And.intro hK (Exists.intro N0 (And.intro hN0 ?_)))
  intro m hm
  have hmPos : 0 < m := by omega
  have hnPos : 0 < 2 * m := by omega
  letI : NeZero (2 * m) := NeZero.mk (Nat.ne_of_gt hnPos)
  let Q := hamiltonianPrimeCutoff (2 * (2 * m))
  choose R hGrid hDivM hEven hDiv using
    hamiltonian_common_auxiliary_period (2 * (2 * m)) Q (by omega)
  have hR : 0 < R := by omega
  letI : NeZero R := NeZero.mk (Nat.ne_of_gt hR)
  have hError := hApprox (n := 2 * m) (R := R) (by omega : N0 <= 2 * m)
    hGrid hDivM hDiv
  choose U V hModel hU hV using
    hamiltonian_prime_real_finite_mode_factors (2 * m) R K hnPos
  let f : Fin m -> Fin (2 * m) := fun i => hamiltonianParityIndex m (Sum.inl i)
  let g : Fin m -> Fin (2 * m) := fun i => hamiltonianParityIndex m (Sum.inr i)
  have hf : Function.Injective f := by
    intro i j h
    exact Sum.inl.inj ((hamiltonian_parity_index_bijective m).1 h)
  have hg : Function.Injective g := by
    intro i j h
    exact Sum.inr.inj ((hamiltonian_parity_index_bijective m).1 h)
  let A := U.submatrix f id
  let B := V.submatrix id g
  have hCrossModel :
      (hamiltonianPrimeRealFiniteModeModel (2 * m) R K).submatrix f g = A * B := by
    rw [hModel, hamiltonian_restricted_product]
  have hIdentity : hamiltonianPrimeCrossBlock m - A * B =
      (hamiltonianUnweightedPrimeMatrix (2 * m) -
        hamiltonianPrimeRealFiniteModeModel (2 * m) R K).submatrix f g := by
    rw [<- hCrossModel]
    rfl
  have hA : norm A <=
      (Fintype.card (Sum (lpfRationalCenters (27 * K ^ 4))
        (lpfRationalCenters (27 * K ^ 4))) : Real) + 1 :=
    (hamiltonian_injective_rows_norm f hf U).trans hU
  have hB : norm B <=
      (Fintype.card (Sum (lpfRationalCenters (27 * K ^ 4))
        (lpfRationalCenters (27 * K ^ 4))) : Real) + 1 :=
    (hamiltonian_injective_columns_norm g hg V).trans hV
  refine Exists.intro A (Exists.intro B (And.intro ?_ (And.intro hA hB)))
  rw [hIdentity]
  exact (hamiltonian_injective_submatrix_norm f g hf hg _).trans hError

end PrimeFactorOscillations.LPF
