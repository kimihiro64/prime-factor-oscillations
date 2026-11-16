/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPrimeFactorEigenvalues
import PrimeFactorOscillations.Helpers.HamiltonianPrimeFactorLimits

/-! # One near-optimal prime-factor family with its actual nontrivial spectrum

The same family and full-support stochastic reference work on every terminal
interval. The epsilon threshold depends on the requested error, not the family.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

theorem hamiltonian_prime_factor_constant_eigenvector
    (B : Real) (m : Nat) (F : Finset (Prod (Fin m) (Fin m)))
    (h : HamiltonianPrimeFactorPacket B m F) (i : Fin (2 * m)) :
    (hamiltonianPrimeFactorAdjacency m F).mulVec (fun _ => (1 : Real)) i =
      (hamiltonianPrimeFactorRank B m : Real) := by
  simpa only [Matrix.mulVec, dotProduct, mul_one] using
    hamiltonian_prime_factor_physical_degree m (hamiltonianPrimeFactorRank B m) F
      h.left_regular h.right_regular i

def hamiltonianPrimeFactorParity (m : Nat) (i : Fin (2 * m)) : Real :=
  Sum.elim (fun _ : Fin m => (1 : Real)) (fun _ : Fin m => (-1 : Real))
    ((hamiltonianParityEquiv m).symm i)

theorem hamiltonian_prime_factor_parity_eigenvector
    (B : Real) (m : Nat) (F : Finset (Prod (Fin m) (Fin m)))
    (h : HamiltonianPrimeFactorPacket B m F) (i : Fin (2 * m)) :
    (hamiltonianPrimeFactorAdjacency m F).mulVec (hamiltonianPrimeFactorParity m) i =
      -(hamiltonianPrimeFactorRank B m : Real) * hamiltonianPrimeFactorParity m i := by
  let sign : Sum (Fin m) (Fin m) -> Real :=
    Sum.elim (fun _ => (1 : Real)) (fun _ => (-1 : Real))
  have hSigned : forall s : Sum (Fin m) (Fin m),
      Finset.univ.sum (fun t => hamiltonianFactorAdjacency F s t * sign t) =
        -(sign s) * Finset.univ.sum (fun t => hamiltonianFactorAdjacency F s t) := by
    intro s
    cases s <;>
      simp [Fintype.sum_sum_type, hamiltonianFactorAdjacency, sign, Finset.sum_neg_distrib]
  change Finset.univ.sum (fun j => hamiltonianFactorAdjacency F
    ((hamiltonianParityEquiv m).symm i) ((hamiltonianParityEquiv m).symm j) *
      sign ((hamiltonianParityEquiv m).symm j)) = _
  rw [hamiltonian_sum_reindex (hamiltonianParityEquiv m).symm
    (fun t => hamiltonianFactorAdjacency F ((hamiltonianParityEquiv m).symm i) t * sign t)]
  rw [hSigned]
  have hRow := hamiltonian_prime_factor_physical_degree m (hamiltonianPrimeFactorRank B m) F
    h.left_regular h.right_regular i
  change Finset.univ.sum (fun j => hamiltonianFactorAdjacency F
    ((hamiltonianParityEquiv m).symm i) ((hamiltonianParityEquiv m).symm j)) = _ at hRow
  rw [hamiltonian_sum_reindex (hamiltonianParityEquiv m).symm] at hRow
  rw [hRow]
  change -(hamiltonianPrimeFactorParity m i) * (hamiltonianPrimeFactorRank B m : Real) = _
  ring

theorem hamiltonian_prime_factor_degree_upper
    (B : Real) (m : Nat) (hm : 1 <= m) (F : Finset (Prod (Fin m) (Fin m)))
    (h : HamiltonianPrimeFactorPacket B m F)
    (K : Finset (Prod (Fin m) (Fin m))) (r : Nat)
    (hK : K <= hamiltonianPrimeFactorEdges m)
    (hRegular : forall a, (K.filter (fun e => e.1 = a)).card = r) :
    (r : Real) <= (1 + hamiltonianPrimeFactorDefect B m) * hamiltonianPrimeFactorDegree m := by
  let a : Fin m := Fin.mk 0 (by omega)
  have hSub : K.filter (fun e => e.1 = a) <=
      (hamiltonianPrimeFactorEdges m).filter (fun e => e.1 = a) := by
    intro e he
    have hp := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr (And.intro (hK hp.1) hp.2)
  have hCard := Finset.card_le_card hSub
  rw [hRegular a] at hCard
  exact (Nat.cast_le.mpr hCard).trans (h.original_left_degree a).2

structure HamiltonianPrimeFactorSpectralWindow (B eta : Real) (m : Nat)
    (F : Finset (Prod (Fin m) (Fin m)))
    (P : Matrix (Fin (2 * m)) (Fin (2 * m)) Real) : Prop where
  reference : HamiltonianPrimeFactorReferencePacket B m F P
  relative_rank :
    abs ((hamiltonianPrimeFactorRank B m : Real) / hamiltonianPrimeFactorDegree m - 1) <= eta
  factor_reference : norm (hamiltonianPrimeNormalizedFactor B m F - P) <= eta
  reference_original : norm (P - hamiltonianUnweightedPrimeMatrix (2 * m)) <= eta
  factor_original :
    norm (hamiltonianPrimeNormalizedFactor B m F - hamiltonianUnweightedPrimeMatrix (2 * m)) <= eta
  factor_gap :
    norm (hamiltonianPrimeNormalizedFactor B m F -
      hamiltonianRealConstantParityMatrix (2 * m)) <= (1 / 2 : Real) + eta
  reference_gap :
    norm (P - hamiltonianRealConstantParityMatrix (2 * m)) <= (1 / 2 : Real) + eta
  degree_optimal : forall (K : Finset (Prod (Fin m) (Fin m))) (r : Nat),
    K <= hamiltonianPrimeFactorEdges m ->
    (forall a, (K.filter (fun e => e.1 = a)).card = r) ->
    (r : Real) / hamiltonianPrimeFactorDegree m <= 1 + eta
  eigenvalues : forall i : Fin (2 * m),
    Not ((hamiltonian_prime_factor_hermitian m F).eigenvalues i =
      (hamiltonianPrimeFactorRank B m : Real)) ->
    Not ((hamiltonian_prime_factor_hermitian m F).eigenvalues i =
      -(hamiltonianPrimeFactorRank B m : Real)) ->
    abs ((hamiltonian_prime_factor_hermitian m F).eigenvalues i) <=
      ((1 / 2 : Real) + eta) * (hamiltonianPrimeFactorRank B m : Real)

theorem hamiltonian_prime_factor_spectral_terminal
    (B eta : Real) (hB : 0 < B) (hEta : 0 < eta) :
    Exists (fun M0 : Nat => And (256 <= M0)
      (forall m : Nat, M0 <= m ->
        forall (F : Finset (Prod (Fin m) (Fin m)))
          (P : Matrix (Fin (2 * m)) (Fin (2 * m)) Real),
        HamiltonianPrimeFactorReferencePacket B m F P ->
        HamiltonianPrimeFactorSpectralWindow B eta m F P)) := by
  have hHalf : 0 < eta / 2 := div_pos hEta (by norm_num)
  choose Me hMe hError using
    hamiltonian_prime_factor_packet_deviations_terminal B (eta / 2) hB hHalf
  choose Mg hMg hGap using hamiltonian_unweighted_prime_operator_gap (eta / 2) hHalf
  choose Md hMd hDefect using hamiltonian_prime_factor_error_terminal B eta hB hEta
  refine Exists.intro (max Me (max Mg Md)) (And.intro (hMe.trans (le_max_left _ _)) ?_)
  intro m hm F P h
  have hme : Me <= m := by omega
  have hmg : Mg <= 2 * m := by omega
  have hm1 : 1 <= m := by omega
  have he := hError m hme F P h
  have hg := hGap (2 * m) hmg
  have hd := hDefect m (by omega : Md <= m)
  have hLog : 0 < Real.log (2 * m : Nat) := by linarith only [h.factor_packet.log_large]
  have hTail : 0 <= (24 : Real) / Real.log (2 * m : Nat) := div_nonneg (by norm_num) hLog.le
  have hEps : hamiltonianPrimeFactorDefect B m <= eta := by
    linarith only [hd, hTail, h.factor_packet.defect_positive]
  have hFactor :
      norm (hamiltonianPrimeNormalizedFactor B m F -
        hamiltonianRealConstantParityMatrix (2 * m)) <= (1 / 2 : Real) + eta := by
    have ht := norm_add_le
      (hamiltonianPrimeNormalizedFactor B m F - hamiltonianUnweightedPrimeMatrix (2 * m))
      (hamiltonianUnweightedPrimeMatrix (2 * m) - hamiltonianRealConstantParityMatrix (2 * m))
    have hid :
        (hamiltonianPrimeNormalizedFactor B m F - hamiltonianUnweightedPrimeMatrix (2 * m)) +
          (hamiltonianUnweightedPrimeMatrix (2 * m) -
            hamiltonianRealConstantParityMatrix (2 * m)) =
        hamiltonianPrimeNormalizedFactor B m F - hamiltonianRealConstantParityMatrix (2 * m) := by
      abel
    rw [hid] at ht
    linarith only [ht, he.2.2.2, hg]
  have hReference :
      norm (P - hamiltonianRealConstantParityMatrix (2 * m)) <= (1 / 2 : Real) + eta := by
    have ht := norm_add_le (P - hamiltonianUnweightedPrimeMatrix (2 * m))
      (hamiltonianUnweightedPrimeMatrix (2 * m) - hamiltonianRealConstantParityMatrix (2 * m))
    have hid :
        (P - hamiltonianUnweightedPrimeMatrix (2 * m)) +
          (hamiltonianUnweightedPrimeMatrix (2 * m) -
            hamiltonianRealConstantParityMatrix (2 * m)) =
        P - hamiltonianRealConstantParityMatrix (2 * m) := by abel
    rw [hid] at ht
    linarith only [ht, he.2.2.1, hg]
  refine {
    reference := h
    relative_rank := he.1.trans (by linarith only [hEta])
    factor_reference := he.2.1.trans (by linarith only [hEta])
    reference_original := he.2.2.1.trans (by linarith only [hEta])
    factor_original := he.2.2.2.trans (by linarith only [hEta])
    factor_gap := hFactor
    reference_gap := hReference
    degree_optimal := ?_
    eigenvalues := ?_ }
  . intro K r hK hRegular
    have hUpper := hamiltonian_prime_factor_degree_upper B m hm1 F h.factor_packet K r hK hRegular
    have hD := (hamiltonian_prime_factor_scalars m hm1).2.1
    calc
      (r : Real) / hamiltonianPrimeFactorDegree m <=
          ((1 + hamiltonianPrimeFactorDefect B m) * hamiltonianPrimeFactorDegree m) /
            hamiltonianPrimeFactorDegree m :=
        div_le_div_of_nonneg_right hUpper hD.le
      _ = 1 + hamiltonianPrimeFactorDefect B m := by field_simp [ne_of_gt hD]
      _ <= 1 + eta := by linarith only [hEps]
  . intro i hp hn
    exact hamiltonian_prime_factor_native_eigenvalue_error B m hm1 F h.factor_packet
      ((1 / 2 : Real) + eta) i hp hn hFactor

theorem hamiltonian_prime_near_optimal_factor_family :
    Exists (fun B : Real => And (0 < B)
      (Exists (fun M0 : Nat => And (256 <= M0)
        (Exists (fun F : (m : Nat) -> Finset (Prod (Fin m) (Fin m)) =>
          Exists (fun P : (m : Nat) -> Matrix (Fin (2 * m)) (Fin (2 * m)) Real =>
            And (forall m : Nat, M0 <= m ->
              HamiltonianPrimeFactorReferencePacket B m (F m) (P m))
            (forall eta : Real, 0 < eta ->
              Exists (fun M : Nat => And (M0 <= M)
                (forall m : Nat, M <= m ->
                  HamiltonianPrimeFactorSpectralWindow B eta m (F m) (P m)))))))))) := by
  choose B hB M0 hM0 F P hFamily using hamiltonian_prime_factor_reference_family
  refine Exists.intro B (And.intro hB (Exists.intro M0 (And.intro hM0
    (Exists.intro F (Exists.intro P (And.intro hFamily ?_))))))
  intro eta hEta
  choose Me hMe hWindow using hamiltonian_prime_factor_spectral_terminal B eta hB hEta
  refine Exists.intro (max M0 Me) (And.intro (le_max_left _ _) ?_)
  intro m hm
  exact hWindow m (by omega) (F m) (P m) (hFamily m (by omega))

end PrimeFactorOscillations.LPF
