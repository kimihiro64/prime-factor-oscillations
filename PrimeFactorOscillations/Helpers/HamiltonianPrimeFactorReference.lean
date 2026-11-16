/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPrimeFactorNormalization
import PrimeFactorOscillations.Helpers.HamiltonianPrimePhysicalScaling
import PrimeFactorOscillations.Helpers.HamiltonianSupportMixture

/-!
# One full-support stochastic reference for the chosen prime factors

Only a fixed-accuracy terminal repair is selected. Its positive support is
mixed into the same normalized factor with weight 1/(m+1).
-/

set_option autoImplicit false
set_option Elab.async false

open Finset
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

theorem hamiltonian_prime_normalized_factor_stochastic
    (B : Real) (m : Nat) (hm : 1 <= m)
    (F : Finset (Prod (Fin m) (Fin m))) (h : HamiltonianPrimeFactorPacket B m F) :
    And (forall i j, 0 <= hamiltonianPrimeNormalizedFactor B m F i j)
      (And (forall i j, hamiltonianPrimeNormalizedFactor B m F i j =
          hamiltonianPrimeNormalizedFactor B m F j i)
      (And (forall i, univ.sum (fun j => hamiltonianPrimeNormalizedFactor B m F i j) = 1)
      (And (forall j, univ.sum (fun i => hamiltonianPrimeNormalizedFactor B m F i j) = 1)
      (And (norm (hamiltonianPrimeNormalizedFactor B m F) <= 1)
        (forall i j, hamiltonianUnweightedPrimeMatrix (2 * m) i j = 0 ->
          hamiltonianPrimeNormalizedFactor B m F i j = 0))))) := by
  have hrNat : 0 < hamiltonianPrimeFactorRank B m := by
    have hp := h.rank_positive
    omega
  have hr : 0 < (hamiltonianPrimeFactorRank B m : Real) := Nat.cast_pos.mpr hrNat
  have hc : 0 <= 1 / (hamiltonianPrimeFactorRank B m : Real) :=
    div_nonneg (by norm_num) (le_of_lt hr)
  have hAdj : forall x y : Sum (Fin m) (Fin m), 0 <= hamiltonianFactorAdjacency F x y := by
    intro x y
    cases x with
    | inl a =>
      cases y with
      | inl c => exact le_refl 0
      | inr b =>
        change 0 <= (if Membership.mem F (a, b) then (1 : Real) else 0)
        split_ifs <;> norm_num
    | inr b =>
      cases y with
      | inl a =>
        change 0 <= (if Membership.mem F (a, b) then (1 : Real) else 0)
        split_ifs <;> norm_num
      | inr c => exact le_refl 0
  have hNonneg : forall i j, 0 <= hamiltonianPrimeNormalizedFactor B m F i j := by
    intro i j
    change 0 <= (1 / (hamiltonianPrimeFactorRank B m : Real)) *
      hamiltonianFactorAdjacency F ((hamiltonianParityEquiv m).symm i)
        ((hamiltonianParityEquiv m).symm j)
    exact mul_nonneg hc (hAdj _ _)
  have hSym : forall i j, hamiltonianPrimeNormalizedFactor B m F i j =
      hamiltonianPrimeNormalizedFactor B m F j i := by
    intro i j
    change (1 / (hamiltonianPrimeFactorRank B m : Real)) *
      hamiltonianFactorAdjacency F ((hamiltonianParityEquiv m).symm i)
        ((hamiltonianParityEquiv m).symm j) =
      (1 / (hamiltonianPrimeFactorRank B m : Real)) *
      hamiltonianFactorAdjacency F ((hamiltonianParityEquiv m).symm j)
        ((hamiltonianParityEquiv m).symm i)
    rw [hamiltonian_factor_adjacency_symmetric F]
  have hRow : forall i, univ.sum (fun j => hamiltonianPrimeNormalizedFactor B m F i j) = 1 := by
    intro i
    change univ.sum (fun j => (1 / (hamiltonianPrimeFactorRank B m : Real)) *
      hamiltonianPrimeFactorAdjacency m F i j) = 1
    rw [<- mul_sum, hamiltonian_prime_factor_physical_degree m (hamiltonianPrimeFactorRank B m)
      F h.left_regular h.right_regular i]
    field_simp [ne_of_gt hr]
  have hCol : forall j, univ.sum (fun i => hamiltonianPrimeNormalizedFactor B m F i j) = 1 := by
    intro j
    calc
      _ = univ.sum (fun i => hamiltonianPrimeNormalizedFactor B m F j i) :=
        sum_congr rfl (fun i _ => hSym i j)
      _ = 1 := hRow j
  have hNorm := hamiltonian_symmetric_stochastic_norm
    (hamiltonianPrimeNormalizedFactor B m F) hNonneg hSym hRow
  have hSupport : forall i j, hamiltonianUnweightedPrimeMatrix (2 * m) i j = 0 ->
      hamiltonianPrimeNormalizedFactor B m F i j = 0 := by
    intro i j hu
    by_contra hA
    have hJ : Not (hamiltonianPrimeFactorAdjacency m F i j = 0) := by
      intro hz
      apply hA
      change (1 / (hamiltonianPrimeFactorRank B m : Real)) *
        hamiltonianPrimeFactorAdjacency m F i j = 0
      rw [hz, mul_zero]
    have hp := hamiltonian_prime_factor_physical_support m hm F h.subset_prime i j hJ
    have hzero : hamiltonianPrimeFactorScale m = 0 := by
      simpa only [hamiltonianPrimeFactorScale, hamiltonianUnweightedPrimeMatrix,
        if_neg hp.1, if_pos hp.2] using hu
    exact (ne_of_gt (hamiltonian_prime_factor_scalars m hm).1) hzero
  exact And.intro hNonneg (And.intro hSym (And.intro hRow
    (And.intro hCol (And.intro hNorm hSupport))))

structure HamiltonianPrimeFactorReferencePacket (B : Real) (m : Nat)
    (F : Finset (Prod (Fin m) (Fin m)))
    (P : Matrix (Fin (2 * m)) (Fin (2 * m)) Real) : Prop where
  factor_packet : HamiltonianPrimeFactorPacket B m F
  factor_error :
    norm (hamiltonianPrimeNormalizedFactor B m F - hamiltonianUnweightedPrimeMatrix (2 * m)) <=
      62 * hamiltonianPrimeFactorDefect B m + 24 / Real.log (2 * m : Nat)
  nonnegative : forall i j, 0 <= P i j
  symmetric : forall i j, P i j = P j i
  rows : forall i, univ.sum (fun j => P i j) = 1
  columns : forall j, univ.sum (fun i => P i j) = 1
  support : forall i j, P i j = 0 <-> hamiltonianUnweightedPrimeMatrix (2 * m) i j = 0
  close_factor :
    norm (hamiltonianPrimeNormalizedFactor B m F - P) <= 2 / ((m : Real) + 1)
  close_original :
    norm (P - hamiltonianUnweightedPrimeMatrix (2 * m)) <=
      62 * hamiltonianPrimeFactorDefect B m + 24 / Real.log (2 * m : Nat) +
        2 / ((m : Real) + 1)

theorem hamiltonian_prime_factor_reference_family :
    Exists (fun B : Real => And (0 < B)
      (Exists (fun M0 : Nat => And (256 <= M0)
        (Exists (fun F : (m : Nat) -> Finset (Prod (Fin m) (Fin m)) =>
          Exists (fun P : (m : Nat) -> Matrix (Fin (2 * m)) (Fin (2 * m)) Real =>
            forall m : Nat, M0 <= m ->
              HamiltonianPrimeFactorReferencePacket B m (F m) (P m))))))) := by
  choose B hB Mf hMf F hF using hamiltonian_prime_factor_normalized_single_family
  choose Mr hMr hex using hamiltonian_prime_physical_sharp_uniform (1 / 100) (by norm_num)
  choose z hz using hex
  let R : (m : Nat) -> Matrix (Fin (2 * m)) (Fin (2 * m)) Real :=
    fun m => if h : Mr <= m then hamiltonianPrimePhysicalKernel m (z m h) else 0
  let P : (m : Nat) -> Matrix (Fin (2 * m)) (Fin (2 * m)) Real :=
    fun m => hamiltonianSupportMixture (1 / ((m : Real) + 1))
      (hamiltonianPrimeNormalizedFactor B m (F m)) (R m)
  let M0 := max Mf Mr
  refine Exists.intro B (And.intro hB (Exists.intro M0 (And.intro ?_
    (Exists.intro F (Exists.intro P ?_)))))
  . dsimp only [M0]
    omega
  . intro m hm
    have hmf : Mf <= m := by dsimp only [M0] at hm; omega
    have hmr : Mr <= m := by dsimp only [M0] at hm; omega
    have hm1 : 1 <= m := by omega
    have hf := hF m hmf
    have hA := hamiltonian_prime_normalized_factor_stochastic B m hm1 (F m) hf.1
    have hr := hz m hmr
    have hReq : R m = hamiltonianPrimePhysicalKernel m (z m hmr) := by
      simp only [R, dif_pos hmr]
    have hRN : forall i j, 0 <= R m i j := by
      rw [hReq]
      exact hr.2.2.1
    have hRR : forall i, univ.sum (fun j => R m i j) = 1 := by
      rw [hReq]
      exact hr.2.2.2.1
    have hRS : forall i j, R m i j = R m j i := by
      rw [hReq]
      exact hr.2.2.2.2.1
    have hRP : forall i j, R m i j = 0 <-> hamiltonianUnweightedPrimeMatrix (2 * m) i j = 0 := by
      rw [hReq]
      exact hr.2.2.2.2.2.1
    have hden : 0 < (m : Real) + 1 := by positivity
    have hdenOne : (1 : Real) <= (m : Real) + 1 := by
      linarith only [(Nat.cast_nonneg m : (0 : Real) <= (m : Real))]
    have hDelta : 0 < 1 / ((m : Real) + 1) := div_pos (by norm_num) hden
    have hDeltaOne : 1 / ((m : Real) + 1) <= (1 : Real) := by
      have hd := div_le_div_of_nonneg_left (by norm_num : (0 : Real) <= 1)
        (by norm_num : (0 : Real) < 1) hdenOne
      simpa only [div_one] using hd
    have hMix := hamiltonian_full_support_mixture
      (hamiltonianUnweightedPrimeMatrix (2 * m))
      (hamiltonianPrimeNormalizedFactor B m (F m)) (R m)
      (1 / ((m : Real) + 1)) hDelta hDeltaOne hA.1 hRN hA.2.1 hRS
      hA.2.2.1 hRR hA.2.2.2.2.2 hRP
    have hClose : norm (hamiltonianPrimeNormalizedFactor B m (F m) - P m) <=
        2 / ((m : Real) + 1) := by
      change norm (hamiltonianPrimeNormalizedFactor B m (F m) -
        hamiltonianSupportMixture (1 / ((m : Real) + 1))
          (hamiltonianPrimeNormalizedFactor B m (F m)) (R m)) <= _
      rw [norm_sub_rev]
      convert hMix.2.2.2.2.2 using 1 <;> ring
    have hPA : norm (P m - hamiltonianPrimeNormalizedFactor B m (F m)) <=
        2 / ((m : Real) + 1) := by
      rw [norm_sub_rev]
      exact hClose
    have htriangle : norm (P m - hamiltonianUnweightedPrimeMatrix (2 * m)) <=
        norm (P m - hamiltonianPrimeNormalizedFactor B m (F m)) +
          norm (hamiltonianPrimeNormalizedFactor B m (F m) -
            hamiltonianUnweightedPrimeMatrix (2 * m)) := by
      have heq : P m - hamiltonianUnweightedPrimeMatrix (2 * m) =
          (P m - hamiltonianPrimeNormalizedFactor B m (F m)) +
          (hamiltonianPrimeNormalizedFactor B m (F m) -
            hamiltonianUnweightedPrimeMatrix (2 * m)) := by
        ext i j
        change P m i j - hamiltonianUnweightedPrimeMatrix (2 * m) i j =
          (P m i j - hamiltonianPrimeNormalizedFactor B m (F m) i j) +
          (hamiltonianPrimeNormalizedFactor B m (F m) i j -
            hamiltonianUnweightedPrimeMatrix (2 * m) i j)
        ring
      rw [heq]
      exact norm_add_le _ _
    refine {
      factor_packet := hf.1
      factor_error := hf.2
      nonnegative := hMix.1
      symmetric := hMix.2.1
      rows := hMix.2.2.1
      columns := hMix.2.2.2.1
      support := hMix.2.2.2.2.1
      close_factor := hClose
      close_original := ?_ }
    linarith only [htriangle, hPA, hf.2]

end PrimeFactorOscillations.LPF
