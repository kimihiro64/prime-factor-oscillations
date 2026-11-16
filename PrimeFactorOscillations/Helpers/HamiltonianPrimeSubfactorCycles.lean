/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianFactorDeletion
import PrimeFactorOscillations.Helpers.HamiltonianPrimePackingCount

/-! # Actual regular subfactors retain Hamilton cycles throughout the packing range -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

def hamiltonianRegularSubfactorDeletion {m : Nat} (r d : Nat)
    (F H : Finset (Prod (Fin m) (Fin m))) : Matrix (Fin m) (Fin m) Real :=
  hamiltonianRegularFactorCross r F -
    SMul.smul ((d : Real) / (r : Real)) (hamiltonianRegularFactorCross d H)

theorem hamiltonian_regular_subfactor_deletion_edges {m : Nat} (r d : Nat)
    (hr : 0 < r) (hd : 0 < d)
    (F H : Finset (Prod (Fin m) (Fin m))) (hHF : H <= F) :
    hamiltonianRegularSubfactorDeletion r d F H = hamiltonianRegularFactorCross r (F \ H) := by
  have hr0 : Not ((r : Real) = 0) := ne_of_gt (Nat.cast_pos.mpr hr)
  have hd0 : Not ((d : Real) = 0) := ne_of_gt (Nat.cast_pos.mpr hd)
  ext i j
  change (1 / (r : Real)) * (if Membership.mem F (i, j) then (1 : Real) else 0) -
      ((d : Real) / (r : Real)) *
        ((1 / (d : Real)) * (if Membership.mem H (i, j) then (1 : Real) else 0)) =
    (1 / (r : Real)) * (if Membership.mem (F \ H) (i, j) then (1 : Real) else 0)
  by_cases hH : Membership.mem H (i, j)
  case pos =>
    have hF := hHF hH
    simp only [Finset.mem_sdiff, hH, hF, not_true_eq_false, and_false,
      ite_true, ite_false, mul_one, mul_zero]
    field_simp [hr0, hd0]
    <;> ring
  case neg =>
    simp only [Finset.mem_sdiff, hH, not_false_eq_true, and_true,
      ite_false, mul_zero, sub_zero]

theorem hamiltonian_regular_subfactor_deletion_bounds {m : Nat} (r d : Nat)
    (hr : 0 < r) (hd : 0 < d)
    (F H : Finset (Prod (Fin m) (Fin m))) (hHF : H <= F) :
    (forall i j, 0 <= hamiltonianRegularSubfactorDeletion r d F H i j) /\
      (forall i j, hamiltonianRegularSubfactorDeletion r d F H i j <=
        hamiltonianRegularFactorCross r F i j) := by
  rw [hamiltonian_regular_subfactor_deletion_edges r d hr hd F H hHF]
  have hc : 0 <= 1 / (r : Real) := by positivity
  have hEach (i j : Fin m) :
      0 <= hamiltonianRegularFactorCross r (F \ H) i j /\
        hamiltonianRegularFactorCross r (F \ H) i j <= hamiltonianRegularFactorCross r F i j := by
    unfold hamiltonianRegularFactorCross
    by_cases hF : Membership.mem F (i, j) <;>
      by_cases hH : Membership.mem H (i, j) <;>
        simp [Finset.mem_sdiff, hF, hH, hc]
  exact And.intro (fun i j => (hEach i j).1) (fun i j => (hEach i j).2)

theorem hamiltonian_regular_subfactor_deletion_degrees {m : Nat} (r d : Nat)
    (hr : 0 < r) (hd : 0 < d)
    (F H : Finset (Prod (Fin m) (Fin m)))
    (hFL : forall i, (F.filter (fun e => e.1 = i)).card = r)
    (hFR : forall j, (F.filter (fun e => e.2 = j)).card = r)
    (hHL : forall i, (H.filter (fun e => e.1 = i)).card = d)
    (hHR : forall j, (H.filter (fun e => e.2 = j)).card = d) :
    (forall i, Finset.univ.sum (fun j =>
      hamiltonianRegularSubfactorDeletion r d F H i j) = 1 - (d : Real) / (r : Real)) /\
    (forall j, Finset.univ.sum (fun i =>
      hamiltonianRegularSubfactorDeletion r d F H i j) = 1 - (d : Real) / (r : Real)) := by
  have hF := hamiltonian_regular_factor_cross_stochastic m r hr F hFL hFR
  have hH := hamiltonian_regular_factor_cross_stochastic m d hd H hHL hHR
  refine And.intro ?_ ?_
  next =>
    intro i
    change Finset.univ.sum (fun j => hamiltonianRegularFactorCross r F i j -
      ((d : Real) / (r : Real)) * hamiltonianRegularFactorCross d H i j) = _
    rw [Finset.sum_sub_distrib, <- Finset.mul_sum, hF.1 i, hH.1 i, mul_one]
  next =>
    intro j
    change Finset.univ.sum (fun i => hamiltonianRegularFactorCross r F i j -
      ((d : Real) / (r : Real)) * hamiltonianRegularFactorCross d H i j) = _
    rw [Finset.sum_sub_distrib, <- Finset.mul_sum, hF.2 j, hH.2 j, mul_one]

theorem hamiltonian_regular_subfactor_remaining_kernel {m : Nat} (r d : Nat)
    (hr : 0 < r) (hd : 0 < d) (F H : Finset (Prod (Fin m) (Fin m))) :
    hamiltonianRegularDeletionKernel (hamiltonianRegularFactorCross r F)
      (hamiltonianRegularSubfactorDeletion r d F H) (1 - (d : Real) / (r : Real)) =
        hamiltonianRegularFactorCross d H := by
  have hr0 : Not ((r : Real) = 0) := ne_of_gt (Nat.cast_pos.mpr hr)
  have hd0 : Not ((d : Real) = 0) := ne_of_gt (Nat.cast_pos.mpr hd)
  ext i j
  change (1 / (1 - (1 - (d : Real) / (r : Real)))) *
      (hamiltonianRegularFactorCross r F i j -
        (hamiltonianRegularFactorCross r F i j -
          ((d : Real) / (r : Real)) * hamiltonianRegularFactorCross d H i j)) =
    hamiltonianRegularFactorCross d H i j
  field_simp [hr0, hd0]
  <;> ring

theorem hamiltonian_prime_regular_subfactor_hamiltonian_uniform
    (B kappa : Real) (hB : 0 < B) (hk0 : 0 <= kappa) (hk1 : kappa < (1 / 8 : Real)) :
    exists M0 : Nat, 256 <= M0 /\
      forall m : Nat, M0 <= m ->
        forall (F : Finset (Prod (Fin m) (Fin m)))
          (P : Matrix (Fin (2 * m)) (Fin (2 * m)) Real),
          HamiltonianPrimeFactorReferencePacket B m F P ->
          forall (H : Finset (Prod (Fin m) (Fin m))) (d : Nat), H <= F ->
            (1 - 2 * kappa) * (hamiltonianPrimeFactorRank B m : Real) <= (d : Real) ->
            (forall i, (H.filter (fun e => e.1 = i)).card = d) ->
            (forall j, (H.filter (fun e => e.2 = j)).card = d) ->
            exists f : Equiv.Perm (Sum (Fin m) (Fin m)),
              (hamiltonianPermutationOrbits f).card = 1 /\
                (forall i, Not (hamiltonianFactorAdjacency H (f i) i = 0)) := by
  choose M0 hM0 hCount using hamiltonian_prime_packing_count_uniform B kappa hB hk0 hk1
  refine Exists.intro M0 (And.intro hM0 ?_)
  intro m hm F P hPacket H d hHF hRemain hHL hHR
  have hm256 : 256 <= m := hM0.trans hm
  have hrNat : 0 < hamiltonianPrimeFactorRank B m := by
    have h := hPacket.factor_packet.rank_positive
    omega
  let r := hamiltonianPrimeFactorRank B m
  have hr : 0 < (r : Real) := Nat.cast_pos.mpr hrNat
  have hkGap : 0 < 1 - 2 * kappa := by linarith only [hk1]
  have hdR : 0 < (d : Real) := (mul_pos hkGap hr).trans_le hRemain
  have hdNat : 0 < d := Nat.cast_pos.mp hdR
  let a0 : Fin m := Fin.mk 0 (by omega)
  have hFilter : H.filter (fun e => e.1 = a0) <= F.filter (fun e => e.1 = a0) := by
    intro e he
    have h := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr (And.intro (hHF h.1) h.2)
  have hDegree : d <= r := by
    have h := Finset.card_le_card hFilter
    rw [hHL a0, hPacket.factor_packet.left_regular a0] at h
    exact h
  have hDegreeR : (d : Real) <= (r : Real) := by exact_mod_cast hDegree
  let alpha := 1 - (d : Real) / (r : Real)
  have hRatioUpper : (d : Real) / (r : Real) <= 1 := by
    calc
      _ <= (r : Real) / (r : Real) := div_le_div_of_nonneg_right hDegreeR hr.le
      _ = _ := by field_simp
  have ha0 : 0 <= alpha := by dsimp [alpha]; linarith only [hRatioUpper]
  have hRatioLower : 1 - 2 * kappa <= (d : Real) / (r : Real) := by
    have h := div_le_div_of_nonneg_right hRemain hr.le
    have he : ((1 - 2 * kappa) * (r : Real)) / (r : Real) = 1 - 2 * kappa := by field_simp
    rw [he] at h
    exact h
  have haUpper : alpha <= 2 * kappa := by dsimp [alpha]; linarith only [hRatioLower]
  let Q := hamiltonianRegularSubfactorDeletion r d F H
  have hQDegrees := hamiltonian_regular_subfactor_deletion_degrees r d hrNat hdNat F H
    hPacket.factor_packet.left_regular hPacket.factor_packet.right_regular hHL hHR
  have hQBounds := hamiltonian_regular_subfactor_deletion_bounds r d hrNat hdNat F H hHF
  have hResult := hCount m hm F P hPacket Q alpha ha0 haUpper
    hQDegrees.1 hQDegrees.2 hQBounds.1 hQBounds.2
  change abs (hamiltonianBipartiteCountRatio
    (hamiltonianRegularDeletionKernel (hamiltonianRegularFactorCross r F)
      (hamiltonianRegularSubfactorDeletion r d F H) (1 - (d : Real) / (r : Real))) - 1) <=
        (m : Real) ^ (-1 / 3 : Real) at hResult
  rw [hamiltonian_regular_subfactor_remaining_kernel r d hrNat hdNat F H] at hResult
  have hPow : (m : Real) ^ (-1 / 3 : Real) < 1 := by
    have h := Real.rpow_lt_rpow_of_exponent_lt
      (by exact_mod_cast (by omega : 1 < m) : (1 : Real) < (m : Real))
      (by norm_num : (-1 / 3 : Real) < 0)
    simpa only [Real.rpow_zero] using h
  have hLower := (abs_le.mp hResult).1
  have hPositive : 0 < hamiltonianBipartiteCountRatio (hamiltonianRegularFactorCross d H) := by
    linarith only [hLower, hPow]
  exact hamiltonian_regular_factor_cycle_witness m d H hPositive

end PrimeFactorOscillations.LPF
