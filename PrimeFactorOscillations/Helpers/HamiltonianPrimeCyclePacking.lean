/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianFiniteCyclePacking
import PrimeFactorOscillations.Helpers.HamiltonianPrimeSubfactorCycles

/-! # A positive proportion of actual prime edges in disjoint Hamilton cycles -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.LPF

theorem hamiltonian_prime_packing_rank_margin
    (kappa kappa' eps D r : Real) (hk : kappa < kappa') (hk' : 0 < kappa')
    (hD : 0 < D) (heps : eps = (kappa' - kappa) / (2 * kappa'))
    (hRank : abs (r / D - 1) <= eps) :
    kappa * D <= kappa' * r := by
  have hLower := (abs_le.mp hRank).1
  have hRatio : 1 - eps <= r / D := by linarith only [hLower]
  have hMul := mul_le_mul_of_nonneg_right hRatio hD.le
  have hCancel : (r / D) * D = r := by field_simp [ne_of_gt hD]
  rw [hCancel] at hMul
  have hWeighted := mul_le_mul_of_nonneg_left hMul hk'.le
  have hEps : kappa' * eps = (kappa' - kappa) / 2 := by
    rw [heps]
    field_simp [ne_of_gt hk']
    <;> ring
  have hCoefficient : kappa <= kappa' * (1 - eps) := by
    nlinarith only [hEps, hk]
  calc
    kappa * D <= (kappa' * (1 - eps)) * D :=
      mul_le_mul_of_nonneg_right hCoefficient hD.le
    _ <= kappa' * r := by simpa only [mul_assoc] using hWeighted

theorem hamiltonian_prime_edge_disjoint_cycles_uniform
    (kappa : Real) (hk0 : 0 <= kappa) (hk1 : kappa < (1 / 8 : Real)) :
    exists M0 : Nat, 256 <= M0 /\
      forall m : Nat, M0 <= m ->
        exists Cs : Finset (Finset (Prod (Fin m) (Fin m))),
          Cs.card = Nat.floor (kappa * hamiltonianPrimeFactorDegree m) /\
          (forall C, Membership.mem Cs C -> C <= hamiltonianPrimeFactorEdges m) /\
          (forall C, Membership.mem Cs C ->
            exists f : Equiv.Perm (Sum (Fin m) (Fin m)),
              (hamiltonianPermutationOrbits f).card = 1 /\
              C = hamiltonianBipartiteCycleEdges f /\
              (forall i, Not ((hamiltonianParityEquiv m) (f i) =
                  (hamiltonianParityEquiv m) i) /\
                Nat.Prime ((((hamiltonianParityEquiv m) (f i)).val + 1) +
                  (((hamiltonianParityEquiv m) i).val + 1)))) /\
          (forall C, Membership.mem Cs C -> forall D, Membership.mem Cs D ->
            Not (C = D) -> Disjoint C D) := by
  let kappa' := (kappa + (1 / 8 : Real)) / 2
  have hk'0 : 0 < kappa' := by dsimp [kappa']; linarith only [hk0]
  have hkk' : kappa < kappa' := by dsimp [kappa']; linarith only [hk1]
  have hk'1 : kappa' < (1 / 8 : Real) := by dsimp [kappa']; linarith only [hk1]
  let eps := (kappa' - kappa) / (2 * kappa')
  have hEps : 0 < eps := div_pos (sub_pos.mpr hkk') (by positivity)
  choose B hB Mb hMb F P hFamily hWindows using hamiltonian_prime_near_optimal_factor_family
  choose Mw hMw hWindow using hWindows eps hEps
  choose Mc hMc hCycle using
    hamiltonian_prime_regular_subfactor_hamiltonian_uniform B kappa' hB hk'0.le hk'1
  refine Exists.intro (max Mw Mc) (And.intro (hMc.trans (le_max_right _ _)) ?_)
  intro m hm
  have hmw : Mw <= m := (le_max_left _ _).trans hm
  have hmc : Mc <= m := (le_max_right _ _).trans hm
  have hmb : Mb <= m := hMw.trans hmw
  have hm256 : 256 <= m := hMb.trans hmb
  have hPacket := hFamily m hmb
  have hW := hWindow m hmw
  let r := hamiltonianPrimeFactorRank B m
  let D := hamiltonianPrimeFactorDegree m
  let k := Nat.floor (kappa * D)
  have hD : 0 < D := (hamiltonian_prime_factor_scalars m (by omega : 1 <= m)).2.1
  have hR0 : 0 <= (r : Real) := Nat.cast_nonneg r
  have hMargin : kappa * D <= kappa' * (r : Real) :=
    hamiltonian_prime_packing_rank_margin kappa kappa' eps D (r : Real)
      hkk' hk'0 hD rfl hW.relative_rank
  have hFloor : (k : Real) <= kappa * D := Nat.floor_le (mul_nonneg hk0 hD.le)
  have hKR : (k : Real) <= kappa' * (r : Real) := hFloor.trans hMargin
  have hTwoKR : (2 : Real) * (k : Real) <= (r : Real) := by
    have hBudget := mul_le_mul_of_nonneg_right
      (by linarith only [hk'1] : 2 * kappa' <= (1 : Real)) hR0
    nlinarith only [hKR, hBudget]
  have hSize : 2 * k <= r := by exact_mod_cast hTwoKR
  have hOracle : forall H : Finset (Prod (Fin m) (Fin m)), H <= F m ->
      forall d : Nat, r - 2 * k + 2 <= d ->
        (forall a, (H.filter (fun e => e.1 = a)).card = d) ->
        (forall b, (H.filter (fun e => e.2 = b)).card = d) ->
        exists f : Equiv.Perm (Sum (Fin m) (Fin m)),
          (hamiltonianPermutationOrbits f).card = 1 /\
          (forall i, Not (hamiltonianFactorAdjacency H (f i) i = 0)) := by
    intro H hHF d hd hHL hHR
    have hSub : ((r - 2 * k : Nat) : Real) = (r : Real) - 2 * (k : Real) := by
      rw [Nat.cast_sub hSize, Nat.cast_mul, Nat.cast_ofNat]
    have hRest : r - 2 * k <= d := by omega
    have hRestR : (r : Real) - 2 * (k : Real) <= (d : Real) := by
      rw [<- hSub]
      exact_mod_cast hRest
    have hRetain : (1 - 2 * kappa') * (r : Real) <= (d : Real) := by
      nlinarith only [hRestR, hKR]
    exact hCycle m hmc (F m) (P m) hPacket H d hHF hRetain hHL hHR
  choose Cs hCard hSub hWitness hPair using
    hamiltonian_finite_edge_disjoint_cycle_packing m r k (by omega) hSize (F m)
      hPacket.factor_packet.left_regular hPacket.factor_packet.right_regular hOracle
  refine Exists.intro Cs (And.intro hCard (And.intro ?_ (And.intro ?_ hPair)))
  next =>
    intro C hC
    exact (hSub C hC).trans hPacket.factor_packet.subset_prime
  next =>
    intro C hC
    choose f hOne hSupport hEdges using hWitness C hC
    refine Exists.intro f (And.intro hOne (And.intro hEdges ?_))
    intro i
    apply hamiltonian_prime_factor_physical_support m (by omega : 1 <= m)
      (F m) hPacket.factor_packet.subset_prime
      ((hamiltonianParityEquiv m) (f i)) ((hamiltonianParityEquiv m) i)
    change Not (hamiltonianFactorAdjacency (F m)
      ((hamiltonianParityEquiv m).symm ((hamiltonianParityEquiv m) (f i)))
      ((hamiltonianParityEquiv m).symm ((hamiltonianParityEquiv m) i)) = 0)
    simpa only [Equiv.symm_apply_apply] using hSupport i

end PrimeFactorOscillations.LPF
