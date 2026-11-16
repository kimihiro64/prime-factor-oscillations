/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPrimeSubfactorCycles
import PrimeFactorOscillations.Helpers.HamiltonianQuarterPrimeSpectrum

/-! # Eventual prime Hamilton circles and the exact quarter-degree spectral family -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.LPF

theorem hamiltonian_prime_single_cycle_terminal :
    exists M0 : Nat, 256 <= M0 /\
      forall m : Nat, M0 <= m ->
        exists f : Equiv.Perm (Sum (Fin m) (Fin m)),
          (hamiltonianPermutationOrbits f).card = 1 /\
          forall i, Not ((hamiltonianParityEquiv m) (f i) = (hamiltonianParityEquiv m) i) /\
            Nat.Prime ((((hamiltonianParityEquiv m) (f i)).val + 1) +
              (((hamiltonianParityEquiv m) i).val + 1)) := by
  choose B hB A hA F P hReference hWindows using
    hamiltonian_prime_near_optimal_factor_family
  choose T hT hCycle using
    hamiltonian_prime_regular_subfactor_hamiltonian_uniform B 0 hB (by norm_num) (by norm_num)
  let M0 := max A T
  refine Exists.intro M0 (And.intro (hA.trans (le_max_left _ _)) ?_)
  intro m hm
  have hmA : A <= m := (le_max_left _ _).trans hm
  have hmT : T <= m := (le_max_right _ _).trans hm
  have hm1 : 1 <= m := by have hh := hA.trans hmA; omega
  have hPacket := hReference m hmA
  cases hCycle m hmT (F m) (P m) hPacket (F m) (hamiltonianPrimeFactorRank B m)
      (le_refl _) (by simp) hPacket.factor_packet.left_regular
      hPacket.factor_packet.right_regular with
  | intro f hF =>
    refine Exists.intro f (And.intro hF.1 ?_)
    intro i
    apply hamiltonian_prime_factor_physical_support m hm1 (F m)
      hPacket.factor_packet.subset_prime
      ((hamiltonianParityEquiv m) (f i)) ((hamiltonianParityEquiv m) i)
    change Not (hamiltonianFactorAdjacency (F m)
      ((hamiltonianParityEquiv m).symm ((hamiltonianParityEquiv m) (f i)))
      ((hamiltonianParityEquiv m).symm ((hamiltonianParityEquiv m) i)) = 0)
    simpa only [Equiv.symm_apply_apply] using hF.2 i

structure HamiltonianEventualFilzPacket (m : Nat)
    (E : Finset (Prod (Fin m) (Fin m))) : Prop where
  subset_prime : E <= hamiltonianPrimeFactorEdges m
  left_degree : forall i, (E.filter (fun e => e.1 = i)).card = hamiltonianQuarterPrimeDegree m
  right_degree : forall j, (E.filter (fun e => e.2 = j)).card = hamiltonianQuarterPrimeDegree m
  prime_circle : exists f : Equiv.Perm (Sum (Fin m) (Fin m)),
    (hamiltonianPermutationOrbits f).card = 1 /\
      forall i, Not ((hamiltonianParityEquiv m) (f i) = (hamiltonianParityEquiv m) i) /\
        Nat.Prime ((((hamiltonianParityEquiv m) (f i)).val + 1) +
          (((hamiltonianParityEquiv m) i).val + 1))

theorem hamiltonian_eventual_filz_with_exact_degree_spectrum :
    exists M0 : Nat, 256 <= M0 /\
      exists E : (m : Nat) -> Finset (Prod (Fin m) (Fin m)),
        (forall m : Nat, M0 <= m -> HamiltonianEventualFilzPacket m (E m)) /\
        (forall eta : Real, 0 < eta -> exists M : Nat, M0 <= M /\
          forall m : Nat, M <= m ->
            forall e : Equiv.Perm (Fin (2 * m)),
              (forall i j : Fin (2 * m), i.val <= j.val ->
                (hamiltonian_prime_factor_hermitian m (E m)).eigenvalues (e j) <=
                  (hamiltonian_prime_factor_hermitian m (E m)).eigenvalues (e i)) ->
              forall k : Fin (2 * m), 1 <= k.val ->
                (hamiltonian_prime_factor_hermitian m (E m)).eigenvalues (e k) <=
                  ((1 / 2 : Real) + eta) * (hamiltonianQuarterPrimeDegree m : Real)) := by
  choose A hA E hE hSpectrum using hamiltonian_quarter_prime_ordered_spectral_family
  choose T hT hCircle using hamiltonian_prime_single_cycle_terminal
  let M0 := max A T
  refine Exists.intro M0 (And.intro (hA.trans (le_max_left _ _))
    (Exists.intro E (And.intro ?_ ?_)))
  . intro m hm
    have hmA : A <= m := (le_max_left _ _).trans hm
    have hmT : T <= m := (le_max_right _ _).trans hm
    have hRegular := hE m hmA
    exact {
      subset_prime := hRegular.1
      left_degree := hRegular.2.1
      right_degree := hRegular.2.2
      prime_circle := hCircle m hmT }
  . intro eta hEta
    choose U hU hBound using hSpectrum eta hEta
    refine Exists.intro (max M0 U) (And.intro (le_max_left _ _) ?_)
    intro m hm
    exact hBound m ((le_max_right _ _).trans hm)

end PrimeFactorOscillations.LPF
