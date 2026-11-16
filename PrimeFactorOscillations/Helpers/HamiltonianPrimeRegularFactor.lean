/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPrimeFactorInputs

/-! # Integral regular factors on the actual integer prime-sum graph -/

set_option autoImplicit false
set_option Elab.async false

open Finset
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

def hamiltonianPrimeFactorAdjacency (m : Nat)
    (F : Finset (Prod (Fin m) (Fin m))) : Matrix (Fin (2 * m)) (Fin (2 * m)) Real :=
  (hamiltonianFactorAdjacency F).submatrix
    (hamiltonianParityEquiv m).symm (hamiltonianParityEquiv m).symm

theorem hamiltonian_prime_factor_physical_scale (m : Nat) :
    hamiltonianUnweightedPrimeMatrix (2 * m) =
      SMul.smul (hamiltonianPrimeFactorScale m)
        (hamiltonianPrimeFactorAdjacency m (hamiltonianPrimeFactorEdges m)) := by
  ext i j
  have hp := congrArg (fun M => M ((hamiltonianParityEquiv m).symm i)
    ((hamiltonianParityEquiv m).symm j)) (hamiltonian_prime_factor_adjacency_scale m)
  change hamiltonianUnweightedPrimeMatrix (2 * m)
      ((hamiltonianParityEquiv m) ((hamiltonianParityEquiv m).symm i))
      ((hamiltonianParityEquiv m) ((hamiltonianParityEquiv m).symm j)) =
    hamiltonianPrimeFactorScale m * hamiltonianFactorAdjacency (hamiltonianPrimeFactorEdges m)
      ((hamiltonianParityEquiv m).symm i) ((hamiltonianParityEquiv m).symm j) at hp
  change hamiltonianUnweightedPrimeMatrix (2 * m) i j =
    hamiltonianPrimeFactorScale m * hamiltonianFactorAdjacency (hamiltonianPrimeFactorEdges m)
      ((hamiltonianParityEquiv m).symm i) ((hamiltonianParityEquiv m).symm j)
  simpa only [Equiv.apply_symm_apply] using hp

theorem hamiltonian_prime_factor_physical_loss
    (m : Nat) (E F : Finset (Prod (Fin m) (Fin m))) :
    norm (hamiltonianPrimeFactorAdjacency m E - hamiltonianPrimeFactorAdjacency m F) =
      norm (hamiltonianFactorAdjacency E - hamiltonianFactorAdjacency F) := by
  change norm ((hamiltonianFactorAdjacency E - hamiltonianFactorAdjacency F).submatrix
    (hamiltonianParityEquiv m).symm (hamiltonianParityEquiv m).symm) = _
  exact hamiltonian_reindex_matrix_norm (hamiltonianParityEquiv m).symm _

theorem hamiltonian_prime_factor_physical_degree
    (m r : Nat) (F : Finset (Prod (Fin m) (Fin m)))
    (hleft : forall a, (F.filter (fun e => e.1 = a)).card = r)
    (hright : forall b, (F.filter (fun e => e.2 = b)).card = r)
    (i : Fin (2 * m)) :
    univ.sum (fun j => hamiltonianPrimeFactorAdjacency m F i j) = (r : Real) := by
  change univ.sum (fun j => hamiltonianFactorAdjacency F
    ((hamiltonianParityEquiv m).symm i) ((hamiltonianParityEquiv m).symm j)) = _
  rw [hamiltonian_sum_reindex (hamiltonianParityEquiv m).symm,
    hamiltonian_factor_adjacency_row]
  cases (hamiltonianParityEquiv m).symm i with
  | inl a => simp only [hleft a]
  | inr b => simp only [hright b]

theorem hamiltonian_prime_factor_physical_support
    (m : Nat) (hm : 1 <= m) (F : Finset (Prod (Fin m) (Fin m)))
    (hFE : F <= hamiltonianPrimeFactorEdges m) (i j : Fin (2 * m))
    (hijF : Not (hamiltonianPrimeFactorAdjacency m F i j = 0)) :
    And (Not (i = j)) (Nat.Prime ((i.val + 1) + (j.val + 1))) := by
  have hmask : forall x y : Sum (Fin m) (Fin m),
      hamiltonianFactorAdjacency (hamiltonianPrimeFactorEdges m) x y = 0 ->
        hamiltonianFactorAdjacency F x y = 0 := by
    intro x y hx
    cases x with
    | inl a =>
      cases y with
      | inl c => rfl
      | inr b =>
        by_cases hF : Membership.mem F (a, b)
        . have hE := hFE hF
          simp [hamiltonianFactorAdjacency, hE] at hx
        . simp [hamiltonianFactorAdjacency, hF]
    | inr b =>
      cases y with
      | inl a =>
        by_cases hF : Membership.mem F (a, b)
        . have hE := hFE hF
          simp [hamiltonianFactorAdjacency, hE] at hx
        . simp [hamiltonianFactorAdjacency, hF]
      | inr c => rfl
  change Not (hamiltonianFactorAdjacency F
    ((hamiltonianParityEquiv m).symm i) ((hamiltonianParityEquiv m).symm j) = 0) at hijF
  have hfull : Not (hamiltonianFactorAdjacency (hamiltonianPrimeFactorEdges m)
      ((hamiltonianParityEquiv m).symm i) ((hamiltonianParityEquiv m).symm j) = 0) :=
    fun h => hijF (hmask _ _ h)
  have hp := congrArg (fun M => M i j) (hamiltonian_prime_factor_physical_scale m)
  change hamiltonianUnweightedPrimeMatrix (2 * m) i j =
    hamiltonianPrimeFactorScale m * hamiltonianFactorAdjacency (hamiltonianPrimeFactorEdges m)
      ((hamiltonianParityEquiv m).symm i) ((hamiltonianParityEquiv m).symm j) at hp
  have hu : Not (hamiltonianUnweightedPrimeMatrix (2 * m) i j = 0) := by
    rw [hp]
    exact mul_ne_zero (ne_of_gt (hamiltonian_prime_factor_scalars m hm).1) hfull
  have hne : Not (i = j) := by
    intro h
    simp [hamiltonianUnweightedPrimeMatrix, h] at hu
  have hprime : Nat.Prime ((i.val + 1) + (j.val + 1)) := by
    by_contra h
    apply hu
    simp only [hamiltonianUnweightedPrimeMatrix, hne, h, ite_false]
  exact And.intro hne hprime

theorem hamiltonian_prime_regular_factor_uniform
    (eps : Real) (heps : 0 < eps) (hepsSmall : eps < (1 / 10 : Real)) :
    Exists (fun M0 : Nat => And (256 <= M0)
      (forall m : Nat, M0 <= m -> forall r : Nat,
        (r : Real) <= (1 - 10 * eps) * hamiltonianPrimeFactorDegree m ->
        Exists (fun F : Finset (Prod (Fin m) (Fin m)) =>
          F <= hamiltonianPrimeFactorEdges m /\
          (forall a, (F.filter (fun e => e.1 = a)).card = r) /\
          (forall b, (F.filter (fun e => e.2 = b)).card = r) /\
          norm (hamiltonianPrimeFactorAdjacency m (hamiltonianPrimeFactorEdges m) -
            hamiltonianPrimeFactorAdjacency m F) <=
              (1 + eps) * hamiltonianPrimeFactorDegree m - (r : Real)))) := by
  choose Md hMd hdegree using hamiltonian_prime_factor_degree_uniform eps heps
  choose Mc hMc hcut using hamiltonian_prime_factor_cut_uniform
  refine Exists.intro (max Md Mc) (And.intro (hMd.trans (le_max_left _ _)) ?_)
  intro m hm r hr
  have hd := hdegree m (by omega : Md <= m)
  have hs := hamiltonian_prime_factor_scalars m (by omega : 1 <= m)
  have hr' : (r : Real) <= (1 - 2 * eps / (1 / 5 : Real)) * hamiltonianPrimeFactorDegree m := by
    have heq : (1 - 2 * eps / (1 / 5 : Real)) * hamiltonianPrimeFactorDegree m =
        (1 - 10 * eps) * hamiltonianPrimeFactorDegree m := by ring
    rw [heq]
    exact hr
  have heps' : eps < (1 / 5 : Real) / 2 := by
    norm_num
    exact hepsSmall
  choose F hF using hamiltonian_regular_factor_and_operator
    (hamiltonianPrimeFactorEdges m) r rfl (hamiltonianPrimeFactorDegree m)
    (1 / 5 : Real) eps hs.2.1 (by norm_num) (le_of_lt heps) heps' hr'
    hd.1 hd.2 (hcut m (by omega : Mc <= m))
  refine Exists.intro F (And.intro hF.1 (And.intro hF.2.1 (And.intro hF.2.2.1 ?_)))
  rw [hamiltonian_prime_factor_physical_loss]
  exact hF.2.2.2

end PrimeFactorOscillations.LPF
