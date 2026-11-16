/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianMangoldtSpectralOutliers
import PrimeFactorOscillations.Helpers.HamiltonianQuarterPrimeFamily

/-! # Ordered native spectrum of the actual quarter-degree adjacency matrix -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_one_upper_outlier_ordered_bound
    (n : Nat) (hn : 1 <= n) (lambda : Fin n -> Real) (R : Real)
    (hCount : (Finset.univ.filter (fun i => R < lambda i)).card <= 1)
    (e : Equiv.Perm (Fin n))
    (hSorted : forall i j : Fin n, i.val <= j.val -> lambda (e j) <= lambda (e i))
    (k : Fin n) (hk : 1 <= k.val) : lambda (e k) <= R := by
  classical
  apply le_of_not_gt
  intro hBad
  let first : Fin n := Fin.mk 0 (by omega)
  have hFirst : R < lambda (e first) :=
    hBad.trans_le (hSorted first k (by dsimp [first]; omega))
  have hFirstMem : Membership.mem (Finset.univ.filter (fun j => R < lambda j))
      (e first) := Finset.mem_filter.mpr (And.intro (Finset.mem_univ _) hFirst)
  have hKMem : Membership.mem (Finset.univ.filter (fun j => R < lambda j))
      (e k) := Finset.mem_filter.mpr (And.intro (Finset.mem_univ _) hBad)
  have hEq := e.injective ((Finset.card_le_one.mp hCount) _ hFirstMem _ hKMem)
  have hVal := congrArg Fin.val hEq
  change 0 = k.val at hVal
  omega

namespace LPF

theorem hamiltonian_quarter_prime_raw_outlier_counts
    (m : Nat) (hm : 256 <= m) (E : Finset (Prod (Fin m) (Fin m))) (rho : Real)
    (hNorm : norm (hamiltonianQuarterPrimeMatrix m E -
      hamiltonianRealConstantParityMatrix (2 * m)) <= rho) :
    (Finset.univ.filter (fun i =>
      rho * (hamiltonianQuarterPrimeDegree m : Real) <
        (hamiltonian_prime_factor_hermitian m E).eigenvalues i)).card <= 1 /\
    (Finset.univ.filter (fun i =>
      (hamiltonian_prime_factor_hermitian m E).eigenvalues i <
        -(rho * (hamiltonianQuarterPrimeDegree m : Real)))).card <= 1 := by
  classical
  let d := (hamiltonianQuarterPrimeDegree m : Real)
  have hd : 0 < d := by
    have hh : (1 : Real) <= d := by
      change (1 : Real) <= (hamiltonianQuarterPrimeDegree m : Real)
      exact_mod_cast (hamiltonian_quarter_prime_degree_bounds m hm).1
    linarith only [hh]
  letI : NeZero (2 * m) := NeZero.mk (by omega)
  let u := fun i : Fin (2 * m) => Real.sqrt d * hamiltonianMangoldtFlatMode (2 * m) i
  let v := fun i : Fin (2 * m) => Real.sqrt d * hamiltonianMangoldtParityMode (2 * m) i
  have hRef : hamiltonianSignedRankOneReference u v =
      SMul.smul d (hamiltonianRealConstantParityMatrix (2 * m)) := by
    rw [<- hamiltonian_mangoldt_signed_reference]
    ext i j
    change (Real.sqrt d * hamiltonianMangoldtFlatMode (2 * m) i) *
        (Real.sqrt d * hamiltonianMangoldtFlatMode (2 * m) j) -
      (Real.sqrt d * hamiltonianMangoldtParityMode (2 * m) i) *
        (Real.sqrt d * hamiltonianMangoldtParityMode (2 * m) j) =
      d * (hamiltonianMangoldtFlatMode (2 * m) i * hamiltonianMangoldtFlatMode (2 * m) j -
        hamiltonianMangoldtParityMode (2 * m) i * hamiltonianMangoldtParityMode (2 * m) j)
    calc
      _ = Real.sqrt d ^ 2 *
        (hamiltonianMangoldtFlatMode (2 * m) i * hamiltonianMangoldtFlatMode (2 * m) j -
          hamiltonianMangoldtParityMode (2 * m) i *
            hamiltonianMangoldtParityMode (2 * m) j) := by ring
      _ = _ := by rw [Real.sq_sqrt hd.le]
  have hId : hamiltonianPrimeFactorAdjacency m E - hamiltonianSignedRankOneReference u v =
      SMul.smul d (hamiltonianQuarterPrimeMatrix m E -
        hamiltonianRealConstantParityMatrix (2 * m)) := by
    rw [hRef]
    ext i j
    change hamiltonianPrimeFactorAdjacency m E i j -
        d * hamiltonianRealConstantParityMatrix (2 * m) i j =
      d * ((1 / d) * hamiltonianPrimeFactorAdjacency m E i j -
        hamiltonianRealConstantParityMatrix (2 * m) i j)
    field_simp [ne_of_gt hd]
    <;> ring
  have hRawNorm : norm (hamiltonianPrimeFactorAdjacency m E -
      hamiltonianSignedRankOneReference u v) <= rho * d := by
    rw [hId, hamiltonian_matrix_real_smul_norm, Real.norm_of_nonneg hd.le]
    calc
      _ <= d * rho := mul_le_mul_of_nonneg_left hNorm hd.le
      _ = _ := mul_comm _ _
  exact And.intro
    (hamiltonian_signed_rank_one_upper_eigenvalue_count
      (hamiltonianPrimeFactorAdjacency m E) (hamiltonian_prime_factor_hermitian m E)
      u v (rho * d) hRawNorm)
    (hamiltonian_signed_rank_one_lower_eigenvalue_count
      (hamiltonianPrimeFactorAdjacency m E) (hamiltonian_prime_factor_hermitian m E)
      u v (rho * d) hRawNorm)

theorem hamiltonian_quarter_prime_ordered_spectral_family :
    exists M0 : Nat, 256 <= M0 /\
      exists E : (m : Nat) -> Finset (Prod (Fin m) (Fin m)),
        (forall m : Nat, M0 <= m ->
          E m <= hamiltonianPrimeFactorEdges m /\
          (forall i, ((E m).filter (fun e => e.1 = i)).card =
            hamiltonianQuarterPrimeDegree m) /\
          (forall j, ((E m).filter (fun e => e.2 = j)).card =
            hamiltonianQuarterPrimeDegree m)) /\
        (forall eta : Real, 0 < eta -> exists M : Nat, M0 <= M /\
          forall m : Nat, M <= m ->
            forall e : Equiv.Perm (Fin (2 * m)),
              (forall i j : Fin (2 * m), i.val <= j.val ->
                (hamiltonian_prime_factor_hermitian m (E m)).eigenvalues (e j) <=
                  (hamiltonian_prime_factor_hermitian m (E m)).eigenvalues (e i)) ->
              forall k : Fin (2 * m), 1 <= k.val ->
                (hamiltonian_prime_factor_hermitian m (E m)).eigenvalues (e k) <=
                  ((1 / 2 : Real) + eta) * (hamiltonianQuarterPrimeDegree m : Real)) := by
  choose M0 hM0 E hRegular hWindows using hamiltonian_quarter_prime_factor_family
  refine Exists.intro M0 (And.intro hM0 (Exists.intro E (And.intro hRegular ?_)))
  intro eta hEta
  choose M hM hWindow using hWindows eta hEta
  refine Exists.intro M (And.intro hM ?_)
  intro m hm e hSorted k hk
  have hm256 : 256 <= m := hM0.trans (hM.trans hm)
  have hCount := (hamiltonian_quarter_prime_raw_outlier_counts
    m hm256 (E m) ((1 / 2 : Real) + eta) (hWindow m hm)).1
  exact hamiltonian_one_upper_outlier_ordered_bound (2 * m) (by omega)
    (hamiltonian_prime_factor_hermitian m (E m)).eigenvalues
    (((1 / 2 : Real) + eta) * (hamiltonianQuarterPrimeDegree m : Real))
    hCount e hSorted k hk

end LPF
end PrimeFactorOscillations
