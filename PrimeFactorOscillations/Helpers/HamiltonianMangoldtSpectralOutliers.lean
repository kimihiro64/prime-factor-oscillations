/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianHermitianOutlierCount
import PrimeFactorOscillations.Helpers.HamiltonianPrimeOperatorGap
import PrimeFactorOscillations.Helpers.HamiltonianPrimeRealMatrix

/-! # The actual raw Mangoldt matrix has at most one outlier at either end -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

def hamiltonianRealMangoldtMatrix (n : Nat) : Matrix (Fin n) (Fin n) Real :=
  fun i j => ArithmeticFunction.vonMangoldt ((i.val + 1) + (j.val + 1)) / (n : Real)

theorem hamiltonian_real_mangoldt_complex_matrix (n : Nat) :
    hamiltonianComplexMatrix (hamiltonianRealMangoldtMatrix n) =
      hamiltonianMangoldtSumMatrix n := by
  ext i j
  change ((ArithmeticFunction.vonMangoldt ((i.val + 1) + (j.val + 1)) /
      (n : Real) : Real) : Complex) =
    (ArithmeticFunction.vonMangoldt ((i.val + 1) + (j.val + 1)) : Complex) / (n : Complex)
  push_cast
  <;> rfl

theorem hamiltonian_real_mangoldt_hermitian (n : Nat) :
    (hamiltonianRealMangoldtMatrix n).IsHermitian := by
  change (hamiltonianRealMangoldtMatrix n).conjTranspose = hamiltonianRealMangoldtMatrix n
  ext i j
  change ArithmeticFunction.vonMangoldt ((j.val + 1) + (i.val + 1)) / (n : Real) =
    ArithmeticFunction.vonMangoldt ((i.val + 1) + (j.val + 1)) / (n : Real)
  rw [Nat.add_comm (j.val + 1) (i.val + 1)]

def hamiltonianMangoldtFlatMode (n : Nat) : Fin n -> Real :=
  fun _ => 1 / Real.sqrt (n : Real)

def hamiltonianMangoldtParityMode (n : Nat) : Fin n -> Real :=
  fun i => (-1 : Real) ^ (i.val + 1) / Real.sqrt (n : Real)

theorem hamiltonian_mangoldt_signed_reference (n : Nat) [NeZero n] :
    hamiltonianSignedRankOneReference
      (hamiltonianMangoldtFlatMode n) (hamiltonianMangoldtParityMode n) =
        hamiltonianRealConstantParityMatrix n := by
  let r := Real.sqrt (n : Real)
  have hnPos : (0 : Real) < (n : Real) := Nat.cast_pos.mpr (NeZero.pos n)
  have hr : Not (r = 0) := ne_of_gt (Real.sqrt_pos.mpr hnPos)
  have hSquare : r * r = (n : Real) := by
    rw [<- pow_two]
    exact Real.sq_sqrt hnPos.le
  ext i j
  change (1 / r) * (1 / r) -
      (((-1 : Real) ^ (i.val + 1)) / r) * (((-1 : Real) ^ (j.val + 1)) / r) =
    (1 - (-1 : Real) ^ ((i.val + 1) + (j.val + 1))) / (n : Real)
  calc
    _ = (1 - ((-1 : Real) ^ (i.val + 1)) * ((-1 : Real) ^ (j.val + 1))) / (r * r) := by
      field_simp [hr]
      <;> ring
    _ = _ := by rw [hSquare, <- pow_add]

theorem hamiltonian_real_mangoldt_operator_gap (eps : Real) (hEps : 0 < eps) :
    exists N0 : Nat, 1 <= N0 /\
      forall n : Nat, N0 <= n ->
        norm (hamiltonianRealMangoldtMatrix n - hamiltonianRealConstantParityMatrix n) <=
          (1 / 2 : Real) + eps := by
  choose N0 hN0 hGap using hamiltonian_prime_operator_gap eps hEps
  refine Exists.intro N0 (And.intro hN0 ?_)
  intro n hn
  have h := hamiltonian_real_complex_l2_norm_le
    (hamiltonianRealMangoldtMatrix n - hamiltonianRealConstantParityMatrix n)
  rw [hamiltonian_complex_matrix_sub, hamiltonian_real_mangoldt_complex_matrix,
    hamiltonian_real_constant_parity_complex_matrix] at h
  exact h.trans (hGap n hn)

theorem hamiltonian_mangoldt_native_outlier_counts
    (eps : Real) (hEps : 0 < eps) :
    exists N0 : Nat, 1 <= N0 /\
      forall n : Nat, N0 <= n ->
        (Finset.univ.filter (fun k =>
          (1 / 2 : Real) + eps < (hamiltonian_real_mangoldt_hermitian n).eigenvalues k)).card <= 1 /\
        (Finset.univ.filter (fun k =>
          (hamiltonian_real_mangoldt_hermitian n).eigenvalues k <
            -((1 / 2 : Real) + eps))).card <= 1 := by
  classical
  choose N0 hN0 hGap using hamiltonian_real_mangoldt_operator_gap eps hEps
  refine Exists.intro N0 (And.intro hN0 ?_)
  intro n hn
  have hnPos : 0 < n := by omega
  letI : NeZero n := NeZero.mk (Nat.ne_of_gt hnPos)
  have hNorm :
      norm (hamiltonianRealMangoldtMatrix n -
        hamiltonianSignedRankOneReference
          (hamiltonianMangoldtFlatMode n) (hamiltonianMangoldtParityMode n)) <=
            (1 / 2 : Real) + eps := by
    rw [hamiltonian_mangoldt_signed_reference]
    exact hGap n hn
  exact And.intro
    (hamiltonian_signed_rank_one_upper_eigenvalue_count
      (hamiltonianRealMangoldtMatrix n) (hamiltonian_real_mangoldt_hermitian n)
      (hamiltonianMangoldtFlatMode n) (hamiltonianMangoldtParityMode n)
      ((1 / 2 : Real) + eps) hNorm)
    (hamiltonian_signed_rank_one_lower_eigenvalue_count
      (hamiltonianRealMangoldtMatrix n) (hamiltonian_real_mangoldt_hermitian n)
      (hamiltonianMangoldtFlatMode n) (hamiltonianMangoldtParityMode n)
      ((1 / 2 : Real) + eps) hNorm)


theorem hamiltonian_mangoldt_ordered_spectral_bounds
    (eps : Real) (hEps : 0 < eps) :
    exists N0 : Nat, 2 <= N0 /\
      forall n : Nat, N0 <= n ->
        forall e : Equiv.Perm (Fin n),
          (forall i j : Fin n, i.val <= j.val ->
            (hamiltonian_real_mangoldt_hermitian n).eigenvalues (e j) <=
              (hamiltonian_real_mangoldt_hermitian n).eigenvalues (e i)) ->
          (forall k : Fin n, 1 <= k.val ->
            (hamiltonian_real_mangoldt_hermitian n).eigenvalues (e k) <=
              (1 / 2 : Real) + eps) /\
          (forall k : Fin n, k.val + 1 < n ->
            -((1 / 2 : Real) + eps) <=
              (hamiltonian_real_mangoldt_hermitian n).eigenvalues (e k)) := by
  classical
  choose A hA hCount using hamiltonian_mangoldt_native_outlier_counts eps hEps
  let N0 := max 2 A
  refine Exists.intro N0 (And.intro (le_max_left _ _) ?_)
  intro n hn e hSorted
  have hn2 : 2 <= n := (le_max_left 2 A).trans hn
  have hnA : A <= n := (le_max_right 2 A).trans hn
  have hCensus := hCount n hnA
  let first : Fin n := Fin.mk 0 (by omega)
  let last : Fin n := Fin.mk (n - 1) (by omega)
  constructor
  . intro k hk
    apply le_of_not_gt
    intro hBad
    have hFirst :
        (1 / 2 : Real) + eps < (hamiltonian_real_mangoldt_hermitian n).eigenvalues (e first) :=
      hBad.trans_le (hSorted first k (by dsimp [first]; omega))
    have hFirstMem : Membership.mem
        (Finset.univ.filter (fun j =>
          (1 / 2 : Real) + eps < (hamiltonian_real_mangoldt_hermitian n).eigenvalues j))
        (e first) := Finset.mem_filter.mpr (And.intro (Finset.mem_univ _) hFirst)
    have hKMem : Membership.mem
        (Finset.univ.filter (fun j =>
          (1 / 2 : Real) + eps < (hamiltonian_real_mangoldt_hermitian n).eigenvalues j))
        (e k) := Finset.mem_filter.mpr (And.intro (Finset.mem_univ _) hBad)
    have hEq := e.injective ((Finset.card_le_one.mp hCensus.1) _ hFirstMem _ hKMem)
    have hVal := congrArg Fin.val hEq
    change 0 = k.val at hVal
    omega
  . intro k hk
    apply le_of_not_gt
    intro hBad
    have hLast :
        (hamiltonian_real_mangoldt_hermitian n).eigenvalues (e last) <
          -((1 / 2 : Real) + eps) :=
      (hSorted k last (by dsimp [last]; have h := k.isLt; omega)).trans_lt hBad
    have hKMem : Membership.mem
        (Finset.univ.filter (fun j =>
          (hamiltonian_real_mangoldt_hermitian n).eigenvalues j <
            -((1 / 2 : Real) + eps))) (e k) :=
      Finset.mem_filter.mpr (And.intro (Finset.mem_univ _) hBad)
    have hLastMem : Membership.mem
        (Finset.univ.filter (fun j =>
          (hamiltonian_real_mangoldt_hermitian n).eigenvalues j <
            -((1 / 2 : Real) + eps))) (e last) :=
      Finset.mem_filter.mpr (And.intro (Finset.mem_univ _) hLast)
    have hEq := e.injective ((Finset.card_le_one.mp hCensus.2) _ hKMem _ hLastMem)
    have hVal := congrArg Fin.val hEq
    change k.val = n - 1 at hVal
    omega

end PrimeFactorOscillations.LPF
