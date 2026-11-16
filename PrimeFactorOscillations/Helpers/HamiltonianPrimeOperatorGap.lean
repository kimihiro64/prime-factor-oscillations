/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPrimeOperatorAsymptotic
import PrimeFactorOscillations.Helpers.HamiltonianRationalLowModes

/-! # The unconditional actual integer prime-sum spectral gap

A common auxiliary period exists at every physical scale. Its exact
denominator-one/two operator is the constant-minus-parity matrix, so the
final theorem contains no auxiliary grid, rational cutoff, analytic
hypothesis or subsequence.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

theorem hamiltonian_common_auxiliary_period (M Q : Nat) (hM : 0 < M) :
    exists R : Nat, And (M < R)
      (And (Dvd.dvd M R) (And (Dvd.dvd 2 R)
        (forall q, 0 < q -> q <= Q -> Dvd.dvd q R))) := by
  let R := 2 * M * Q.factorial
  have hFactorial : 1 <= Q.factorial := Nat.factorial_pos Q
  have hMR : M < R := by dsimp [R]; nlinarith only [hM, hFactorial]
  have hDivM : Dvd.dvd M R := by
    refine Dvd.intro (2 * Q.factorial) ?_
    dsimp [R]
    ring
  have hEven : Dvd.dvd 2 R := by
    refine Dvd.intro (M * Q.factorial) ?_
    dsimp [R]
    ring
  have hDiv : forall q, 0 < q -> q <= Q -> Dvd.dvd q R := by
    intro q hq hqQ
    have h := Nat.dvd_factorial hq hqQ
    exact dvd_trans h (dvd_mul_left Q.factorial (2 * M))
  exact Exists.intro R (And.intro hMR (And.intro hDivM (And.intro hEven hDiv)))

theorem hamiltonian_prime_operator_gap (eps : Real) (hEps : 0 < eps) :
    exists N0 : Nat, And (1 <= N0)
      (forall n : Nat, N0 <= n ->
        norm (hamiltonianMangoldtSumMatrix n - hamiltonianConstantParityMatrix n) <=
          (1 / 2 : Real) + eps) := by
  choose A hA hActual using hamiltonian_prime_operator_two_mode_asymptotic eps hEps
  choose B hB hCut using hamiltonian_prime_cutoff_admissible 1 (by norm_num)
  let N0 := max A B
  refine Exists.intro N0 (And.intro (hA.trans (le_max_left _ _)) ?_)
  intro n hn
  have hnA : A <= n := (le_max_left A B).trans hn
  have hnB : B <= n := (le_max_right A B).trans hn
  have hnPos : 0 < n := by omega
  letI : NeZero n := NeZero.mk (Nat.ne_of_gt hnPos)
  let M := 2 * n
  let Q := hamiltonianPrimeCutoff M
  have hM : 0 < M := by dsimp [M]; omega
  have hBM : B <= M := by dsimp [M]; omega
  have hQ : 2 <= Q := by
    have h := (hCut M hBM).1
    change 4 <= Q at h
    omega
  choose R hMR hDivM hEven hDiv using hamiltonian_common_auxiliary_period M Q hM
  have hR : 0 < R := lt_trans hM hMR
  letI : NeZero R := NeZero.mk (Nat.ne_of_gt hR)
  have h := hActual (n := n) (R := R) hnA hMR hDivM hDiv
  change norm (hamiltonianMangoldtSumMatrix n -
    hamiltonianRationalOperator n R Q (hamiltonianRationalLowCoefficient Q)) <= _ at h
  rw [hamiltonian_rational_low_operator_eq n Q hQ hEven] at h
  exact h

end PrimeFactorOscillations.LPF
