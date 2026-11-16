/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPrimeOperatorBudget

/-! # The full moving rational approximation with its frame budget

The established complete major/minor arithmetic estimate is consumed before
the two-mode relaxation. All rational denominators and signed phases remain.
The explicit frame budget is exposed for fixed-dimensional cutoff transfer.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

theorem hamiltonian_prime_rational_approximation_uniform (eps : Real) (hEps : 0 < eps) :
    exists N0 : Nat, And (1 <= N0)
      (forall {n R : Nat} [NeZero n] [NeZero R],
        N0 <= n -> 2 * n < R -> Dvd.dvd (2 * n) R ->
        (forall q, 0 < q -> q <= hamiltonianPrimeCutoff (2 * n) -> Dvd.dvd q R) ->
        norm (hamiltonianMangoldtSumMatrix n -
          hamiltonianRationalSumMatrix n R (hamiltonianPrimeCutoff (2 * n))) +
            2 * (hamiltonianPrimeCutoff (2 * n) : Real) ^ 4 / (n : Real) <= eps) := by
  choose C hC hArithmetic using hamiltonian_prime_operator_comparison
  let H : Real := 65536 * (Real.log 65536 + 1)
  let K : Real := 67108864
  let D : Real := 4 * (H + K + 5 + Real.sqrt (2 * C)) + 8
  have hH : 0 <= H := by
    have h := Real.log_nonneg (by norm_num : (1 : Real) <= 65536)
    dsimp [H]
    positivity
  have hK : 0 <= K := by norm_num [K]
  have hD : 0 < D := by dsimp [D]; positivity
  choose M0 hM0 hCut using hamiltonian_prime_cutoff_admissible (eps / D) (div_pos hEps hD)
  let N0 := max 1 M0
  refine Exists.intro N0 (And.intro (le_max_left _ _) ?_)
  intro n R instN instR hn hMR hDivM hDiv
  let M := 2 * n
  let Q := hamiltonianPrimeCutoff M
  let T := Q ^ 2
  let ell : Real := 1 + Real.log (2 * (M : Real))
  have hM0M : M0 <= M := by
    have h := (le_max_right 1 M0).trans hn
    dsimp [M]
    omega
  have hM : 2 ^ 18 <= M := hM0.trans hM0M
  have hCutoff := hCut M hM0M
  change And (4 <= Q)
    (And ((Q : Real) <= (M : Real) ^ ((1 : Real) / 40))
      (And (8 * Q ^ 2 <= M)
        (And (4 * Q ^ 4 <= M)
          (And ((Q : Real) ^ 5 <= (M : Real))
            (And ((Q : Real) ^ 4 * (M : Real) ^ (15 / 16 : Real) <= (M : Real))
              (And ((M : Real) ^ (8 / 5 : Real) * (Q : Real) <= (M : Real) ^ 2)
                (ell ^ 5 / Real.sqrt (Q : Real) <= eps / D))))))) at hCutoff
  have hQ : 0 < Q := by have h := hCutoff.1; omega
  have hQT : Q <= T := by
    have h := Nat.mul_le_mul_left Q (show 1 <= Q by omega)
    dsimp [T]
    nlinarith only [h]
  have hRange : 4 * T * Q ^ 2 <= M := by
    have h := hCutoff.2.2.2.1
    dsimp [T]
    nlinarith only [h]
  have hRaw := hArithmetic (n := n) (R := R) M Q T hM hQ hQT
    hCutoff.2.2.1 hRange hCutoff.2.1 hDivM hDiv (le_refl _) hMR
  have hnR : (0 : Real) < (n : Real) := by exact_mod_cast (NeZero.pos n)
  have hMR0 : (1 : Real) <= (M : Real) := by exact_mod_cast (show 1 <= M by omega)
  have hMPos : (0 : Real) < (M : Real) := by linarith only [hMR0]
  have hQR : (1 : Real) <= (Q : Real) := by exact_mod_cast (show 1 <= Q by omega)
  have hLogM : 0 <= Real.log (M : Real) := Real.log_nonneg hMR0
  have hEll : 1 <= ell := by
    have h := Real.log_nonneg (show (1 : Real) <= 2 * (M : Real) by linarith only [hMR0])
    dsimp [ell]
    linarith only [h]
  have hLogCompare : 1 + Real.log (M : Real) <= ell := by
    have h := Real.log_le_log hMPos (show (M : Real) <= 2 * (M : Real) by linarith only [hMR0])
    dsimp [ell]
    linarith only [h]
  have hLogSquare := wick_nonnegative_power_le _ _
    (show 0 <= 1 + Real.log (M : Real) by linarith only [hLogM]) hLogCompare 2
  let E : Real := max
    (H + K * (Q : Real) ^ 2 * Real.sqrt (Q : Real) *
      (M : Real) ^ (15 / 16 : Real) * ell ^ 2 + 4 * (Q : Real) ^ 3)
    (Real.sqrt (C * ((M : Real) ^ 2 / (Q : Real) + (M : Real) ^ (8 / 5 : Real)) *
      ell ^ 10) + (Q : Real) * (M : Real) / (2 * (Q : Real) ^ 2))
  have hCastT : (T : Real) = (Q : Real) ^ 2 := by dsimp [T]; norm_cast
  rw [hCastT] at hRaw
  have hArith : norm (hamiltonianMangoldtSumMatrix n -
      hamiltonianRationalSumMatrix n R Q) <= E / (n : Real) := by
    apply hRaw.trans
    apply div_le_div_of_nonneg_right _ hnR.le
    apply max_le_max
    . have h := mul_le_mul_of_nonneg_left hLogSquare
        (show 0 <= K * (Q : Real) ^ 2 * Real.sqrt (Q : Real) *
          (M : Real) ^ (15 / 16 : Real) by positivity)
      change H + K * (Q : Real) ^ 2 * Real.sqrt (Q : Real) *
          (M : Real) ^ (15 / 16 : Real) * (1 + Real.log (M : Real)) ^ 2 +
          4 * (Q : Real) ^ 3 <= _
      nlinarith only [h]
    . change Real.sqrt (C * ((M : Real) ^ 2 / (Q : Real) +
        (M : Real) ^ (8 / 5 : Real)) * ell ^ 10) +
        (Q : Real) * ((M : Real) / (2 * (Q : Real) ^ 2)) <= _
      exact le_of_eq (by ring)
  have hBudget := hamiltonian_prime_operator_scalar_budget H K C
    (M : Real) (n : Real) (Q : Real) ell
    ((M : Real) ^ (15 / 16 : Real)) ((M : Real) ^ (8 / 5 : Real))
    hH hK hC.le hMR0 hnR hQR hEll (by positivity) (by positivity)
    (by dsimp [M]; push_cast; linarith)
    hCutoff.2.2.2.2.1 hCutoff.2.2.2.2.2.1 hCutoff.2.2.2.2.2.2.1
  change E / (n : Real) + 2 * (Q : Real) ^ 4 / (n : Real) <=
    D * ell ^ 5 / Real.sqrt (Q : Real) at hBudget
  have hScale : D * ell ^ 5 / Real.sqrt (Q : Real) <= eps := by
    calc
      _ = D * (ell ^ 5 / Real.sqrt (Q : Real)) := by ring
      _ <= D * (eps / D) := mul_le_mul_of_nonneg_left hCutoff.2.2.2.2.2.2.2 hD.le
      _ = _ := by field_simp
  calc
    norm (hamiltonianMangoldtSumMatrix n -
        hamiltonianRationalSumMatrix n R Q) + 2 * (Q : Real) ^ 4 / (n : Real) <=
      E / (n : Real) + 2 * (Q : Real) ^ 4 / (n : Real) :=
        add_le_add hArith (le_refl _)
    _ <= eps := hBudget.trans hScale

end PrimeFactorOscillations.LPF
