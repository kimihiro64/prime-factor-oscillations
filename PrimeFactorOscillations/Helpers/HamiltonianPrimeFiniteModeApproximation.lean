/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPrimeRationalApproximation
import PrimeFactorOscillations.Helpers.HamiltonianRationalCutoffTransport

/-! # Uniform prime-operator approximation through a fixed finite mode set

For every requested precision one fixed denominator index works at every
sufficiently large order and every admissible auxiliary grid. The moving
rational tail and all major/minor error and frame terms are charged.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

def hamiltonianPrimeFiniteModeModel (n R : Nat) [NeZero R] (K : Nat) :
    Matrix (Fin n) (Fin n) Complex :=
  hamiltonianRationalOperator n R (27 * K ^ 4)
    (fun u => if u.1.val + 1 <= hamiltonianPrimeCutoff (2 * n)
      then lpfRationalCoefficient (u.1.val + 1) else 0)

theorem hamiltonian_prime_finite_mode_budget_uniform
    (K : Nat) (hK : 0 < K) (eps : Real) (hEps : 0 < eps) :
    Exists (fun N0 : Nat => And (1 <= N0)
      (forall {n R : Nat} [NeZero n] [NeZero R],
        N0 <= n -> 2 * n < R -> Dvd.dvd (2 * n) R ->
        (forall q, 0 < q -> q <= hamiltonianPrimeCutoff (2 * n) -> Dvd.dvd q R) ->
        norm (hamiltonianMangoldtSumMatrix n - hamiltonianPrimeFiniteModeModel n R K) <=
          eps + (1 / (K : Real)) * (1 + 2 * eps))) := by
  choose N1 hN1 hApprox using hamiltonian_prime_rational_approximation_uniform eps hEps
  choose M2 hM2 hCutoff using hamiltonian_prime_cutoff_admissible 1 (by norm_num)
  refine Exists.intro (max N1 M2) (And.intro (hN1.trans (le_max_left _ _)) ?_)
  intro n R instN instR hn hMR hDivM hDiv
  let Q := hamiltonianPrimeCutoff (2 * n)
  have hCut := hCutoff (2 * n) (by omega : M2 <= 2 * n)
  have hQFour : 4 <= Q := hCut.1
  have hQ : 0 < Q := by omega
  have hQ1 : 1 <= Q := by omega
  have hQSquare : 1 <= Q ^ 2 := by
    have h := Nat.mul_le_mul hQ1 hQ1
    nlinarith only [h]
  have hQ24 : Q ^ 2 <= Q ^ 4 := by
    have h := Nat.mul_le_mul_left (Q ^ 2) hQSquare
    nlinarith only [h]
  have hFour : 4 * Q ^ 4 <= 2 * n := hCut.2.2.2.1
  have hRange : 4 * Q ^ 2 <= R :=
    (Nat.mul_le_mul_left 4 hQ24).trans (hFour.trans hMR.le)
  have hFull := hApprox (n := n) (R := R) (by omega : N1 <= n) hMR hDivM hDiv
  change norm (hamiltonianMangoldtSumMatrix n - hamiltonianRationalSumMatrix n R Q) +
    2 * (Q : Real) ^ 4 / (n : Real) <= eps at hFull
  have hTail := hamiltonian_rational_fixed_denominator_model_error (n := n) (R := R)
    Q K hQ hK hRange hDiv
  change norm (hamiltonianRationalSumMatrix n R Q - hamiltonianPrimeFiniteModeModel n R K) <=
    (1 / (K : Real)) * (1 + 4 * (Q : Real) ^ 4 / (n : Real)) at hTail
  have hNonnegative : 0 <= 2 * (Q : Real) ^ 4 / (n : Real) := by positivity
  have hNorm0 := norm_nonneg (hamiltonianMangoldtSumMatrix n - hamiltonianRationalSumMatrix n R Q)
  have hFrame : 4 * (Q : Real) ^ 4 / (n : Real) <= 2 * eps := by
    have hPart : 2 * (Q : Real) ^ 4 / (n : Real) <= eps := by
      linarith only [hFull, hNorm0]
    calc
      _ = 2 * (2 * (Q : Real) ^ 4 / (n : Real)) := by ring
      _ <= 2 * eps := mul_le_mul_of_nonneg_left hPart (by norm_num)
  have hInv : 0 <= 1 / (K : Real) := by positivity
  have hScaled := mul_le_mul_of_nonneg_left (add_le_add (le_refl (1 : Real)) hFrame) hInv
  have hTriangle := norm_sub_le_norm_sub_add_norm_sub (hamiltonianMangoldtSumMatrix n)
    (hamiltonianRationalSumMatrix n R Q) (hamiltonianPrimeFiniteModeModel n R K)
  linarith only [hTriangle, hFull, hTail, hScaled, hNonnegative]

theorem hamiltonian_prime_finite_mode_approximation_uniform
    (eta : Real) (hEta : 0 < eta) :
    Exists (fun K : Nat => And (0 < K)
      (Exists (fun N0 : Nat => And (1 <= N0)
        (forall {n R : Nat} [NeZero n] [NeZero R],
          N0 <= n -> 2 * n < R -> Dvd.dvd (2 * n) R ->
          (forall q, 0 < q -> q <= hamiltonianPrimeCutoff (2 * n) -> Dvd.dvd q R) ->
          norm (hamiltonianMangoldtSumMatrix n - hamiltonianPrimeFiniteModeModel n R K) <= eta)))) := by
  choose K hK using exists_nat_gt ((4 : Real) / eta)
  have hKR : 0 < (K : Real) := lt_trans (div_pos (by norm_num) hEta) hK
  have hKNat : 0 < K := Nat.cast_pos.mp hKR
  let eps := min (eta / 4) (1 / 4)
  have hEps : 0 < eps := lt_min (div_pos hEta (by norm_num)) (by norm_num)
  have he1 : eps <= eta / 4 := min_le_left _ _
  have he2 : eps <= (1 / 4 : Real) := min_le_right _ _
  have hInverse : 1 / (K : Real) <= eta / 4 := by
    calc
      _ <= 1 / (4 / eta) := div_le_div_of_nonneg_left (by norm_num)
        (div_pos (by norm_num) hEta) hK.le
      _ = _ := by field_simp [ne_of_gt hEta]
  have hInv0 : 0 <= 1 / (K : Real) := by positivity
  have hFactor : 1 + 2 * eps <= (2 : Real) := by linarith only [he2]
  have hProduct := mul_le_mul_of_nonneg_left hFactor hInv0
  have hBound : eps + (1 / (K : Real)) * (1 + 2 * eps) <= eta := by
    linarith only [he1, hInverse, hProduct, hEta]
  choose N0 hN0 hApprox using hamiltonian_prime_finite_mode_budget_uniform K hKNat eps hEps
  refine Exists.intro K (And.intro hKNat (Exists.intro N0 (And.intro hN0 ?_)))
  intro n R instN instR hn hMR hDivM hDiv
  exact (hApprox hn hMR hDivM hDiv).trans hBound

theorem hamiltonian_prime_finite_mode_factorization (n R : Nat) [NeZero R] (K : Nat) :
    And (Fintype.card (lpfRationalCenters (27 * K ^ 4)) <= (27 * K ^ 4) ^ 2)
      (Exists (fun A : Matrix (Fin n) (lpfRationalCenters (27 * K ^ 4)) Complex =>
        Exists (fun B : Matrix (lpfRationalCenters (27 * K ^ 4)) (Fin n) Complex =>
          hamiltonianPrimeFiniteModeModel n R K = A * B))) := by
  let H := 27 * K ^ 4
  let V := hamiltonianPhysicalFourierFrame n R (fun u => -hamiltonianRationalCenter R H u)
  let W := hamiltonianPhysicalFourierFrame n R (hamiltonianRationalCenter R H)
  let w : lpfRationalCenters H -> Complex :=
    fun u => if u.1.val + 1 <= hamiltonianPrimeCutoff (2 * n)
      then lpfRationalCoefficient (u.1.val + 1) else 0
  let c := Inv.inv (n : Complex)
  refine And.intro (lpfRationalCenters_card_le H)
    (Exists.intro (HSMul.hSMul c (V * Matrix.diagonal w))
      (Exists.intro W.conjTranspose ?_))
  change HSMul.hSMul c ((V * Matrix.diagonal w) * W.conjTranspose) =
    (HSMul.hSMul c (V * Matrix.diagonal w)) * W.conjTranspose
  ext i j
  change c * Finset.univ.sum (fun u => (V * Matrix.diagonal w) i u * W.conjTranspose u j) =
    Finset.univ.sum (fun u => (c * (V * Matrix.diagonal w) i u) * W.conjTranspose u j)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  ring

end PrimeFactorOscillations.LPF
