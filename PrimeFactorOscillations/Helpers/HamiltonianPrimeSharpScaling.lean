/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPrimeCircleAsymptotic

/-! # The sharp repaired prime half-gap on the same counting witness -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

theorem hamiltonian_prime_cross_sharp_scaling (eps : Real) (hEps : 0 < eps) :
    exists M0 : Nat, And (256 <= M0)
      (forall m : Nat, M0 <= m ->
        exists z : Sum (Fin m) (Fin m) -> Real,
          norm z <= eps /\
          (forall i, 0 < 1 + z i) /\
          (forall i j, 0 <= hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z i j) /\
          (forall i, Finset.univ.sum (fun j =>
            hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z i j) = 1) /\
          (forall j, Finset.univ.sum (fun i =>
            hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z i j) = 1) /\
          (forall i j, hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z i j = 0 <->
            hamiltonianPrimeCrossBlock m i j = 0) /\
          (forall i j, hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z i j <=
            ((3 / 5 : Real) * Real.log (2 * m : Nat)) / (m : Real)) /\
          norm (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z -
            hamiltonianPrimeCrossBlock m) <= eps /\
          norm (centeredKernel (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z)
            (1 / (m : Real))) <= (1 / 2 : Real) + eps /\
          abs (hamiltonianBipartiteCountRatio
            (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z) - 1) <=
              (m : Real) ^ (-3 / 5 : Real)) := by
  let eta := min (1 : Real) (eps / 12)
  have hEta : 0 < eta := lt_min (by norm_num) (div_pos hEps (by norm_num))
  have hEta1 : eta <= 1 := min_le_left _ _
  have hEtaEps : eta <= eps / 12 := min_le_right _ _
  choose N1 hN1 hCount using hamiltonian_actual_prime_relative_count eta hEta
  choose N2 hN2 hDegree using hamiltonian_prime_cross_degree_uniform 1 (by norm_num)
  choose N3 hN3 hGap using hamiltonian_prime_cross_operator_uniform (eps / 2) (by positivity)
  let M0 := max N1 (max N2 N3)
  refine Exists.intro M0 (And.intro (by dsimp only [M0]; omega) ?_)
  intro m hm
  have hm1 : N1 <= m := by dsimp only [M0] at hm; omega
  have hm2 : N2 <= m := by dsimp only [M0] at hm; omega
  have hm3 : N3 <= m := by dsimp only [M0] at hm; omega
  have hmPos : 1 <= m := by omega
  haveI : NeZero m := { out := by omega }
  choose z hZ hPos hNonneg hRows hCols hSupport hCap hOldGap hCountError using hCount m hm1
  have hZpoint (i : Sum (Fin m) (Fin m)) : abs (z i) <= eta :=
    (pi_norm_le_iff_of_nonneg hEta.le).mp hZ i
  have hRowUpper (i : Fin m) :
      Finset.univ.sum (fun j => hamiltonianPrimeCrossBlock m i j) <= 2 := by
    have h := (abs_le.mp ((hDegree m hm2).1 i)).2
    linarith only [h]
  have hColUpper (j : Fin m) :
      Finset.univ.sum (fun i => hamiltonianPrimeCrossBlock m i j) <= 2 := by
    have h := (abs_le.mp ((hDegree m hm2).2 j)).2
    linarith only [h]
  have hError := hamiltonian_scaled_cross_operator_error (hamiltonianPrimeCrossBlock m) z
    eta 2 hEta.le (by norm_num) hZpoint (hamiltonian_prime_cross_nonnegative m hmPos)
    hRowUpper hColUpper
  have hEtaSq : eta ^ 2 <= eta := by nlinarith only [hEta, hEta1]
  have hErrHalf : norm (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z -
      hamiltonianPrimeCrossBlock m) <= eps / 2 := by
    have hBudget : (2 * eta + eta ^ 2) * 2 <= eps / 2 := by
      nlinarith only [hEtaSq, hEtaEps]
    exact hError.trans hBudget
  have hFinalGap :
      norm (centeredKernel (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z)
        (1 / (m : Real))) <= (1 / 2 : Real) + eps := by
    have hId : centeredKernel (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z)
        (1 / (m : Real)) =
        (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z - hamiltonianPrimeCrossBlock m) +
          centeredKernel (hamiltonianPrimeCrossBlock m) (1 / (m : Real)) := by
      unfold centeredKernel
      abel
    rw [hId]
    have h := norm_add_le
      (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z - hamiltonianPrimeCrossBlock m)
      (centeredKernel (hamiltonianPrimeCrossBlock m) (1 / (m : Real)))
    have hOld := hGap m hm3
    linarith only [h, hOld, hErrHalf]
  refine Exists.intro z (And.intro (hZ.trans (by linarith only [hEtaEps, hEps])) ?_)
  exact And.intro hPos (And.intro hNonneg (And.intro hRows (And.intro hCols
    (And.intro hSupport (And.intro hCap (And.intro (hErrHalf.trans (by linarith only [hEps]))
      (And.intro hFinalGap hCountError)))))))

end PrimeFactorOscillations.LPF
