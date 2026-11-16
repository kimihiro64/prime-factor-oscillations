/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCountPowerDecay
import PrimeFactorOscillations.Helpers.HamiltonianPrimeStochasticScaling

/-! # The actual prime cross block satisfies the relative counting theorem -/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

theorem hamiltonian_actual_prime_relative_count (eta : Real) (hEta : 0 < eta) :
    exists M0 : Nat, And (256 <= M0)
      (forall m : Nat, M0 <= m ->
        exists z : Sum (Fin m) (Fin m) -> Real,
          norm z <= eta /\
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
          norm (centeredKernel (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z)
            (1 / (m : Real))) <= 3 / 5 /\
          abs (hamiltonianBipartiteCountRatio
            (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z) - 1) <=
              (m : Real) ^ (-3 / 5 : Real)) := by
  choose N1 hN1 hScaling using hamiltonian_prime_cross_stochastic_scaling eta hEta
  choose N2 hN2 hCount using stochastic_three_fifths_cycle_power_uniform.{0}
  choose N3 hN3 hLog using hamiltonian_log_terminal_lower 64
  let M0 := max N1 (max N2 N3)
  refine Exists.intro M0 (And.intro (by dsimp only [M0]; omega) ?_)
  intro m hm
  have hm1 : N1 <= m := by dsimp only [M0] at hm; omega
  have hm2 : N2 <= m := by dsimp only [M0] at hm; omega
  have hm3 : N3 <= 2 * m := by dsimp only [M0] at hm; omega
  have hmPos : 0 < m := by omega
  haveI : NeZero m := { out := by omega }
  choose z hZ hPos hNonneg hRows hCols hSupport hCap hGap using hScaling m hm1
  let L := Real.log (2 * m : Nat)
  let a := (3 / 5 : Real) * L
  have hL : 64 <= L := hLog (2 * m) hm3
  have ha : 1 <= a := by dsimp only [a]; linarith only [hL]
  have hmR : 0 < (m : Real) := Nat.cast_pos.mpr hmPos
  have hq : (Fintype.card (Fin m) : Real) * (1 / (m : Real)) = 1 := by
    simp only [Fintype.card_fin]
    field_simp [ne_of_gt hmR]
  have hUpper (i j : Fin m) :
      hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z i j <=
        a * (1 / (m : Real)) := by
    simpa only [a, L, div_eq_mul_inv, one_mul] using hCap i j
  have hSplit : L = Real.log 2 + Real.log (m : Real) := by
    dsimp only [L]
    push_cast
    exact Real.log_mul (by norm_num : Not ((2 : Real) = 0)) (ne_of_gt hmR)
  have hLog2 : Real.log (2 : Real) <= 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
    linarith only [h]
  have hDensity : a - 1 <= (3 / 5 : Real) * Real.log (Fintype.card (Fin m) : Real) := by
    simp only [Fintype.card_fin]
    dsimp only [a]
    linarith only [hSplit, hLog2]
  have hResult := hCount (Fin m) (by simpa only [Fintype.card_fin] using hm2)
    (hamiltonianScaledCross (hamiltonianPrimeCrossBlock m) z) (1 / (m : Real)) a
    hq ha hRows hCols hNonneg hUpper hGap hDensity
  simp only [Fintype.card_fin] at hResult
  exact Exists.intro z (And.intro hZ (And.intro hPos (And.intro hNonneg
    (And.intro hRows (And.intro hCols (And.intro hSupport (And.intro hCap
      (And.intro hGap hResult))))))))

end PrimeFactorOscillations.LPF
