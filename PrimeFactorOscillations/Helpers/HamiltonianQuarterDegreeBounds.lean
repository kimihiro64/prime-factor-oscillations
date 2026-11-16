/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPrimeCutoffSelection

/-! # The exact prescribed quarter-power degree and both uniform size bounds -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.LPF

def hamiltonianQuarterPrimeDegree (m : Nat) : Nat :=
  Nat.floor ((2 * (m : Real)) ^ (1 / 4 : Real))

theorem hamiltonian_quarter_prime_degree_bounds (m : Nat) (hm : 256 <= m) :
    1 <= hamiltonianQuarterPrimeDegree m /\
      (hamiltonianQuarterPrimeDegree m : Real) <= (m : Real) ^ (1 / 2 : Real) /\
      (m : Real) ^ (1 / 4 : Real) <= 2 * (hamiltonianQuarterPrimeDegree m : Real) := by
  have hM : (256 : Real) <= (m : Real) := by exact_mod_cast hm
  have hM0 : 0 <= (m : Real) := Nat.cast_nonneg _
  have hTwoM : 0 <= 2 * (m : Real) := by linarith only [hM]
  let x : Real := (2 * (m : Real)) ^ (1 / 4 : Real)
  let d := hamiltonianQuarterPrimeDegree m
  have hx0 : 0 <= x := Real.rpow_nonneg hTwoM _
  have hx4 : x ^ 4 = 2 * (m : Real) := by
    calc
      _ = (2 * (m : Real)) ^ ((1 / 4 : Real) * (4 : Real)) := by
        dsimp [x]
        rw [<- Real.rpow_natCast, <- Real.rpow_mul hTwoM]
        norm_num
      _ = _ := by norm_num
  have hx2 : 2 <= x := by
    apply le_of_not_gt
    intro hBad
    have hPower := wick_nonnegative_power_le x 2 hx0 hBad.le 4
    norm_num at hPower
    linarith only [hPower, hx4, hM]
  have hFloor : x < (d : Real) + 1 := Nat.lt_floor_add_one x
  have hdReal : (1 : Real) <= (d : Real) := by linarith only [hFloor, hx2]
  have hd : 1 <= d := by exact_mod_cast hdReal
  have hdX : (d : Real) <= x := Nat.floor_le hx0
  have hBase : 2 * (m : Real) <= (m : Real) ^ 2 := by nlinarith only [hM]
  have hUpper := Real.rpow_le_rpow hTwoM hBase (by norm_num : (0 : Real) <= 1 / 4)
  have hSquarePower :
      ((m : Real) ^ (2 : Nat)) ^ (1 / 4 : Real) = (m : Real) ^ (1 / 2 : Real) := by
    rw [<- Real.rpow_natCast, <- Real.rpow_mul hM0]
    norm_num
  rw [hSquarePower] at hUpper
  have hLower : (m : Real) ^ (1 / 4 : Real) <= x :=
    Real.rpow_le_rpow hM0 (by linarith only [hM]) (by norm_num)
  have hxD : x <= 2 * (d : Real) := by linarith only [hFloor, hx2]
  exact And.intro hd (And.intro (hdX.trans hUpper) (hLower.trans hxD))

end PrimeFactorOscillations.LPF
