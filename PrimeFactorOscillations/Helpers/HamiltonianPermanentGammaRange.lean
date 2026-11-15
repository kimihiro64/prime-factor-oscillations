/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPermanentPolylogWindow

/-! # Uniform Gamma window range for every fixed polylogarithmic cap

One threshold supplies both the existing complete local-rook cutoff and
a root-scale cap small enough for all three actual Gamma regions.
The threshold is independent of the kernel and the particular admissible cap.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianGammaCoreRoot (x : Real) : Real := x ^ (1 / 8 : Real)

def hamiltonianGammaCoreWidth (x : Real) : Real :=
  1 / hamiltonianGammaCoreRoot x

theorem hamiltonian_permanent_gamma_polylog_range (delta K : Real)
    (hDelta0 : 0 < delta) :
    Exists (fun N0 : Nat => And (16 <= N0)
      (forall n : Nat, N0 <= n -> forall a : Real,
        1 <= a -> a <= (Real.log (n : Real)) ^ K ->
        And (hamiltonianPermanentCutoffThreshold delta a <= Real.sqrt (n : Real))
          (And (64 / delta <= hamiltonianGammaCoreRoot (n : Real))
            (a <= delta ^ 3 * hamiltonianGammaCoreRoot (n : Real) / 1000000)))) := by
  let c := delta ^ 3 / 1000000
  have hc : 0 < c := by dsimp only [c]; positivity
  let cut := hamiltonian_permanent_polylog_real_cutoff delta K hDelta0
  let xCut := cut.choose
  have hCut := cut.choose_spec
  have hLittle := _root_.isLittleO_log_rpow_rpow_atTop (s := (1 / 8 : Real))
    K (by norm_num)
  let small := Filter.eventually_atTop.mp (hLittle.bound hc)
  let xLittle := small.choose
  have hLittleBound := small.choose_spec
  let B := 64 / delta
  have hB : 0 < B := by dsimp only [B]; positivity
  let x0 := 16 + max 0 xCut + max 0 xLittle + B ^ 8
  let N0 := max 16 (Nat.ceil x0)
  refine Exists.intro N0 (And.intro (le_max_left _ _) ?_)
  intro n hn a ha hA
  have hNat : Nat.ceil x0 <= n := le_trans (le_max_right _ _) hn
  have hx : x0 <= (n : Real) := le_trans (Nat.le_ceil x0) (by exact_mod_cast hNat)
  have hCut0 : 0 <= max 0 xCut := le_max_left _ _
  have hCutMax : xCut <= max 0 xCut := le_max_right _ _
  have hLittle0 : 0 <= max 0 xLittle := le_max_left _ _
  have hLittleMax : xLittle <= max 0 xLittle := le_max_right _ _
  have hB8 : 0 <= B ^ 8 := pow_nonneg hB.le 8
  have hxCut : xCut <= (n : Real) := by
    dsimp only [x0] at hx
    linarith only [hx, hCut0, hCutMax, hLittle0, hB8]
  have hxLittle : xLittle <= (n : Real) := by
    dsimp only [x0] at hx
    linarith only [hx, hCut0, hLittle0, hLittleMax, hB8]
  have hxRoot : B ^ 8 <= (n : Real) := by
    dsimp only [x0] at hx
    linarith only [hx, hCut0, hLittle0]
  have hx16 : (16 : Real) <= (n : Real) := by
    have hn16 : 16 <= n := le_trans (le_max_left _ _) hn
    exact_mod_cast hn16
  have hx1 : 1 <= (n : Real) := by linarith only [hx16]
  have hx0 : 0 <= (n : Real) := Nat.cast_nonneg n
  have hLog0 : 0 <= Real.log (n : Real) := Real.log_nonneg hx1
  have hRaw := hLittleBound (n : Real) hxLittle
  simp only [Real.norm_eq_abs] at hRaw
  rw [abs_of_nonneg (Real.rpow_nonneg hLog0 K),
    abs_of_nonneg (Real.rpow_nonneg hx0 (1 / 8 : Real))] at hRaw
  have hRootBase : (B ^ 8) ^ (1 / 8 : Real) = B := by
    calc
      _ = (B ^ (8 : Real)) ^ (1 / 8 : Real) :=
        congrArg (fun u : Real => u ^ (1 / 8 : Real))
          (Real.rpow_natCast B 8).symm
      _ = B ^ ((8 : Real) * (1 / 8 : Real)) := (Real.rpow_mul hB.le _ _).symm
      _ = B := by norm_num
  have hRoot := Real.rpow_le_rpow hB8 hxRoot (by norm_num : (0 : Real) <= 1 / 8)
  rw [hRootBase] at hRoot
  refine And.intro (hCut (n : Real) hxCut a ha hA) (And.intro hRoot ?_)
  calc
    _ <= (Real.log (n : Real)) ^ K := hA
    _ <= c * ((n : Real) ^ (1 / 8 : Real)) := hRaw
    _ = _ := by dsimp only [c, hamiltonianGammaCoreRoot]; ring

end PrimeFactorOscillations
