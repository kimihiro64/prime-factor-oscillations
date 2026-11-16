/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianPrimeMajorArc
import PrimeFactorOscillations.Helpers.HamiltonianReferencePhysicalCutoff

/-! # Complete arithmetic prime-sum operator comparison

One arithmetic constant precedes all matrix orders, physical scales,
rational cutoffs and auxiliary grids. Both major and minor frequencies
are controlled for the actual Mangoldt matrix. The full signed rational
model remains the main term. No unestimated arc-extension term remains.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations.LPF

theorem hamiltonian_prime_operator_comparison :
    exists C : Real, And (0 < C)
      (forall {n R : Nat} [NeZero n] [NeZero R] (M Q T : Nat),
        2 ^ 18 <= M -> 0 < Q -> Q <= T -> 8 * T <= M ->
        4 * T * Q ^ 2 <= M ->
        (Q : Real) <= (M : Real) ^ ((1 : Real) / 40) ->
        Dvd.dvd M R -> (forall q, 0 < q -> q <= Q -> Dvd.dvd q R) ->
        2 * n <= M -> M < R ->
        norm (hamiltonianMangoldtSumMatrix n - hamiltonianRationalSumMatrix n R Q) <=
          max
            (65536 * (Real.log 65536 + 1) +
              67108864 * (T : Real) * Real.sqrt (Q : Real) *
                (M : Real) ^ (15 / 16 : Real) * (1 + Real.log (M : Real)) ^ 2 +
              4 * (Q : Real) ^ 3)
            (Real.sqrt (C * ((M : Real) ^ 2 / (Q : Real) +
                (M : Real) ^ (8 / 5 : Real)) *
                (1 + Real.log (2 * (M : Real))) ^ 10) +
              (Q : Real) * ((M : Real) / (2 * (T : Real)))) / (n : Real)) := by
  choose C hC hMinorSource using hamiltonian_prime_prefix_minor_logarithmic
  refine Exists.intro C (And.intro hC ?_)
  intro n R instN instR M Q T hM hQ hQT hEight hRange hPower hDivM hDiv hSize hMR
  let W := (R / M) * T
  let D := R / (4 * Q ^ 2)
  let Emajor : Real := 65536 * (Real.log 65536 + 1) +
    67108864 * (T : Real) * Real.sqrt (Q : Real) *
      (M : Real) ^ (15 / 16 : Real) * (1 + Real.log (M : Real)) ^ 2
  let Eminor : Real := Real.sqrt (C * ((M : Real) ^ 2 / (Q : Real) +
    (M : Real) ^ (8 / 5 : Real)) * (1 + Real.log (2 * (M : Real))) ^ 10)
  let E : Real := max (Emajor + 4 * (Q : Real) ^ 3)
    (Eminor + (Q : Real) * ((M : Real) / (2 * (T : Real))))
  have hMPos : 0 < M := by omega
  have hT : 0 < T := by omega
  have hRadius := hamiltonian_reference_physical_radius M Q T hMPos hQ hT hDivM hRange
  change And (1 <= W) (And (W <= D)
    (And (2 * D * Q ^ 2 < R)
      ((R : Real) / (2 * (D : Real)) <= 4 * (Q : Real) ^ 2))) at hRadius
  have hMajor : forall u : lpfRationalCenters Q, forall k : Int,
      Membership.mem (Finset.Icc (-(W : Int)) (W : Int)) k ->
      norm (lpfGridIntervalWeight R 0 M (lpfRationalPacketPoint R (u, k)) -
        lpfRationalCoefficient (u.1.val + 1) * lpfGridIntervalKernel R 0 M k) <= Emajor := by
    intro u k hk
    have hqQ : u.1.val + 1 <= Q := by have h := u.1.isLt; omega
    exact hamiltonian_prime_prefix_major u.2 M Q T k
      (by omega) hQ (by omega) hT hEight hDivM
      (hDiv _ (Nat.succ_pos _) hqQ) hqQ hk
  have hMinor : forall x, Not (Membership.mem (lpfRationalGrid R Q W) x) ->
      norm (lpfGridIntervalWeight R 0 M x) <= Eminor := by
    intro x hx
    have hNarrow : Not (Membership.mem (lpfRationalGrid R Q ((R / M) * Q)) x) := by
      intro h
      apply hx
      exact hamiltonian_rational_grid_mono R Q ((R / M) * Q) W
        (Nat.mul_le_mul_left (R / M) hQT) h
    have hSource := hMinorSource (N := R) M Q hM hQ hPower hDivM hDiv (x.val : Int)
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val] at hSource
    have hBound := hSource hNarrow
    have hRadicand : 0 <= C * ((M : Real) ^ 2 / (Q : Real) +
        (M : Real) ^ (8 / 5 : Real)) * (1 + Real.log (2 * (M : Real))) ^ 10 := by
      positivity
    have hSquare := Real.sq_sqrt hRadicand
    have hRoot := Real.sqrt_nonneg (C * ((M : Real) ^ 2 / (Q : Real) +
      (M : Real) ^ (8 / 5 : Real)) * (1 + Real.log (2 * (M : Real))) ^ 10)
    dsimp [Eminor]
    nlinarith only [hBound, hSquare, hRoot, norm_nonneg (lpfGridIntervalWeight R 0 M x)]
  have hR : 0 < R := Nat.pos_of_ne_zero (NeZero.ne R)
  have hB : 0 < R / M := Nat.div_pos (Nat.le_of_dvd hR hDivM) hMPos
  have hFactor : (R : Real) = ((R / M : Nat) : Real) * (M : Real) := by
    exact_mod_cast (Nat.div_mul_cancel hDivM).symm
  have hBR : (0 : Real) < ((R / M : Nat) : Real) := by exact_mod_cast hB
  have hTR : (0 : Real) < (T : Real) := by exact_mod_cast hT
  have hFar : (R : Real) / (2 * (W : Real)) = (M : Real) / (2 * (T : Real)) := by
    dsimp [W]
    rw [hFactor, Nat.cast_mul]
    field_simp
  have hError : forall x, norm (lpfGridIntervalWeight R 0 M x -
      hamiltonianFullRationalReference R Q 0 M x) <= E := by
    intro x
    have h := hamiltonian_full_symbol_comparison Q 0 M W D hRadius.1 hRadius.2.1
      hDiv hRadius.2.2.1 (lpfGridIntervalWeight R 0 M) Emajor Eminor hMajor hMinor x
    apply h.trans
    apply max_le_max
    . have hScaled := mul_le_mul_of_nonneg_left hRadius.2.2.2 (Nat.cast_nonneg Q)
      have hTarget : (Q : Real) * ((R : Real) / (2 * (D : Real))) <=
          4 * (Q : Real) ^ 3 := by nlinarith only [hScaled]
      exact add_le_add (le_refl Emajor) hTarget
    . rw [hFar]
  have hLog : 0 <= Real.log (65536 : Real) := Real.log_nonneg (by norm_num)
  have hE : 0 <= E := by
    apply le_trans _ (le_max_left _ _)
    dsimp [Emajor]
    positivity
  exact hamiltonian_full_reference_operator_error Q M hSize hMR E hE hError

end PrimeFactorOscillations.LPF
