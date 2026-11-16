/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCoprimeInteriorLower

/-! # Complete signed positive native endpoint-path lower bound

Independent cycle mass dominates the complete avoidance allowance.
No signed term is discarded: the base minus avoidance difference is
transferred with its exact reciprocal-totient cutting coefficient.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_coprime_avoidance_half_mass
    (n : Nat) (hn : 512 <= n)
    (hBudget : 1 + 170 * ((n : Real) / (n.totient : Real)) +
      64 * ((n : Real) / (n.totient : Real)) * Real.log (2 * (n : Real)) +
      Real.log (8 * ((n - 2 : Nat) : Real)) <=
        (n : Real) / (4 * ((n : Real) / (n.totient : Real)) ^ 2)) :
    Real.exp (-((n - 2 : Nat) : Real) -
        ((n.totient : Real) ^ 2 / (2 * (n : Real)) - 2) / 2 +
          64 * ((n : Real) / (n.totient : Real)) * Real.log (2 * (n : Real))) <=
      Real.exp (-((n - 2 : Nat) : Real) -
          170 * ((n : Real) / (n.totient : Real))) /
        (8 * ((n - 2 : Nat) : Real)) := by
  let A := (n : Real) / (n.totient : Real)
  let m : Real := (n - 2 : Nat)
  have hnPos : 0 < (n : Real) := by exact_mod_cast (show 0 < n by omega)
  have hdPos : 0 < (n.totient : Real) := by
    exact_mod_cast Nat.totient_pos.mpr (show 0 < n by omega)
  have hmPos : 0 < m := by dsimp only [m]; exact_mod_cast (show 0 < n - 2 by omega)
  have hSaving : (n : Real) / (4 * A ^ 2) =
      (n.totient : Real) ^ 2 / (4 * (n : Real)) := by
    dsimp only [A]
    field_simp [ne_of_gt hnPos, ne_of_gt hdPos]
    <;> ring
  have hCompensation : ((n.totient : Real) ^ 2 / (2 * (n : Real)) - 2) / 2 =
      (n.totient : Real) ^ 2 / (4 * (n : Real)) - 1 := by
    field_simp [ne_of_gt hnPos]
    <;> ring
  have hBound : 1 + 170 * A + 64 * A * Real.log (2 * (n : Real)) +
      Real.log (8 * m) <= (n.totient : Real) ^ 2 / (4 * (n : Real)) := by
    rw [<- hSaving]
    exact hBudget
  have hExponent : -m -
      ((n.totient : Real) ^ 2 / (2 * (n : Real)) - 2) / 2 +
        64 * A * Real.log (2 * (n : Real)) <=
      (-m - 170 * A) - Real.log (8 * m) := by
    rw [hCompensation]
    linarith only [hBound]
  have hExp := Real.exp_le_exp.mpr hExponent
  rw [Real.exp_sub, Real.exp_log (mul_pos (by norm_num) hmPos)] at hExp
  exact hExp

theorem hamiltonian_coprime_path_positive_lower_uniform :
    exists N0 : Nat, 512 <= N0 /\
      forall (n : Nat) [NeZero n] [Nontrivial (ZMod n)], N0 <= n ->
        forall a b : ZMod n, Not (a = b) -> (Odd n \/ Odd (-(a - b)).val) ->
          0 < hamiltonianPrescribedPathSum (hamiltonianCoprimeKernel (n := n)) a b /\
          Real.exp (-((n - 2 : Nat) : Real) -
              170 * ((n : Real) / (n.totient : Real))) /
            (8 * ((n - 2 : Nat) : Real) * (n.totient : Real)) <=
          hamiltonianPrescribedPathSum (hamiltonianCoprimeKernel (n := n)) a b := by
  choose C hC hBaseCount using hamiltonian_coprime_interior_cycle_lower_uniform
  choose B hB hBudget using hamiltonian_coprime_path_uniform_parameter_budget
    1 1 (by norm_num) (by norm_num)
  let N0 := max C B
  refine Exists.intro N0 (And.intro (hB.trans (le_max_right _ _)) ?_)
  intro n inst instN hn a b hab hParity
  have hnC : C <= n := (le_max_left _ _).trans hn
  have hnB : B <= n := (le_max_right _ _).trans hn
  have hn512 : 512 <= n := hB.trans hnB
  let A := (n : Real) / (n.totient : Real)
  let m : Real := (n - 2 : Nat)
  let L := Real.exp (-m - 170 * A) / (4 * m)
  let V := Real.exp (-m - ((n.totient : Real) ^ 2 / (2 * (n : Real)) - 2) / 2 +
    64 * A * Real.log (2 * (n : Real)))
  have hPar := hBudget n hnB
  have hd : 0 < (n.totient : Real) := by linarith only [hPar.1]
  have hm : 0 < m := by dsimp only [m]; exact_mod_cast (show 0 < n - 2 by omega)
  have hBase : L <= hamiltonianCycleSum (hamiltonianCoprimeInteriorKernel a b) :=
    hBaseCount n hnC a b hab hParity
  have hAvoid : V <= L / 2 := by
    have h := hamiltonian_coprime_avoidance_half_mass n hn512 hPar.2.2.2.2
    have hEq : Real.exp (-m - 170 * A) / (8 * m) = L / 2 := by
      dsimp only [L]
      ring
    exact h.trans_eq hEq
  have hSigned := hamiltonian_coprime_path_full_signed_lower a b hab hParity hPar.1
  have hDifference : L / 2 <=
      hamiltonianCycleSum (hamiltonianCoprimeInteriorKernel a b) - V := by
    linarith only [hBase, hAvoid]
  have hLower := (mul_le_mul_of_nonneg_left hDifference
    (div_nonneg (by norm_num : (0 : Real) <= 1) hd.le)).trans hSigned
  have hEq : (1 / (n.totient : Real)) * (L / 2) =
      Real.exp (-m - 170 * A) / (8 * m * (n.totient : Real)) := by
    dsimp only [L]
    ring
  rw [hEq] at hLower
  refine And.intro ?_ hLower
  exact (div_pos (Real.exp_pos _)
    (mul_pos (mul_pos (by norm_num) hm) hd)).trans_le hLower

end PrimeFactorOscillations
