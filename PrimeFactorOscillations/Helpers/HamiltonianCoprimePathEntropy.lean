/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCoprimeCycleEntropy
import PrimeFactorOscillations.Helpers.HamiltonianCoprimePathUpper

/-! # Uniform actual integer coprime-path entropy through every modulus -/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_coprime_path_log_count_uniform :
    exists N0 : Nat, 512 <= N0 /\ forall (n : Nat) [NeZero n], N0 <= n ->
      forall a b : ZMod n, Not (a = b) -> (Odd n \/ Odd (-(a - b)).val) ->
        0 < (hamiltonianGraphPathCount (hamiltonianCoprimeRelation (n := n)) a b : Real) /\
        abs (Real.log
          (hamiltonianGraphPathCount (hamiltonianCoprimeRelation (n := n)) a b : Real) -
          hamiltonianCoprimeEntropyMain n) <=
            200 * ((n : Real) / (n.totient : Real)) * Real.log (2 * (n : Real)) := by
  choose N0 hN0 hCount using hamiltonian_coprime_path_positive_lower_uniform
  refine Exists.intro N0 (And.intro hN0 ?_)
  intro n inst hn a b hab hParity
  have hn512 : 512 <= n := hN0.trans hn
  letI : Fact (1 < n) := Fact.mk (by omega)
  letI : Nontrivial (ZMod n) := inferInstance
  let A := (n : Real) / (n.totient : Real)
  let d : Real := n.totient
  let m : Real := (n - 2 : Nat)
  let L := Real.log (2 * (n : Real))
  let Z := hamiltonianPrescribedPathSum (hamiltonianCoprimeKernel (n := n)) a b
  let H : Real := hamiltonianGraphPathCount (hamiltonianCoprimeRelation (n := n)) a b
  have hRaw := hCount n hn a b hab hParity
  have hUpper := hamiltonian_coprime_path_upper (by omega) a b hab
  have hdPos : 0 < d := by
    dsimp only [d]
    exact_mod_cast Nat.totient_pos.mpr (show 0 < n by omega)
  have hd1 : 1 <= d := by
    dsimp only [d]
    exact_mod_cast Nat.totient_pos.mpr (show 0 < n by omega)
  have hmPos : 0 < m := by dsimp only [m]; exact_mod_cast (show 0 < n - 2 by omega)
  have hDenPos : 0 < 8 * m * d := mul_pos (mul_pos (by norm_num) hmPos) hdPos
  have hZPos : 0 < Z := hRaw.1
  have hWeight : H = d ^ (n - 1) * Z := by
    dsimp only [H, Z, d]
    rw [hamiltonian_coprime_path_weight]
    field_simp [ne_of_gt hdPos]
  have hHPos : 0 < H := by
    rw [hWeight]
    exact mul_pos (pow_pos hdPos _) hZPos
  have hLogH : Real.log H = ((n - 1 : Nat) : Real) * Real.log d + Real.log Z := by
    rw [hWeight, Real.log_mul (ne_of_gt (pow_pos hdPos _)) (ne_of_gt hZPos), Real.log_pow]
  have hLogLower : -m - 170 * A - Real.log (8 * m * d) <= Real.log Z := by
    have h := Real.log_le_log (div_pos (Real.exp_pos _) hDenPos) hRaw.2
    rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt hDenPos), Real.log_exp] at h
    exact h
  rw [Real.log_mul (ne_of_gt (mul_pos (by norm_num) hmPos)) (ne_of_gt hdPos)] at hLogLower
  have hLogUpper : Real.log Z <= -((n - 1 : Nat) : Real) + 16 * A * L := by
    have h := Real.log_le_log hZPos hUpper
    rw [Real.log_exp] at h
    exact h
  have hL1 : 1 <= L := hamiltonian_log_twice_dimension_lower n (by omega)
  have hL0 : 0 <= L := le_trans (by norm_num) hL1
  have hA1 : 1 <= A := hamiltonian_totient_ratio_ge_one n (by omega)
  have hA0 : 0 <= A := le_trans (by norm_num) hA1
  have hALgeA : A <= A * L := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hL1 hA0
  have hALgeL : L <= A * L := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hA1 hL0
  have hAL1 : 1 <= A * L := hA1.trans hALgeA
  have hLogd0 : 0 <= Real.log d := Real.log_nonneg hd1
  have hLogdL : Real.log d <= L := by
    apply Real.log_le_log hdPos
    have hTot : d <= (n : Real) := by dsimp only [d]; exact_mod_cast Nat.totient_le n
    have hn0 : 0 <= (n : Real) := Nat.cast_nonneg n
    linarith only [hTot, hn0]
  have hMAdd : m + 2 = (n : Real) := by
    dsimp only [m]
    exact_mod_cast Nat.sub_add_cancel (show 2 <= n by omega)
  have hKAdd : ((n - 1 : Nat) : Real) + 1 = (n : Real) := by
    exact_mod_cast Nat.sub_add_cancel (show 1 <= n by omega)
  have hK : ((n - 1 : Nat) : Real) = (n : Real) - 1 := by linarith only [hKAdd]
  have hArg : 8 * m <= (2 * (n : Real)) ^ 2 := by
    nlinarith only [hMAdd, sq_nonneg ((n : Real) - 1)]
  have hLog8m : Real.log (8 * m) <= 2 * L := by
    have h := Real.log_le_log (mul_pos (by norm_num) hmPos) hArg
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hCenter : Real.log H - hamiltonianCoprimeEntropyMain n =
      Real.log Z - Real.log d + (n : Real) := by
    unfold hamiltonianCoprimeEntropyMain
    rw [hLogH, hK]
    change ((n : Real) - 1) * Real.log d + Real.log Z -
      (n : Real) * (Real.log d - 1) = _
    ring
  refine And.intro hHPos ?_
  rw [hCenter]
  apply abs_le.mpr
  refine And.intro ?_ ?_
  . linarith only [hLogLower, hLogdL, hLog8m, hMAdd, hALgeA, hALgeL, hAL1]
  . rw [hK] at hLogUpper
    linarith only [hLogUpper, hLogd0, hAL1]

theorem hamiltonian_coprime_path_entropy_uniform :
    exists N0 : Nat, 512 <= N0 /\ forall (n : Nat) [NeZero n], N0 <= n ->
      forall a b : ZMod n, Not (a = b) -> (Odd n \/ Odd (-(a - b)).val) ->
        0 < (hamiltonianGraphPathCount (hamiltonianCoprimeRelation (n := n)) a b : Real) /\
        abs (Real.log
          (hamiltonianGraphPathCount (hamiltonianCoprimeRelation (n := n)) a b : Real) -
          hamiltonianCoprimeEntropyMain n) <=
            200 * ((n : Real) * (n.totient : Real) ^ (-1 / 8 : Real) *
              Real.log (2 * (n : Real))) := by
  choose N0 hN0 hCount using hamiltonian_coprime_path_log_count_uniform
  refine Exists.intro N0 (And.intro hN0 ?_)
  intro n inst hn a b hab hParity
  have h := hCount n hn a b hab hParity
  have hd1 : (1 : Real) <= n.totient := by
    exact_mod_cast Nat.totient_pos.mpr (show 0 < n by have h := hN0.trans hn; omega)
  have hL0 : 0 <= Real.log (2 * (n : Real)) :=
    le_trans (by norm_num) (hamiltonian_log_twice_dimension_lower n (by omega))
  have hPow := Real.rpow_le_rpow_of_exponent_le hd1
    (by norm_num : (-1 : Real) <= -1 / 8)
  have hInv : 1 / (n.totient : Real) <= (n.totient : Real) ^ (-1 / 8 : Real) := by
    simpa only [Real.rpow_neg_one, one_div] using hPow
  have hA : (n : Real) / (n.totient : Real) <=
      (n : Real) * (n.totient : Real) ^ (-1 / 8 : Real) := by
    have h := mul_le_mul_of_nonneg_left hInv (Nat.cast_nonneg n)
    simpa only [div_eq_mul_inv, one_mul] using h
  refine And.intro h.1 (h.2.trans ?_)
  calc
    _ <= 200 * ((n : Real) * (n.totient : Real) ^ (-1 / 8 : Real)) *
        Real.log (2 * (n : Real)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hA (by norm_num)) hL0
    _ = _ := by ring

theorem hamiltonian_coprime_even_shift_parity {n : Nat} [NeZero n]
    (hEven : Dvd.dvd 2 n) (a b : ZMod n) :
    Odd (-(a - b)).val <-> Not (a.val % 2 = b.val % 2) := by
  have hNeg : -(a - b) = b - a := neg_sub a b
  have hVal : (-(a - b)).val = (b - a).val :=
    congrArg (fun z : ZMod n => z.val) hNeg
  have hDiff := hamiltonian_even_difference_parity hEven b a
  constructor
  case mp =>
    intro hOdd
    have hEq := hOdd.choose_spec
    omega
  case mpr =>
    intro hNot
    refine Exists.intro ((-(a - b)).val / 2) ?_
    omega

theorem hamiltonian_coprime_path_entropy_compatible_endpoints :
    exists N0 : Nat, 512 <= N0 /\ forall (n : Nat) [NeZero n], N0 <= n ->
      forall a b : ZMod n, Not (a = b) ->
        (Odd n \/ Not (a.val % 2 = b.val % 2)) ->
        0 < (hamiltonianGraphPathCount (hamiltonianCoprimeRelation (n := n)) a b : Real) /\
        abs (Real.log
          (hamiltonianGraphPathCount (hamiltonianCoprimeRelation (n := n)) a b : Real) -
          hamiltonianCoprimeEntropyMain n) <=
            200 * ((n : Real) * (n.totient : Real) ^ (-1 / 8 : Real) *
              Real.log (2 * (n : Real))) := by
  choose N0 hN0 hCount using hamiltonian_coprime_path_entropy_uniform
  refine Exists.intro N0 (And.intro hN0 ?_)
  intro n inst hn a b hab hParity
  apply hCount n hn a b hab
  by_cases hOdd : Odd n
  case pos => exact Or.inl hOdd
  case neg =>
    have hEven : Even n := by
      apply Classical.byContradiction
      intro hNotEven
      exact hOdd (Nat.not_even_iff_odd.mp hNotEven)
    have hDiv : Dvd.dvd 2 n := Exists.intro hEven.choose (by
      have h := hEven.choose_spec
      omega)
    exact Or.inr ((hamiltonian_coprime_even_shift_parity hDiv a b).mpr
      (hParity.resolve_left hOdd))

end PrimeFactorOscillations
