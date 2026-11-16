/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCoprimeEvenBaseLower
import PrimeFactorOscillations.Helpers.HamiltonianCoprimeOddBaseLower

/-! # One native positive interior-cycle lower count through all moduli -/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_coprime_odd_shift_cross_endpoints
    (k : Nat) [NeZero k] (a b : ZMod (2 * k))
    (hOdd : Odd (-(a - b)).val) :
    exists i j : Fin k, ({a, b} : Finset (ZMod (2 * k))) =
      {hamiltonianCoprimeParityEquiv k (Sum.inl i),
        hamiltonianCoprimeParityEquiv k (Sum.inr j)} := by
  let e := hamiltonianCoprimeParityEquiv k
  have hEval (x : ZMod (2 * k)) (s : Sum (Fin k) (Fin k))
      (h : e.symm x = s) : x = e s := by
    rw [<- h, e.apply_symm_apply]
  have hValues (s : Sum (Fin k) (Fin k)) :
      (e s).val % 2 = Sum.elim (fun _ => 0) (fun _ => 1) s := by
    rw [hamiltonian_coprime_parity_equiv_value]
    cases s <;> simp [LPF.hamiltonianParityIndex]
  let t : Nat := hOdd.choose
  have hOriginal : (-(a - b)).val = 2 * t + 1 := hOdd.choose_spec
  have hNeg : -(a - b) = b - a := neg_sub a b
  have hOddEq : (b - a).val = 2 * t + 1 :=
    (congrArg (fun z : ZMod (2 * k) => z.val) hNeg).symm.trans hOriginal
  have hDiff := hamiltonian_even_difference_parity (dvd_mul_right 2 k) b a
  have hSum : (a.val + b.val) % 2 = 1 := by omega
  cases hA : e.symm a with
  | inl i =>
      have ha0 : a.val % 2 = 0 := by
        rw [hEval a (Sum.inl i) hA]
        exact hValues (Sum.inl i)
      cases hB : e.symm b with
      | inl j =>
          have hb0 : b.val % 2 = 0 := by
            rw [hEval b (Sum.inl j) hB]
            exact hValues (Sum.inl j)
          omega
      | inr j =>
          refine Exists.intro i (Exists.intro j ?_)
          rw [hEval a (Sum.inl i) hA, hEval b (Sum.inr j) hB]
  | inr i =>
      have ha1 : a.val % 2 = 1 := by
        rw [hEval a (Sum.inr i) hA]
        exact hValues (Sum.inr i)
      cases hB : e.symm b with
      | inl j =>
          refine Exists.intro j (Exists.intro i ?_)
          rw [hEval a (Sum.inr i) hA, hEval b (Sum.inl j) hB]
          exact Finset.pair_comm _ _
      | inr j =>
          have hb1 : b.val % 2 = 1 := by
            rw [hEval b (Sum.inr j) hB]
            exact hValues (Sum.inr j)
          omega

theorem hamiltonian_coprime_even_interior_cycle_lower_uniform :
    exists N0 : Nat, 512 <= N0 /\ forall (n : Nat) [NeZero n], N0 <= n ->
      Dvd.dvd 2 n -> forall a b : ZMod n, Odd (-(a - b)).val ->
        Real.exp (-((n - 2 : Nat) : Real) -
            160 * ((n : Real) / (n.totient : Real))) / ((n - 2 : Nat) : Real) <=
        hamiltonianPrincipalCycleSum (hamiltonianCoprimeKernel (n := n)) {a, b} := by
  choose N0 hN0 hCount using hamiltonian_coprime_even_cross_cycle_lower_uniform
  refine Exists.intro N0 (And.intro hN0 ?_)
  intro n inst hn hEven
  let k := n / 2
  have hSize : 2 * k = n := by
    dsimp only [k]
    simpa only [Nat.mul_comm] using Nat.div_mul_cancel hEven
  have hkPos : 0 < k := by have h := hN0.trans hn; omega
  letI : NeZero k := NeZero.mk (by omega)
  let P : Nat -> Prop := fun q => forall [NeZero q], forall a b : ZMod q,
    Odd (-(a - b)).val ->
      Real.exp (-((q - 2 : Nat) : Real) -
          160 * ((q : Real) / (q.totient : Real))) / ((q - 2 : Nat) : Real) <=
      hamiltonianPrincipalCycleSum (hamiltonianCoprimeKernel (n := q)) {a, b}
  have hPk : P (2 * k) := by
    intro instQ a b hOdd
    choose i j hPair using hamiltonian_coprime_odd_shift_cross_endpoints k a b hOdd
    rw [hPair]
    exact hCount k (by omega) i j
  have hPn : P n := @Eq.mp (P (2 * k)) (P n) (congrArg P hSize) (@hPk)
  exact hPn

theorem hamiltonian_coprime_interior_cycle_lower_uniform :
    exists N0 : Nat, 512 <= N0 /\ forall (n : Nat) [NeZero n], N0 <= n ->
      forall a b : ZMod n, Not (a = b) -> (Odd n \/ Odd (-(a - b)).val) ->
        Real.exp (-((n - 2 : Nat) : Real) -
            170 * ((n : Real) / (n.totient : Real))) /
          (4 * ((n - 2 : Nat) : Real)) <=
        hamiltonianCycleSum (hamiltonianCoprimeInteriorKernel a b) := by
  choose O hO hOddCount using hamiltonian_coprime_odd_interior_cycle_lower_uniform
  choose E hE hEvenCount using hamiltonian_coprime_even_interior_cycle_lower_uniform
  let N0 := max O E
  refine Exists.intro N0 (And.intro (hO.trans (le_max_left _ _)) ?_)
  intro n inst hn a b hab hParity
  have hnO : O <= n := (le_max_left _ _).trans hn
  have hnE : E <= n := (le_max_right _ _).trans hn
  have hn512 : 512 <= n := hO.trans hnO
  let m : Real := (n - 2 : Nat)
  let A := (n : Real) / (n.totient : Real)
  have hm : 0 < m := by dsimp only [m]; exact_mod_cast (show 0 < n - 2 by omega)
  have h4m : 0 < 4 * m := mul_pos (by norm_num) hm
  have hA : 0 <= A :=
    le_trans (by norm_num) (hamiltonian_totient_ratio_ge_one n (by omega))
  rw [hamiltonian_coprime_interior_cycle_principal]
  by_cases hOdd : Odd n
  case pos =>
    have hRaw := hOddCount n hnO hOdd a b hab
    have hExp : Real.exp (-m - 170 * A) <= Real.exp (-m - 170 * A + 5) :=
      Real.exp_le_exp.mpr (by linarith)
    exact (div_le_div_of_nonneg_right hExp h4m.le).trans hRaw
  case neg =>
    have hEven : Even n := by
      apply Classical.byContradiction
      intro hNotEven
      exact hOdd (Nat.not_even_iff_odd.mp hNotEven)
    have hDiv : Dvd.dvd 2 n := Exists.intro hEven.choose (by
      have h := hEven.choose_spec
      omega)
    have hShift : Odd (-(a - b)).val := hParity.resolve_left hOdd
    have hRaw := hEvenCount n hnE hDiv a b hShift
    have hExp : Real.exp (-m - 170 * A) <= Real.exp (-m - 160 * A) :=
      Real.exp_le_exp.mpr (by linarith only [hA])
    have hDen : Real.exp (-m - 160 * A) / (4 * m) <=
        Real.exp (-m - 160 * A) / m := by
      apply le_of_mul_le_mul_right _ h4m
      have hLeft : (Real.exp (-m - 160 * A) / (4 * m)) * (4 * m) =
          Real.exp (-m - 160 * A) := by field_simp [ne_of_gt hm]
      have hRight : (Real.exp (-m - 160 * A) / m) * (4 * m) =
          4 * Real.exp (-m - 160 * A) := by field_simp [ne_of_gt hm]
      rw [hLeft, hRight]
      linarith only [Real.exp_pos (-m - 160 * A)]
    exact ((div_le_div_of_nonneg_right hExp h4m.le).trans hDen).trans hRaw

end PrimeFactorOscillations
