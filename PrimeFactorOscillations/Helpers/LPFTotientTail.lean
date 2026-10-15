/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
An exact uniform coefficient input for the retained singular-series tail:
2*q^3 <= 27*totient(q)^4, with equality at q=6. Its consumer is the
q^(-3/2) envelope on 1/totient(q)^2, not an asserted full tail estimate.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

namespace PrimeFactorOscillations.LPF

private theorem lpf_prod_erase_decompose (S : Finset Nat) (f : Nat -> Real) (a : Nat) :
    S.prod f = (if Membership.mem S a then f a else 1) * (S.erase a).prod f := by
  by_cases ha : Membership.mem S a
  . rw [ite_eq_left ha]
    exact (Finset.mul_prod_erase S f ha).symm
  . have hErase : S.erase a = S := by
      apply Finset.ext
      intro x
      simp only [Finset.mem_erase]
      constructor
      . intro h; exact h.2
      . intro hx
        refine And.intro ?_ hx
        intro hxa
        rw [hxa] at hx
        exact ha hx
    rw [ite_eq_right ha, hErase, one_mul]

theorem lpf_primeProduct_quartic_lower_bound (S : Finset Nat)
    (hS : forall p, Membership.mem S p -> Nat.Prime p) :
    2 * (S.prod (fun p => (p : Real))) ^ 3 <=
      27 * (S.prod (fun p => ((p - 1 : Nat) : Real))) ^ 4 := by
  let U := (S.erase 2).erase 3
  have hBig : (U.prod (fun p => (p : Real))) ^ 3 <=
      (U.prod (fun p => ((p - 1 : Nat) : Real))) ^ 4 := by
    have hPoint : forall p, Membership.mem U p ->
        (p : Real) ^ 3 <= ((p - 1 : Nat) : Real) ^ 4 := by
      intro p hp
      have h3 := Finset.mem_erase.mp hp
      have h2 := Finset.mem_erase.mp h3.2
      have hpPrime := hS p h2.2
      have h4 : 4 <= p := by have h := hpPrime.two_le; omega
      have h4r : (4 : Real) <= (p : Real) := by exact_mod_cast h4
      rw [Nat.cast_sub (show 1 <= p by omega), Nat.cast_one]
      have hNonneg : 0 <= ((p : Real) - 4) ^ 4 + 11 * ((p : Real) - 4) ^ 3 +
          42 * ((p : Real) - 4) ^ 2 + 60 * ((p : Real) - 4) + 17 := by positivity
      nlinarith only [hNonneg]
    have hProd : forall V : Finset Nat, V <= U ->
        V.prod (fun p => (p : Real) ^ 3) <= V.prod (fun p => ((p - 1 : Nat) : Real) ^ 4) := by
      intro V
      induction V using Finset.induction_on with
      | empty => intro h; simp
      | @insert p V hp ih =>
        intro hSub
        have hpU := hSub (Finset.mem_insert_self p V)
        have hVU : V <= U := fun x hx => hSub (Finset.mem_insert_of_mem hx)
        rw [Finset.prod_insert hp, Finset.prod_insert hp]
        exact mul_le_mul (hPoint p hpU) (ih hVU)
          (Finset.prod_nonneg (fun x hx => by positivity)) (by positivity)
    simpa only [Finset.prod_pow] using hProd U (le_refl U)
  have hR : S.prod (fun p => (p : Real)) =
      (if Membership.mem S 2 then 2 else 1) *
        (if Membership.mem S 3 then 3 else 1) * U.prod (fun p => (p : Real)) := by
    rw [lpf_prod_erase_decompose S _ 2, lpf_prod_erase_decompose (S.erase 2) _ 3]
    by_cases h2 : Membership.mem S 2 <;> by_cases h3 : Membership.mem S 3 <;>
      simp [U, h2, h3, Finset.mem_erase] <;> ring
  have hB : S.prod (fun p => ((p - 1 : Nat) : Real)) =
      (if Membership.mem S 3 then 2 else 1) * U.prod (fun p => ((p - 1 : Nat) : Real)) := by
    rw [lpf_prod_erase_decompose S _ 2, lpf_prod_erase_decompose (S.erase 2) _ 3]
    by_cases h2 : Membership.mem S 2 <;> by_cases h3 : Membership.mem S 3 <;>
      simp [U, h2, h3, Finset.mem_erase]
  have hR0 : 0 <= (U.prod (fun p => (p : Real))) ^ 3 := by positivity
  rw [hR, hB]
  by_cases h2 : Membership.mem S 2 <;> by_cases h3 : Membership.mem S 3 <;>
    simp only [h2, h3, ite_true, ite_false] <;> nlinarith only [hBig, hR0]

theorem lpf_totient_quartic_lower_bound (n : Nat) :
    2 * n ^ 3 <= 27 * n.totient ^ 4 := by
  by_cases hn : n = 0
  . simp [hn]
  have hnPos : 0 < n := Nat.pos_of_ne_zero hn
  let R : Real := n.primeFactors.prod (fun p => (p : Real))
  let B : Real := n.primeFactors.prod (fun p => ((p - 1 : Nat) : Real))
  have hPrime : 2 * R ^ 3 <= 27 * B ^ 4 :=
    lpf_primeProduct_quartic_lower_bound n.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have hRpos : 0 < R := Finset.prod_pos (fun p hp => by
    exact_mod_cast Nat.pos_of_mem_primeFactors hp)
  have hRn : R <= (n : Real) := by
    have h := Nat.le_of_dvd hnPos (Nat.prod_primeFactors_dvd n)
    have hCast : ((n.primeFactors.prod (fun p => p) : Nat) : Real) <= (n : Real) :=
      Nat.cast_le.mpr h
    simpa only [Nat.cast_prod] using hCast
  have hEuler : (n.totient : Real) * R = (n : Real) * B := by
    have h := congrArg (fun a : Nat => (a : Real)) (Nat.totient_mul_prod_primeFactors n)
    simpa only [Nat.cast_mul, Nat.cast_prod] using h
  have hFourth : (n.totient : Real) ^ 4 * R ^ 4 = (n : Real) ^ 4 * B ^ 4 := by
    have h := congrArg (fun a : Real => a ^ 4) hEuler
    simpa only [mul_pow] using h
  have hOne := mul_le_mul_of_nonneg_left hPrime (pow_nonneg (Nat.cast_nonneg n) 4)
  have hTwo := mul_le_mul_of_nonneg_left hRn
    (by positivity : 0 <= 2 * (n : Real) ^ 3 * R ^ 3)
  have hFinal : 2 * (n : Real) ^ 3 <= 27 * (n.totient : Real) ^ 4 := by
    apply (mul_le_mul_iff_of_pos_right (pow_pos hRpos 4)).mp
    nlinarith only [hOne, hTwo, hFourth]
  exact_mod_cast hFinal

theorem lpf_totient_inverse_sq_power_bound (q : Nat) (hq : 0 < q) :
    1 / (q.totient : Real) ^ 2 <= 4 / (q : Real) ^ (3 / 2 : Real) := by
  have hqR : (0 : Real) < (q : Real) := by exact_mod_cast hq
  have hPhi : (0 : Real) < (q.totient : Real) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hQuartic : 2 * (q : Real) ^ 3 <= 27 * (q.totient : Real) ^ 4 := by
    exact_mod_cast lpf_totient_quartic_lower_bound q
  have hSqrt : Real.sqrt ((q : Real) ^ 3) ^ 2 = (q : Real) ^ 3 := Real.sq_sqrt (by positivity)
  have hRoot : Real.sqrt ((q : Real) ^ 3) <= 4 * (q.totient : Real) ^ 2 := by
    have h0 := Real.sqrt_nonneg ((q : Real) ^ 3)
    nlinarith only [hQuartic, hSqrt, h0, sq_nonneg (q.totient : Real)]
  have hRootPos : 0 < Real.sqrt ((q : Real) ^ 3) := Real.sqrt_pos.mpr (by positivity)
  have hBound : 1 / (q.totient : Real) ^ 2 <= 4 / Real.sqrt ((q : Real) ^ 3) := by
    apply (mul_le_mul_iff_of_pos_right (mul_pos (pow_pos hPhi 2) hRootPos)).mp
    field_simp
    nlinarith only [hRoot]
  have hConvert : Real.sqrt ((q : Real) ^ 3) = (q : Real) ^ (3 / 2 : Real) := by
    rw [Real.sqrt_eq_rpow, <- Real.rpow_natCast, <- Real.rpow_mul hqR.le]
    norm_num
  rwa [hConvert] at hBound

end PrimeFactorOscillations.LPF
