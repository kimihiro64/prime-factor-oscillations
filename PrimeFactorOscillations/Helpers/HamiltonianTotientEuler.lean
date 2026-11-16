/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Nat.Totient
import PrimeFactorOscillations.Helpers.LPFPrimeTargetTail

/-! # The exact totient Euler product and its retained large-prime tail

The actual prime-factor set is retained. The existing signed-target
large-prime product theorem also dominates the totient factors, so
its complete divisor and cutoff hypotheses are reused.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianTotientEulerFactor (p : Nat) : Real :=
  (p : Real) / ((p : Real) - 1)

theorem hamiltonian_totient_euler_factor_positive (p : Nat) (hp : 2 <= p) :
    0 < hamiltonianTotientEulerFactor p := by
  have hpR : (2 : Real) <= (p : Real) := by exact_mod_cast hp
  exact div_pos (by linarith only [hpR]) (by linarith only [hpR])

theorem hamiltonian_totient_euler_product (n : Nat) (hn : 0 < n) :
    (n : Real) / (n.totient : Real) =
      n.primeFactors.prod hamiltonianTotientEulerFactor := by
  have hPhi : 0 < (n.totient : Real) := by exact_mod_cast Nat.totient_pos.mpr hn
  have hB : 0 < n.primeFactors.prod (fun p => ((p - 1 : Nat) : Real)) := by
    apply Finset.prod_pos
    intro p hp
    have hPrime := Nat.prime_of_mem_primeFactors hp
    exact_mod_cast (show 0 < p - 1 by have h := hPrime.two_le; omega)
  have hEuler :
      (n.totient : Real) * n.primeFactors.prod (fun p => (p : Real)) =
        (n : Real) * n.primeFactors.prod (fun p => ((p - 1 : Nat) : Real)) := by
    have h := congrArg (fun a : Nat => (a : Real)) (Nat.totient_mul_prod_primeFactors n)
    simpa only [Nat.cast_mul, Nat.cast_prod] using h
  have hProduct : n.primeFactors.prod hamiltonianTotientEulerFactor =
      n.primeFactors.prod (fun p => (p : Real)) /
        n.primeFactors.prod (fun p => ((p - 1 : Nat) : Real)) := by
    rw [<- Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hPrime := Nat.prime_of_mem_primeFactors hp
    unfold hamiltonianTotientEulerFactor
    rw [Nat.cast_sub (show 1 <= p by have h := hPrime.two_le; omega), Nat.cast_one]
  rw [hProduct]
  apply (div_eq_div_iff (ne_of_gt hPhi) (ne_of_gt hB)).mpr
  nlinarith only [hEuler]

theorem hamiltonian_totient_factor_le_singular (p : Nat) (hp : 4 <= p) :
    hamiltonianTotientEulerFactor p <= LPF.singularFactor p := by
  have hpR : (4 : Real) <= (p : Real) := by exact_mod_cast hp
  have hDen : 0 < (p : Real) - 1 := by linarith only [hpR]
  have hDen2 : 0 < (p : Real) - 2 := by linarith only [hpR]
  have hEq : (p : Real) / ((p : Real) - 1) = 1 + 1 / ((p : Real) - 1) := by
    field_simp
    <;> ring
  unfold hamiltonianTotientEulerFactor LPF.singularFactor
  rw [hEq]
  have hInv : 1 / ((p : Real) - 1) <= 1 / ((p : Real) - 2) :=
    one_div_le_one_div_of_le hDen2 (by linarith)
  linarith only [hInv]

theorem hamiltonian_totient_large_prime_product (P : Finset Nat) (n : Nat) (Y : Real)
    (hn : 0 < n) (hY : 4 <= Y)
    (hP : forall p, Membership.mem P p ->
      Nat.Prime p /\ Y <= (p : Real) /\ Dvd.dvd p n) :
    P.prod hamiltonianTotientEulerFactor <=
      Real.exp (2 * Real.log (n : Real) / (Y * Real.log Y)) := by
  have hCompare : forall V : Finset Nat, V <= P ->
      V.prod hamiltonianTotientEulerFactor <= V.prod LPF.singularFactor := by
    intro V
    induction V using Finset.induction_on with
    | empty =>
        intro hSub
        simp
    | @insert p V hp ih =>
        intro hSub
        have hpP := hSub (Finset.mem_insert_self p V)
        have hVP : V <= P := fun q hq => hSub (Finset.mem_insert_of_mem hq)
        have hBound : (4 : Real) <= (p : Real) := hY.trans (hP p hpP).2.1
        have hp4 : 4 <= p := by exact_mod_cast hBound
        have hSingular : 0 <= LPF.singularFactor p := by
          unfold LPF.singularFactor
          have hDen : 0 < (p : Real) - 2 := by linarith only [hBound]
          positivity
        rw [Finset.prod_insert hp, Finset.prod_insert hp]
        exact mul_le_mul (hamiltonian_totient_factor_le_singular p hp4) (ih hVP)
          (Finset.prod_nonneg (fun q hq =>
            (hamiltonian_totient_euler_factor_positive q (hP q (hVP hq)).1.two_le).le))
          hSingular
  exact (hCompare P (le_refl P)).trans
    (LPF.singular_large_prime_product_le P n Y hn hY hP)

end PrimeFactorOscillations
