/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Nat.PrimeFin
import PrimeFactorOscillations.Helpers.LocalizedAscentCount

/-!
# Modulus budgets for actual selected ascent primes

A moving modulus can exclude only as many distinct selected primes as its
size permits. This is a finite divisibility argument on the actual sampled
primes, with no distribution theorem for prime pairs in progressions.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open PrimeFactorUnimodality

def localAscentUnitIndices (m : Nat -> Nat)
    (a : (X : Nat) -> Fin (m X) -> Nat) (X c : Nat) : Finset (Fin (m X)) := by
  classical
  exact Finset.univ.filter (fun i => Nat.Coprime (primeAt (a X i)) c)

theorem localAscent_nonunit_count_le (m : Nat -> Nat)
    (a : (X : Nat) -> Fin (m X) -> Nat) (X c A : Nat)
    (hX : 2 <= X) (hc : 0 < c) (hInj : Function.Injective (a X))
    (hLow : forall i, X <= primeAt (a X i)) (hMod : c <= X ^ A) :
    (Finset.univ.filter (fun i : Fin (m X) =>
      Not (Nat.Coprime (primeAt (a X i)) c))).card <= A := by
  classical
  let B : Finset (Fin (m X)) := Finset.univ.filter
    (fun i => Not (Nat.Coprime (primeAt (a X i)) c))
  let T : Finset Nat := B.image (fun i => primeAt (a X i))
  have hPrimeInj : Function.Injective (fun i : Fin (m X) => primeAt (a X i)) :=
    primeAt_strictMono.injective.comp hInj
  have hCard : T.card = B.card := Finset.card_image_of_injective B hPrimeInj
  have hSub : T <= c.primeFactors := by
    intro p hp
    choose i hi hEq using Finset.mem_image.mp hp
    subst p
    have hNot : Not (Nat.Coprime (primeAt (a X i)) c) :=
      (Finset.mem_filter.mp hi).2
    have hDiv : Dvd.dvd (primeAt (a X i)) c := by
      by_contra hn
      exact hNot ((prime_primeAt (a X i)).coprime_iff_not_dvd.mpr hn)
    exact (prime_primeAt (a X i)).mem_primeFactors hDiv (ne_of_gt hc)
  have hProdDiv : Dvd.dvd (T.prod id) c :=
    (Finset.prod_dvd_prod_of_subset T c.primeFactors id hSub).trans
      (Nat.prod_primeFactors_dvd c)
  have hPow : X ^ T.card <= T.prod id := by
    rw [<- Finset.prod_const]
    apply Finset.prod_le_prod
    intro p hp
    choose i hi hEq using Finset.mem_image.mp hp
    rw [<- hEq]
    exact hLow i
  have hCount : T.card <= A :=
    (Nat.pow_le_pow_iff_right (by omega : 1 < X)).mp
      (hPow.trans ((Nat.le_of_dvd hc hProdDiv).trans hMod))
  rw [hCard] at hCount
  exact hCount

theorem localAscent_unit_count_ge_half (m : Nat -> Nat)
    (a : (X : Nat) -> Fin (m X) -> Nat) (X c : Nat)
    (hX : 2 <= X) (hc : 0 < c) (hInj : Function.Injective (a X))
    (hLow : forall i, X <= primeAt (a X i)) (hMod : c <= X ^ (m X / 2)) :
    (m X : Real) / 2 <= (localAscentUnitIndices m a X c).card := by
  classical
  have hBad := localAscent_nonunit_count_le m a X c (m X / 2)
    hX hc hInj hLow hMod
  have hPartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (m X))))
    (fun i => Nat.Coprime (primeAt (a X i)) c)
  simp only [Finset.card_univ, Fintype.card_fin] at hPartition
  have hNat : m X <= 2 * (localAscentUnitIndices m a X c).card := by
    unfold localAscentUnitIndices
    omega
  have hReal : (m X : Real) <= 2 * ((localAscentUnitIndices m a X c).card : Real) := by
    exact_mod_cast hNat
  linarith

end PrimeFactorOscillations
