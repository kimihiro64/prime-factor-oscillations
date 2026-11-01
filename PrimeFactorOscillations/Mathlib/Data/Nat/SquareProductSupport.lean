/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Mathlib.Data.Nat.IsSquareTrans

/-! # Square-class divisors controlled by common prime support

A positive square product admits a square-class representative for either
factor supported only on its common primes with the other factor.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Nat

theorem squarefree_dvd_of_positive_square_product {a b : Nat}
    (ha : 0 < a) (hb : 0 < b) (hsf : Squarefree a)
    (hsq : IsSquare (a * b)) : Dvd.dvd a b := by
  have ha0 : Not (a = 0) := Nat.ne_of_gt ha
  have hb0 : Not (b = 0) := Nat.ne_of_gt hb
  choose k hk using hsq
  have hk0 : Not (k = 0) := by
    intro hz
    apply mul_ne_zero ha0 hb0
    rw [hk, hz, zero_mul]
  apply (Nat.factorization_le_iff_dvd ha0 hb0).mp
  intro p
  have hsf_p := (Nat.squarefree_iff_factorization_le_one ha0).mp hsf p
  have hfac := congrArg Nat.factorization hk
  rw [Nat.factorization_mul ha0 hb0, Nat.factorization_mul hk0 hk0] at hfac
  have hval := congrArg (fun f : Finsupp Nat Nat => f p) hfac
  simp only [Finsupp.add_apply] at hval
  omega

theorem exists_square_class_divisor_of_common_prime_support
    (m n D : Nat) (hm : 0 < m) (hn : 0 < n) (hD : 0 < D)
    (hsq : IsSquare (m * n))
    (hSupport : forall p : Nat, Nat.Prime p ->
      Dvd.dvd p m -> Dvd.dvd p n -> Dvd.dvd p D) :
    exists d : Nat, And (0 < d) (And (Dvd.dvd d D) (IsSquare (d * m))) := by
  choose d hd using Nat.sq_mul_squarefree_of_pos hm
  choose b hb using hd
  have hdpos : 0 < d := hb.1
  have hbpos : 0 < b := hb.2.1
  have hdecomp : b ^ 2 * d = m := hb.2.2.1
  have hsf : Squarefree d := hb.2.2.2
  have hd0 : Not (d = 0) := Nat.ne_of_gt hdpos
  have hD0 : Not (D = 0) := Nat.ne_of_gt hD
  have hbn : IsSquare ((b * b) * (d * n)) := by
    have heq : (b * b) * (d * n) = m * n := by
      rw [<- hdecomp]
      ring
    rw [heq]
    exact hsq
  have hdnsq : IsSquare (d * n) := by
    have hh := Nat.isSquare_mul_trans_of_pos
      (a := 1) (b := b * b) (c := d * n) (Nat.mul_pos hbpos hbpos)
      (Exists.intro b (by ring)) hbn
    simpa only [one_mul] using hh
  have hdn : Dvd.dvd d n :=
    squarefree_dvd_of_positive_square_product hdpos hn hsf hdnsq
  have hdm : Dvd.dvd d m := Exists.intro (b ^ 2) (by rw [<- hdecomp]; ring)
  have hdD : Dvd.dvd d D := by
    apply (Nat.factorization_le_iff_dvd hd0 hD0).mp
    intro p
    by_cases hz : d.factorization p = 0
    . rw [hz]
      exact Nat.zero_le _
    . have hmem : Membership.mem d.primeFactors p := by
        have hh : Membership.mem d.factorization.support p := Finsupp.mem_support_iff.mpr hz
        simpa only [Nat.support_factorization] using hh
      have hp := Nat.mem_primeFactors.mp hmem
      have hpD : Dvd.dvd p D :=
        hSupport p hp.1 (dvd_trans hp.2.1 hdm) (dvd_trans hp.2.1 hdn)
      have hle := (Nat.factorization_le_iff_dvd hp.1.ne_zero hD0).mpr hpD
      have hval := hle p
      have hone : 1 <= D.factorization p := by
        simpa [hp.1.factorization] using hval
      exact ((Nat.squarefree_iff_factorization_le_one hd0).mp hsf p).trans hone
  have hdsq : IsSquare (d * m) := Exists.intro (d * b) (by rw [<- hdecomp]; ring)
  exact Exists.intro d (And.intro hdpos (And.intro hdD hdsq))

end Nat
