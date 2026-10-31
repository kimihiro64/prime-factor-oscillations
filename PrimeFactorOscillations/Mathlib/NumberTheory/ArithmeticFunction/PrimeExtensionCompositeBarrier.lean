/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.ArithmeticFunction.PrimeExtensionTotientGap

/-!
# A sharp composite barrier and a finite prime alphabet

For every prime extension degree ell, composite admissible totients are at
least2*ell*(2*ell+1). The finite alphabet uses trial tests at small rational
primes, with the exact equivalent square-power condition retained.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Nat

theorem primeExtension_composite_totient_barrier (ell d : Nat) (hell : Nat.Prime ell)
    (hdo : Odd d) (hd : 1<d)
    (hdiv : Dvd.dvd d (3^ell-1) \/ Dvd.dvd d (3^ell+1))
    (hcomposite : Not (Nat.Prime d)) :
    2*ell*(2*ell+1)<=d.totient := by
  choose p hp using Nat.exists_prime_and_dvd (by omega : Not (d=1))
  choose k hk using hp.2
  have hk0 : Not (k=0) := by
    intro heq
    rw [heq,Nat.mul_zero] at hk
    omega
  have hk1 : Not (k=1) := by
    intro heq
    apply hcomposite
    simpa only [hk,heq,Nat.mul_one] using hp.1
  have hklarge : 1<k := by omega
  have hkdvd : Dvd.dvd k d :=
    Exists.intro p (hk.trans (Nat.mul_comm p k))
  have hpdiv : Dvd.dvd p (3^ell-1) \/ Dvd.dvd p (3^ell+1) := by
    cases hdiv with
    | inl h => exact Or.inl (Nat.dvd_trans hp.2 h)
    | inr h => exact Or.inr (Nat.dvd_trans hp.2 h)
  have hkdiv : Dvd.dvd k (3^ell-1) \/ Dvd.dvd k (3^ell+1) := by
    cases hdiv with
    | inl h => exact Or.inl (Nat.dvd_trans hkdvd h)
    | inr h => exact Or.inr (Nat.dvd_trans hkdvd h)
  have hpweight : 2*ell<=p.totient :=
    Nat.le_of_dvd (Nat.totient_pos.mpr hp.1.pos)
      (primeExtension_totient_dvd ell p hell
        (Odd.of_dvd_nat hdo hp.2) (by have ht := hp.1.two_le; omega) hpdiv)
  have hkweight : 2*ell<=k.totient :=
    Nat.le_of_dvd (Nat.totient_pos.mpr (by omega))
      (primeExtension_totient_dvd ell k hell
        (Odd.of_dvd_nat hdo hkdvd) hklarge hkdiv)
  by_cases hpk : Dvd.dvd p k
  . have hp2dvd : Dvd.dvd (p^2) d := by
      choose t ht using hpk
      exact Exists.intro t (by rw [hk,ht,pow_two,Nat.mul_assoc])
    have hphile : (p^2).totient<=d.totient :=
      Nat.le_of_dvd (Nat.totient_pos.mpr (by omega))
        (Nat.totient_dvd_of_dvd hp2dvd)
    have hpminus : 2*ell<=p-1 := by
      simpa only [Nat.totient_prime hp.1] using hpweight
    have hp2 := hp.1.two_le
    have hsq : 2*ell*(2*ell+1)<=(p^2).totient := by
      rw [Nat.totient_prime_pow hp.1 (by decide : 0<(2 : Nat)),
        show (2 : Nat)-1=1 from rfl,pow_one]
      calc
        _ = (2*ell+1)*(2*ell) := Nat.mul_comm _ _
        _ <= p*(p-1) := Nat.mul_le_mul (by omega) hpminus
    exact Nat.le_trans hsq hphile
  . rw [hk,Nat.totient_mul ((hp.1.coprime_iff_not_dvd).mpr hpk)]
    by_cases hpa : p.totient=2*ell
    . have hkne : Not (k.totient=2*ell) := by
        intro hka
        have hkval := primeExtension_first_weight_degree ell k hell
          (Odd.of_dvd_nat hdo hkdvd) hklarge hkdiv hka
        have hpval : p=2*ell+1 := by
          rw [Nat.totient_prime hp.1] at hpa
          have hp2 := hp.1.two_le
          omega
        apply hpk
        rw [hkval,<- hpval]
      have hkplus : 2*ell+1<=k.totient := by omega
      exact Nat.mul_le_mul hpweight hkplus
    . have hpplus : 2*ell+1<=p.totient := by omega
      calc
        _ = (2*ell+1)*(2*ell) := Nat.mul_comm _ _
        _ <= p.totient*k.totient := Nat.mul_le_mul hpplus hkweight

theorem primeExtension_below_barrier_prime (ell d : Nat) (hell : Nat.Prime ell)
    (hdo : Odd d) (hd : 1<d)
    (hdiv : Dvd.dvd d (3^ell-1) \/ Dvd.dvd d (3^ell+1))
    (hsmall : d.totient<2*ell*(2*ell+1)) : Nat.Prime d := by
  by_contra hcomposite
  have hlo := primeExtension_composite_totient_barrier ell d hell hdo hd hdiv hcomposite
  omega

def primeExtensionPrimeAlphabet (ell : Nat) : Finset Nat :=
  (Finset.range (2*ell*(2*ell+1)+1)).filter (fun p =>
    Nat.Prime p /\ Odd p /\
      (Dvd.dvd p (3^ell-1) \/ Dvd.dvd p (3^ell+1)))

theorem mem_primeExtensionPrimeAlphabet (ell p : Nat) :
    Membership.mem (primeExtensionPrimeAlphabet ell) p <->
      Nat.Prime p /\ Odd p /\ p-1<2*ell*(2*ell+1) /\
        (Dvd.dvd p (3^ell-1) \/ Dvd.dvd p (3^ell+1)) := by
  rw [primeExtensionPrimeAlphabet,Finset.mem_filter,Finset.mem_range]
  constructor
  . intro h
    have hp2 := h.2.1.two_le
    exact And.intro h.2.1 (And.intro h.2.2.1 (And.intro (by omega) h.2.2.2))
  . intro h
    have hp2 := h.1.two_le
    exact And.intro (by omega) (And.intro h.1 (And.intro h.2.1 h.2.2.2))

theorem mem_primeExtensionPrimeAlphabet_power (ell p : Nat) :
    Membership.mem (primeExtensionPrimeAlphabet ell) p <->
      Nat.Prime p /\ Odd p /\ p-1<2*ell*(2*ell+1) /\
        (9 : ZMod p)^ell=1 := by
  constructor
  . intro h
    have hd := (mem_primeExtensionPrimeAlphabet ell p).mp h
    exact And.intro hd.1 (And.intro hd.2.1 (And.intro hd.2.2.1
      ((ternaryExtension_primeFactor_iff ell p hd.1).mp hd.2.2.2)))
  . intro h
    apply (mem_primeExtensionPrimeAlphabet ell p).mpr
    exact And.intro h.1 (And.intro h.2.1 (And.intro h.2.2.1
      ((ternaryExtension_primeFactor_iff ell p h.1).mpr h.2.2.2)))

theorem primeExtensionPrimeAlphabet_five :
    primeExtensionPrimeAlphabet 5=({11,61} : Finset Nat) := by
  decide

theorem primeExtensionPrimeAlphabet_five_no_boundary_sum (P : Finset Nat)
    (hP : forall p, Membership.mem P p ->
      Membership.mem (primeExtensionPrimeAlphabet 5) p) :
    Not (P.sum (fun p => p-1)=110) := by
  intro heq
  have hle := Finset.sum_le_sum_of_subset
    (s:=P) (t:=primeExtensionPrimeAlphabet 5) (f:=fun p => p-1) hP
  norm_num [primeExtensionPrimeAlphabet_five] at hle
  omega

end Nat
