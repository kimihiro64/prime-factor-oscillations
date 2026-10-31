/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import PrimeFactorOscillations.Mathlib.NumberTheory.ArithmeticFunction.TernaryExtensionOrder

/-!
# The second prime-extension totient level

Composite admissible degrees have totient at least (2*ell)^2. Quadratic
reciprocity excludes the prime degree 4*ell+1 except at ell=3. The extension
degree2 is included in every statement.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Nat

theorem primeExtension_composite_totient_lower (ell d : Nat) (hell : Nat.Prime ell)
    (hdo : Odd d) (hd : 1<d)
    (hdiv : Dvd.dvd d (3^ell-1) \/ Dvd.dvd d (3^ell+1))
    (hcomposite : Not (Nat.Prime d)) :
    (2*ell)^2<=d.totient := by
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
    have hsq : (2*ell)^2<=(p^2).totient := by
      rw [Nat.totient_prime_pow hp.1 (by decide : 0<(2 : Nat)),
        show (2 : Nat)-1=1 from rfl,pow_one,pow_two]
      exact Nat.mul_le_mul (by omega) hpminus
    exact Nat.le_trans hsq hphile
  . rw [hk,Nat.totient_mul ((hp.1.coprime_iff_not_dvd).mpr hpk),pow_two]
    exact Nat.mul_le_mul hpweight hkweight

theorem primeExtension_small_weight_prime (ell d : Nat) (hell : Nat.Prime ell)
    (hdo : Odd d) (hd : 1<d)
    (hdiv : Dvd.dvd d (3^ell-1) \/ Dvd.dvd d (3^ell+1))
    (hsmall : d.totient<=4*ell) : Nat.Prime d := by
  by_contra hcomposite
  have hlo := primeExtension_composite_totient_lower ell d hell hdo hd hdiv hcomposite
  have hthree : 3<=2*ell := by have he := hell.two_le; omega
  have hmul := Nat.mul_le_mul_left (2*ell) hthree
  rw [pow_two] at hlo
  omega

theorem primeExtension_first_weight_degree (ell d : Nat) (hell : Nat.Prime ell)
    (hdo : Odd d) (hd : 1<d)
    (hdiv : Dvd.dvd d (3^ell-1) \/ Dvd.dvd d (3^ell+1))
    (hphi : d.totient=2*ell) : d=2*ell+1 := by
  have hp := primeExtension_small_weight_prime ell d hell hdo hd hdiv (by omega)
  rw [Nat.totient_prime hp] at hphi
  have hp2 := hp.two_le
  omega

theorem primeExtension_primeFactor_ne_four (ell p : Nat) (hell : Nat.Prime ell)
    (hne : Not (ell=3)) (hp : Nat.Prime p)
    (hdiv : Dvd.dvd p (3^ell-1) \/ Dvd.dvd p (3^ell+1)) :
    Not (p=4*ell+1) := by
  intro heq
  have hell2 := hell.two_le
  have hp3 : Not (p=3) := by omega
  have hnell : Not (Dvd.dvd 3 ell) := by
    intro hd
    cases (Nat.dvd_prime hell).mp hd with
    | inl h => omega
    | inr h => exact hne h.symm
  have hnp : Not (Dvd.dvd 3 p) := by
    intro hd
    cases (Nat.dvd_prime hp).mp hd with
    | inl h => omega
    | inr h => exact hp3 h.symm
  have hellmod : Not (ell%3=0) := by
    intro h
    exact hnell (Nat.dvd_iff_mod_eq_zero.mpr h)
  have hpmod : Not (p%3=0) := by
    intro h
    exact hnp (Nat.dvd_iff_mod_eq_zero.mpr h)
  have hmod3 : p%3=2 := by omega
  have hmod4 : p%4=1 := by omega
  have hhalf : p/2=2*ell := by omega
  have hmodInt : (p : Int)%3=2 := by omega
  let _ : Fact (Nat.Prime p) := Fact.mk hp
  let _ : Fact (Nat.Prime 3) := Fact.mk (by decide)
  have hrec := legendreSym.quadratic_reciprocity_one_mod_four
    (p:=p) (q:=3) hmod4 (by decide)
  norm_num only at hrec
  have htwo : legendreSym 3 (2 : Int)=-1 := by
    rw [legendreSym.at_two (by decide : Not ((3 : Nat)=2))]
    decide
  have hsym : legendreSym p (3 : Int)=-1 := by
    rw [<- hrec,legendreSym.mod 3 (p : Int)]
    norm_num only
    rw [hmodInt]
    exact htwo
  have hthreepow : (3 : ZMod p)^(2*ell)=1 := by
    have h := (ternaryExtension_primeFactor_iff ell p hp).mp hdiv
    have h9 : (9 : ZMod p)=(3 : ZMod p)^2 := by norm_num
    rw [h9,<- _root_.pow_mul] at h
    exact h
  have hcast : (-1 : ZMod p)=1 := by
    calc
      _ = (legendreSym p (3 : Int) : ZMod p) := by
        rw [hsym]
        norm_num
      _ = (3 : ZMod p)^(p/2) := by
        have heuler := legendreSym.eq_pow p (3 : Int)
        norm_num only at heuler
        exact heuler
      _ = 1 := by rw [hhalf,hthreepow]
  have htwozero : (2 : ZMod p)=0 := by
    calc
      _ = (1 : ZMod p)-(-1) := by norm_num
      _ = 0 := by rw [hcast,sub_self]
  have hpdvd : Dvd.dvd p 2 := (ZMod.natCast_eq_zero_iff 2 p).mp htwozero
  have hle := Nat.le_of_dvd (by decide : 0<(2 : Nat)) hpdvd
  omega

theorem primeExtension_second_weight_iff (ell d : Nat) (hell : Nat.Prime ell)
    (hdo : Odd d) (hd : 1<d)
    (hdiv : Dvd.dvd d (3^ell-1) \/ Dvd.dvd d (3^ell+1)) :
    d.totient=4*ell <-> ell=3 /\ d=13 := by
  constructor
  . intro hphi
    have hp := primeExtension_small_weight_prime ell d hell hdo hd hdiv (by omega)
    have hdval : d=4*ell+1 := by
      rw [Nat.totient_prime hp] at hphi
      have hp2 := hp.two_le
      omega
    have heq : ell=3 := by
      by_contra hne
      exact primeExtension_primeFactor_ne_four ell d hell hne hp hdiv hdval
    exact And.intro heq (by omega)
  . intro h
    have he := h.1
    have hdval := h.2
    subst ell
    subst d
    decide

end Nat
