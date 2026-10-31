/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum

/-!
# Prime extension factors and totient divisibility

These classical arithmetic inputs feed the exact signed odd-Pell support
consumer. The prime extension degree2 is retained as a finite exceptional case.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Nat

theorem primeExtension_primeFactor_progression (ell p : Nat) (hell : Nat.Prime ell)
    (hello : Odd ell) (hp : Nat.Prime p) (hpo : Odd p)
    (hdiv : Dvd.dvd p (3^ell-1) \/ Dvd.dvd p (3^ell+1)) :
    Dvd.dvd (2*ell) (p-1) := by
  let _ : Fact (Nat.Prime p) := Fact.mk hp
  have hqpos : 0<(3 : Nat)^ell := pow_pos (by decide) _
  have hq : 1<=(3 : Nat)^ell := by omega
  have hcase : (3 : ZMod p)^ell=1 \/ (3 : ZMod p)^ell=-1 := by
    cases hdiv with
    | inl hd =>
      have hz := (ZMod.natCast_eq_zero_iff (3^ell-1) p).mpr hd
      have hz' : (3 : ZMod p)^ell-1=0 := by
        simpa only [Nat.cast_sub hq,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] using hz
      exact Or.inl (sub_eq_zero.mp hz')
    | inr hd =>
      have hz := (ZMod.natCast_eq_zero_iff (3^ell+1) p).mpr hd
      have hz' : (3 : ZMod p)^ell+1=0 := by
        simpa only [Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] using hz
      exact Or.inr (eq_neg_of_add_eq_zero_left hz')
  have h9pow : (9 : ZMod p)^ell=1 := by
    have h9 : (9 : ZMod p)=(3 : ZMod p)^2 := by norm_num
    rw [h9,_root_.pow_right_comm (3 : ZMod p) 2 ell]
    cases hcase with
    | inl h => rw [h]; norm_num
    | inr h => rw [h]; norm_num
  have h9zero : Not ((9 : ZMod p)=0) := by
    intro hz
    have hb := h9pow
    rw [hz,zero_pow hell.ne_zero] at hb
    exact zero_ne_one hb
  have h9one : Not ((9 : ZMod p)=1) := by
    intro heq
    have h8 : (8 : ZMod p)=0 := by
      calc
        _ = (9 : ZMod p)-1 := by norm_num
        _ = 0 := sub_eq_zero.mpr heq
    have hp8 : Dvd.dvd p 8 := (ZMod.natCast_eq_zero_iff 8 p).mp h8
    have hc2 : Nat.Coprime p 2 := Nat.coprime_two_right.mpr hpo
    have hc8 : Nat.gcd p 8=1 := by
      simpa only [show (2 : Nat)^3=8 from rfl] using Nat.Coprime.pow_right 3 hc2
    rw [Nat.gcd_eq_left_iff_dvd.mpr hp8] at hc8
    exact hp.ne_one hc8
  have hord : orderOf (9 : ZMod p)=ell := by
    have hd := orderOf_dvd_of_pow_eq_one h9pow
    cases (Nat.dvd_prime hell).mp hd with
    | inl heq => exact False.elim (h9one (orderOf_eq_one_iff.mp heq))
    | inr heq => exact heq
  have hediv : Dvd.dvd ell (p-1) := by
    have hd := orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one h9zero)
    simpa only [hord] using hd
  have htwo : Dvd.dvd 2 (p-1) := by
    choose k hk using hpo
    exact Exists.intro k (by omega)
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.coprime_two_left.mpr hello) htwo hediv

theorem primeExtension_totient_dvd (ell d : Nat) (hell : Nat.Prime ell)
    (hdo : Odd d) (hd : 1<d)
    (hdiv : Dvd.dvd d (3^ell-1) \/ Dvd.dvd d (3^ell+1)) :
    Dvd.dvd (2*ell) d.totient := by
  by_cases he : ell=2
  . subst ell
    have hsmall : forall a : Nat,
        Membership.mem (Union.union (8 : Nat).divisors (10 : Nat).divisors) a ->
        Odd a -> 1<a -> Dvd.dvd 4 a.totient := by decide
    have hm : Membership.mem (Union.union (8 : Nat).divisors (10 : Nat).divisors) d := by
      apply Finset.mem_union.mpr
      cases hdiv with
      | inl hv =>
        apply Or.inl
        exact Nat.mem_divisors.mpr (And.intro hv (by decide))
      | inr hv =>
        apply Or.inr
        exact Nat.mem_divisors.mpr (And.intro hv (by decide))
    exact hsmall d hm hdo hd
  . have hello : Odd ell := by
      by_cases hz : ell%2=0
      . have hv : Dvd.dvd 2 ell := Nat.dvd_iff_mod_eq_zero.mpr hz
        cases (Nat.dvd_prime hell).mp hv with
        | inl hb => omega
        | inr hb => exact False.elim (he hb.symm)
      . exact Exists.intro (ell/2) (by omega)
    have hd1 : Not (d=1) := by omega
    choose p hp using Nat.exists_prime_and_dvd hd1
    have hpo : Odd p := Odd.of_dvd_nat hdo hp.2
    have hpdiv : Dvd.dvd p (3^ell-1) \/ Dvd.dvd p (3^ell+1) := by
      cases hdiv with
      | inl hv => exact Or.inl (Nat.dvd_trans hp.2 hv)
      | inr hv => exact Or.inr (Nat.dvd_trans hp.2 hv)
    have hprogress := primeExtension_primeFactor_progression ell p hell hello hp.1 hpo hpdiv
    have hphi : Dvd.dvd (p-1) d.totient := by
      simpa only [Nat.totient_prime hp.1] using Nat.totient_dvd_of_dvd hp.2
    exact Nat.dvd_trans hprogress hphi

theorem primeExtension_safePrime_factor (ell : Nat) (hell : 2<=ell)
    (hp : Nat.Prime (2*ell+1)) :
    Dvd.dvd (2*ell+1) (3^ell-1) \/ Dvd.dvd (2*ell+1) (3^ell+1) := by
  let p := 2*ell+1
  let _ : Fact (Nat.Prime p) := Fact.mk hp
  have hthree : Not ((3 : ZMod p)=0) := by
    intro hz
    have hd : Dvd.dvd p 3 := (ZMod.natCast_eq_zero_iff 3 p).mp hz
    have hle := Nat.le_of_dvd (by decide : 0<(3 : Nat)) hd
    dsimp [p] at hle
    omega
  have hf := ZMod.pow_card_sub_one_eq_one hthree
  have he : p-1=2*ell := by dsimp [p]
  rw [he] at hf
  have hs : ((3 : ZMod p)^ell)^2=1 := by
    calc
      _ = (3 : ZMod p)^(ell*2) := (_root_.pow_mul _ _ _).symm
      _ = (3 : ZMod p)^(2*ell) := by rw [Nat.mul_comm ell 2]
      _ = 1 := hf
  have hqpos : 0<(3 : Nat)^ell := pow_pos (by decide) _
  have hq : 1<=(3 : Nat)^ell := by omega
  cases sq_eq_one_iff.mp hs with
  | inl h =>
    apply Or.inl
    apply (ZMod.natCast_eq_zero_iff (3^ell-1) p).mp
    rw [Nat.cast_sub hq,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one,h,sub_self]
  | inr h =>
    apply Or.inr
    apply (ZMod.natCast_eq_zero_iff (3^ell+1) p).mp
    rw [Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one,h,neg_add_cancel]


theorem primeExtension_endpoint_prime (ell d : Nat) (hell : Nat.Prime ell)
    (hdo : Odd d) (hd : 1<d)
    (hdiv : Dvd.dvd d (3^ell-1) \/ Dvd.dvd d (3^ell+1))
    (hphi : d.totient=2*ell) : Nat.Prime (2*ell+1) := by
  by_cases he : ell=2
  . subst ell
    decide
  . have hello : Odd ell := by
      by_cases hz : ell%2=0
      . have hv : Dvd.dvd 2 ell := Nat.dvd_iff_mod_eq_zero.mpr hz
        cases (Nat.dvd_prime hell).mp hv with
        | inl hb => omega
        | inr hb => exact False.elim (he hb.symm)
      . exact Exists.intro (ell/2) (by omega)
    have hd1 : Not (d=1) := by omega
    choose p hp using Nat.exists_prime_and_dvd hd1
    have hpo : Odd p := Odd.of_dvd_nat hdo hp.2
    have hpdiv : Dvd.dvd p (3^ell-1) \/ Dvd.dvd p (3^ell+1) := by
      cases hdiv with
      | inl hv => exact Or.inl (Nat.dvd_trans hp.2 hv)
      | inr hv => exact Or.inr (Nat.dvd_trans hp.2 hv)
    have hprogress := primeExtension_primeFactor_progression ell p hell hello hp.1 hpo hpdiv
    have hphidvd : Dvd.dvd (p-1) d.totient := by
      simpa only [Nat.totient_prime hp.1] using Nat.totient_dvd_of_dvd hp.2
    have hpositive : 0<d.totient := Nat.totient_pos.mpr (by omega)
    have hleP : p-1<=d.totient := Nat.le_of_dvd hpositive hphidvd
    have hp2 := hp.1.two_le
    have hleEll : 2*ell<=p-1 := Nat.le_of_dvd (by omega) hprogress
    have heq : p=2*ell+1 := by omega
    simpa only [heq] using hp.1

end Nat
