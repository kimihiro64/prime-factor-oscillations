/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.ArithmeticFunction.PrimeExtensionTotient

/-!
# Ternary extension orders and least-prime-factor bounds

The extension degree n is arbitrary with n>=2 in the lower bounds. Prime
factor lifting is retained for all divisor-related degrees. These arithmetic
inputs feed the full signed support consumer, without a prime-degree shortcut.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Nat

theorem ternaryExtension_primeFactor_iff (n p : Nat) (hp : Nat.Prime p) :
    (Dvd.dvd p (3^n-1) \/ Dvd.dvd p (3^n+1)) <->
      (9 : ZMod p)^n=1 := by
  let _ : Fact (Nat.Prime p) := Fact.mk hp
  have hqpos : 0<(3 : Nat)^n := pow_pos (by decide) _
  have hq : 1<=(3 : Nat)^n := by omega
  have h9 : (9 : ZMod p)=(3 : ZMod p)^2 := by norm_num
  constructor
  . intro hdiv
    have hcase : (3 : ZMod p)^n=1 \/ (3 : ZMod p)^n=-1 := by
      cases hdiv with
      | inl hd =>
        have hz := (ZMod.natCast_eq_zero_iff (3^n-1) p).mpr hd
        have hz' : (3 : ZMod p)^n-1=0 := by
          simpa only [Nat.cast_sub hq,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] using hz
        exact Or.inl (sub_eq_zero.mp hz')
      | inr hd =>
        have hz := (ZMod.natCast_eq_zero_iff (3^n+1) p).mpr hd
        have hz' : (3 : ZMod p)^n+1=0 := by
          simpa only [Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] using hz
        exact Or.inr (eq_neg_of_add_eq_zero_left hz')
    rw [h9,_root_.pow_right_comm (3 : ZMod p) 2 n]
    cases hcase with
    | inl h => rw [h]; norm_num
    | inr h => rw [h]; norm_num
  . intro hpow
    have hs : ((3 : ZMod p)^n)^2=1 := by
      simpa only [h9,_root_.pow_right_comm (3 : ZMod p) 2 n] using hpow
    cases sq_eq_one_iff.mp hs with
    | inl h =>
      apply Or.inl
      apply (ZMod.natCast_eq_zero_iff (3^n-1) p).mp
      rw [Nat.cast_sub hq,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one,h,sub_self]
    | inr h =>
      apply Or.inr
      apply (ZMod.natCast_eq_zero_iff (3^n+1) p).mp
      rw [Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one,h,neg_add_cancel]

theorem ternaryExtension_primeFactor_lift (r n p : Nat) (hp : Nat.Prime p)
    (hrn : Dvd.dvd r n)
    (hdiv : Dvd.dvd p (3^r-1) \/ Dvd.dvd p (3^r+1)) :
    Dvd.dvd p (3^n-1) \/ Dvd.dvd p (3^n+1) := by
  have hr := (ternaryExtension_primeFactor_iff r p hp).mp hdiv
  choose k hk using hrn
  apply (ternaryExtension_primeFactor_iff n p hp).mpr
  rw [hk,_root_.pow_mul,hr,one_pow]

theorem ternaryExtension_primeFactor_lower (n p : Nat) (hn : 2<=n)
    (hp : Nat.Prime p) (hpo : Odd p)
    (hdiv : Dvd.dvd p (3^n-1) \/ Dvd.dvd p (3^n+1)) :
    2*n.minFac<=p-1 := by
  let _ : Fact (Nat.Prime p) := Fact.mk hp
  have hpow := (ternaryExtension_primeFactor_iff n p hp).mp hdiv
  have h9zero : Not ((9 : ZMod p)=0) := by
    intro hz
    have hb := hpow
    rw [hz,zero_pow (by omega : Not (n=0))] at hb
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
  have horddiv := orderOf_dvd_of_pow_eq_one hpow
  have hord2 : 2<=orderOf (9 : ZMod p) := by
    have hone : Not (orderOf (9 : ZMod p)=1) := by
      intro heq
      exact h9one (orderOf_eq_one_iff.mp heq)
    have hzero : Not (orderOf (9 : ZMod p)=0) := by
      intro hz
      choose a ha using horddiv
      rw [hz,zero_mul] at ha
      omega
    omega
  have hthree : Not ((3 : ZMod p)=0) := by
    intro hz
    apply h9zero
    calc
      _ = (3 : ZMod p)^2 := by norm_num
      _ = 0 := by rw [hz]; norm_num
  have htwo : Dvd.dvd 2 (p-1) := by
    choose k hk using hpo
    exact Exists.intro k (by omega)
  have he : (p-1)/2*2=p-1 := Nat.div_mul_cancel htwo
  have hhalf : (9 : ZMod p)^((p-1)/2)=1 := by
    have h9 : (9 : ZMod p)=(3 : ZMod p)^2 := by norm_num
    rw [h9,_root_.pow_right_comm (3 : ZMod p) 2 ((p-1)/2),
      <- _root_.pow_mul,he]
    exact ZMod.pow_card_sub_one_eq_one hthree
  have hp3 : 3<=p := by
    have hp2 := hp.two_le
    choose k hk using hpo
    omega
  have hhpos : 0<(p-1)/2 := by omega
  have horderle := Nat.le_of_dvd hhpos (orderOf_dvd_of_pow_eq_one hhalf)
  have hmin := Nat.minFac_le_of_dvd hord2 horddiv
  omega

theorem ternaryExtension_totient_lower (n d : Nat) (hn : 2<=n)
    (hdo : Odd d) (hd : 1<d)
    (hdiv : Dvd.dvd d (3^n-1) \/ Dvd.dvd d (3^n+1)) :
    2*n.minFac<=d.totient := by
  have hd1 : Not (d=1) := by omega
  choose p hp using Nat.exists_prime_and_dvd hd1
  have hpo : Odd p := Odd.of_dvd_nat hdo hp.2
  have hpdiv : Dvd.dvd p (3^n-1) \/ Dvd.dvd p (3^n+1) := by
    cases hdiv with
    | inl hv => exact Or.inl (Nat.dvd_trans hp.2 hv)
    | inr hv => exact Or.inr (Nat.dvd_trans hp.2 hv)
  have hlo := ternaryExtension_primeFactor_lower n p hn hp.1 hpo hpdiv
  have hphidvd : Dvd.dvd (p-1) d.totient := by
    simpa only [Nat.totient_prime hp.1] using Nat.totient_dvd_of_dvd hp.2
  have hpositive : 0<d.totient := Nat.totient_pos.mpr (by omega)
  exact Nat.le_trans hlo (Nat.le_of_dvd hpositive hphidvd)

theorem ternaryExtension_endpoint_prime (n d : Nat) (hn : 2<=n)
    (hdo : Odd d) (hd : 1<d)
    (hdiv : Dvd.dvd d (3^n-1) \/ Dvd.dvd d (3^n+1))
    (hphi : d.totient=2*n.minFac) : Nat.Prime (2*n.minFac+1) := by
  have hd1 : Not (d=1) := by omega
  choose p hp using Nat.exists_prime_and_dvd hd1
  have hpo : Odd p := Odd.of_dvd_nat hdo hp.2
  have hpdiv : Dvd.dvd p (3^n-1) \/ Dvd.dvd p (3^n+1) := by
    cases hdiv with
    | inl hv => exact Or.inl (Nat.dvd_trans hp.2 hv)
    | inr hv => exact Or.inr (Nat.dvd_trans hp.2 hv)
  have hlo := ternaryExtension_primeFactor_lower n p hn hp.1 hpo hpdiv
  have hphidvd : Dvd.dvd (p-1) d.totient := by
    simpa only [Nat.totient_prime hp.1] using Nat.totient_dvd_of_dvd hp.2
  have hpositive : 0<d.totient := Nat.totient_pos.mpr (by omega)
  have hhi := Nat.le_of_dvd hpositive hphidvd
  have hp2 := hp.1.two_le
  have heq : p=2*n.minFac+1 := by omega
  simpa only [heq] using hp.1

end Nat
