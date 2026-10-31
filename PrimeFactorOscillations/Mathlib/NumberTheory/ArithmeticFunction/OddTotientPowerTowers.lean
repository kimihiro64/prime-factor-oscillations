/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.FieldTheory.Finite.Basic
import PrimeFactorOscillations.Mathlib.NumberTheory.ArithmeticFunction.OddTotientSpectrum

/-!
# Explicit power towers realizing the stable odd-totient spectrum

Euler periods are charged separately on coprime degree factors. This retains
the periods720*5^j,720*3^j and12*3^j; charging the full product totient
would overstate the period. Every selected degree belongs to the split sector.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096

namespace Nat

theorem oddTotient_degree_period (p d m : Nat) (hp : 0<p)
    (hc : Nat.Coprime p d) (hperiod : Dvd.dvd d.totient m) :
    Dvd.dvd d (p^m-1) := by
  choose k hk using hperiod
  have hEuler := (Nat.ModEq.pow_totient hc).pow k
  have hpow : Nat.ModEq d (p^m) 1 := by
    rw [hk,_root_.pow_mul]
    simpa only [one_pow] using hEuler
  have hlo : 1<=p^m := by have hh := pow_pos hp m; omega
  exact (Nat.modEq_iff_dvd' hlo).mp hpow.symm

theorem oddTotient_coprime_product_period (p a b m : Nat) (hp : 0<p)
    (hpa : Nat.Coprime p a) (hpb : Nat.Coprime p b) (hab : Nat.Coprime a b)
    (ha : Dvd.dvd a.totient m) (hb : Dvd.dvd b.totient m) :
    Dvd.dvd (a*b) (p^m-1) := by
  exact hab.mul_dvd_of_dvd_of_dvd
    (oddTotient_degree_period p a m hp hpa ha)
    (oddTotient_degree_period p b m hp hpb hb)

theorem oddTotient_scaled_block_period (p r C i j d : Nat)
    (hp : 0<p) (hr : Nat.Prime r) (hpr : Nat.Coprime p r)
    (hC : Dvd.dvd (r-1) C)
    (haux : forall e, Membership.mem oddTotientAuxiliaryPrimes e ->
      Nat.Coprime p e /\ Nat.Coprime e r /\ Dvd.dvd e.totient C)
    (hij : i<=j) (hd : Membership.mem (oddTotientScaledBlock r i) d) :
    Dvd.dvd d (p^(C*r^j)-1) := by
  choose e he using Finset.mem_image.mp hd
  have hdata := haux e he.1
  have heperiod : Dvd.dvd e.totient (C*r^j) :=
    Nat.dvd_trans hdata.2.2 (Exists.intro (r^j) rfl)
  have hrperiod : Dvd.dvd (r^(i+1)).totient (C*r^j) := by
    rw [Nat.totient_prime_pow hr (by omega : 0 < (i+1)),show i+1-1=i by omega,
      Nat.mul_comm C (r^j)]
    exact _root_.mul_dvd_mul (Nat.pow_dvd_pow r hij) hC
  rw [<- he.2]
  exact oddTotient_coprime_product_period p e (r^(i+1)) (C*r^j) hp
    hdata.1 (Nat.Coprime.pow_right (i+1) hpr)
    (Nat.Coprime.pow_right (i+1) hdata.2.1) heperiod hrperiod

theorem oddTotient_three_family_period (j d : Nat)
    (hd : Membership.mem (oddTotientThreeDegrees j) d) :
    Dvd.dvd d (3^(720*5^j)-1) := by
  cases oddTotient_three_mem_cases d j hd with
  | inl hb =>
    have hbase : forall e, Membership.mem oddTotientBaseThree e ->
        Nat.Coprime 3 e /\ Dvd.dvd e.totient 720 := by decide
    exact oddTotient_degree_period 3 d (720*5^j) (by decide) (hbase d hb).1
      (Nat.dvd_trans (hbase d hb).2 (Exists.intro (5^j) rfl))
  | inr hex =>
    choose i hi using hex
    apply oddTotient_scaled_block_period 3 5 720 i j d
      (by decide) (by decide) (by decide) (by decide)
    . intro e he
      have hh := oddTotient_auxiliary_data e he
      exact And.intro
        ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mpr hh.2.2.2.2.1)
        (And.intro
          (((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 5)).mpr
            hh.2.2.2.2.2.1).symm) hh.2.2.2.2.2.2)
    . exact hi.1
    . exact hi.2

theorem oddTotient_five_family_period (j d : Nat)
    (hd : Membership.mem (oddTotientFiveDegrees j) d) :
    Dvd.dvd d (5^(720*3^j)-1) := by
  cases oddTotient_five_mem_cases d j hd with
  | inl hb =>
    have hbase : forall e, Membership.mem oddTotientBaseFive e ->
        Nat.Coprime 5 e /\ Dvd.dvd e.totient 720 := by decide
    exact oddTotient_degree_period 5 d (720*3^j) (by decide) (hbase d hb).1
      (Nat.dvd_trans (hbase d hb).2 (Exists.intro (3^j) rfl))
  | inr hex =>
    choose i hi using hex
    apply oddTotient_scaled_block_period 5 3 720 i j d
      (by decide) (by decide) (by decide) (by decide)
    . intro e he
      have hh := oddTotient_auxiliary_data e he
      exact And.intro
        ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 5)).mpr hh.2.2.2.2.2.1)
        (And.intro
          (((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mpr
            hh.2.2.2.2.1).symm) hh.2.2.2.2.2.2)
    . exact hi.1
    . exact hi.2

theorem oddTotient_other_block_period (p i j d : Nat) (hp : 0<p)
    (hp3 : Nat.Coprime p 3) (hp5 : Nat.Coprime p 5) (hij : i<=j)
    (hd : Membership.mem (oddTotientOtherBlock i) d) :
    Dvd.dvd d (p^(12*3^j)-1) := by
  have hs : d=3^(i+2) \/ d=5*3^(i+1) := by
    simpa only [oddTotientOtherBlock,Finset.mem_insert,Finset.mem_singleton] using hd
  cases hs with
  | inl heq =>
    rw [heq]
    apply oddTotient_degree_period p (3^(i+2)) (12*3^j) hp
      (Nat.Coprime.pow_right (i+2) hp3)
    have hphi : (3^(i+2) : Nat).totient=6*3^i := by
      rw [Nat.totient_prime_pow (by decide : Nat.Prime 3) (by omega : 0 < (i+2)),
        show i+2-1=i+1 by omega,show (3 : Nat)-1=2 from rfl,pow_succ]
      omega
    rw [hphi]
    exact _root_.mul_dvd_mul (by decide : Dvd.dvd 6 12) (Nat.pow_dvd_pow 3 hij)
  | inr heq =>
    rw [heq]
    apply oddTotient_coprime_product_period p 5 (3^(i+1)) (12*3^j) hp hp5
      (Nat.Coprime.pow_right (i+1) hp3)
      (Nat.Coprime.pow_right (i+1) (by decide))
    . have hphi : (5 : Nat).totient=4 := by decide
      rw [hphi]
      exact Nat.dvd_trans (by decide : Dvd.dvd 4 12) (Exists.intro (3^j) rfl)
    . rw [Nat.totient_prime_pow (by decide : Nat.Prime 3) (by omega : 0 < (i+1)),
        show i+1-1=i by omega,show (3 : Nat)-1=2 from rfl,Nat.mul_comm 12 (3^j)]
      exact _root_.mul_dvd_mul (Nat.pow_dvd_pow 3 hij) (by decide : Dvd.dvd 2 12)

theorem oddTotient_other_family_period (p j d : Nat) (hp : 0<p)
    (hp3 : Nat.Coprime p 3) (hp5 : Nat.Coprime p 5)
    (hd : Membership.mem (oddTotientOtherDegrees j) d) :
    Dvd.dvd d (p^(12*3^j)-1) := by
  cases oddTotient_other_mem_cases d j hd with
  | inl hb =>
    have hphi : forall e, Membership.mem oddTotientBaseOther e ->
        Dvd.dvd e.totient 12 := by decide
    have hcp := (oddTotient_other_data p d j hp3 hp5 hd).2.2
    exact oddTotient_degree_period p d (12*3^j) hp hcp
      (Nat.dvd_trans (hphi d hb) (Exists.intro (3^j) rfl))
  | inr hex =>
    choose i hi using hex
    exact oddTotient_other_block_period p i j d hp hp3 hp5 hi.1 hi.2


def oddTotientTowerDegree (p j : Nat) : Nat :=
  if p=3 then 720*5^j else if p=5 then 720*3^j else 12*3^j

def oddTotientTowerDegrees (p j : Nat) : Finset Nat :=
  if p=3 then oddTotientThreeDegrees j
    else if p=5 then oddTotientFiveDegrees j else oddTotientOtherDegrees j

theorem oddTotient_tower_degree_lower (p j : Nat) : 12<=oddTotientTowerDegree p j := by
  have h3 : 0<(3 : Nat)^j := pow_pos (by decide) _
  have h5 : 0<(5 : Nat)^j := pow_pos (by decide) _
  by_cases hp3 : p=3
  . simp only [oddTotientTowerDegree,ite_eq_left hp3]
    omega
  by_cases hp5 : p=5
  . simp only [oddTotientTowerDegree,ite_eq_right hp3,ite_eq_left hp5]
    omega
  . simp only [oddTotientTowerDegree,ite_eq_right hp3,ite_eq_right hp5]
    omega

theorem oddTotient_prime_power_card_bounds (p m : Nat) (hp : 3<=p) (hm : 2<=m) :
    9<=p^m /\ Dvd.dvd p (p^m) := by
  apply And.intro
  . have hs : 9<=p^2 := by
      rw [pow_two]
      exact Nat.mul_le_mul hp hp
    have he := Nat.pow_le_pow_right (n:=p) (i:=2) (j:=m) (by omega) hm
    exact Nat.le_trans hs he
  . apply Exists.intro (p^(m-1))
    calc
      p^m = p^((m-1)+1) := congrArg (fun k : Nat => p^k) (by omega)
      _ = p^(m-1)*p := pow_succ p (m-1)
      _ = p*p^(m-1) := Nat.mul_comm _ _

theorem oddTotient_tower_data (p j d : Nat) (hp : Nat.Prime p) (hpo : Odd p)
    (hd : Membership.mem (oddTotientTowerDegrees p j) d) :
    Odd d /\ 1<d /\ Nat.Coprime p d /\
      Dvd.dvd d (p^(oddTotientTowerDegree p j)-1) := by
  by_cases hp3 : p=3
  . subst p
    change Membership.mem (oddTotientThreeDegrees j) d at hd
    change Odd d /\ 1<d /\ Nat.Coprime 3 d /\ Dvd.dvd d (3^(720*5^j)-1)
    have hh := oddTotient_three_data d j hd
    exact And.intro hh.1 (And.intro hh.2.1
      (And.intro hh.2.2 (oddTotient_three_family_period j d hd)))
  by_cases hp5 : p=5
  . subst p
    change Membership.mem (oddTotientFiveDegrees j) d at hd
    change Odd d /\ 1<d /\ Nat.Coprime 5 d /\ Dvd.dvd d (5^(720*3^j)-1)
    have hh := oddTotient_five_data d j hd
    exact And.intro hh.1 (And.intro hh.2.1
      (And.intro hh.2.2 (oddTotient_five_family_period j d hd)))
  have hp7 : 7<=p := by
    have hpm := Nat.odd_iff.mp hpo
    have hp2 := hp.two_le
    omega
  have hcp3 : Nat.Coprime p 3 := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hh
    have hlo := Nat.le_of_dvd (by decide : 0<(3 : Nat)) hh
    omega
  have hcp5 : Nat.Coprime p 5 := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hh
    have hlo := Nat.le_of_dvd (by decide : 0<(5 : Nat)) hh
    omega
  simp only [oddTotientTowerDegrees,ite_eq_right hp3,ite_eq_right hp5] at hd
  simp only [oddTotientTowerDegree,ite_eq_right hp3,ite_eq_right hp5]
  have hh := oddTotient_other_data p d j hcp3 hcp5 hd
  exact And.intro hh.1 (And.intro hh.2.1 (And.intro hh.2.2
    (oddTotient_other_family_period p j d hp.pos hcp3 hcp5 hd)))

theorem oddTotient_tower_eventual_realize (p N j : Nat)
    (hallowed : oddTotientSupportAllowed p N) (hj : N<=j) :
    exists D : Finset Nat, Membership.mem (oddTotientTowerDegrees p j).powerset D /\
      D.sum Nat.totient=N := by
  by_cases hp3 : p=3
  . subst p
    change exists D : Finset Nat,
      Membership.mem (oddTotientThreeDegrees j).powerset D /\ D.sum Nat.totient=N
    exact oddTotient_three_eventual_realize N j hallowed hj
  by_cases hp5 : p=5
  . subst p
    change exists D : Finset Nat,
      Membership.mem (oddTotientFiveDegrees j).powerset D /\ D.sum Nat.totient=N
    exact oddTotient_five_eventual_realize N j hallowed hj
  simp only [oddTotientTowerDegrees,ite_eq_right hp3,ite_eq_right hp5]
  exact oddTotient_other_eventual_realize N j hallowed.1 hj

end Nat
