/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.ArithmeticFunction.OddTotientCoverage

/-!
# The exceptional holes in the stable odd-totient spectrum

The exclusions apply to every finite set of admissible odd degrees, not
only the constructive tower families. Composite degrees and the repeated
normalized weights at different prime degrees are retained.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096

namespace Nat

theorem oddTotient_positive_even_lower (d : Nat) (hodd : Odd d) (hd : 1<d) :
    2<=d.totient := by
  have hp := Nat.totient_pos.mpr (by omega : 0<d)
  have hh := oddTotient_normalized_weight_double d hodd hd
  omega

theorem oddTotient_coprime_three_lower (d : Nat) (hodd : Odd d)
    (hd : 1<d) (hc : Nat.Coprime 3 d) : 4<=d.totient := by
  choose p hp using Nat.exists_prime_and_dvd (by omega : Not (d=1))
  have hpo := Nat.odd_iff.mp (Odd.of_dvd_nat hodd hp.2)
  have hp2 := hp.1.two_le
  have hpne3 : Not (p=3) := by
    intro heq
    have hh : Dvd.dvd 3 d := by simpa only [heq] using hp.2
    exact ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mp hc) hh
  have hp5 : 5<=p := by omega
  have hle := Nat.le_of_dvd (Nat.totient_pos.mpr (by omega : 0<d))
    (Nat.totient_dvd_of_dvd hp.2)
  rw [Nat.totient_prime hp.1] at hle
  omega

theorem oddTotient_composite_factor_bound (d B : Nat) (hd : 1<d)
    (hcomposite : Not (Nat.Prime d))
    (hfactor : forall k : Nat, Dvd.dvd k d -> 1<k -> B<=k.totient) :
    B*B<=d.totient := by
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
  have hkl : 1<k := by omega
  have hkdvd : Dvd.dvd k d := Exists.intro p (hk.trans (Nat.mul_comm p k))
  have hpweight := hfactor p hp.2 (by have hh := hp.1.two_le; omega)
  have hkweight := hfactor k hkdvd hkl
  by_cases hpk : Dvd.dvd p k
  . have hp2dvd : Dvd.dvd (p^2) d := by
      choose t ht using hpk
      exact Exists.intro t (by rw [hk,ht,pow_two,Nat.mul_assoc])
    have hphile := Nat.le_of_dvd (Nat.totient_pos.mpr (by omega : 0<d))
      (Nat.totient_dvd_of_dvd hp2dvd)
    have hpminus : B<=p-1 := by
      simpa only [Nat.totient_prime hp.1] using hpweight
    have hmul := Nat.mul_le_mul (show B<=p by omega) hpminus
    rw [Nat.totient_prime_pow hp.1 (by decide : 0<(2 : Nat)),
      show (2 : Nat)-1=1 from rfl,pow_one] at hphile
    exact Nat.le_trans hmul hphile
  . rw [hk,Nat.totient_mul ((hp.1.coprime_iff_not_dvd).mpr hpk)]
    exact Nat.mul_le_mul hpweight hkweight

theorem oddTotient_composite_lower_six (d : Nat) (hodd : Odd d)
    (hd : 1<d) (hcomposite : Not (Nat.Prime d)) : 6<=d.totient := by
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
  have hkl : 1<k := by omega
  have hkdvd : Dvd.dvd k d := Exists.intro p (hk.trans (Nat.mul_comm p k))
  have hko := Odd.of_dvd_nat hodd hkdvd
  have hpo := Nat.odd_iff.mp (Odd.of_dvd_nat hodd hp.2)
  have hp2 := hp.1.two_le
  have hp3 : 3<=p := by omega
  by_cases hpk : Dvd.dvd p k
  . have hp2dvd : Dvd.dvd (p^2) d := by
      choose t ht using hpk
      exact Exists.intro t (by rw [hk,ht,pow_two,Nat.mul_assoc])
    have hphile := Nat.le_of_dvd (Nat.totient_pos.mpr (by omega : 0<d))
      (Nat.totient_dvd_of_dvd hp2dvd)
    rw [Nat.totient_prime_pow hp.1 (by decide : 0<(2 : Nat)),
      show (2 : Nat)-1=1 from rfl,pow_one] at hphile
    have hmul := Nat.mul_le_mul hp3 (show 2<=p-1 by omega)
    exact Nat.le_trans hmul hphile
  . have hkweight : 2<=k.totient := oddTotient_positive_even_lower k hko hkl
    by_cases heq : p=3
    . have hkc : Nat.Coprime 3 k := by
        apply (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mpr
        simpa only [heq] using hpk
      have hkfour := oddTotient_coprime_three_lower k hko hkl hkc
      rw [hk,Nat.totient_mul ((hp.1.coprime_iff_not_dvd).mpr hpk),heq]
      have hphi : (3 : Nat).totient=2 := by decide
      rw [hphi]
      omega
    . have hp5 : 5<=p := by omega
      rw [hk,Nat.totient_mul ((hp.1.coprime_iff_not_dvd).mpr hpk),
        Nat.totient_prime hp.1]
      have hmul := Nat.mul_le_mul (show 4<=p-1 by omega) hkweight
      omega

theorem oddTotient_three_small_degrees (d : Nat) (hodd : Odd d)
    (hd : 1<d) (hc : Nat.Coprime 3 d) (hsmall : d.totient<=8) :
    d=5 \/ d=7 := by
  have hprime : Nat.Prime d := by
    by_contra hcomposite
    have hlo := oddTotient_composite_factor_bound d 4 hd hcomposite (by
      intro k hkd hkl
      apply oddTotient_coprime_three_lower k (Odd.of_dvd_nat hodd hkd) hkl
      apply (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mpr
      intro hthree
      exact ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mp hc)
        (Nat.dvd_trans hthree hkd))
    omega
  have hphi := Nat.totient_prime hprime
  have hmod := Nat.odd_iff.mp hodd
  have hne3 : Not (d=3) := by
    intro heq
    subst d
    exact ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mp hc) (by decide)
  have hne9 : Not (d=9) := by
    intro heq
    subst d
    exact (by decide : Not (Nat.Prime 9)) hprime
  omega

theorem oddTotient_five_small_degree (d : Nat) (hodd : Odd d)
    (hd : 1<d) (hc : Nat.Coprime 5 d) (hsmall : d.totient<=4) : d=3 := by
  have hprime : Nat.Prime d := by
    by_contra hcomposite
    have hlo := oddTotient_composite_lower_six d hodd hd hcomposite
    omega
  have hphi := Nat.totient_prime hprime
  have hmod := Nat.odd_iff.mp hodd
  have hne5 : Not (d=5) := by
    intro heq
    subst d
    exact ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 5)).mp hc) (by decide)
  omega

theorem oddTotient_three_forbidden (D : Finset Nat)
    (hD : forall d, Membership.mem D d -> Odd d /\ 1<d /\ Nat.Coprime 3 d) :
    Not (D.sum Nat.totient=2) /\ Not (D.sum Nat.totient=8) := by
  have hbounded : D.sum Nat.totient<=8 ->
      Not (D.sum Nat.totient=2) /\ Not (D.sum Nat.totient=8) := by
    intro hsum
    have hsub : forall d, Membership.mem D d -> Membership.mem ({5,7} : Finset Nat) d := by
      intro d hd
      have hdata := hD d hd
      have hle : d.totient<=D.sum Nat.totient :=
        Finset.single_le_sum (fun a ha => Nat.zero_le a.totient) hd
      exact Finset.mem_insert.mpr (by
        cases oddTotient_three_small_degrees d hdata.1 hdata.2.1 hdata.2.2 (by omega) with
        | inl heq => exact Or.inl heq
        | inr heq => exact Or.inr (Finset.mem_singleton.mpr heq))
    have hfinite : forall U : Finset Nat, Membership.mem ({5,7} : Finset Nat).powerset U ->
        Not (U.sum Nat.totient=2) /\ Not (U.sum Nat.totient=8) := by decide
    exact hfinite D (Finset.mem_powerset.mpr hsub)
  exact And.intro (by intro h; exact (hbounded (by omega)).1 h)
    (by intro h; exact (hbounded (by omega)).2 h)

theorem oddTotient_five_forbidden (D : Finset Nat)
    (hD : forall d, Membership.mem D d -> Odd d /\ 1<d /\ Nat.Coprime 5 d) :
    Not (D.sum Nat.totient=4) := by
  intro heq
  have hsub : forall d, Membership.mem D d -> Membership.mem ({3} : Finset Nat) d := by
    intro d hd
    have hdata := hD d hd
    have hle : d.totient<=D.sum Nat.totient :=
      Finset.single_le_sum (fun a ha => Nat.zero_le a.totient) hd
    exact Finset.mem_singleton.mpr
      (oddTotient_five_small_degree d hdata.1 hdata.2.1 hdata.2.2 (by omega))
  have hfinite : forall U : Finset Nat, Membership.mem ({3} : Finset Nat).powerset U ->
      Not (U.sum Nat.totient=4) := by decide
  exact hfinite D (Finset.mem_powerset.mpr hsub) heq


def oddTotientSupportAllowed (p N : Nat) : Prop :=
  Even N /\ (p=3 -> Not (N=2) /\ Not (N=8)) /\ (p=5 -> Not (N=4))

theorem oddTotient_support_necessary (p : Nat) (D : Finset Nat)
    (hD : forall d, Membership.mem D d -> Odd d /\ 1<d /\ Nat.Coprime p d) :
    oddTotientSupportAllowed p (D.sum Nat.totient) := by
  apply And.intro
  . have hh := oddTotient_sum_normalized_double D (by
      intro d hd
      exact And.intro (hD d hd).1 (hD d hd).2.1)
    exact Exists.intro (D.sum (fun d => d.totient/2)) (by omega)
  . apply And.intro
    . intro heq
      subst p
      exact oddTotient_three_forbidden D hD
    . intro heq
      subst p
      exact oddTotient_five_forbidden D hD

private theorem oddTotient_zero_in_family (T : Finset Nat) :
    exists D : Finset Nat, Membership.mem T.powerset D /\ D.sum Nat.totient=0 := by
  apply Exists.intro (EmptyCollection.emptyCollection : Finset Nat)
  apply And.intro
  . exact Finset.mem_powerset.mpr (Finset.empty_subset _)
  . rfl

private theorem oddTotient_singleton_in_family (T : Finset Nat) (d N : Nat)
    (hd : Membership.mem T d) (hphi : d.totient=N) :
    exists D : Finset Nat, Membership.mem T.powerset D /\ D.sum Nat.totient=N := by
  apply Exists.intro ({d} : Finset Nat)
  apply And.intro
  . apply Finset.mem_powerset.mpr
    intro a ha
    have heq := Finset.mem_singleton.mp ha
    rw [heq]
    exact hd
  . simpa only [Finset.sum_singleton] using hphi

theorem oddTotient_three_horizon_realize (N j : Nat)
    (hallowed : oddTotientSupportAllowed 3 N) (hhi : N+6<=310*5^j) :
    exists D : Finset Nat, Membership.mem (oddTotientThreeDegrees j).powerset D /\
      D.sum Nat.totient=N := by
  choose k hk using hallowed.1
  have hN : N=2*k := by omega
  by_cases hk0 : k=0
  . rw [hN,hk0,Nat.mul_zero]
    exact oddTotient_zero_in_family (oddTotientThreeDegrees j)
  by_cases hk2 : k=2
  . apply oddTotient_singleton_in_family (oddTotientThreeDegrees j) 5 N
    . exact oddTotient_three_base_subset j 5 (by decide)
    . have hphi : (5 : Nat).totient=4 := by decide
      omega
  by_cases hk3 : k=3
  . apply oddTotient_singleton_in_family (oddTotientThreeDegrees j) 7 N
    . exact oddTotient_three_base_subset j 7 (by decide)
    . have hphi : (7 : Nat).totient=6 := by decide
      omega
  have hlo : 5<=k := by
    have hne := hallowed.2.1 rfl
    omega
  choose D hD using oddTotient_three_realize_interval j k hlo (by
    simp only [pow_succ]
    omega)
  exact Exists.intro D (And.intro hD.1 (hD.2.trans hN.symm))

theorem oddTotient_three_eventual_realize (N j : Nat)
    (hallowed : oddTotientSupportAllowed 3 N) (hj : N<=j) :
    exists D : Finset Nat, Membership.mem (oddTotientThreeDegrees j).powerset D /\
      D.sum Nat.totient=N := by
  have hpow := oddTotient_stage_le_power 5 j (by decide)
  exact oddTotient_three_horizon_realize N j hallowed (by omega)

theorem oddTotient_five_horizon_realize (N j : Nat)
    (hallowed : oddTotientSupportAllowed 5 N) (hhi : N<=186*3^j+2) :
    exists D : Finset Nat, Membership.mem (oddTotientFiveDegrees j).powerset D /\
      D.sum Nat.totient=N := by
  choose k hk using hallowed.1
  have hN : N=2*k := by omega
  by_cases hk0 : k=0
  . rw [hN,hk0,Nat.mul_zero]
    exact oddTotient_zero_in_family (oddTotientFiveDegrees j)
  by_cases hk1 : k=1
  . apply oddTotient_singleton_in_family (oddTotientFiveDegrees j) 3 N
    . exact oddTotient_five_base_subset j 3 (by decide)
    . have hphi : (3 : Nat).totient=2 := by decide
      omega
  have hlo : 3<=k := by
    have hne := hallowed.2.2 rfl
    omega
  choose D hD using oddTotient_five_realize_interval j k hlo (by
    simp only [pow_succ]
    omega)
  exact Exists.intro D (And.intro hD.1 (hD.2.trans hN.symm))

theorem oddTotient_five_eventual_realize (N j : Nat)
    (hallowed : oddTotientSupportAllowed 5 N) (hj : N<=j) :
    exists D : Finset Nat, Membership.mem (oddTotientFiveDegrees j).powerset D /\
      D.sum Nat.totient=N := by
  have hpow := oddTotient_stage_le_power 3 j (by decide)
  exact oddTotient_five_horizon_realize N j hallowed (by omega)

theorem oddTotient_other_horizon_realize (N j : Nat)
    (heven : Even N) (hhi : N+1<=21*3^j) :
    exists D : Finset Nat, Membership.mem (oddTotientOtherDegrees j).powerset D /\
      D.sum Nat.totient=N := by
  choose k hk using heven
  have hN : N=2*k := by omega
  choose D hD using oddTotient_other_realize_interval j k (Nat.zero_le _) (by
    simp only [pow_succ]
    omega)
  exact Exists.intro D (And.intro hD.1 (hD.2.trans hN.symm))

theorem oddTotient_other_eventual_realize (N j : Nat)
    (heven : Even N) (hj : N<=j) :
    exists D : Finset Nat, Membership.mem (oddTotientOtherDegrees j).powerset D /\
      D.sum Nat.totient=N := by
  have hpow := oddTotient_stage_le_power 3 j (by decide)
  exact oddTotient_other_horizon_realize N j heven (by omega)

theorem oddTotient_support_spectrum (p N : Nat) (hp : Nat.Prime p) (hpo : Odd p) :
    (exists D : Finset Nat,
      (forall d, Membership.mem D d -> Odd d /\ 1<d /\ Nat.Coprime p d) /\
        D.sum Nat.totient=N) <-> oddTotientSupportAllowed p N := by
  constructor
  . intro hex
    choose D hD using hex
    rw [<- hD.2]
    exact oddTotient_support_necessary p D hD.1
  . intro hallowed
    by_cases hp3 : p=3
    . subst p
      choose D hD using oddTotient_three_eventual_realize N N hallowed (Nat.le_refl _)
      apply Exists.intro D
      apply And.intro
      . intro d hd
        exact oddTotient_three_data d N ((Finset.mem_powerset.mp hD.1) hd)
      . exact hD.2
    by_cases hp5 : p=5
    . subst p
      choose D hD using oddTotient_five_eventual_realize N N hallowed (Nat.le_refl _)
      apply Exists.intro D
      apply And.intro
      . intro d hd
        exact oddTotient_five_data d N ((Finset.mem_powerset.mp hD.1) hd)
      . exact hD.2
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
    choose D hD using oddTotient_other_eventual_realize N N hallowed.1 (Nat.le_refl _)
    apply Exists.intro D
    apply And.intro
    . intro d hd
      exact oddTotient_other_data p d N hcp3 hcp5 ((Finset.mem_powerset.mp hD.1) hd)
    . exact hD.2

end Nat
