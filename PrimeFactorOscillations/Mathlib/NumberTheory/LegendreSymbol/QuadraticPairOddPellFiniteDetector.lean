/-
Copyright (c) 2026 Jonas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonas
-/
import Mathlib.FieldTheory.Finite.GaloisField
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairOddPellUniform

/-!
# One finite field detects all bounded odd-Pell relations

The factorial extension exposes every characteristic-coprime input divisor.
Native atom weights and the characteristic-three exception are retained.
This is an information theorem, not an integer prime-pair counting estimate.
-/

set_option autoImplicit false
set_option Elab.async false

universe u

namespace FiniteField

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

theorem oddPell_probe_zero_iff_amplitudes (h : F) (hh : Not (h=0))
    (S : Finset Nat) (a : Nat -> Real) (hq : 5<=Fintype.card F)
    (htwo : Not ((2 : F)=0)) :
    (forall c, oddPellSignedProbe h S a c=0) <->
      forall i, Membership.mem (oddPellAtomLabels (F:=F)) i ->
        (S.filter (fun k => Dvd.dvd (oddPellAtomDegree i) (2*k+1))).sum a=0 := by
  classical
  let b : Sum Nat Nat -> Real := fun i => oddPellAtomWeight (F:=F) i *
    (S.filter (fun k => Dvd.dvd (oddPellAtomDegree i) (2*k+1))).sum a
  have hexpand : (fun c => oddPellSignedProbe h S a c)=
      (oddPellAtomLabels (F:=F)).sum (fun i => fun c => b i * oddPellAtomIndicator h i c) := by
    exact oddPell_probe_atom_expansion h hh S a hq htwo
  constructor
  . intro hz i hi
    have hpos : 0<(oddPellAtom (F:=F) i).card := by
      rw [oddPell_atom_card i hi htwo]
      exact Nat.totient_pos.mpr (oddPell_atomDegree_pos i hi)
    choose c hc using Finset.card_pos.mp hpos
    let x := (h/2)*c
    have hx : Membership.mem (oddPellShiftAtom h i) x := by
      exact Finset.mem_image.mpr (Exists.intro c (And.intro hc rfl))
    have heval : oddPellSignedProbe h S a x=b i := by
      exact (congrFun hexpand x).trans
        (oddPell_atom_sum_on_shiftAtom h hh b i hi x hx htwo)
    have hb : b i=0 := heval.symm.trans (hz x)
    exact (mul_eq_zero.mp hb).resolve_left (ne_of_gt (oddPell_atomWeight_pos i hq))
  . intro ha c
    have hzfun : (fun x => oddPellSignedProbe h S a x)=(0 : F -> Real) := by
      rw [hexpand]
      apply Finset.sum_eq_zero
      intro i hi
      simp only [b,ha i hi,mul_zero,zero_mul]
      funext x
      rfl
    exact congrFun hzfun c

theorem oddPell_split_amplitude_zero (h : F) (hh : Not (h=0))
    (S : Finset Nat) (a : Nat -> Real) (hq : 5<=Fintype.card F)
    (htwo : Not ((2 : F)=0)) (hz : forall c, oddPellSignedProbe h S a c=0)
    (e : Nat) (ho : Odd e) (he : 1<e) (hd : Dvd.dvd e (Fintype.card F-1)) :
    (S.filter (fun k => Dvd.dvd e (2*k+1))).sum a=0 := by
  classical
  have hD : forall d, Membership.mem ({e} : Finset Nat) d ->
      Odd d /\ 1<d /\ Dvd.dvd d (Fintype.card F-1) := by
    intro d hm
    have hdEq : d=e := Finset.mem_singleton.mp hm
    subst d
    exact And.intro ho (And.intro he hd)
  have hs := oddPell_universal_split_labels (F:=F) {e} hD hq
  have hi : Membership.mem (({e} : Finset Nat).image
      (fun d => (Sum.inl d : Sum Nat Nat))) (Sum.inl e) :=
    Finset.mem_image.mpr (Exists.intro e (And.intro (Finset.mem_singleton_self e) rfl))
  rw [<- hs] at hi
  exact (oddPell_probe_zero_iff_amplitudes h hh S a hq htwo).mp hz
    (Sum.inl e) (Finset.mem_filter.mp hi).1

theorem oddPell_bounded_amplitudes_suffice (h : F) (hh : Not (h=0))
    (p M : Nat) (hp : Nat.Prime p) (hpq : Dvd.dvd p (Fintype.card F))
    (S : Finset Nat) (a : Nat -> Real)
    (hbound : forall k, Membership.mem S k -> 2*k+1<=M)
    (hq : 5<=Fintype.card F) (htwo : Not ((2 : F)=0))
    (ha : forall e, Odd e -> 1<e -> Nat.Coprime p e -> e<=M ->
      (S.filter (fun k => Dvd.dvd e (2*k+1))).sum a=0) :
    forall c, oddPellSignedProbe h S a c=0 := by
  classical
  apply (oddPell_probe_zero_iff_amplitudes h hh S a hq htwo).mpr
  intro i hi
  have hdata := oddPell_atom_characteristic_data p hp hq hpq i hi
  by_cases he : oddPellAtomDegree i<=M
  . exact ha _ hdata.1 hdata.2.1 hdata.2.2 he
  . apply Finset.sum_eq_zero
    intro k hk
    have hm := Finset.mem_filter.mp hk
    have hupper := hbound k hm.1
    have hlower := Nat.le_of_dvd (by omega : 0<2*k+1) hm.2
    omega

theorem oddPell_factorial_zero_iff (h : F) (hh : Not (h=0))
    (p M : Nat) (hp : Nat.Prime p) (hpo : Odd p) (hM : 2<=M)
    (hcard : Fintype.card F=p^M.factorial)
    (S : Finset Nat) (a : Nat -> Real)
    (hbound : forall k, Membership.mem S k -> 2*k+1<=M)
    (htwo : Not ((2 : F)=0)) :
    (forall c, oddPellSignedProbe h S a c=0) <->
      forall e, Odd e -> 1<e -> Nat.Coprime p e -> e<=M ->
        (S.filter (fun k => Dvd.dvd e (2*k+1))).sum a=0 := by
  have hp3 : 3<=p := by
    have ho := Nat.odd_iff.mp hpo
    have ht := hp.two_le
    omega
  have hm : 2<=M.factorial := Nat.factorial_le hM
  have hb := Nat.oddTotient_prime_power_card_bounds p M.factorial hp3 hm
  have hq : 5<=Fintype.card F := by rw [hcard]; omega
  have hpq : Dvd.dvd p (Fintype.card F) := by simpa only [hcard] using hb.2
  constructor
  . intro hz e ho he hc hle
    apply oddPell_split_amplitude_zero h hh S a hq htwo hz e ho he
    rw [hcard]
    exact Nat.oddTotient_degree_period p e M.factorial hp.pos hc
      (Nat.dvd_factorial (Nat.totient_pos.mpr (by omega))
        (le_trans (Nat.totient_le e) hle))
  . exact oddPell_bounded_amplitudes_suffice h hh p M hp hpq S a hbound hq htwo

theorem oddPell_factorial_vanishing_transfer (h : F) (hh : Not (h=0))
    (p M : Nat) (hp : Nat.Prime p) (hpo : Odd p) (hM : 2<=M)
    (hcard : Fintype.card F=p^M.factorial)
    (S : Finset Nat) (a : Nat -> Real)
    (hbound : forall k, Membership.mem S k -> 2*k+1<=M)
    (htwo : Not ((2 : F)=0)) (hz : forall c, oddPellSignedProbe h S a c=0)
    (G : Type*) [Field G] [Fintype G] [DecidableEq G]
    (hpG : Dvd.dvd p (Fintype.card G)) (g : G) (hg : Not (g=0))
    (htwoG : Not ((2 : G)=0)) :
    forall c, oddPellSignedProbe g S a c=0 := by
  have ha := (oddPell_factorial_zero_iff h hh p M hp hpo hM hcard S a hbound htwo).mp hz
  by_cases hq : 5<=Fintype.card G
  . exact oddPell_bounded_amplitudes_suffice g hg p M hp hpG S a hbound hq htwoG ha
  . have hpos : 0<Fintype.card G := Fintype.card_pos_iff.mpr inferInstance
    have hpq := Nat.le_of_dvd hpos hpG
    have hp3 : p=3 := by
      have ho := Nat.odd_iff.mp hpo
      have ht := hp.two_le
      omega
    have hmod : Fintype.card G%3=0 := Nat.mod_eq_zero_of_dvd (by simpa only [hp3] using hpG)
    have hthree : Fintype.card G=3 := by omega
    intro c
    exact oddPell_card_three_probe_zero g hg S a c hthree htwoG

theorem oddPell_factorial_all_fields_iff (h : F) (hh : Not (h=0))
    (p M : Nat) (hp : Nat.Prime p) (hpo : Odd p) (hM : 2<=M)
    (hcard : Fintype.card F=p^M.factorial)
    (S : Finset Nat) (a : Nat -> Real)
    (hbound : forall k, Membership.mem S k -> 2*k+1<=M)
    (htwo : Not ((2 : F)=0)) :
    (forall c, oddPellSignedProbe h S a c=0) <->
      forall (G : Type u) [Field G] [Fintype G] [DecidableEq G],
        Dvd.dvd p (Fintype.card G) -> forall g : G, Not (g=0) ->
          Not ((2 : G)=0) -> forall c, oddPellSignedProbe g S a c=0 := by
  constructor
  . intro hz G instField instFintype instDecidableEq hpG g hg htwoG
    exact oddPell_factorial_vanishing_transfer h hh p M hp hpo hM hcard
      S a hbound htwo hz G hpG g hg htwoG
  . intro ha
    have hp3 : 3<=p := by
      have ho := Nat.odd_iff.mp hpo
      have ht := hp.two_le
      omega
    have hm : 2<=M.factorial := Nat.factorial_le hM
    have hb := Nat.oddTotient_prime_power_card_bounds p M.factorial hp3 hm
    have hpF : Dvd.dvd p (Fintype.card F) := by simpa only [hcard] using hb.2
    exact ha F hpF h hh htwo

theorem oddPell_probe_sub (h : F) (S : Finset Nat) (a b : Nat -> Real) (c : F) :
    oddPellSignedProbe h S (fun k => a k-b k) c=
      oddPellSignedProbe h S a c-oddPellSignedProbe h S b c := by
  unfold oddPellSignedProbe
  simp only [sub_mul,Finset.sum_sub_distrib]

theorem oddPell_factorial_compare_iff (h : F) (hh : Not (h=0))
    (p M : Nat) (hp : Nat.Prime p) (hpo : Odd p) (hM : 2<=M)
    (hcard : Fintype.card F=p^M.factorial)
    (S : Finset Nat) (a b : Nat -> Real)
    (hbound : forall k, Membership.mem S k -> 2*k+1<=M)
    (htwo : Not ((2 : F)=0)) :
    (forall c, oddPellSignedProbe h S a c=oddPellSignedProbe h S b c) <->
      forall e, Odd e -> 1<e -> Nat.Coprime p e -> e<=M ->
        (S.filter (fun k => Dvd.dvd e (2*k+1))).sum a=
          (S.filter (fun k => Dvd.dvd e (2*k+1))).sum b := by
  classical
  have hz := oddPell_factorial_zero_iff h hh p M hp hpo hM hcard S
    (fun k => a k-b k) hbound htwo
  constructor
  . intro heq e ho he hc hle
    have hzero : forall c, oddPellSignedProbe h S (fun k => a k-b k) c=0 := by
      intro c
      rw [oddPell_probe_sub,heq c,sub_self]
    have hs := hz.mp hzero e ho he hc hle
    rw [Finset.sum_sub_distrib,sub_eq_zero] at hs
    exact hs
  . intro ha
    have hzero := hz.mpr (fun e ho he hc hle => by
      rw [Finset.sum_sub_distrib,sub_eq_zero]
      exact ha e ho he hc hle)
    intro c
    have hs := hzero c
    rw [oddPell_probe_sub,sub_eq_zero] at hs
    exact hs

theorem oddPell_factorial_comparison_transfer (h : F) (hh : Not (h=0))
    (p M : Nat) (hp : Nat.Prime p) (hpo : Odd p) (hM : 2<=M)
    (hcard : Fintype.card F=p^M.factorial)
    (S : Finset Nat) (a b : Nat -> Real)
    (hbound : forall k, Membership.mem S k -> 2*k+1<=M)
    (htwo : Not ((2 : F)=0))
    (heq : forall c, oddPellSignedProbe h S a c=oddPellSignedProbe h S b c)
    (G : Type*) [Field G] [Fintype G] [DecidableEq G]
    (hpG : Dvd.dvd p (Fintype.card G)) (g : G) (hg : Not (g=0))
    (htwoG : Not ((2 : G)=0)) :
    forall c, oddPellSignedProbe g S a c=oddPellSignedProbe g S b c := by
  have hz : forall c, oddPellSignedProbe h S (fun k => a k-b k) c=0 := by
    intro c
    rw [oddPell_probe_sub,heq c,sub_self]
  have hzG := oddPell_factorial_vanishing_transfer h hh p M hp hpo hM hcard
    S (fun k => a k-b k) hbound htwo hz G hpG g hg htwoG
  intro c
  have hc := hzG c
  rw [oddPell_probe_sub,sub_eq_zero] at hc
  exact hc

theorem oddPell_galois_factorial_zero_iff (p M : Nat) [Fact (Nat.Prime p)]
    [Fintype (GaloisField p M.factorial)] [DecidableEq (GaloisField p M.factorial)]
    (hpo : Odd p) (hM : 2<=M) (S : Finset Nat) (a : Nat -> Real)
    (hbound : forall k, Membership.mem S k -> 2*k+1<=M) :
    (forall c : GaloisField p M.factorial, oddPellSignedProbe 1 S a c=0) <->
      forall e, Odd e -> 1<e -> Nat.Coprime p e -> e<=M ->
        (S.filter (fun k => Dvd.dvd e (2*k+1))).sum a=0 := by
  have hp : Nat.Prime p := Fact.out
  have hcard : Fintype.card (GaloisField p M.factorial)=p^M.factorial :=
    Fintype.card_eq_nat_card.trans (GaloisField.card p M.factorial
      (Nat.ne_of_gt (Nat.factorial_pos M)))
  have htwo : Not ((2 : GaloisField p M.factorial)=0) := by
    intro hz
    have hd : Dvd.dvd p 2 :=
      (CharP.cast_eq_zero_iff (GaloisField p M.factorial) p 2).mp hz
    have ht := Nat.le_of_dvd (by decide : 0<(2 : Nat)) hd
    have ho := Nat.odd_iff.mp hpo
    have hp2 := hp.two_le
    omega
  exact oddPell_factorial_zero_iff 1 one_ne_zero p M hp hpo hM hcard S a hbound htwo

end FiniteField
