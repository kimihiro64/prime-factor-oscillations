/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.ArithmeticFunction.PrimeExtensionTotientGap
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairOddPellRoughness

/-!
# The forbidden second support level

For every prime extension degree ell except3, the complete finite signed
odd-Pell probe space has support sizes0,2*ell,or at least6*ell. The missing
level4*ell occurs exactly at ell=3. Non-Sophie degrees have minimum at least
6*ell, and degree17 attains102. All signed cancellations are retained through
the existing exact support-cardinality spectrum.
-/

set_option autoImplicit false
set_option Elab.async false

namespace FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] [DecidableEq F] in
private theorem oddPell_gap_card_ge_five (n : Nat) (hn : 2<=n)
    (hcard : Fintype.card F=3^n) : 5<=Fintype.card F := by
  have hp : (9 : Nat)<=3^n :=
    Nat.pow_le_pow_right (n:=3) (i:=2) (j:=n) (by decide) hn
  rw [hcard]
  omega

omit [Field F] [DecidableEq F] in
private theorem oddPell_gap_atom_data (n : Nat)
    (hcard : Fintype.card F=3^n) (i : Sum Nat Nat)
    (hi : Membership.mem (oddPellAtomLabels (F:=F)) i) :
    Odd (oddPellAtomDegree i) /\ 1<oddPellAtomDegree i /\
      (Dvd.dvd (oddPellAtomDegree i) (3^n-1) \/
        Dvd.dvd (oddPellAtomDegree i) (3^n+1)) := by
  cases i with
  | inl d =>
    have hm := (oddPell_atomLabels_left (F:=F) d).mp hi
    have ho := (Finset.mem_filter.mp hm.2).2
    have hp := oddPell_atomDegree_pos (Sum.inl d) hi
    change 0<d at hp
    have hd : 1<d := by have hh := hm.1; omega
    have hv : Dvd.dvd d (3^n-1) := by
      have hh := (Nat.mem_divisors.mp (Finset.mem_filter.mp hm.2).1).1
      change Dvd.dvd d (Fintype.card F-1) at hh
      simpa only [hcard] using hh
    exact And.intro ho (And.intro hd (Or.inl hv))
  | inr d =>
    have hm := (oddPell_atomLabels_right (F:=F) d).mp hi
    have ho := (Finset.mem_filter.mp hm.2).2
    have hp := oddPell_atomDegree_pos (Sum.inr d) hi
    change 0<d at hp
    have hd : 1<d := by have hh := hm.1; omega
    have hv : Dvd.dvd d (3^n+1) := by
      have hh := (Nat.mem_divisors.mp (Finset.mem_filter.mp hm.2).1).1
      change Dvd.dvd d (Fintype.card F+1) at hh
      simpa only [hcard] using hh
    exact And.intro ho (And.intro hd (Or.inr hv))

omit [Field F] [DecidableEq F] in
theorem oddPell_primeExtension_first_atom_degree (ell : Nat) (hell : Nat.Prime ell)
    (hcard : Fintype.card F=3^ell) (i : Sum Nat Nat)
    (hi : Membership.mem (oddPellAtomLabels (F:=F)) i)
    (hphi : (oddPellAtomDegree i).totient=2*ell) :
    oddPellAtomDegree i=2*ell+1 := by
  have hd := oddPell_gap_atom_data ell hcard i hi
  exact Nat.primeExtension_first_weight_degree ell (oddPellAtomDegree i) hell
    hd.1 hd.2.1 hd.2.2 hphi

omit [Field F] [DecidableEq F] in
theorem oddPell_primeExtension_second_atom_iff (ell : Nat) (hell : Nat.Prime ell)
    (hcard : Fintype.card F=3^ell) (i : Sum Nat Nat)
    (hi : Membership.mem (oddPellAtomLabels (F:=F)) i) :
    (oddPellAtomDegree i).totient=4*ell <->
      ell=3 /\ oddPellAtomDegree i=13 := by
  have hd := oddPell_gap_atom_data ell hcard i hi
  exact Nat.primeExtension_second_weight_iff ell (oddPellAtomDegree i) hell
    hd.1 hd.2.1 hd.2.2

omit [Field F] [DecidableEq F] in
private theorem oddPell_gap_small_weight (ell : Nat) (hell : Nat.Prime ell)
    (hne : Not (ell=3)) (hcard : Fintype.card F=3^ell) (i : Sum Nat Nat)
    (hi : Membership.mem (oddPellAtomLabels (F:=F)) i)
    (hsmall : (oddPellAtomDegree i).totient<=4*ell) :
    (oddPellAtomDegree i).totient=2*ell := by
  have hpos : 0<(oddPellAtomDegree i).totient :=
    Nat.totient_pos.mpr (oddPell_atomDegree_pos i hi)
  have hneweight : Not ((oddPellAtomDegree i).totient=4*ell) := by
    intro h
    exact hne ((oddPell_primeExtension_second_atom_iff ell hell hcard i hi).mp h).1
  choose k hk using oddPell_primeExtension_atom_totient_dvd ell hell hcard i hi
  have hell2 := hell.two_le
  have hkbound : k<=2 := by
    by_contra hbad
    have hm := Nat.mul_le_mul_left (2*ell) (show 3<=k by omega)
    omega
  have hcases : k=0 \/ k=1 \/ k=2 := by omega
  cases hcases with
  | inl h =>
    rw [h,mul_zero] at hk
    omega
  | inr h =>
    cases h with
    | inl h => simpa only [h,mul_one] using hk
    | inr h =>
      rw [h] at hk
      have heq : (oddPellAtomDegree i).totient=4*ell := by omega
      exact False.elim (hneweight heq)

theorem oddPell_primeExtension_support_ne_four (h : F) (hh : Not (h=0))
    (ell : Nat) (hell : Nat.Prime ell) (hne : Not (ell=3))
    (hcard : Fintype.card F=3^ell) (htwo : Not ((2 : F)=0))
    (f : F -> Real) (hf : Membership.mem (oddPellProbeSpace h) f) :
    Not ((oddPellFunctionSupport f).card=4*ell) := by
  classical
  intro heq
  have hell2 := hell.two_le
  have hq := oddPell_gap_card_ge_five ell hell.two_le hcard
  choose T hT using (oddPell_support_card_spectrum h hh
    (oddPellFunctionSupport f).card hq htwo).mp
      (Exists.intro f (And.intro hf rfl))
  have hsum : T.sum (fun i => (oddPellAtomDegree i).totient)=4*ell :=
    hT.2.trans heq
  have hweights : forall i : Sum Nat Nat, Membership.mem T i ->
      (oddPellAtomDegree i).totient=2*ell := by
    intro i hi
    have hle := Finset.single_le_sum
      (s:=T) (f:=fun j => (oddPellAtomDegree j).totient)
      (fun j hj => Nat.zero_le _) hi
    apply oddPell_gap_small_weight ell hell hne hcard i (hT.1 i hi)
    omega
  have hnon : T.Nonempty := by
    by_contra hn
    have hz := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [hz,Finset.sum_empty] at hsum
    omega
  choose i hi using hnon
  have hsumle := Finset.sum_le_sum_of_subset
    (s:=T) (t:=({i} : Finset (Sum Nat Nat)))
    (f:=fun j => (oddPellAtomDegree j).totient)
    (fun j hj => Finset.mem_singleton.mpr (by
      have hjdegree := oddPell_primeExtension_first_atom_degree ell hell hcard j
        (hT.1 j hj) (hweights j hj)
      have hidegree := oddPell_primeExtension_first_atom_degree ell hell hcard i
        (hT.1 i hi) (hweights i hi)
      exact oddPell_atomDegree_injective j i (hT.1 j hj) (hT.1 i hi) hq
        (hjdegree.trans hidegree.symm)))
  rw [Finset.sum_singleton,hweights i hi] at hsumle
  omega

theorem oddPell_primeExtension_support_four_iff (h : F) (hh : Not (h=0))
    (ell : Nat) (hell : Nat.Prime ell) (hcard : Fintype.card F=3^ell)
    (htwo : Not ((2 : F)=0)) :
    (exists f : F -> Real, Membership.mem (oddPellProbeSpace h) f /\
      (oddPellFunctionSupport f).card=4*ell) <-> ell=3 := by
  constructor
  . intro hex
    by_contra hne
    choose f hf using hex
    exact oddPell_primeExtension_support_ne_four h hh ell hell hne hcard htwo
      f hf.1 hf.2
  . intro he
    subst ell
    have hq := oddPell_gap_card_ge_five 3 (by decide) hcard
    have hi : Membership.mem (oddPellAtomLabels (F:=F)) (Sum.inl 13) := by
      apply (oddPell_atomLabels_left (F:=F) 13).mpr
      apply And.intro (by decide)
      apply Finset.mem_filter.mpr
      apply And.intro
      . apply Nat.mem_divisors.mpr
        apply And.intro
        . change Dvd.dvd 13 (Fintype.card F-1)
          rw [hcard]
          decide
        . change Not (Fintype.card F-1=0)
          omega
      . decide
    have hsum : ({Sum.inl 13} : Finset (Sum Nat Nat)).sum
        (fun i => (oddPellAtomDegree i).totient)=12 := by
      rw [Finset.sum_singleton]
      change (13 : Nat).totient=12
      decide
    apply (oddPell_support_card_spectrum h hh (4*3) hq htwo).mpr
    apply Exists.intro ({Sum.inl 13} : Finset (Sum Nat Nat))
    apply And.intro
    . intro i hiT
      have heqi := Finset.mem_singleton.mp hiT
      subst i
      exact hi
    . exact hsum

theorem oddPell_primeExtension_support_gap (h : F) (hh : Not (h=0))
    (ell : Nat) (hell : Nat.Prime ell) (hne : Not (ell=3))
    (hcard : Fintype.card F=3^ell) (htwo : Not ((2 : F)=0))
    (f : F -> Real) (hf : Membership.mem (oddPellProbeSpace h) f) :
    (oddPellFunctionSupport f).card=0 \/
      (oddPellFunctionSupport f).card=2*ell \/
        6*ell<=(oddPellFunctionSupport f).card := by
  by_cases hz : (oddPellFunctionSupport f).card=0
  . exact Or.inl hz
  . apply Or.inr
    by_cases ho : (oddPellFunctionSupport f).card=2*ell
    . exact Or.inl ho
    . apply Or.inr
      have hfour := oddPell_primeExtension_support_ne_four h hh ell hell hne
        hcard htwo f hf
      choose k hk using oddPell_primeExtension_support_dvd h hh ell hell hcard htwo f hf
      have hk3 : 3<=k := by
        by_contra hbad
        have hcases : k=0 \/ k=1 \/ k=2 := by omega
        cases hcases with
        | inl h => exact hz (by simpa only [h,mul_zero] using hk)
        | inr h =>
          cases h with
          | inl h => exact ho (by simpa only [h,mul_one] using hk)
          | inr h =>
            rw [h] at hk
            exact hfour (by omega)
      calc
        6*ell = (2*ell)*3 := by omega
        _ <= (2*ell)*k := Nat.mul_le_mul_left (2*ell) hk3
        _ = _ := hk.symm

omit [Field F] [DecidableEq F] in
theorem oddPell_primeExtension_minSupport_nonSophie_gap (ell : Nat)
    (hell : Nat.Prime ell) (hcard : Fintype.card F=3^ell)
    (hnot : Not (Nat.Prime (2*ell+1))) :
    6*ell<=oddPellMinSupport (F:=F) := by
  have hq := oddPell_gap_card_ge_five ell hell.two_le hcard
  have hne3 : Not (ell=3) := by
    intro he
    subst ell
    exact hnot (by decide)
  have hlo := oddPell_primeExtension_minSupport_composite_gap ell hell hcard hnot
  have hne : Not (oddPellMinSupport (F:=F)=4*ell) := by
    intro heq
    choose i hi using (oddPell_minSupport_spec (F:=F) hq).1
    exact hne3 ((oddPell_primeExtension_second_atom_iff ell hell hcard i hi.1).mp
      (hi.2.trans heq)).1
  choose k hk using oddPell_primeExtension_minSupport_dvd ell hell hcard
  have hk3 : 3<=k := by
    by_contra hbad
    have hmul := Nat.mul_le_mul_left (2*ell) (show k<=2 by omega)
    have heq : oddPellMinSupport (F:=F)=4*ell := by omega
    exact hne heq
  calc
    6*ell = (2*ell)*3 := by omega
    _ <= (2*ell)*k := Nat.mul_le_mul_left (2*ell) hk3
    _ = _ := hk.symm

omit [Field F] [DecidableEq F] in
theorem oddPell_primeExtension_minSupport_seventeen
    (hcard : Fintype.card F=3^17) : oddPellMinSupport (F:=F)=102 := by
  have hq := oddPell_gap_card_ge_five 17 (by decide) hcard
  have hlo := oddPell_primeExtension_minSupport_nonSophie_gap 17 (by decide)
    hcard (by decide)
  have hi : Membership.mem (oddPellAtomLabels (F:=F)) (Sum.inr 103) := by
    apply (oddPell_atomLabels_right (F:=F) 103).mpr
    apply And.intro (by decide)
    apply Finset.mem_filter.mpr
    apply And.intro
    . apply Nat.mem_divisors.mpr
      apply And.intro
      . change Dvd.dvd 103 (Fintype.card F+1)
        rw [hcard]
        decide
      . change Not (Fintype.card F+1=0)
        omega
    . decide
  have hhi := (oddPell_minSupport_spec (F:=F) hq).2 (Sum.inr 103) hi
  change oddPellMinSupport (F:=F)<=(103 : Nat).totient at hhi
  have hphi : (103 : Nat).totient=102 := by decide
  rw [hphi] at hhi
  omega

theorem oddPell_primeExtension_seventeen_attained (h : F) (hh : Not (h=0))
    (hcard : Fintype.card F=3^17) (htwo : Not ((2 : F)=0)) :
    exists f : F -> Real, Membership.mem (oddPellProbeSpace h) f /\ Not (f=0) /\
      (oddPellFunctionSupport f).card=102 := by
  have hq := oddPell_gap_card_ge_five 17 (by decide) hcard
  choose f hf using (oddPell_sharp_support_minimum h hh hq htwo).2
  exact Exists.intro f (And.intro hf.1 (And.intro hf.2.1
    (hf.2.2.trans (oddPell_primeExtension_minSupport_seventeen hcard))))

end FiniteField
