/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.ArithmeticFunction.PrimeExtensionTotient
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairOddPellSpectrum

/-!
# Prime-extension support lattices and the Sophie Germain endpoint

Every prime extension degree is retained. The index ell is the field extension
degree, not an odd-Pell polynomial index. The consumers are actual finite signed
probe supports and their attained minimum.
-/

set_option autoImplicit false
set_option Elab.async false

namespace FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] [DecidableEq F] in
private theorem oddPell_primeExtension_card_ge_five (ell : Nat) (hell : Nat.Prime ell)
    (hcard : Fintype.card F=3^ell) : 5<=Fintype.card F := by
  have hp : (9 : Nat)<=3^ell :=
    Nat.pow_le_pow_right (n:=3) (i:=2) (j:=ell) (by decide) hell.two_le
  rw [hcard]
  omega

omit [Field F] [DecidableEq F] in
theorem oddPell_primeExtension_atom_totient_dvd (ell : Nat) (hell : Nat.Prime ell)
    (hcard : Fintype.card F=3^ell) (i : Sum Nat Nat)
    (hi : Membership.mem (oddPellAtomLabels (F:=F)) i) :
    Dvd.dvd (2*ell) (oddPellAtomDegree i).totient := by
  cases i with
  | inl d =>
    have hm := (oddPell_atomLabels_left (F:=F) d).mp hi
    have ho := (Finset.mem_filter.mp hm.2).2
    have hp := oddPell_atomDegree_pos (Sum.inl d) hi
    change 0<d at hp
    have hd : 1<d := by have hn := hm.1; omega
    have hv : Dvd.dvd d (3^ell-1) := by
      have hh := (Nat.mem_divisors.mp (Finset.mem_filter.mp hm.2).1).1
      change Dvd.dvd d (Fintype.card F-1) at hh
      simpa only [hcard] using hh
    exact Nat.primeExtension_totient_dvd ell d hell ho hd (Or.inl hv)
  | inr d =>
    have hm := (oddPell_atomLabels_right (F:=F) d).mp hi
    have ho := (Finset.mem_filter.mp hm.2).2
    have hp := oddPell_atomDegree_pos (Sum.inr d) hi
    change 0<d at hp
    have hd : 1<d := by have hn := hm.1; omega
    have hv : Dvd.dvd d (3^ell+1) := by
      have hh := (Nat.mem_divisors.mp (Finset.mem_filter.mp hm.2).1).1
      change Dvd.dvd d (Fintype.card F+1) at hh
      simpa only [hcard] using hh
    exact Nat.primeExtension_totient_dvd ell d hell ho hd (Or.inr hv)

omit [Field F] [DecidableEq F] in
theorem oddPell_primeExtension_minSupport_dvd (ell : Nat) (hell : Nat.Prime ell)
    (hcard : Fintype.card F=3^ell) :
    Dvd.dvd (2*ell) (oddPellMinSupport (F:=F)) := by
  have hq := oddPell_primeExtension_card_ge_five ell hell hcard
  choose i hi using (oddPell_minSupport_spec (F:=F) hq).1
  have hd := oddPell_primeExtension_atom_totient_dvd ell hell hcard i hi.1
  simpa only [hi.2] using hd

omit [Field F] [DecidableEq F] in
theorem oddPell_primeExtension_minSupport_lower (ell : Nat) (hell : Nat.Prime ell)
    (hcard : Fintype.card F=3^ell) :
    2*ell<=oddPellMinSupport (F:=F) := by
  have hq := oddPell_primeExtension_card_ge_five ell hell hcard
  have hm := oddPell_minSupport_two_le (F:=F) hq
  exact Nat.le_of_dvd (by omega) (oddPell_primeExtension_minSupport_dvd ell hell hcard)

theorem oddPell_primeExtension_support_dvd (h : F) (hh : Not (h=0))
    (ell : Nat) (hell : Nat.Prime ell) (hcard : Fintype.card F=3^ell)
    (htwo : Not ((2 : F)=0)) (f : F -> Real)
    (hf : Membership.mem (oddPellProbeSpace h) f) :
    Dvd.dvd (2*ell) (oddPellFunctionSupport f).card := by
  have hq := oddPell_primeExtension_card_ge_five ell hell hcard
  have hs := (oddPell_support_card_spectrum h hh (oddPellFunctionSupport f).card hq htwo).mp
    (Exists.intro f (And.intro hf rfl))
  choose T hT using hs
  rw [hT.2.symm]
  exact Finset.dvd_sum (fun i hi =>
    oddPell_primeExtension_atom_totient_dvd ell hell hcard i (hT.1 i hi))

omit [Field F] [DecidableEq F] in
theorem oddPell_primeExtension_minSupport_eq_iff_prime (ell : Nat) (hell : Nat.Prime ell)
    (hcard : Fintype.card F=3^ell) :
    oddPellMinSupport (F:=F)=2*ell <-> Nat.Prime (2*ell+1) := by
  have hq := oddPell_primeExtension_card_ge_five ell hell hcard
  constructor
  . intro heq
    choose i hi using (oddPell_minSupport_spec (F:=F) hq).1
    have hphi : (oddPellAtomDegree i).totient=2*ell := hi.2.trans heq
    cases i with
    | inl d =>
      have hm := (oddPell_atomLabels_left (F:=F) d).mp hi.1
      have ho := (Finset.mem_filter.mp hm.2).2
      have hp := oddPell_atomDegree_pos (Sum.inl d) hi.1
      change 0<d at hp
      have hd : 1<d := by have hn := hm.1; omega
      have hv : Dvd.dvd d (3^ell-1) := by
        have hh := (Nat.mem_divisors.mp (Finset.mem_filter.mp hm.2).1).1
        change Dvd.dvd d (Fintype.card F-1) at hh
        simpa only [hcard] using hh
      exact Nat.primeExtension_endpoint_prime ell d hell ho hd (Or.inl hv) hphi
    | inr d =>
      have hm := (oddPell_atomLabels_right (F:=F) d).mp hi.1
      have ho := (Finset.mem_filter.mp hm.2).2
      have hp := oddPell_atomDegree_pos (Sum.inr d) hi.1
      change 0<d at hp
      have hd : 1<d := by have hn := hm.1; omega
      have hv : Dvd.dvd d (3^ell+1) := by
        have hh := (Nat.mem_divisors.mp (Finset.mem_filter.mp hm.2).1).1
        change Dvd.dvd d (Fintype.card F+1) at hh
        simpa only [hcard] using hh
      exact Nat.primeExtension_endpoint_prime ell d hell ho hd (Or.inr hv) hphi
  . intro hp
    have hlo := oddPell_primeExtension_minSupport_lower ell hell hcard
    have hsupply := Nat.primeExtension_safePrime_factor ell hell.two_le hp
    have hphi : (2*ell+1).totient=2*ell := by rw [Nat.totient_prime hp]; omega
    have hhi : oddPellMinSupport (F:=F)<=(2*ell+1).totient := by
      cases hsupply with
      | inl hv =>
        have hi : Membership.mem (oddPellAtomLabels (F:=F)) (Sum.inl (2*ell+1)) := by
          apply (oddPell_atomLabels_left (F:=F) (2*ell+1)).mpr
          apply And.intro
          . have he2 := hell.two_le
            omega
          . apply Finset.mem_filter.mpr
            apply And.intro
            . apply Nat.mem_divisors.mpr
              apply And.intro
              . change Dvd.dvd (2*ell+1) (Fintype.card F-1)
                simpa only [hcard] using hv
              . change Not (Fintype.card F-1=0)
                omega
            . exact Exists.intro ell rfl
        exact (oddPell_minSupport_spec (F:=F) hq).2 (Sum.inl (2*ell+1)) hi
      | inr hv =>
        have hi : Membership.mem (oddPellAtomLabels (F:=F)) (Sum.inr (2*ell+1)) := by
          apply (oddPell_atomLabels_right (F:=F) (2*ell+1)).mpr
          apply And.intro
          . have he2 := hell.two_le
            omega
          . apply Finset.mem_filter.mpr
            apply And.intro
            . apply Nat.mem_divisors.mpr
              apply And.intro
              . change Dvd.dvd (2*ell+1) (Fintype.card F+1)
                simpa only [hcard] using hv
              . change Not (Fintype.card F+1=0)
                omega
            . exact Exists.intro ell rfl
        exact (oddPell_minSupport_spec (F:=F) hq).2 (Sum.inr (2*ell+1)) hi
    rw [hphi] at hhi
    exact Nat.le_antisymm hhi hlo

omit [Field F] [DecidableEq F] in
theorem oddPell_primeExtension_minSupport_composite_gap (ell : Nat) (hell : Nat.Prime ell)
    (hcard : Fintype.card F=3^ell) (hnot : Not (Nat.Prime (2*ell+1))) :
    4*ell<=oddPellMinSupport (F:=F) := by
  have hq := oddPell_primeExtension_card_ge_five ell hell hcard
  have hne : Not (oddPellMinSupport (F:=F)=2*ell) := by
    intro heq
    exact hnot ((oddPell_primeExtension_minSupport_eq_iff_prime ell hell hcard).mp heq)
  choose k hk using oddPell_primeExtension_minSupport_dvd ell hell hcard
  have hk2 : 2<=k := by
    by_contra hn
    have hc : k=0 \/ k=1 := by omega
    cases hc with
    | inl hz =>
      have hm0 : oddPellMinSupport (F:=F)=0 := by simpa only [hz,mul_zero] using hk
      have hm2 := oddPell_minSupport_two_le (F:=F) hq
      omega
    | inr hz =>
      have hm1 : oddPellMinSupport (F:=F)=2*ell := by simpa only [hz,mul_one] using hk
      exact hne hm1
  calc
    4*ell = (2*ell)*2 := by omega
    _ <= (2*ell)*k := Nat.mul_le_mul_left (2*ell) hk2
    _ = _ := hk.symm

theorem oddPell_primeExtension_endpoint_iff_prime (h : F) (hh : Not (h=0))
    (ell : Nat) (hell : Nat.Prime ell) (hcard : Fintype.card F=3^ell)
    (htwo : Not ((2 : F)=0)) :
    (exists f : F -> Real, Membership.mem (oddPellProbeSpace h) f /\ Not (f=0) /\
      (oddPellFunctionSupport f).card=2*ell) <-> Nat.Prime (2*ell+1) := by
  have hq := oddPell_primeExtension_card_ge_five ell hell hcard
  constructor
  . intro hf
    choose f hf using hf
    have hlo := oddPell_primeExtension_minSupport_lower ell hell hcard
    have hhi := (oddPell_sharp_support_minimum h hh hq htwo).1 f hf.1 hf.2.1
    rw [hf.2.2] at hhi
    exact (oddPell_primeExtension_minSupport_eq_iff_prime ell hell hcard).mp
      (Nat.le_antisymm hhi hlo)
  . intro hp
    have heq := (oddPell_primeExtension_minSupport_eq_iff_prime ell hell hcard).mpr hp
    choose f hf using (oddPell_sharp_support_minimum h hh hq htwo).2
    exact Exists.intro f (And.intro hf.1 (And.intro hf.2.1 (hf.2.2.trans heq)))

end FiniteField
