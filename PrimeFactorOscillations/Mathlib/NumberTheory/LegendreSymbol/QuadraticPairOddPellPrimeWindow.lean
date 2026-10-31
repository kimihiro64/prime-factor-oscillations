/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.ArithmeticFunction.PrimeExtensionCompositeBarrier
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairOddPellSupportGap

/-!
# A sharp rational-prime window for the full signed support spectrum

Every support below2*ell*(2*ell+1) is a union of prime-degree primitive
classes. Its entire cardinality spectrum is exactly the subset sums of p-1
over the finite small rational-prime alphabet. Both actual finite converse
directions and the sharp degree5 boundary are retained.
-/

set_option autoImplicit false
set_option Elab.async false

namespace FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] [DecidableEq F] in
private theorem oddPell_primeWindow_card_ge_five (n : Nat) (hn : 2<=n)
    (hcard : Fintype.card F=3^n) : 5<=Fintype.card F := by
  have hp : (9 : Nat)<=3^n :=
    Nat.pow_le_pow_right (n:=3) (i:=2) (j:=n) (by decide) hn
  rw [hcard]
  omega

omit [Field F] [DecidableEq F] in
private theorem oddPell_primeWindow_atom_data (n : Nat)
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

theorem oddPell_primeWindow_support_iff_union (h : F) (hh : Not (h=0))
    (ell : Nat) (hell : Nat.Prime ell) (hcard : Fintype.card F=3^ell)
    (htwo : Not ((2 : F)=0)) (A : Finset F)
    (hsmall : A.card<2*ell*(2*ell+1)) :
    (exists f : F -> Real, Membership.mem (oddPellProbeSpace h) f /\
      oddPellFunctionSupport f=A) <->
    exists T : Finset (Sum Nat Nat),
      (forall i, Membership.mem T i ->
        Membership.mem (oddPellAtomLabels (F:=F)) i /\ Nat.Prime (oddPellAtomDegree i)) /\
      A=T.biUnion (oddPellShiftAtom h) := by
  classical
  have hq := oddPell_primeWindow_card_ge_five ell hell.two_le hcard
  constructor
  . intro hf
    choose T hT using (oddPell_probe_support_iff_union h hh A hq htwo).mp hf
    have hsum : T.sum (fun i => (oddPellAtomDegree i).totient)=A.card := by
      calc
        _ = (T.biUnion (oddPellShiftAtom h)).card :=
          (oddPell_shiftAtom_union_card h hh T hT.1 htwo).symm
        _ = A.card := congrArg Finset.card hT.2.symm
    apply Exists.intro T
    apply And.intro
    . intro i hi
      have hd := oddPell_primeWindow_atom_data ell hcard i (hT.1 i hi)
      have hle := Finset.single_le_sum
        (s:=T) (f:=fun j => (oddPellAtomDegree j).totient)
        (fun j hj => Nat.zero_le _) hi
      apply And.intro (hT.1 i hi)
      exact Nat.primeExtension_below_barrier_prime ell (oddPellAtomDegree i) hell
        hd.1 hd.2.1 hd.2.2 (by omega)
    . exact hT.2
  . intro hT
    choose T hT using hT
    exact (oddPell_probe_support_iff_union h hh A hq htwo).mpr
      (Exists.intro T (And.intro (fun i hi => (hT.1 i hi).1) hT.2))

theorem oddPell_primeWindow_support_card_iff (h : F) (hh : Not (h=0))
    (ell : Nat) (hell : Nat.Prime ell) (hcard : Fintype.card F=3^ell)
    (htwo : Not ((2 : F)=0)) (n : Nat) (hn : n<2*ell*(2*ell+1)) :
    (exists f : F -> Real, Membership.mem (oddPellProbeSpace h) f /\
      (oddPellFunctionSupport f).card=n) <->
    exists P : Finset Nat,
      (forall p, Membership.mem P p ->
        Membership.mem (Nat.primeExtensionPrimeAlphabet ell) p) /\
      P.sum (fun p => p-1)=n := by
  classical
  have hq := oddPell_primeWindow_card_ge_five ell hell.two_le hcard
  constructor
  . intro hf
    choose f hf using hf
    have hsmall : (oddPellFunctionSupport f).card<2*ell*(2*ell+1) := by
      rw [hf.2]
      exact hn
    choose T hT using (oddPell_primeWindow_support_iff_union h hh ell hell hcard htwo
      (oddPellFunctionSupport f) hsmall).mp (Exists.intro f (And.intro hf.1 rfl))
    have hlabels : forall i, Membership.mem T i ->
        Membership.mem (oddPellAtomLabels (F:=F)) i := fun i hi => (hT.1 i hi).1
    have hsum : T.sum (fun i => (oddPellAtomDegree i).totient)=n := by
      calc
        _ = (T.biUnion (oddPellShiftAtom h)).card :=
          (oddPell_shiftAtom_union_card h hh T hlabels htwo).symm
        _ = (oddPellFunctionSupport f).card := congrArg Finset.card hT.2.symm
        _ = n := hf.2
    apply Exists.intro (T.image oddPellAtomDegree)
    apply And.intro
    . intro p hp
      choose i hi using Finset.mem_image.mp hp
      have hd := oddPell_primeWindow_atom_data ell hcard i (hlabels i hi.1)
      have hprime := (hT.1 i hi.1).2
      have hle := Finset.single_le_sum
        (s:=T) (f:=fun j => (oddPellAtomDegree j).totient)
        (fun j hj => Nat.zero_le _) hi.1
      have hless : oddPellAtomDegree i-1<2*ell*(2*ell+1) := by
        rw [<- Nat.totient_prime hprime]
        omega
      have hm := (Nat.mem_primeExtensionPrimeAlphabet ell (oddPellAtomDegree i)).mpr
        (And.intro hprime (And.intro hd.1 (And.intro hless hd.2.2)))
      simpa only [hi.2] using hm
    . rw [Finset.sum_image]
      . calc
          T.sum (fun i => oddPellAtomDegree i-1) =
              T.sum (fun i => (oddPellAtomDegree i).totient) :=
            Finset.sum_congr rfl (fun i hi => (Nat.totient_prime (hT.1 i hi).2).symm)
          _ = n := hsum
      . intro i hi j hj heq
        exact oddPell_atomDegree_injective i j (hlabels i hi) (hlabels j hj) hq heq
  . intro hP
    choose P hP using hP
    let label : Nat -> Sum Nat Nat := fun p =>
      if Dvd.dvd p (3^ell-1) then Sum.inl p else Sum.inr p
    have hdegree : forall p, oddPellAtomDegree (label p)=p := by
      intro p
      by_cases hd : Dvd.dvd p (3^ell-1)
      . simp only [label,ite_eq_left hd]
        rfl
      . simp only [label,ite_eq_right hd]
        rfl
    have hlabelinj : Function.Injective label := by
      intro p q heq
      have hd := congrArg oddPellAtomDegree heq
      simpa only [hdegree] using hd
    have hlabel : forall p, Membership.mem P p ->
        Membership.mem (oddPellAtomLabels (F:=F)) (label p) := by
      intro p hp
      have hd := (Nat.mem_primeExtensionPrimeAlphabet ell p).mp (hP.1 p hp)
      by_cases hminus : Dvd.dvd p (3^ell-1)
      . simp only [label,ite_eq_left hminus]
        apply (oddPell_atomLabels_left (F:=F) p).mpr
        apply And.intro hd.1.ne_one
        apply Finset.mem_filter.mpr
        apply And.intro
        . apply Nat.mem_divisors.mpr
          apply And.intro
          . change Dvd.dvd p (Fintype.card F-1)
            simpa only [hcard] using hminus
          . change Not (Fintype.card F-1=0)
            omega
        . exact hd.2.1
      . have hplus := hd.2.2.2.resolve_left hminus
        simp only [label,ite_eq_right hminus]
        apply (oddPell_atomLabels_right (F:=F) p).mpr
        apply And.intro hd.1.ne_one
        apply Finset.mem_filter.mpr
        apply And.intro
        . apply Nat.mem_divisors.mpr
          apply And.intro
          . change Dvd.dvd p (Fintype.card F+1)
            simpa only [hcard] using hplus
          . change Not (Fintype.card F+1=0)
            omega
        . exact hd.2.1
    apply (oddPell_support_card_spectrum h hh n hq htwo).mpr
    apply Exists.intro (P.image label)
    apply And.intro
    . intro i hi
      choose p hp using Finset.mem_image.mp hi
      have hm := hlabel p hp.1
      simpa only [hp.2] using hm
    . rw [Finset.sum_image]
      . calc
          P.sum (fun p => (oddPellAtomDegree (label p)).totient) =
              P.sum (fun p => p-1) := by
            apply Finset.sum_congr rfl
            intro p hp
            have hd := (Nat.mem_primeExtensionPrimeAlphabet ell p).mp (hP.1 p hp)
            simpa only [hdegree] using Nat.totient_prime hd.1
          _ = n := hP.2
      . intro p hp q hq heq
        exact hlabelinj heq

theorem oddPell_primeWindow_nonzero_iff (h : F) (hh : Not (h=0))
    (ell : Nat) (hell : Nat.Prime ell) (hcard : Fintype.card F=3^ell)
    (htwo : Not ((2 : F)=0)) :
    (exists f : F -> Real, Membership.mem (oddPellProbeSpace h) f /\ Not (f=0) /\
      (oddPellFunctionSupport f).card<2*ell*(2*ell+1)) <->
    (Nat.primeExtensionPrimeAlphabet ell).Nonempty := by
  classical
  constructor
  . intro hf
    choose f hf using hf
    choose P hP using (oddPell_primeWindow_support_card_iff h hh ell hell hcard htwo
      (oddPellFunctionSupport f).card hf.2.2).mp
        (Exists.intro f (And.intro hf.1 rfl))
    have hpos : 0<(oddPellFunctionSupport f).card :=
      Finset.card_pos.mpr ((oddPell_functionSupport_nonempty_iff f).mpr hf.2.1)
    have hnon : P.Nonempty := by
      by_contra hn
      have hz := Finset.not_nonempty_iff_eq_empty.mp hn
      rw [hz,Finset.sum_empty] at hP
      omega
    choose p hp using hnon
    exact Exists.intro p (hP.1 p hp)
  . intro hp
    choose p hp using hp
    have hd := (Nat.mem_primeExtensionPrimeAlphabet ell p).mp hp
    have hp2 := hd.1.two_le
    have hf := (oddPell_primeWindow_support_card_iff h hh ell hell hcard htwo
      (p-1) hd.2.2.1).mpr
        (Exists.intro ({p} : Finset Nat) (And.intro
          (fun q hq => by
            have heq := Finset.mem_singleton.mp hq
            simpa only [heq] using hp)
          (Finset.sum_singleton (f:=fun q : Nat => q-1) p)))
    choose f hf using hf
    have hfn : Not (f=0) := (oddPell_functionSupport_nonempty_iff f).mp
      (Finset.card_pos.mp (by rw [hf.2]; omega))
    exact Exists.intro f (And.intro hf.1 (And.intro hfn (by rw [hf.2]; exact hd.2.2.1)))

theorem oddPell_primeWindow_five_boundary_attained (h : F) (hh : Not (h=0))
    (hcard : Fintype.card F=3^5) (htwo : Not ((2 : F)=0)) :
    exists f : F -> Real, Membership.mem (oddPellProbeSpace h) f /\ Not (f=0) /\
      (oddPellFunctionSupport f).card=110 := by
  have hq := oddPell_primeWindow_card_ge_five 5 (by decide) hcard
  have hi : Membership.mem (oddPellAtomLabels (F:=F)) (Sum.inl 121) := by
    apply (oddPell_atomLabels_left (F:=F) 121).mpr
    apply And.intro (by decide)
    apply Finset.mem_filter.mpr
    apply And.intro
    . apply Nat.mem_divisors.mpr
      apply And.intro
      . change Dvd.dvd 121 (Fintype.card F-1)
        rw [hcard]
        decide
      . change Not (Fintype.card F-1=0)
        omega
    . decide
  have hsum : ({Sum.inl 121} : Finset (Sum Nat Nat)).sum
      (fun i => (oddPellAtomDegree i).totient)=110 := by
    rw [Finset.sum_singleton]
    change (121 : Nat).totient=110
    decide
  have hex := (oddPell_support_card_spectrum h hh 110 hq htwo).mpr
    (Exists.intro ({Sum.inl 121} : Finset (Sum Nat Nat)) (And.intro
      (fun i hiT => by
        have heq := Finset.mem_singleton.mp hiT
        subst i
        exact hi)
      hsum))
  choose f hf using hex
  have hfn : Not (f=0) := (oddPell_functionSupport_nonempty_iff f).mp
    (Finset.card_pos.mp (by rw [hf.2]; decide))
  exact Exists.intro f (And.intro hf.1 (And.intro hfn hf.2))

end FiniteField
