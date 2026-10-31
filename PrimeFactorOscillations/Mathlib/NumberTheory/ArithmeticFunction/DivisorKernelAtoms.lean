/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.Totient

/-!
# Primitive atoms of finite divisor kernels

A finite divisor ideal with exact gcd intersections has least-label atoms.
Each active label is a multiple of the unique least active divisor, so the
original sets are disjoint divisor unions. Exact kernel cardinalities will
then determine the primitive cardinalities by the divisor-totient identity.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Finset

variable {alpha : Type*} [DecidableEq alpha]

noncomputable def divisorKernelAtom (D : Finset Nat) (E : Nat -> Finset alpha)
    (d : Nat) : Finset alpha := by
  classical
  exact (E d).filter (fun x => forall e, Membership.mem D e ->
    Membership.mem (E e) x -> d<=e)

theorem mem_divisorKernelAtom (D : Finset Nat) (E : Nat -> Finset alpha)
    (d : Nat) (x : alpha) :
    Membership.mem (divisorKernelAtom D E d) x <->
      Membership.mem (E d) x /\
        forall e, Membership.mem D e -> Membership.mem (E e) x -> d<=e := by
  classical
  simp only [divisorKernelAtom,mem_filter]

theorem divisorKernelAtom_subset (D : Finset Nat) (E : Nat -> Finset alpha)
    (d : Nat) : divisorKernelAtom D E d <= E d := by
  intro x hx
  exact ((mem_divisorKernelAtom D E d x).mp hx).1

theorem divisorKernelAtom_disjoint (D : Finset Nat) (E : Nat -> Finset alpha)
    {d e : Nat} (hd : Membership.mem D d) (he : Membership.mem D e)
    (hne : Not (d=e)) :
    Disjoint (divisorKernelAtom D E d) (divisorKernelAtom D E e) := by
  apply disjoint_left.mpr
  intro x hx hy
  have hx' := (mem_divisorKernelAtom D E d x).mp hx
  have hy' := (mem_divisorKernelAtom D E e x).mp hy
  exact hne (Nat.le_antisymm (hx'.2 e he hy'.1) (hy'.2 d hd hx'.1))

theorem divisorKernel_subset_of_dvd (D : Finset Nat) (E : Nat -> Finset alpha)
    (hmeet : forall d, Membership.mem D d -> forall e, Membership.mem D e ->
      Inter.inter (E d) (E e)=E (d.gcd e))
    {d e : Nat} (hd : Membership.mem D d) (he : Membership.mem D e)
    (hde : Dvd.dvd d e) : E d <= E e := by
  intro x hx
  have hg : d.gcd e=d := Nat.gcd_eq_left_iff_dvd.mpr hde
  have hi : Inter.inter (E d) (E e)=E d := by rw [hmeet d hd e he,hg]
  have hm : Membership.mem (Inter.inter (E d) (E e)) x := by rw [hi]; exact hx
  exact (mem_inter.mp hm).2

theorem divisorKernelAtom_dvd_of_mem (D : Finset Nat) (E : Nat -> Finset alpha)
    (hpos : forall d, Membership.mem D d -> 0<d)
    (hdown : forall d, Membership.mem D d -> forall e, Dvd.dvd e d -> Membership.mem D e)
    (hmeet : forall d, Membership.mem D d -> forall e, Membership.mem D e ->
      Inter.inter (E d) (E e)=E (d.gcd e))
    {d e : Nat} (hd : Membership.mem D d) (he : Membership.mem D e)
    {x : alpha} (hx : Membership.mem (divisorKernelAtom D E d) x)
    (hxe : Membership.mem (E e) x) : Dvd.dvd d e := by
  have hx' := (mem_divisorKernelAtom D E d x).mp hx
  have hgD : Membership.mem D (d.gcd e) := hdown d hd _ (Nat.gcd_dvd_left d e)
  have hxg : Membership.mem (E (d.gcd e)) x := by
    rw [<- hmeet d hd e he]
    exact mem_inter.mpr (And.intro hx'.1 hxe)
  have hlow : d<=d.gcd e := hx'.2 _ hgD hxg
  have hupp : d.gcd e<=d := Nat.le_of_dvd (hpos d hd) (Nat.gcd_dvd_left d e)
  exact Nat.gcd_eq_left_iff_dvd.mp (Nat.le_antisymm hupp hlow)

theorem exists_divisorKernelAtom_of_mem (D : Finset Nat) (E : Nat -> Finset alpha)
    (hpos : forall d, Membership.mem D d -> 0<d)
    (hdown : forall d, Membership.mem D d -> forall e, Dvd.dvd e d -> Membership.mem D e)
    (hmeet : forall d, Membership.mem D d -> forall e, Membership.mem D e ->
      Inter.inter (E d) (E e)=E (d.gcd e))
    {d : Nat} (hd : Membership.mem D d) {x : alpha}
    (hx : Membership.mem (E d) x) :
    exists e, Membership.mem d.divisors e /\ Membership.mem (divisorKernelAtom D E e) x := by
  classical
  have hex : exists e, Membership.mem D e /\ Membership.mem (E e) x :=
    Exists.intro d (And.intro hd hx)
  let e := Nat.find hex
  have he : Membership.mem D e /\ Membership.mem (E e) x := Nat.find_spec hex
  have ha : Membership.mem (divisorKernelAtom D E e) x := by
    apply (mem_divisorKernelAtom D E e x).mpr
    apply And.intro he.2
    intro n hn hxn
    exact Nat.find_min' hex (And.intro hn hxn)
  have hed : Dvd.dvd e d := divisorKernelAtom_dvd_of_mem D E hpos hdown hmeet he.1 hd ha hx
  exact Exists.intro e (And.intro
    (Nat.mem_divisors.mpr (And.intro hed (Nat.ne_of_gt (hpos d hd)))) ha)

theorem divisorKernel_eq_biUnion_atoms (D : Finset Nat) (E : Nat -> Finset alpha)
    (hpos : forall d, Membership.mem D d -> 0<d)
    (hdown : forall d, Membership.mem D d -> forall e, Dvd.dvd e d -> Membership.mem D e)
    (hmeet : forall d, Membership.mem D d -> forall e, Membership.mem D e ->
      Inter.inter (E d) (E e)=E (d.gcd e))
    {d : Nat} (hd : Membership.mem D d) :
    E d=d.divisors.biUnion (fun e => divisorKernelAtom D E e) := by
  classical
  apply Finset.ext
  intro x
  constructor
  . intro hx
    cases exists_divisorKernelAtom_of_mem D E hpos hdown hmeet hd hx with
    | intro e he =>
      exact mem_biUnion.mpr (Exists.intro e he)
  . intro hx
    cases mem_biUnion.mp hx with
    | intro e he =>
      have hed : Dvd.dvd e d := (Nat.mem_divisors.mp he.1).1
      have heD := hdown d hd e hed
      exact divisorKernel_subset_of_dvd D E hmeet heD hd hed
        (divisorKernelAtom_subset D E e he.2)

theorem divisorKernel_card_sum_atoms (D : Finset Nat) (E : Nat -> Finset alpha)
    (hpos : forall d, Membership.mem D d -> 0<d)
    (hdown : forall d, Membership.mem D d -> forall e, Dvd.dvd e d -> Membership.mem D e)
    (hmeet : forall d, Membership.mem D d -> forall e, Membership.mem D e ->
      Inter.inter (E d) (E e)=E (d.gcd e))
    {d : Nat} (hd : Membership.mem D d) :
    (E d).card=d.divisors.sum (fun e => (divisorKernelAtom D E e).card) := by
  classical
  rw [divisorKernel_eq_biUnion_atoms D E hpos hdown hmeet hd]
  apply card_biUnion
  intro a ha b hb hab
  exact divisorKernelAtom_disjoint D E
    (hdown d hd a (Nat.mem_divisors.mp ha).1)
    (hdown d hd b (Nat.mem_divisors.mp hb).1) hab

theorem divisorKernelAtom_one_card (D : Finset Nat) (E : Nat -> Finset alpha)
    (hcard : forall d, Membership.mem D d -> (E d).card+1=d)
    (hone : Membership.mem D 1) :
    (divisorKernelAtom D E 1).card=0 := by
  have he := hcard 1 hone
  have hs := card_le_card (divisorKernelAtom_subset D E 1)
  omega


theorem divisorKernelAtom_card (D : Finset Nat) (E : Nat -> Finset alpha)
    (hpos : forall d, Membership.mem D d -> 0<d)
    (hdown : forall d, Membership.mem D d -> forall e, Dvd.dvd e d -> Membership.mem D e)
    (hmeet : forall d, Membership.mem D d -> forall e, Membership.mem D e ->
      Inter.inter (E d) (E e)=E (d.gcd e))
    (hcard : forall d, Membership.mem D d -> (E d).card+1=d) :
    forall d, Membership.mem D d -> 1<d -> (divisorKernelAtom D E d).card=d.totient := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd hd1
    have hd0 : Not (d=0) := Nat.ne_of_gt (hpos d hd)
    have hmemd : Membership.mem d.divisors d :=
      Nat.mem_divisors.mpr (And.intro (dvd_refl d) hd0)
    have hmem1 : Membership.mem d.divisors 1 :=
      Nat.mem_divisors.mpr (And.intro (one_dvd d) hd0)
    have hdne : Not (d=1) := by omega
    have hmemd' : Membership.mem (d.divisors.erase 1) d :=
      mem_erase.mpr (And.intro hdne hmemd)
    let U := (d.divisors.erase 1).erase d
    have hlocal : forall e, Membership.mem U e ->
        (divisorKernelAtom D E e).card=e.totient := by
      intro e he
      have he' := mem_erase.mp he
      have he'' := mem_erase.mp he'.2
      have heD := hdown d hd e (Nat.mem_divisors.mp he''.2).1
      have hele : e<=d := Nat.divisor_le he''.2
      have hepos := hpos e heD
      exact ih e (by omega) heD (by omega)
    have hsumU : U.sum (fun e => (divisorKernelAtom D E e).card)=
        U.sum Nat.totient := sum_congr rfl hlocal
    have honeD := hdown d hd 1 (one_dvd d)
    have hone := divisorKernelAtom_one_card D E hcard honeD
    have ha := sum_erase_add (d.divisors.erase 1)
      (fun e => (divisorKernelAtom D E e).card) hmemd'
    have hb := sum_erase_add d.divisors
      (fun e => (divisorKernelAtom D E e).card) hmem1
    have hc := divisorKernel_card_sum_atoms D E hpos hdown hmeet hd
    have hAtoms : U.sum (fun e => (divisorKernelAtom D E e).card)+
        (divisorKernelAtom D E d).card=(E d).card := by
      calc
        _ = (d.divisors.erase 1).sum (fun e => (divisorKernelAtom D E e).card) := ha
        _ = d.divisors.sum (fun e => (divisorKernelAtom D E e).card) := by
          simpa only [hone,add_zero] using hb
        _ = _ := hc.symm
    have hpa := sum_erase_add (d.divisors.erase 1) Nat.totient hmemd'
    have hpb := sum_erase_add d.divisors Nat.totient hmem1
    have hPhi : U.sum Nat.totient+d.totient+1=d := by
      calc
        _ = (d.divisors.erase 1).sum Nat.totient+1 :=
          congrArg (fun n : Nat => n+1) hpa
        _ = d.divisors.sum Nat.totient := by
          simpa only [Nat.totient_one] using hpb
        _ = _ := Nat.sum_totient d
    rw [hsumU] at hAtoms
    have hsize := hcard d hd
    omega

end Finset
