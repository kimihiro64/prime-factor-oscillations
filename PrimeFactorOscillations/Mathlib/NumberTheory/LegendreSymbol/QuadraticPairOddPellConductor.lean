/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.ArithmeticFunction.DivisorKernelAtoms
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairOddPellOverlap

/-!
# Primitive native odd-Pell sectors

The endpoint sectors factor exactly through the odd divisors of q-1 and q+1.
The generic least-divisor atoms therefore have native cardinality phi(d).
Membership in any odd-degree sector is precisely divisibility by the atom's
primitive label. No characteristic-coprimality restriction is imposed.
-/

set_option autoImplicit false
set_option Elab.async false

namespace FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def oddPellSectorModulus (split : Bool) : Nat :=
  if split then Fintype.card F-1 else Fintype.card F+1

noncomputable def oddPellSectorDivisors (split : Bool) : Finset Nat := by
  classical
  exact (oddPellSectorModulus (F:=F) split).divisors.filter Odd

noncomputable def oddPellDegreeSector (split : Bool) (m : Nat) : Finset F :=
  oddPellEndpointSector
    (fun c : F => if split then IsSquare (c*(c+2)) else Not (IsSquare (c*(c+2))))
    ((m-1)/2)

noncomputable def oddPellPrimitiveSector (split : Bool) (d : Nat) : Finset F :=
  Finset.divisorKernelAtom (oddPellSectorDivisors (F:=F) split)
    (oddPellDegreeSector (F:=F) split) d

private theorem oddPell_odd_degree_index (m : Nat) (hm : Odd m) :
    2*((m-1)/2)+1=m := by
  cases hm with
  | intro k hk => omega

omit [Field F] [DecidableEq F] in
theorem oddPell_sectorDivisors_pos (split : Bool) {d : Nat}
    (hd : Membership.mem (oddPellSectorDivisors (F:=F) split) d) : 0<d := by
  have hmem := (Finset.mem_filter.mp hd).1
  have hdiv := Nat.mem_divisors.mp hmem
  by_contra h
  have hz : d=0 := by omega
  have hn : oddPellSectorModulus (F:=F) split=0 := by
    simpa only [hz,zero_dvd_iff] using hdiv.1
  exact hdiv.2 hn

omit [Field F] [DecidableEq F] in
theorem oddPell_sectorDivisors_down (split : Bool) {d e : Nat}
    (hd : Membership.mem (oddPellSectorDivisors (F:=F) split) d)
    (hed : Dvd.dvd e d) :
    Membership.mem (oddPellSectorDivisors (F:=F) split) e := by
  have hm := Finset.mem_filter.mp hd
  have hdN := Nat.mem_divisors.mp hm.1
  apply Finset.mem_filter.mpr
  exact And.intro
    (Nat.mem_divisors.mpr (And.intro (Nat.dvd_trans hed hdN.1) hdN.2))
    (Odd.of_dvd_nat hm.2 hed)

theorem oddPell_degree_sector_card (split : Bool) (m : Nat) (hm : Odd m)
    (htwo : Not ((2 : F)=0)) :
    (oddPellDegreeSector (F:=F) split m).card+1=
      (oddPellSectorModulus (F:=F) split).gcd m := by
  have hi := oddPell_odd_degree_index m hm
  have hc := oddPell_common_sector_sizes (F:=F) ((m-1)/2) ((m-1)/2) htwo
  cases split with
  | false =>
    change (oddPellEndpointSector (fun c : F => Not (IsSquare (c*(c+2))))
      ((m-1)/2)).card+1=(Fintype.card F+1).gcd m
    simpa only [Finset.inter_self,Nat.gcd_self,hi] using hc.2
  | true =>
    change (oddPellEndpointSector (fun c : F => IsSquare (c*(c+2)))
      ((m-1)/2)).card+1=(Fintype.card F-1).gcd m
    simpa only [Finset.inter_self,Nat.gcd_self,hi] using hc.1

theorem oddPell_degree_sector_inter (split : Bool) (m n : Nat)
    (hm : Odd m) (hn : Odd n) (htwo : Not ((2 : F)=0)) :
    Inter.inter (oddPellDegreeSector (F:=F) split m)
      (oddPellDegreeSector (F:=F) split n)=
        oddPellDegreeSector (F:=F) split (m.gcd n) := by
  have hg : Odd (m.gcd n) := Odd.of_dvd_nat hm (Nat.gcd_dvd_left m n)
  exact oddPell_endpoint_sector_inter _
    ((m-1)/2) ((n-1)/2) (((m.gcd n)-1)/2)
    (by rw [oddPell_odd_degree_index m hm,oddPell_odd_degree_index n hn,
      oddPell_odd_degree_index (m.gcd n) hg]) htwo

theorem oddPell_degree_sector_gcd (split : Bool) (m : Nat) (hm : Odd m)
    (htwo : Not ((2 : F)=0)) :
    oddPellDegreeSector (F:=F) split m=
      oddPellDegreeSector (F:=F) split ((oddPellSectorModulus (F:=F) split).gcd m) := by
  let N := oddPellSectorModulus (F:=F) split
  let r := N.gcd m
  have hr : Odd r := Odd.of_dvd_nat hm (Nat.gcd_dvd_right N m)
  have hrdvd : Dvd.dvd r m := Nat.gcd_dvd_right N m
  have hrr : r.gcd m=r := Nat.gcd_eq_left_iff_dvd.mpr hrdvd
  have hi : Inter.inter (oddPellDegreeSector (F:=F) split r)
      (oddPellDegreeSector (F:=F) split m)=oddPellDegreeSector (F:=F) split r := by
    rw [oddPell_degree_sector_inter split r m hr hm htwo,hrr]
  have hs : oddPellDegreeSector (F:=F) split r<=oddPellDegreeSector (F:=F) split m := by
    intro c hc
    have hx : Membership.mem
        (Inter.inter (oddPellDegreeSector (F:=F) split r)
          (oddPellDegreeSector (F:=F) split m)) c := by rw [hi]; exact hc
    exact (Finset.mem_inter.mp hx).2
  have hcr := oddPell_degree_sector_card (F:=F) split r hr htwo
  have hcm := oddPell_degree_sector_card (F:=F) split m hm htwo
  have hNr : N.gcd r=r := by
    rw [Nat.gcd_comm]
    exact Nat.gcd_eq_left_iff_dvd.mpr (Nat.gcd_dvd_left N m)
  change (oddPellDegreeSector (F:=F) split r).card+1=N.gcd r at hcr
  rw [hNr] at hcr
  change (oddPellDegreeSector (F:=F) split m).card+1=r at hcm
  exact (Finset.eq_of_subset_of_card_le hs (by omega)).symm

theorem oddPell_primitiveSector_card (split : Bool) (d : Nat)
    (hd : Membership.mem (oddPellSectorDivisors (F:=F) split) d)
    (hd1 : 1<d) (htwo : Not ((2 : F)=0)) :
    (oddPellPrimitiveSector (F:=F) split d).card=d.totient := by
  apply Finset.divisorKernelAtom_card
    (oddPellSectorDivisors (F:=F) split) (oddPellDegreeSector (F:=F) split)
    (fun e he => oddPell_sectorDivisors_pos split he)
    (fun e he f hfe => oddPell_sectorDivisors_down split he hfe)
    (fun e he f hf => oddPell_degree_sector_inter split e f
      (Finset.mem_filter.mp he).2 (Finset.mem_filter.mp hf).2 htwo)
    (fun e he => ?_) d hd hd1
  have heN := (Nat.mem_divisors.mp (Finset.mem_filter.mp he).1).1
  have hg : (oddPellSectorModulus (F:=F) split).gcd e=e := by
    rw [Nat.gcd_comm]
    exact Nat.gcd_eq_left_iff_dvd.mpr heN
  exact (oddPell_degree_sector_card split e (Finset.mem_filter.mp he).2 htwo).trans hg

theorem oddPell_primitiveSector_disjoint (split : Bool) (d e : Nat)
    (hd : Membership.mem (oddPellSectorDivisors (F:=F) split) d)
    (he : Membership.mem (oddPellSectorDivisors (F:=F) split) e)
    (hne : Not (d=e)) :
    Disjoint (oddPellPrimitiveSector (F:=F) split d)
      (oddPellPrimitiveSector (F:=F) split e) :=
  Finset.divisorKernelAtom_disjoint _ _ hd he hne

theorem oddPell_primitiveSector_mem_degree (split : Bool) (d m : Nat)
    (hd : Membership.mem (oddPellSectorDivisors (F:=F) split) d)
    (hm : Odd m) (htwo : Not ((2 : F)=0)) (c : F)
    (hc : Membership.mem (oddPellPrimitiveSector (F:=F) split d) c) :
    Membership.mem (oddPellDegreeSector (F:=F) split m) c <-> Dvd.dvd d m := by
  let N := oddPellSectorModulus (F:=F) split
  let r := N.gcd m
  have hdN := Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1
  have hrD : Membership.mem (oddPellSectorDivisors (F:=F) split) r := by
    apply Finset.mem_filter.mpr
    exact And.intro
      (Nat.mem_divisors.mpr (And.intro (Nat.gcd_dvd_left N m) hdN.2))
      (Odd.of_dvd_nat hm (Nat.gcd_dvd_right N m))
  have heq := oddPell_degree_sector_gcd (F:=F) split m hm htwo
  have hpos := fun e he => oddPell_sectorDivisors_pos (F:=F) split (d:=e) he
  have hdown := fun e he f hfe => oddPell_sectorDivisors_down (F:=F) split (d:=e) (e:=f) he hfe
  have hmeet : forall e, Membership.mem (oddPellSectorDivisors (F:=F) split) e ->
      forall f, Membership.mem (oddPellSectorDivisors (F:=F) split) f ->
        Inter.inter (oddPellDegreeSector (F:=F) split e)
          (oddPellDegreeSector (F:=F) split f)=oddPellDegreeSector (F:=F) split (e.gcd f) := by
    intro e he f hf
    exact oddPell_degree_sector_inter split e f
      (Finset.mem_filter.mp he).2 (Finset.mem_filter.mp hf).2 htwo
  constructor
  . intro hx
    rw [heq] at hx
    exact Nat.dvd_trans
      (Finset.divisorKernelAtom_dvd_of_mem
        (oddPellSectorDivisors (F:=F) split) (oddPellDegreeSector (F:=F) split)
        hpos hdown hmeet hd hrD hc hx) (Nat.gcd_dvd_right N m)
  . intro hdm
    rw [heq]
    exact Finset.divisorKernel_subset_of_dvd
      (oddPellSectorDivisors (F:=F) split) (oddPellDegreeSector (F:=F) split)
      hmeet hd hrD (Nat.dvd_gcd hdN.1 hdm)
      (Finset.divisorKernelAtom_subset _ _ d hc)


theorem oddPell_degree_sector_eq_biUnion_atoms (split : Bool) (m : Nat)
    (hm : Odd m) (hq : 5<=Fintype.card F) (htwo : Not ((2 : F)=0)) :
    oddPellDegreeSector (F:=F) split m=
      ((oddPellSectorModulus (F:=F) split).gcd m).divisors.biUnion
        (fun d => oddPellPrimitiveSector (F:=F) split d) := by
  classical
  let N := oddPellSectorModulus (F:=F) split
  let r := N.gcd m
  have hN0 : Not (N=0) := by
    cases split with
    | false => change Not (Fintype.card F+1=0); omega
    | true => change Not (Fintype.card F-1=0); omega
  have hrD : Membership.mem (oddPellSectorDivisors (F:=F) split) r := by
    apply Finset.mem_filter.mpr
    exact And.intro
      (Nat.mem_divisors.mpr (And.intro (Nat.gcd_dvd_left N m) hN0))
      (Odd.of_dvd_nat hm (Nat.gcd_dvd_right N m))
  calc
    _ = oddPellDegreeSector (F:=F) split r :=
      oddPell_degree_sector_gcd split m hm htwo
    _ = _ := Finset.divisorKernel_eq_biUnion_atoms
      (oddPellSectorDivisors (F:=F) split) (oddPellDegreeSector (F:=F) split)
      (fun e he => oddPell_sectorDivisors_pos split he)
      (fun e he f hfe => oddPell_sectorDivisors_down split he hfe)
      (fun e he f hf => oddPell_degree_sector_inter split e f
        (Finset.mem_filter.mp he).2 (Finset.mem_filter.mp hf).2 htwo) hrD

theorem oddPell_primitiveSector_opposite_disjoint (d e : Nat) :
    Disjoint (oddPellPrimitiveSector (F:=F) true d)
      (oddPellPrimitiveSector (F:=F) false e) := by
  classical
  apply Finset.disjoint_left.mpr
  intro c hc hd
  have hp : Membership.mem
      (oddPellEndpointSector (fun x : F => IsSquare (x*(x+2))) ((d-1)/2)) c :=
    Finset.divisorKernelAtom_subset _ _ d hc
  have hn : Membership.mem
      (oddPellEndpointSector (fun x : F => Not (IsSquare (x*(x+2)))) ((e-1)/2)) c :=
    Finset.divisorKernelAtom_subset _ _ e hd
  simp only [oddPellEndpointSector,Finset.mem_filter,Finset.mem_univ,true_and] at hp hn
  exact hn.2.2.1 hp.2.2.1

end FiniteField
