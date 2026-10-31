/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairOddPellConductor
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairOddPellEnergy

/-!
# Signed odd-Pell probes on primitive atoms

The exact compensated defects are constant on the native primitive classes.
Both sectors and arbitrary real coefficient signs are retained.
-/

set_option autoImplicit false
set_option Elab.async false

namespace FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def oddPellSignedProbe (h : F) (S : Finset Nat) (a : Nat -> Real)
    (c : F) : Real := S.sum (fun k => a k*oddPellDefect h c k)

noncomputable def oddPellAtomLabels : Finset (Sum Nat Nat) :=
  Union.union
    (((oddPellSectorDivisors (F:=F) true).erase 1).image
      (Sum.inl : Nat -> Sum Nat Nat))
    (((oddPellSectorDivisors (F:=F) false).erase 1).image
      (Sum.inr : Nat -> Sum Nat Nat))

noncomputable def oddPellAtom (i : Sum Nat Nat) : Finset F :=
  Sum.elim (oddPellPrimitiveSector (F:=F) true)
    (oddPellPrimitiveSector (F:=F) false) i

def oddPellAtomDegree (i : Sum Nat Nat) : Nat := Sum.elim id id i

noncomputable def oddPellAtomWeight (i : Sum Nat Nat) : Real :=
  Sum.elim (fun _ : Nat => oddPellSplitWeight (F:=F))
    (fun _ : Nat => oddPellNonsplitWeight (F:=F)) i

omit [Field F] [DecidableEq F] in
theorem oddPell_atomLabels_left (d : Nat) :
    Membership.mem (oddPellAtomLabels (F:=F)) (Sum.inl d) <->
      Not (d=1) /\ Membership.mem (oddPellSectorDivisors (F:=F) true) d := by
  classical
  simp [oddPellAtomLabels]

omit [Field F] [DecidableEq F] in
theorem oddPell_atomLabels_right (d : Nat) :
    Membership.mem (oddPellAtomLabels (F:=F)) (Sum.inr d) <->
      Not (d=1) /\ Membership.mem (oddPellSectorDivisors (F:=F) false) d := by
  classical
  simp [oddPellAtomLabels]

theorem oddPell_atom_card (i : Sum Nat Nat)
    (hi : Membership.mem (oddPellAtomLabels (F:=F)) i) (htwo : Not ((2 : F)=0)) :
    (oddPellAtom (F:=F) i).card=(oddPellAtomDegree i).totient := by
  cases i with
  | inl d =>
    have hd := (oddPell_atomLabels_left (F:=F) d).mp hi
    have hpos := oddPell_sectorDivisors_pos (F:=F) true hd.2
    exact oddPell_primitiveSector_card true d hd.2 (by omega) htwo
  | inr d =>
    have hd := (oddPell_atomLabels_right (F:=F) d).mp hi
    have hpos := oddPell_sectorDivisors_pos (F:=F) false hd.2
    exact oddPell_primitiveSector_card false d hd.2 (by omega) htwo

theorem oddPell_atom_disjoint (i j : Sum Nat Nat)
    (hi : Membership.mem (oddPellAtomLabels (F:=F)) i)
    (hj : Membership.mem (oddPellAtomLabels (F:=F)) j) (hne : Not (i=j)) :
    Disjoint (oddPellAtom (F:=F) i) (oddPellAtom (F:=F) j) := by
  cases i with
  | inl d =>
    cases j with
    | inl e =>
      exact oddPell_primitiveSector_disjoint true d e
        ((oddPell_atomLabels_left (F:=F) d).mp hi).2
        ((oddPell_atomLabels_left (F:=F) e).mp hj).2
        (fun h => hne (congrArg (Sum.inl : Nat -> Sum Nat Nat) h))
    | inr e => exact oddPell_primitiveSector_opposite_disjoint d e
  | inr d =>
    cases j with
    | inl e => exact (oddPell_primitiveSector_opposite_disjoint e d).symm
    | inr e =>
      exact oddPell_primitiveSector_disjoint false d e
        ((oddPell_atomLabels_right (F:=F) d).mp hi).2
        ((oddPell_atomLabels_right (F:=F) e).mp hj).2
        (fun h => hne (congrArg (Sum.inr : Nat -> Sum Nat Nat) h))

theorem oddPell_defect_degree_sectors (c : F) (k : Nat) (htwo : Not ((2 : F)=0)) :
    oddPellDefect 2 c k=
      (if Membership.mem (oddPellDegreeSector (F:=F) true (2*k+1)) c
        then oddPellSplitWeight (F:=F) else 0)+
      (if Membership.mem (oddPellDegreeSector (F:=F) false (2*k+1)) c
        then oddPellNonsplitWeight (F:=F) else 0) := by
  classical
  have hk : (2*k+1-1)/2=k := by omega
  change oddPellDefect 2 c k=
    (if Membership.mem (oddPellEndpointSector
      (fun x : F => IsSquare (x*(x+2))) ((2*k+1-1)/2)) c
      then oddPellSplitWeight (F:=F) else 0)+
    (if Membership.mem (oddPellEndpointSector
      (fun x : F => Not (IsSquare (x*(x+2)))) ((2*k+1-1)/2)) c
      then oddPellNonsplitWeight (F:=F) else 0)
  rw [hk]
  simp only [oddPellDefect,oddPellShiftMap,div_self htwo,one_mul]
  rw [oddPell_weight_loss_sectors c k htwo]
  unfold oddPellSplitWeight oddPellNonsplitWeight
  ring

private theorem oddPell_split_atom_avoids_nonsplit (d m : Nat) (c : F)
    (hc : Membership.mem (oddPellPrimitiveSector (F:=F) true d) c) :
    Not (Membership.mem (oddPellDegreeSector (F:=F) false m) c) := by
  classical
  intro hn
  have hp : Membership.mem
      (oddPellEndpointSector (fun x : F => IsSquare (x*(x+2))) ((d-1)/2)) c :=
    Finset.divisorKernelAtom_subset _ _ d hc
  change Membership.mem
    (oddPellEndpointSector (fun x : F => Not (IsSquare (x*(x+2)))) ((m-1)/2)) c at hn
  simp only [oddPellEndpointSector,Finset.mem_filter,Finset.mem_univ,true_and] at hp hn
  exact hn.2.2.1 hp.2.2.1

private theorem oddPell_nonsplit_atom_avoids_split (d m : Nat) (c : F)
    (hc : Membership.mem (oddPellPrimitiveSector (F:=F) false d) c) :
    Not (Membership.mem (oddPellDegreeSector (F:=F) true m) c) := by
  classical
  intro hp
  have hn : Membership.mem
      (oddPellEndpointSector (fun x : F => Not (IsSquare (x*(x+2)))) ((d-1)/2)) c :=
    Finset.divisorKernelAtom_subset _ _ d hc
  change Membership.mem
    (oddPellEndpointSector (fun x : F => IsSquare (x*(x+2))) ((m-1)/2)) c at hp
  simp only [oddPellEndpointSector,Finset.mem_filter,Finset.mem_univ,true_and] at hp hn
  exact hn.2.2.1 hp.2.2.1

theorem oddPell_defect_on_atom (i : Sum Nat Nat)
    (hi : Membership.mem (oddPellAtomLabels (F:=F)) i) (c : F)
    (hc : Membership.mem (oddPellAtom (F:=F) i) c) (k : Nat)
    (htwo : Not ((2 : F)=0)) :
    oddPellDefect 2 c k=
      if Dvd.dvd (oddPellAtomDegree i) (2*k+1)
        then oddPellAtomWeight (F:=F) i else 0 := by
  classical
  cases i with
  | inl d =>
    have hd := (oddPell_atomLabels_left (F:=F) d).mp hi
    have hown := oddPell_primitiveSector_mem_degree true d (2*k+1) hd.2
      (Exists.intro k rfl) htwo c hc
    have hopen := oddPell_split_atom_avoids_nonsplit d (2*k+1) c hc
    change oddPellDefect 2 c k=if Dvd.dvd d (2*k+1) then oddPellSplitWeight (F:=F) else 0
    rw [oddPell_defect_degree_sectors c k htwo]
    simp only [hopen,ite_false,add_zero,hown]
  | inr d =>
    have hd := (oddPell_atomLabels_right (F:=F) d).mp hi
    have hown := oddPell_primitiveSector_mem_degree false d (2*k+1) hd.2
      (Exists.intro k rfl) htwo c hc
    have hopen := oddPell_nonsplit_atom_avoids_split d (2*k+1) c hc
    change oddPellDefect 2 c k=if Dvd.dvd d (2*k+1) then oddPellNonsplitWeight (F:=F) else 0
    rw [oddPell_defect_degree_sectors c k htwo]
    simp only [hopen,ite_false,zero_add,hown]

theorem oddPell_probe_on_atom (S : Finset Nat) (a : Nat -> Real)
    (i : Sum Nat Nat) (hi : Membership.mem (oddPellAtomLabels (F:=F)) i)
    (c : F) (hc : Membership.mem (oddPellAtom (F:=F) i) c) (htwo : Not ((2 : F)=0)) :
    oddPellSignedProbe 2 S a c=
      oddPellAtomWeight (F:=F) i*
        ((S.filter (fun k => Dvd.dvd (oddPellAtomDegree i) (2*k+1))).sum a) := by
  classical
  calc
    _ = S.sum (fun k => if Dvd.dvd (oddPellAtomDegree i) (2*k+1)
        then oddPellAtomWeight (F:=F) i*a k else 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [oddPell_defect_on_atom i hi c hc k htwo]
      split_ifs <;> ring
    _ = (S.filter (fun k => Dvd.dvd (oddPellAtomDegree i) (2*k+1))).sum
        (fun k => oddPellAtomWeight (F:=F) i*a k) := by rw [Finset.sum_filter]
    _ = _ := by rw [Finset.mul_sum]


private theorem oddPell_primitive_one_empty (split : Bool) (htwo : Not ((2 : F)=0)) :
    oddPellPrimitiveSector (F:=F) split 1=(EmptyCollection.emptyCollection : Finset F) := by
  have hb := oddPell_degree_sector_card (F:=F) split 1 (Exists.intro 0 rfl) htwo
  have hb' : (oddPellDegreeSector (F:=F) split 1).card+1=1 := by simpa using hb
  have hs : (oddPellPrimitiveSector (F:=F) split 1).card<=
      (oddPellDegreeSector (F:=F) split 1).card :=
    Finset.card_le_card (Finset.divisorKernelAtom_subset _ _ 1)
  apply Finset.card_eq_zero.mp
  omega

theorem oddPell_exists_atom_of_sector (split : Bool) (m : Nat) (hm : Odd m)
    (hq : 5<=Fintype.card F) (htwo : Not ((2 : F)=0)) (c : F)
    (hc : Membership.mem (oddPellDegreeSector (F:=F) split m) c) :
    exists i, Membership.mem (oddPellAtomLabels (F:=F)) i /\
      Membership.mem (oddPellAtom (F:=F) i) c := by
  classical
  let N := oddPellSectorModulus (F:=F) split
  have hN0 : Not (N=0) := by
    cases split with
    | false => change Not (Fintype.card F+1=0); omega
    | true => change Not (Fintype.card F-1=0); omega
  rw [oddPell_degree_sector_eq_biUnion_atoms split m hm hq htwo] at hc
  cases Finset.mem_biUnion.mp hc with
  | intro d hd =>
    have hdr : Dvd.dvd d (N.gcd m) := (Nat.mem_divisors.mp hd.1).1
    have hdD : Membership.mem (oddPellSectorDivisors (F:=F) split) d := by
      apply Finset.mem_filter.mpr
      exact And.intro
        (Nat.mem_divisors.mpr
          (And.intro (Nat.dvd_trans hdr (Nat.gcd_dvd_left N m)) hN0))
        (Odd.of_dvd_nat hm (Nat.dvd_trans hdr (Nat.gcd_dvd_right N m)))
    have hd1 : Not (d=1) := by
      intro he
      have hc1 : Membership.mem (oddPellPrimitiveSector (F:=F) split 1) c := by
        simpa only [he] using hd.2
      rw [oddPell_primitive_one_empty split htwo] at hc1
      simp at hc1
    cases split with
    | false =>
      exact Exists.intro (Sum.inr d) (And.intro
        ((oddPell_atomLabels_right (F:=F) d).mpr (And.intro hd1 hdD)) hd.2)
    | true =>
      exact Exists.intro (Sum.inl d) (And.intro
        ((oddPell_atomLabels_left (F:=F) d).mpr (And.intro hd1 hdD)) hd.2)

theorem oddPell_defect_off_atoms (c : F) (k : Nat)
    (hq : 5<=Fintype.card F) (htwo : Not ((2 : F)=0))
    (hnone : forall i, Membership.mem (oddPellAtomLabels (F:=F)) i ->
      Not (Membership.mem (oddPellAtom (F:=F) i) c)) :
    oddPellDefect 2 c k=0 := by
  classical
  have hp : Not (Membership.mem (oddPellDegreeSector (F:=F) true (2*k+1)) c) := by
    intro hc
    cases oddPell_exists_atom_of_sector true (2*k+1) (Exists.intro k rfl)
        hq htwo c hc with
    | intro i hi => exact hnone i hi.1 hi.2
  have hn : Not (Membership.mem (oddPellDegreeSector (F:=F) false (2*k+1)) c) := by
    intro hc
    cases oddPell_exists_atom_of_sector false (2*k+1) (Exists.intro k rfl)
        hq htwo c hc with
    | intro i hi => exact hnone i hi.1 hi.2
  rw [oddPell_defect_degree_sectors c k htwo]
  simp only [hp,hn,ite_false,add_zero]

theorem oddPell_probe_off_atoms (S : Finset Nat) (a : Nat -> Real) (c : F)
    (hq : 5<=Fintype.card F) (htwo : Not ((2 : F)=0))
    (hnone : forall i, Membership.mem (oddPellAtomLabels (F:=F)) i ->
      Not (Membership.mem (oddPellAtom (F:=F) i) c)) :
    oddPellSignedProbe 2 S a c=0 := by
  unfold oddPellSignedProbe
  apply Finset.sum_eq_zero
  intro k hk
  rw [oddPell_defect_off_atoms c k hq htwo hnone,mul_zero]

theorem oddPell_probe_distribution_two (S : Finset Nat) (a : Nat -> Real)
    (f : Real -> Real) (hq : 5<=Fintype.card F) (htwo : Not ((2 : F)=0)) :
    (1/(Fintype.card F : Real))*
      (Finset.univ.sum fun c : F => f (oddPellSignedProbe 2 S a c))=
      f 0+(1/(Fintype.card F : Real))*
        (oddPellAtomLabels (F:=F)).sum (fun i =>
          ((oddPellAtomDegree i).totient : Real)*
            (f (oddPellAtomWeight (F:=F) i*
              ((S.filter (fun k => Dvd.dvd (oddPellAtomDegree i) (2*k+1))).sum a))-f 0)) := by
  classical
  let L := oddPellAtomLabels (F:=F)
  let v : Sum Nat Nat -> Real := fun i => oddPellAtomWeight (F:=F) i*
    ((S.filter (fun k => Dvd.dvd (oddPellAtomDegree i) (2*k+1))).sum a)
  have hpoint (c : F) :
      f (oddPellSignedProbe 2 S a c)=
        f 0+L.sum (fun i => if Membership.mem (oddPellAtom (F:=F) i) c
          then f (v i)-f 0 else 0) := by
    by_cases hex : exists i, Membership.mem L i /\
        Membership.mem (oddPellAtom (F:=F) i) c
    . cases hex with
      | intro i hi =>
        have hv : oddPellSignedProbe 2 S a c=v i :=
          oddPell_probe_on_atom S a i hi.1 c hi.2 htwo
        have hs : L.sum (fun j => if Membership.mem (oddPellAtom (F:=F) j) c
            then f (v j)-f 0 else 0)=f (v i)-f 0 := by
          calc
            _ = (if Membership.mem (oddPellAtom (F:=F) i) c
                then f (v i)-f 0 else 0) := by
              apply Finset.sum_eq_single i
              . intro j hj hji
                apply ite_eq_right
                intro hcj
                exact (Finset.disjoint_left.mp
                  (oddPell_atom_disjoint j i hj hi.1 hji)) hcj hi.2
              . intro hnot
                exact False.elim (hnot hi.1)
            _ = _ := ite_eq_left hi.2
        rw [hv,hs]
        ring
    . have hnone : forall i, Membership.mem L i ->
          Not (Membership.mem (oddPellAtom (F:=F) i) c) := by
        intro i hi hci
        exact hex (Exists.intro i (And.intro hi hci))
      have hz := oddPell_probe_off_atoms S a c hq htwo hnone
      have hs : L.sum (fun i => if Membership.mem (oddPellAtom (F:=F) i) c
          then f (v i)-f 0 else 0)=0 := by
        apply Finset.sum_eq_zero
        intro i hi
        exact ite_eq_right (hnone i hi)
      rw [hz,hs,add_zero]
  have htotal :
      (Finset.univ.sum fun c : F => f (oddPellSignedProbe 2 S a c))=
        (Fintype.card F : Real)*f 0+
          L.sum (fun i => ((oddPellAtomDegree i).totient : Real)*(f (v i)-f 0)) := by
    calc
      _ = Finset.univ.sum (fun c : F => f 0+
          L.sum (fun i => if Membership.mem (oddPellAtom (F:=F) i) c
            then f (v i)-f 0 else 0)) := Finset.sum_congr rfl (fun c _ => hpoint c)
      _ = (Finset.univ.sum fun _ : F => f 0)+
          L.sum (fun i => Finset.univ.sum (fun c : F =>
            if Membership.mem (oddPellAtom (F:=F) i) c then f (v i)-f 0 else 0)) := by
        rw [Finset.sum_add_distrib,Finset.sum_comm]
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_ite_mem]
        simp only [Finset.univ_inter,Finset.sum_const,nsmul_eq_mul,
          oddPell_atom_card i hi htwo]
  rw [htotal]
  have hq0 : Not (Fintype.card F=0) := by omega
  have hqR : Not ((Fintype.card F : Real)=0) := by exact_mod_cast hq0
  have hqq : (1/(Fintype.card F : Real))*(Fintype.card F : Real)=1 := by simp [hqR]
  calc
    _ = ((1/(Fintype.card F : Real))*(Fintype.card F : Real))*f 0+
        (1/(Fintype.card F : Real))*
          L.sum (fun i => ((oddPellAtomDegree i).totient : Real)*(f (v i)-f 0)) := by ring
    _ = _ := by rw [hqq,one_mul]

theorem oddPell_probe_normalize (h : F) (hh : Not (h=0))
    (S : Finset Nat) (a : Nat -> Real) (c : F) (htwo : Not ((2 : F)=0)) :
    oddPellSignedProbe h S a c=oddPellSignedProbe 2 S a ((2/h)*c) := by
  unfold oddPellSignedProbe
  apply Finset.sum_congr rfl
  intro k hk
  rw [oddPell_defect_normalize h c k hh htwo]

theorem oddPell_probe_distribution (h : F) (hh : Not (h=0))
    (S : Finset Nat) (a : Nat -> Real) (f : Real -> Real)
    (hq : 5<=Fintype.card F) (htwo : Not ((2 : F)=0)) :
    (1/(Fintype.card F : Real))*
      (Finset.univ.sum fun c : F => f (oddPellSignedProbe h S a c))=
      f 0+(1/(Fintype.card F : Real))*
        (oddPellAtomLabels (F:=F)).sum (fun i =>
          ((oddPellAtomDegree i).totient : Real)*
            (f (oddPellAtomWeight (F:=F) i*
              ((S.filter (fun k => Dvd.dvd (oddPellAtomDegree i) (2*k+1))).sum a))-f 0)) := by
  let e : Equiv F F :=
    { toFun := fun c => (2/h)*c
      invFun := fun c => (h/2)*c
      left_inv := by intro c; field_simp [hh,htwo]
      right_inv := by intro c; field_simp [hh,htwo] }
  have hs :
      (Finset.univ.sum fun c : F => f (oddPellSignedProbe h S a c))=
        (Finset.univ.sum fun c : F => f (oddPellSignedProbe 2 S a c)) := by
    calc
      _ = Finset.univ.sum (fun c : F => f (oddPellSignedProbe 2 S a (e c))) :=
        Finset.sum_congr rfl (fun c _ => congrArg f
          (oddPell_probe_normalize h hh S a c htwo))
      _ = _ := Equiv.sum_comp e (fun c : F => f (oddPellSignedProbe 2 S a c))
  rw [hs]
  exact oddPell_probe_distribution_two S a f hq htwo

end FiniteField
