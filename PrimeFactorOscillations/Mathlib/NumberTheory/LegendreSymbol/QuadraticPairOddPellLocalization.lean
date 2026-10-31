/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.LinearAlgebra.Span.Basic
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairOddPellDistribution

/-!
# Finite signed odd-Pell localization

The space below records actual finite signed probes. Primitive indicators are
isolated by finite triangular divisor inversion, with nonzero native weights.
-/

set_option autoImplicit false
set_option Elab.async false

namespace FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem oddPell_splitWeight_pos (hq : 5<=Fintype.card F) :
    0<oddPellSplitWeight (F:=F) := by
  have hs := quadraticChar_sq_one
    (neg_ne_zero.mpr (one_ne_zero : Not ((1 : F)=0)))
  have hlo : -1<=(quadraticChar F) (-1) := by nlinarith only [hs]
  have hqr : (5 : Real)<=(Fintype.card F : Real) := by exact_mod_cast hq
  have hlr : (-1 : Real)<=((quadraticChar F) (-1) : Real) := by exact_mod_cast hlo
  unfold oddPellSplitWeight
  exact div_pos (by linarith) (by linarith)

theorem oddPell_nonsplitWeight_pos (hq : 5<=Fintype.card F) :
    0<oddPellNonsplitWeight (F:=F) := by
  have hs := quadraticChar_sq_one
    (neg_ne_zero.mpr (one_ne_zero : Not ((1 : F)=0)))
  have hhi : (quadraticChar F) (-1)<=1 := by nlinarith only [hs]
  have hqr : (5 : Real)<=(Fintype.card F : Real) := by exact_mod_cast hq
  have hhr : ((quadraticChar F) (-1) : Real)<=(1 : Real) := by exact_mod_cast hhi
  unfold oddPellNonsplitWeight
  exact div_pos (by linarith) (by linarith)

theorem oddPell_atomWeight_pos (i : Sum Nat Nat) (hq : 5<=Fintype.card F) :
    0<oddPellAtomWeight (F:=F) i := by
  cases i with
  | inl d => exact oddPell_splitWeight_pos hq
  | inr d => exact oddPell_nonsplitWeight_pos hq

omit [Field F] [DecidableEq F] in
theorem oddPell_atomDegree_pos (i : Sum Nat Nat)
    (hi : Membership.mem (oddPellAtomLabels (F:=F)) i) :
    0<oddPellAtomDegree i := by
  cases i with
  | inl d =>
    exact oddPell_sectorDivisors_pos true ((oddPell_atomLabels_left d).mp hi).2
  | inr d =>
    exact oddPell_sectorDivisors_pos false ((oddPell_atomLabels_right d).mp hi).2

omit [Field F] [DecidableEq F] in
theorem oddPell_atomDegree_odd (i : Sum Nat Nat)
    (hi : Membership.mem (oddPellAtomLabels (F:=F)) i) :
    Odd (oddPellAtomDegree i) := by
  cases i with
  | inl d => exact (Finset.mem_filter.mp ((oddPell_atomLabels_left d).mp hi).2).2
  | inr d => exact (Finset.mem_filter.mp ((oddPell_atomLabels_right d).mp hi).2).2

omit [Field F] [DecidableEq F] in
private theorem oddPell_opposite_degree_ne (d e : Nat)
    (hd : Membership.mem (oddPellAtomLabels (F:=F)) (Sum.inl d))
    (he : Membership.mem (oddPellAtomLabels (F:=F)) (Sum.inr e))
    (hq : 5<=Fintype.card F) : Not (d=e) := by
  intro hde
  subst e
  have hdm := (oddPell_atomLabels_left (F:=F) d).mp hd
  have hdp := (oddPell_atomLabels_right (F:=F) d).mp he
  have hminus : Dvd.dvd d (Fintype.card F-1) :=
    (Nat.mem_divisors.mp (Finset.mem_filter.mp hdm.2).1).1
  have hplus : Dvd.dvd d (Fintype.card F+1) :=
    (Nat.mem_divisors.mp (Finset.mem_filter.mp hdp.2).1).1
  have hdifference : Dvd.dvd d ((Fintype.card F+1)-(Fintype.card F-1)) :=
    Nat.dvd_sub hplus hminus
  have htwo : Dvd.dvd d 2 := by
    have heq : (Fintype.card F+1)-(Fintype.card F-1)=2 := by omega
    simpa only [heq] using hdifference
  have hle : d<=2 := Nat.le_of_dvd (by decide) htwo
  have hpos : 0<d := oddPell_atomDegree_pos (Sum.inl d) hd
  have hodd : Odd d := oddPell_atomDegree_odd (Sum.inl d) hd
  choose k hk using hodd
  exact hdm.1 (by omega)

omit [Field F] [DecidableEq F] in
theorem oddPell_atomDegree_injective (i j : Sum Nat Nat)
    (hi : Membership.mem (oddPellAtomLabels (F:=F)) i)
    (hj : Membership.mem (oddPellAtomLabels (F:=F)) j)
    (hq : 5<=Fintype.card F)
    (heq : oddPellAtomDegree i=oddPellAtomDegree j) : i=j := by
  cases i with
  | inl d =>
    cases j with
    | inl e =>
      change d=e at heq
      subst e
      rfl
    | inr e => exact False.elim (oddPell_opposite_degree_ne d e hi hj hq heq)
  | inr d =>
    cases j with
    | inl e => exact False.elim (oddPell_opposite_degree_ne e d hj hi hq heq.symm)
    | inr e =>
      change d=e at heq
      subst e
      rfl

noncomputable def oddPellAtomIndicator (h : F) (i : Sum Nat Nat) : F -> Real :=
  fun c => if Membership.mem (oddPellAtom (F:=F) i) ((2/h)*c) then 1 else 0

theorem oddPell_probe_add (h : F) (S T : Finset Nat) (a b : Nat -> Real) (c : F) :
    oddPellSignedProbe h (Union.union S T)
      (fun k => (if Membership.mem S k then a k else 0)+
        (if Membership.mem T k then b k else 0)) c=
      oddPellSignedProbe h S a c+oddPellSignedProbe h T b c := by
  classical
  have hS : Inter.inter (Union.union S T) S=S := by ext k; simp
  have hT : Inter.inter (Union.union S T) T=T := by ext k; simp
  unfold oddPellSignedProbe
  simp only [add_mul,Finset.sum_add_distrib,ite_mul,zero_mul]
  rw [Finset.sum_ite_mem,Finset.sum_ite_mem,hS,hT]

noncomputable def oddPellProbeSpace (h : F) : Submodule Real (F -> Real) := by
  classical
  exact
    { carrier := fun f => exists S : Finset Nat, exists a : Nat -> Real,
        forall c, oddPellSignedProbe h S a c=f c
      zero_mem' := by
        apply Exists.intro (EmptyCollection.emptyCollection : Finset Nat)
        apply Exists.intro (fun _ => 0)
        intro c
        simp [oddPellSignedProbe]
      add_mem' := by
        intro f g hf hg
        choose S a hf using hf
        choose T b hg using hg
        apply Exists.intro (Union.union S T)
        apply Exists.intro (fun k => (if Membership.mem S k then a k else 0)+
          (if Membership.mem T k then b k else 0))
        intro c
        change oddPellSignedProbe h (Union.union S T) _ c=f c+g c
        rw [oddPell_probe_add,hf c,hg c]
      smul_mem' := by
        intro r f hf
        choose S a hf using hf
        apply Exists.intro S
        apply Exists.intro (fun k => r*a k)
        intro c
        change oddPellSignedProbe h S (fun k => r*a k) c=r*f c
        calc
          _ = r*oddPellSignedProbe h S a c := by
            unfold oddPellSignedProbe
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k hk
            ring
          _ = _ := by rw [hf c] }

theorem oddPell_mem_probeSpace (h : F) (f : F -> Real) :
    Membership.mem (oddPellProbeSpace h) f <->
      exists S : Finset Nat, exists a : Nat -> Real,
        forall c, oddPellSignedProbe h S a c=f c := Iff.rfl

theorem oddPell_defect_mem_probeSpace (h : F) (k : Nat) :
    Membership.mem (oddPellProbeSpace h) (fun c => oddPellDefect h c k) := by
  apply Exists.intro (Singleton.singleton k : Finset Nat)
  apply Exists.intro (fun _ => 1)
  intro c
  simp [oddPellSignedProbe]


theorem oddPell_probe_atom_expansion (h : F) (hh : Not (h=0))
    (S : Finset Nat) (a : Nat -> Real)
    (hq : 5<=Fintype.card F) (htwo : Not ((2 : F)=0)) :
    (fun c => oddPellSignedProbe h S a c)=
      (oddPellAtomLabels (F:=F)).sum (fun i =>
        HSMul.hSMul (oddPellAtomWeight (F:=F) i*
          ((S.filter (fun k => Dvd.dvd (oddPellAtomDegree i) (2*k+1))).sum a))
          (oddPellAtomIndicator h i)) := by
  classical
  funext c
  rw [Finset.sum_apply]
  change oddPellSignedProbe h S a c=
    (oddPellAtomLabels (F:=F)).sum (fun i =>
      (oddPellAtomWeight (F:=F) i*
        ((S.filter (fun k => Dvd.dvd (oddPellAtomDegree i) (2*k+1))).sum a)) *
        oddPellAtomIndicator h i c)
  by_cases hex : exists i, Membership.mem (oddPellAtomLabels (F:=F)) i /\
      Membership.mem (oddPellAtom (F:=F) i) ((2/h)*c)
  . choose i hi using hex
    have hc := hi.2
    have hi := hi.1
    have hv : oddPellSignedProbe h S a c=
        oddPellAtomWeight (F:=F) i*
          ((S.filter (fun k => Dvd.dvd (oddPellAtomDegree i) (2*k+1))).sum a) := by
      rw [oddPell_probe_normalize h hh S a c htwo]
      exact oddPell_probe_on_atom S a i hi ((2/h)*c) hc htwo
    have hs :
        (oddPellAtomLabels (F:=F)).sum (fun j =>
          (oddPellAtomWeight (F:=F) j*
            ((S.filter (fun k => Dvd.dvd (oddPellAtomDegree j) (2*k+1))).sum a)) *
              oddPellAtomIndicator h j c)=
          (oddPellAtomWeight (F:=F) i*
            ((S.filter (fun k => Dvd.dvd (oddPellAtomDegree i) (2*k+1))).sum a)) *
              oddPellAtomIndicator h i c := by
      apply Finset.sum_eq_single i
      . intro j hj hji
        have hn : Not (Membership.mem (oddPellAtom (F:=F) j) ((2/h)*c)) := by
          intro hcj
          exact (Finset.disjoint_left.mp (oddPell_atom_disjoint j i hj hi hji)) hcj hc
        simp only [oddPellAtomIndicator,ite_eq_right hn,mul_zero]
      . intro hn
        exact False.elim (hn hi)
    rw [hs,hv]
    simp only [oddPellAtomIndicator,ite_eq_left hc,mul_one]
  . have hn : forall i, Membership.mem (oddPellAtomLabels (F:=F)) i ->
        Not (Membership.mem (oddPellAtom (F:=F) i) ((2/h)*c)) := by
      intro i hi hc
      exact hex (Exists.intro i (And.intro hi hc))
    rw [oddPell_probe_normalize h hh S a c htwo,
      oddPell_probe_off_atoms S a ((2/h)*c) hq htwo hn]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    simp only [oddPellAtomIndicator,ite_eq_right (hn i hi),mul_zero]

theorem oddPell_defect_atom_expansion (h : F) (hh : Not (h=0))
    (k : Nat) (hq : 5<=Fintype.card F) (htwo : Not ((2 : F)=0)) :
    (fun c => oddPellDefect h c k)=
      (oddPellAtomLabels (F:=F)).sum (fun i =>
        HSMul.hSMul (if Dvd.dvd (oddPellAtomDegree i) (2*k+1)
          then oddPellAtomWeight (F:=F) i else 0) (oddPellAtomIndicator h i)) := by
  classical
  have he := oddPell_probe_atom_expansion h hh (Singleton.singleton k : Finset Nat)
    (fun _ => 1) hq htwo
  simpa only [oddPellSignedProbe,Finset.sum_singleton,one_mul,Finset.sum_filter,
    mul_ite,mul_one,mul_zero] using he

theorem oddPell_atomIndicator_mem_probeSpace (h : F) (hh : Not (h=0))
    (i : Sum Nat Nat) (hi : Membership.mem (oddPellAtomLabels (F:=F)) i)
    (hq : 5<=Fintype.card F) (htwo : Not ((2 : F)=0)) :
    Membership.mem (oddPellProbeSpace h) (oddPellAtomIndicator h i) := by
  classical
  have main : forall d : Nat, forall i : Sum Nat Nat,
      Membership.mem (oddPellAtomLabels (F:=F)) i ->
      oddPellAtomDegree i=d ->
      Membership.mem (oddPellProbeSpace h) (oddPellAtomIndicator h i) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro i hi hdi
      let k := (d-1)/2
      have hdpos : 0<d := by simpa only [hdi] using oddPell_atomDegree_pos i hi
      have hdodd : Odd d := by simpa only [hdi] using oddPell_atomDegree_odd i hi
      have hmk : 2*k+1=d := by
        choose t ht using hdodd
        dsimp [k]
        omega
      let term : Sum Nat Nat -> F -> Real := fun j =>
        HSMul.hSMul (if Dvd.dvd (oddPellAtomDegree j) d
          then oddPellAtomWeight (F:=F) j else 0) (oddPellAtomIndicator h j)
      let R := ((oddPellAtomLabels (F:=F)).erase i).sum term
      have hR : Membership.mem (oddPellProbeSpace h) R := by
        apply (oddPellProbeSpace h).sum_mem
        intro j hj
        have hjL := (Finset.mem_erase.mp hj).2
        have hji := (Finset.mem_erase.mp hj).1
        by_cases hdvd : Dvd.dvd (oddPellAtomDegree j) d
        . have hle : oddPellAtomDegree j<=d := Nat.le_of_dvd hdpos hdvd
          have hne : Not (oddPellAtomDegree j=d) := by
            intro heq
            exact hji (oddPell_atomDegree_injective j i hjL hi hq (heq.trans hdi.symm))
          have hlt : oddPellAtomDegree j<d := by omega
          have hjmem := ih (oddPellAtomDegree j) hlt j hjL rfl
          simpa only [term,ite_eq_left hdvd] using
            (oddPellProbeSpace h).smul_mem (oddPellAtomWeight (F:=F) j) hjmem
        . change Membership.mem (oddPellProbeSpace h)
            (HSMul.hSMul (if Dvd.dvd (oddPellAtomDegree j) d
              then oddPellAtomWeight (F:=F) j else 0) (oddPellAtomIndicator h j))
          simp only [ite_eq_right hdvd,zero_smul]
          exact (oddPellProbeSpace h).zero_mem
      have hself : term i=HSMul.hSMul (oddPellAtomWeight (F:=F) i) (oddPellAtomIndicator h i) := by
        dsimp [term]
        rw [hdi]
        simp only [dvd_refl,ite_true]
      have hdec : (fun c => oddPellDefect h c k)=
          R+HSMul.hSMul (oddPellAtomWeight (F:=F) i) (oddPellAtomIndicator h i) := by
        calc
          _ = (oddPellAtomLabels (F:=F)).sum term := by
            have he := oddPell_defect_atom_expansion h hh k hq htwo
            rw [hmk] at he
            exact he
          _ = R+term i :=
            (Finset.sum_erase_add (oddPellAtomLabels (F:=F)) term hi).symm
          _ = _ := by rw [hself]
      have hm : Membership.mem (oddPellProbeSpace h)
          (HSMul.hSMul (oddPellAtomWeight (F:=F) i) (oddPellAtomIndicator h i)) := by
        have heq : HSMul.hSMul (oddPellAtomWeight (F:=F) i) (oddPellAtomIndicator h i)=
            (fun c => oddPellDefect h c k)-R := by rw [hdec]; simp
        rw [heq]
        exact (oddPellProbeSpace h).sub_mem (oddPell_defect_mem_probeSpace h k) hR
      have hw : Not (oddPellAtomWeight (F:=F) i=0) :=
        ne_of_gt (oddPell_atomWeight_pos i hq)
      have hcancel : (1/oddPellAtomWeight (F:=F) i)*oddPellAtomWeight (F:=F) i=1 := by
        simp [hw]
      have ht := (oddPellProbeSpace h).smul_mem (1/oddPellAtomWeight (F:=F) i) hm
      simpa only [smul_smul,hcancel,one_smul] using ht
  exact main (oddPellAtomDegree i) i hi rfl

theorem oddPell_probeSpace_iff_atom_expansion (h : F) (hh : Not (h=0))
    (f : F -> Real) (hq : 5<=Fintype.card F) (htwo : Not ((2 : F)=0)) :
    Membership.mem (oddPellProbeSpace h) f <->
      exists b : Sum Nat Nat -> Real,
        f=(oddPellAtomLabels (F:=F)).sum (fun i => HSMul.hSMul (b i) (oddPellAtomIndicator h i)) := by
  constructor
  . intro hf
    choose S a hf using (oddPell_mem_probeSpace h f).mp hf
    apply Exists.intro (fun i => oddPellAtomWeight (F:=F) i*
      ((S.filter (fun k => Dvd.dvd (oddPellAtomDegree i) (2*k+1))).sum a))
    calc
      f = (fun c => oddPellSignedProbe h S a c) := by funext c; exact (hf c).symm
      _ = _ := oddPell_probe_atom_expansion h hh S a hq htwo
  . intro hb
    choose b hb using hb
    rw [hb]
    apply (oddPellProbeSpace h).sum_mem
    intro i hi
    exact (oddPellProbeSpace h).smul_mem (b i)
      (oddPell_atomIndicator_mem_probeSpace h hh i hi hq htwo)

end FiniteField
