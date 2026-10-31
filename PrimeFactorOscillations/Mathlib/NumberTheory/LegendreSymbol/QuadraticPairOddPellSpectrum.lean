/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairOddPellLocalization

/-!
# The exact finite signed odd-Pell support spectrum

Supports are exactly unions of disjoint primitive classes, and their attainable
cardinalities are exactly the corresponding totient subset sums.
-/

set_option autoImplicit false
set_option Elab.async false

namespace FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def oddPellShiftAtom (h : F) (i : Sum Nat Nat) : Finset F :=
  (oddPellAtom (F:=F) i).image (fun c => (h/2)*c)

noncomputable def oddPellFunctionSupport (f : F -> Real) : Finset F := by
  classical
  exact Finset.univ.filter (fun c => Not (f c=0))

theorem oddPell_mem_shiftAtom (h : F) (hh : Not (h=0)) (i : Sum Nat Nat)
    (c : F) (htwo : Not ((2 : F)=0)) :
    Membership.mem (oddPellShiftAtom h i) c <->
      Membership.mem (oddPellAtom (F:=F) i) ((2/h)*c) := by
  constructor
  . intro hc
    choose x hx using Finset.mem_image.mp hc
    have heq : (2/h)*c=x := by rw [hx.2.symm]; field_simp [hh,htwo]
    rw [heq]
    exact hx.1
  . intro hc
    apply Finset.mem_image.mpr
    apply Exists.intro ((2/h)*c)
    apply And.intro hc
    field_simp [hh,htwo]

theorem oddPell_shiftAtom_card (h : F) (hh : Not (h=0)) (i : Sum Nat Nat)
    (hi : Membership.mem (oddPellAtomLabels (F:=F)) i) (htwo : Not ((2 : F)=0)) :
    (oddPellShiftAtom h i).card=(oddPellAtomDegree i).totient := by
  have hinj : Function.Injective (fun c : F => (h/2)*c) := by
    intro x y heq
    have he := congrArg (fun z : F => (2/h)*z) heq
    have hp (z : F) : (2/h)*((h/2)*z)=z := by field_simp [hh,htwo]
    simpa only [hp] using he
  rw [oddPellShiftAtom,Finset.card_image_of_injective _ hinj]
  exact oddPell_atom_card i hi htwo

theorem oddPell_shiftAtom_disjoint (h : F) (hh : Not (h=0))
    (i j : Sum Nat Nat) (hi : Membership.mem (oddPellAtomLabels (F:=F)) i)
    (hj : Membership.mem (oddPellAtomLabels (F:=F)) j) (hij : Not (i=j))
    (htwo : Not ((2 : F)=0)) :
    Disjoint (oddPellShiftAtom h i) (oddPellShiftAtom h j) := by
  apply Finset.disjoint_left.mpr
  intro c hc hd
  exact (Finset.disjoint_left.mp (oddPell_atom_disjoint i j hi hj hij))
    ((oddPell_mem_shiftAtom h hh i c htwo).mp hc)
    ((oddPell_mem_shiftAtom h hh j c htwo).mp hd)

omit [Field F] [DecidableEq F] in
theorem oddPell_mem_functionSupport (f : F -> Real) (c : F) :
    Membership.mem (oddPellFunctionSupport f) c <-> Not (f c=0) := by
  classical
  simp only [oddPellFunctionSupport,Finset.mem_filter,Finset.mem_univ,true_and]

theorem oddPell_atomIndicator_eq_shiftAtom (h : F) (hh : Not (h=0))
    (i : Sum Nat Nat) (c : F) (htwo : Not ((2 : F)=0)) :
    oddPellAtomIndicator h i c=
      if Membership.mem (oddPellShiftAtom h i) c then 1 else 0 := by
  simp only [oddPellAtomIndicator,oddPell_mem_shiftAtom h hh i c htwo]

theorem oddPell_atom_sum_on_shiftAtom (h : F) (hh : Not (h=0))
    (b : Sum Nat Nat -> Real) (i : Sum Nat Nat)
    (hi : Membership.mem (oddPellAtomLabels (F:=F)) i) (c : F)
    (hc : Membership.mem (oddPellShiftAtom h i) c) (htwo : Not ((2 : F)=0)) :
    ((oddPellAtomLabels (F:=F)).sum
      (fun j => HSMul.hSMul (b j) (oddPellAtomIndicator h j))) c=b i := by
  classical
  rw [Finset.sum_apply]
  change (oddPellAtomLabels (F:=F)).sum (fun j => b j*oddPellAtomIndicator h j c)=b i
  calc
    _ = b i*oddPellAtomIndicator h i c := by
      apply Finset.sum_eq_single i
      . intro j hj hji
        have hn : Not (Membership.mem (oddPellShiftAtom h j) c) := by
          intro hd
          exact (Finset.disjoint_left.mp
            (oddPell_shiftAtom_disjoint h hh j i hj hi hji htwo)) hd hc
        rw [oddPell_atomIndicator_eq_shiftAtom h hh j c htwo,ite_eq_right hn,mul_zero]
      . intro hn
        exact False.elim (hn hi)
    _ = _ := by
      rw [oddPell_atomIndicator_eq_shiftAtom h hh i c htwo,ite_eq_left hc,mul_one]

theorem oddPell_atom_sum_support (h : F) (hh : Not (h=0))
    (b : Sum Nat Nat -> Real) (htwo : Not ((2 : F)=0)) :
    oddPellFunctionSupport ((oddPellAtomLabels (F:=F)).sum
      (fun i => HSMul.hSMul (b i) (oddPellAtomIndicator h i)))=
      ((oddPellAtomLabels (F:=F)).filter (fun i => Not (b i=0))).biUnion
        (oddPellShiftAtom h) := by
  classical
  apply Finset.ext
  intro c
  rw [oddPell_mem_functionSupport,Finset.mem_biUnion]
  constructor
  . intro hc
    by_contra hn
    have hz : ((oddPellAtomLabels (F:=F)).sum
        (fun i => HSMul.hSMul (b i) (oddPellAtomIndicator h i))) c=0 := by
      rw [Finset.sum_apply]
      apply Finset.sum_eq_zero
      intro i hi
      change b i*oddPellAtomIndicator h i c=0
      by_cases hb : b i=0
      . rw [hb,zero_mul]
      . have hm : Not (Membership.mem (oddPellShiftAtom h i) c) := by
          intro hci
          exact hn (Exists.intro i
            (And.intro (Finset.mem_filter.mpr (And.intro hi hb)) hci))
        rw [oddPell_atomIndicator_eq_shiftAtom h hh i c htwo,ite_eq_right hm,mul_zero]
    exact hc hz
  . intro hc
    choose i hi using hc
    have hlabel := (Finset.mem_filter.mp hi.1).1
    have hnonzero := (Finset.mem_filter.mp hi.1).2
    rw [oddPell_atom_sum_on_shiftAtom h hh b i hlabel c hi.2 htwo]
    exact hnonzero

theorem oddPell_shiftAtom_union_card (h : F) (hh : Not (h=0))
    (T : Finset (Sum Nat Nat))
    (hT : forall i, Membership.mem T i -> Membership.mem (oddPellAtomLabels (F:=F)) i)
    (htwo : Not ((2 : F)=0)) :
    (T.biUnion (oddPellShiftAtom h)).card=
      T.sum (fun i => (oddPellAtomDegree i).totient) := by
  classical
  have hd : (T : Set (Sum Nat Nat)).PairwiseDisjoint (oddPellShiftAtom h) := by
    intro i hi j hj hij
    exact oddPell_shiftAtom_disjoint h hh i j (hT i hi) (hT j hj) hij htwo
  rw [Finset.card_biUnion hd]
  apply Finset.sum_congr rfl
  intro i hi
  exact oddPell_shiftAtom_card h hh i (hT i hi) htwo

theorem oddPell_probe_support_iff_union (h : F) (hh : Not (h=0))
    (A : Finset F) (hq : 5<=Fintype.card F) (htwo : Not ((2 : F)=0)) :
    (exists f : F -> Real, Membership.mem (oddPellProbeSpace h) f /\
      oddPellFunctionSupport f=A) <->
    exists T : Finset (Sum Nat Nat),
      (forall i, Membership.mem T i -> Membership.mem (oddPellAtomLabels (F:=F)) i) /\
      A=T.biUnion (oddPellShiftAtom h) := by
  classical
  constructor
  . intro hf
    choose f hf using hf
    choose b hb using (oddPell_probeSpace_iff_atom_expansion h hh f hq htwo).mp hf.1
    let T := (oddPellAtomLabels (F:=F)).filter (fun i => Not (b i=0))
    apply Exists.intro T
    apply And.intro
    . intro i hi
      exact (Finset.mem_filter.mp hi).1
    . calc
        A = oddPellFunctionSupport f := hf.2.symm
        _ = _ := by rw [hb]; exact oddPell_atom_sum_support h hh b htwo
  . intro hT
    choose T hT using hT
    let b : Sum Nat Nat -> Real := fun i => if Membership.mem T i then 1 else 0
    let f := (oddPellAtomLabels (F:=F)).sum
      (fun i => HSMul.hSMul (b i) (oddPellAtomIndicator h i))
    have hf : Membership.mem (oddPellProbeSpace h) f :=
      (oddPell_probeSpace_iff_atom_expansion h hh f hq htwo).mpr (Exists.intro b rfl)
    have hfilter : (oddPellAtomLabels (F:=F)).filter (fun i => Not (b i=0))=T := by
      apply Finset.ext
      intro i
      rw [Finset.mem_filter]
      constructor
      . intro hi
        by_contra hn
        have hz : b i=0 := by simp only [b,ite_eq_right hn]
        exact hi.2 hz
      . intro hi
        apply And.intro (hT.1 i hi)
        simpa only [b,ite_eq_left hi] using (one_ne_zero : Not ((1 : Real)=0))
    apply Exists.intro f
    apply And.intro hf
    change oddPellFunctionSupport
      ((oddPellAtomLabels (F:=F)).sum
        (fun i => HSMul.hSMul (b i) (oddPellAtomIndicator h i)))=A
    rw [oddPell_atom_sum_support h hh b htwo,hfilter]
    exact hT.2.symm

theorem oddPell_support_card_spectrum (h : F) (hh : Not (h=0))
    (n : Nat) (hq : 5<=Fintype.card F) (htwo : Not ((2 : F)=0)) :
    (exists f : F -> Real, Membership.mem (oddPellProbeSpace h) f /\
      (oddPellFunctionSupport f).card=n) <->
    exists T : Finset (Sum Nat Nat),
      (forall i, Membership.mem T i -> Membership.mem (oddPellAtomLabels (F:=F)) i) /\
      T.sum (fun i => (oddPellAtomDegree i).totient)=n := by
  constructor
  . intro hf
    choose f hf using hf
    have hs := (oddPell_probe_support_iff_union h hh (oddPellFunctionSupport f) hq htwo).mp
      (Exists.intro f (And.intro hf.1 rfl))
    choose T hT using hs
    apply Exists.intro T
    apply And.intro hT.1
    calc
      _ = (T.biUnion (oddPellShiftAtom h)).card :=
        (oddPell_shiftAtom_union_card h hh T hT.1 htwo).symm
      _ = (oddPellFunctionSupport f).card := congrArg Finset.card hT.2.symm
      _ = n := hf.2
  . intro hT
    choose T hT using hT
    have hs := (oddPell_probe_support_iff_union h hh
      (T.biUnion (oddPellShiftAtom h)) hq htwo).mpr (Exists.intro T (And.intro hT.1 rfl))
    choose f hf using hs
    apply Exists.intro f
    apply And.intro hf.1
    rw [hf.2,oddPell_shiftAtom_union_card h hh T hT.1 htwo]
    exact hT.2


omit [Field F] [DecidableEq F] in
private theorem oddPell_label_of_divisor (split : Bool) (d : Nat)
    (hd : 1<d) (ho : Odd d) (hv : Dvd.dvd d (oddPellSectorModulus (F:=F) split))
    (hN : Not (oddPellSectorModulus (F:=F) split=0)) :
    exists i, Membership.mem (oddPellAtomLabels (F:=F)) i /\ oddPellAtomDegree i=d := by
  have hm : Membership.mem (oddPellSectorDivisors (F:=F) split) d :=
    Finset.mem_filter.mpr (And.intro (Nat.mem_divisors.mpr (And.intro hv hN)) ho)
  have hn : Not (d=1) := by omega
  cases split with
  | false =>
    exact Exists.intro (Sum.inr d)
      (And.intro ((oddPell_atomLabels_right d).mpr (And.intro hn hm)) rfl)
  | true =>
    exact Exists.intro (Sum.inl d)
      (And.intro ((oddPell_atomLabels_left d).mpr (And.intro hn hm)) rfl)

omit [Field F] [DecidableEq F] in
theorem oddPell_atomLabels_nonempty (hq : 5<=Fintype.card F) :
    (oddPellAtomLabels (F:=F)).Nonempty := by
  let q := Fintype.card F
  have hq' : 5<=q := hq
  by_cases heven : q%2=0
  . have ho : Odd (q-1) := Exists.intro (q/2-1) (by omega)
    have hl := oddPell_label_of_divisor (F:=F) true (q-1) (by omega) ho
      (dvd_refl _) (by change Not (q-1=0); omega)
    choose i hi using hl
    exact Exists.intro i hi.1
  . by_cases hmod : q%4=1
    . have ho : Odd ((q+1)/2) := Exists.intro (q/4) (by omega)
      have hv : Dvd.dvd ((q+1)/2) (q+1) := Exists.intro 2 (by omega)
      have hl := oddPell_label_of_divisor (F:=F) false ((q+1)/2)
        (by omega) ho hv (by change Not (q+1=0); omega)
      choose i hi using hl
      exact Exists.intro i hi.1
    . have hmod3 : q%4=3 := by omega
      have ho : Odd ((q-1)/2) := Exists.intro (q/4) (by omega)
      have hv : Dvd.dvd ((q-1)/2) (q-1) := Exists.intro 2 (by omega)
      have hl := oddPell_label_of_divisor (F:=F) true ((q-1)/2)
        (by omega) ho hv (by change Not (q-1=0); omega)
      choose i hi using hl
      exact Exists.intro i hi.1

noncomputable def oddPellMinSupport : Nat :=
  WithTop.untopD 0
    (((oddPellAtomLabels (F:=F)).image (fun i => (oddPellAtomDegree i).totient)).min)

omit [Field F] [DecidableEq F] in
theorem oddPell_minSupport_spec (hq : 5<=Fintype.card F) :
    (exists i, Membership.mem (oddPellAtomLabels (F:=F)) i /\
      (oddPellAtomDegree i).totient=oddPellMinSupport (F:=F)) /\
    (forall i, Membership.mem (oddPellAtomLabels (F:=F)) i ->
      oddPellMinSupport (F:=F)<=(oddPellAtomDegree i).totient) := by
  classical
  let C := (oddPellAtomLabels (F:=F)).image (fun i => (oddPellAtomDegree i).totient)
  choose i hi using oddPell_atomLabels_nonempty (F:=F) hq
  have hC : C.Nonempty := Exists.intro ((oddPellAtomDegree i).totient)
    (Finset.mem_image.mpr (Exists.intro i (And.intro hi rfl)))
  have heq : oddPellMinSupport (F:=F)=C.min' hC := by
    change WithTop.untopD 0 C.min=C.min' hC
    rw [(Finset.coe_min' hC).symm,WithTop.untopD_coe]
  apply And.intro
  . choose j hj using Finset.mem_image.mp (Finset.min'_mem C hC)
    exact Exists.intro j (And.intro hj.1 (hj.2.trans heq.symm))
  . intro j hj
    rw [heq]
    exact Finset.min'_le C ((oddPellAtomDegree j).totient)
      (Finset.mem_image.mpr (Exists.intro j (And.intro hj rfl)))

omit [Field F] [DecidableEq F] in
theorem oddPell_atom_totient_two_le (i : Sum Nat Nat)
    (hi : Membership.mem (oddPellAtomLabels (F:=F)) i) :
    2<=(oddPellAtomDegree i).totient := by
  have hp := oddPell_atomDegree_pos i hi
  have ho := oddPell_atomDegree_odd i hi
  have hn : Not (oddPellAtomDegree i=1) := by
    cases i with
    | inl d => exact ((oddPell_atomLabels_left d).mp hi).1
    | inr d => exact ((oddPell_atomLabels_right d).mp hi).1
  have hgt : 2<oddPellAtomDegree i := by
    choose k hk using ho
    omega
  have hpositive := Nat.totient_pos.mpr hp
  choose k hk using Nat.totient_even hgt
  omega

omit [Field F] [DecidableEq F] in
theorem oddPell_minSupport_two_le (hq : 5<=Fintype.card F) :
    2<=oddPellMinSupport (F:=F) := by
  choose i hi using (oddPell_minSupport_spec (F:=F) hq).1
  rw [hi.2.symm]
  exact oddPell_atom_totient_two_le i hi.1

omit [Field F] [DecidableEq F] in
theorem oddPell_functionSupport_nonempty_iff (f : F -> Real) :
    (oddPellFunctionSupport f).Nonempty <-> Not (f=0) := by
  classical
  constructor
  . intro hc
    choose c hc using hc
    intro hz
    exact ((oddPell_mem_functionSupport f c).mp hc) (congrFun hz c)
  . intro hf
    by_contra hn
    apply hf
    funext c
    by_contra hc
    exact hn (Exists.intro c ((oddPell_mem_functionSupport f c).mpr hc))

theorem oddPell_sharp_support_minimum (h : F) (hh : Not (h=0))
    (hq : 5<=Fintype.card F) (htwo : Not ((2 : F)=0)) :
    (forall f : F -> Real, Membership.mem (oddPellProbeSpace h) f -> Not (f=0) ->
      oddPellMinSupport (F:=F)<=(oddPellFunctionSupport f).card) /\
    (exists f : F -> Real, Membership.mem (oddPellProbeSpace h) f /\ Not (f=0) /\
      (oddPellFunctionSupport f).card=oddPellMinSupport (F:=F)) := by
  classical
  apply And.intro
  . intro f hf hn
    have hp : 0<(oddPellFunctionSupport f).card :=
      Finset.card_pos.mpr ((oddPell_functionSupport_nonempty_iff f).mpr hn)
    have hs := (oddPell_support_card_spectrum h hh (oddPellFunctionSupport f).card hq htwo).mp
      (Exists.intro f (And.intro hf rfl))
    choose T hT using hs
    have hne : T.Nonempty := by
      by_contra hz
      have hsum : T.sum (fun i => (oddPellAtomDegree i).totient)=0 := by
        apply Finset.sum_eq_zero
        intro i hi
        exact False.elim (hz (Exists.intro i hi))
      omega
    choose i hi using hne
    calc
      _ <= (oddPellAtomDegree i).totient :=
        (oddPell_minSupport_spec (F:=F) hq).2 i (hT.1 i hi)
      _ <= T.sum (fun j => (oddPellAtomDegree j).totient) :=
        Finset.single_le_sum (f:=fun j => (oddPellAtomDegree j).totient)
          (fun j hj => Nat.zero_le ((oddPellAtomDegree j).totient)) hi
      _ = _ := hT.2
  . choose i hi using (oddPell_minSupport_spec (F:=F) hq).1
    have hT : forall j, Membership.mem (Singleton.singleton i : Finset (Sum Nat Nat)) j ->
        Membership.mem (oddPellAtomLabels (F:=F)) j := by
      intro j hj
      have heq := Finset.mem_singleton.mp hj
      subst j
      exact hi.1
    have hs := (oddPell_support_card_spectrum h hh (oddPellMinSupport (F:=F)) hq htwo).mpr
      (Exists.intro (Singleton.singleton i : Finset (Sum Nat Nat))
        (And.intro hT (by simpa only [Finset.sum_singleton] using hi.2)))
    choose f hf using hs
    have hnonzero : Not (f=0) := by
      intro hz
      have hm0 : oddPellMinSupport (F:=F)=0 := by
        simpa [hz,oddPellFunctionSupport] using hf.2.symm
      have hm2 := oddPell_minSupport_two_le (F:=F) hq
      omega
    exact Exists.intro f (And.intro hf.1 (And.intro hnonzero hf.2))

omit [Field F] [DecidableEq F] in
theorem oddPell_minSupport_eq_two_of_not_three_dvd (hq : 5<=Fintype.card F)
    (hthree : Not (Dvd.dvd 3 (Fintype.card F))) : oddPellMinSupport (F:=F)=2 := by
  have hmod : Not (Fintype.card F%3=0) := by
    intro hz
    exact hthree (Nat.dvd_iff_mod_eq_zero.mpr hz)
  have hlabel : exists i, Membership.mem (oddPellAtomLabels (F:=F)) i /\
      oddPellAtomDegree i=3 := by
    by_cases h1 : Fintype.card F%3=1
    . have hv : Dvd.dvd 3 (Fintype.card F-1) :=
        Nat.dvd_iff_mod_eq_zero.mpr (by omega)
      exact oddPell_label_of_divisor (F:=F) true 3 (by decide) (by decide) hv
        (by change Not (Fintype.card F-1=0); omega)
    . have hv : Dvd.dvd 3 (Fintype.card F+1) :=
        Nat.dvd_iff_mod_eq_zero.mpr (by omega)
      exact oddPell_label_of_divisor (F:=F) false 3 (by decide) (by decide) hv
        (by change Not (Fintype.card F+1=0); omega)
  choose i hi using hlabel
  have hlo := oddPell_minSupport_two_le (F:=F) hq
  have hhi := (oddPell_minSupport_spec (F:=F) hq).2 i hi.1
  have hphi : (3 : Nat).totient=2 := by decide
  rw [hi.2,hphi] at hhi
  omega

theorem oddPell_card_three_probe_zero (h : F) (hh : Not (h=0))
    (S : Finset Nat) (a : Nat -> Real) (c : F)
    (hq : Fintype.card F=3) (htwo : Not ((2 : F)=0)) :
    oddPellSignedProbe h S a c=0 := by
  have hp : oddPellSplitWeight (F:=F)=0 := by simp [oddPellSplitWeight,hq]
  have hn : oddPellNonsplitWeight (F:=F)=0 := by simp [oddPellNonsplitWeight,hq]
  unfold oddPellSignedProbe
  apply Finset.sum_eq_zero
  intro k hk
  rw [oddPell_defect_normalize h c k hh htwo,
    oddPell_defect_degree_sectors ((2/h)*c) k htwo,hp,hn]
  simp

omit [Field F] [DecidableEq F] in
theorem oddPell_minSupport_card_three (hq : Fintype.card F=3) :
    oddPellMinSupport (F:=F)=0 := by
  simp only [oddPellMinSupport,oddPellAtomLabels,oddPellSectorDivisors,
    oddPellSectorModulus,oddPellAtomDegree,hq]
  decide

omit [Field F] [DecidableEq F] in
theorem oddPell_minSupport_card_nine (hq : Fintype.card F=9) :
    oddPellMinSupport (F:=F)=4 := by
  simp only [oddPellMinSupport,oddPellAtomLabels,oddPellSectorDivisors,
    oddPellSectorModulus,oddPellAtomDegree,hq]
  decide

omit [Field F] [DecidableEq F] in
theorem oddPell_minSupport_card_twentyseven (hq : Fintype.card F=27) :
    oddPellMinSupport (F:=F)=6 := by
  simp only [oddPellMinSupport,oddPellAtomLabels,oddPellSectorDivisors,
    oddPellSectorModulus,oddPellAtomDegree,hq]
  decide

omit [Field F] [DecidableEq F] in
theorem oddPell_minSupport_card_twofortythree (hq : Fintype.card F=243) :
    oddPellMinSupport (F:=F)=10 := by
  simp only [oddPellMinSupport,oddPellAtomLabels,oddPellSectorDivisors,
    oddPellSectorModulus,oddPellAtomDegree,hq]
  decide

end FiniteField
