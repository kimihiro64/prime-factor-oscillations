/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.ArithmeticFunction.OddTotientPowerTowers
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairOddPellPrimeWindow

/-!
# Complete stable signed-support spectra in odd characteristic

All witnesses retain actual finite polynomial indices and real coefficients,
their split primitive classes, and the exact support cardinality. Universal
exclusions concern every signed probe. The three quantitative horizons and
the every-late-stage classification use the same explicit extension towers.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096

namespace FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def oddPellSplitSupportWitness (h : F) (E : Finset Nat) (N : Nat) : Prop :=
  exists S : Finset Nat, exists a : Nat -> Real, exists D : Finset Nat,
    Membership.mem E.powerset D /\
      oddPellFunctionSupport (fun c => oddPellSignedProbe h S a c)=
        (D.image (fun d => (Sum.inl d : Sum Nat Nat))).biUnion (oddPellShiftAtom h) /\
      (oddPellFunctionSupport (fun c => oddPellSignedProbe h S a c)).card=N

private theorem oddPell_stable_neighbor_coprime (p q d : Nat) (hp : Nat.Prime p)
    (hq : 0<q) (hpq : Dvd.dvd p q)
    (hd : Dvd.dvd d (q-1) \/ Dvd.dvd d (q+1)) : Nat.Coprime p d := by
  apply hp.coprime_iff_not_dvd.mpr
  intro hpd
  have hp2 := hp.two_le
  have h1 : Dvd.dvd p 1 := by
    cases hd with
    | inl hminus =>
      have hh := Nat.dvd_sub hpq (Nat.dvd_trans hpd hminus)
      have heq : q-(q-1)=1 := by omega
      simpa only [heq] using hh
    | inr hplus =>
      have hh := Nat.dvd_sub (Nat.dvd_trans hpd hplus) hpq
      have heq : q+1-q=1 := by omega
      simpa only [heq] using hh
  have hh := Nat.le_of_dvd (by decide : 0<(1 : Nat)) h1
  omega

omit [Field F] [DecidableEq F] in
private theorem oddPell_stable_atom_data (p : Nat) (hp : Nat.Prime p)
    (hq : 5<=Fintype.card F) (hpq : Dvd.dvd p (Fintype.card F))
    (i : Sum Nat Nat) (hi : Membership.mem (oddPellAtomLabels (F:=F)) i) :
    Odd (oddPellAtomDegree i) /\ 1<oddPellAtomDegree i /\
      Nat.Coprime p (oddPellAtomDegree i) := by
  cases i with
  | inl d =>
    have hm := (oddPell_atomLabels_left (F:=F) d).mp hi
    have ho := (Finset.mem_filter.mp hm.2).2
    have hp0 := oddPell_atomDegree_pos (Sum.inl d) hi
    change 0<d at hp0
    have hd : 1<d := by have hh := hm.1; omega
    have hv : Dvd.dvd d (Fintype.card F-1) := by
      exact (Nat.mem_divisors.mp (Finset.mem_filter.mp hm.2).1).1
    exact And.intro ho (And.intro hd
      (oddPell_stable_neighbor_coprime p (Fintype.card F) d hp (by omega) hpq (Or.inl hv)))
  | inr d =>
    have hm := (oddPell_atomLabels_right (F:=F) d).mp hi
    have ho := (Finset.mem_filter.mp hm.2).2
    have hp0 := oddPell_atomDegree_pos (Sum.inr d) hi
    change 0<d at hp0
    have hd : 1<d := by have hh := hm.1; omega
    have hv : Dvd.dvd d (Fintype.card F+1) := by
      exact (Nat.mem_divisors.mp (Finset.mem_filter.mp hm.2).1).1
    exact And.intro ho (And.intro hd
      (oddPell_stable_neighbor_coprime p (Fintype.card F) d hp (by omega) hpq (Or.inr hv)))

theorem oddPell_stable_support_necessary (h : F) (hh : Not (h=0))
    (p : Nat) (hp : Nat.Prime p) (hq : 5<=Fintype.card F)
    (hpq : Dvd.dvd p (Fintype.card F)) (htwo : Not ((2 : F)=0))
    (f : F -> Real) (hf : Membership.mem (oddPellProbeSpace h) f) :
    Nat.oddTotientSupportAllowed p (oddPellFunctionSupport f).card := by
  classical
  choose T hT using (oddPell_support_card_spectrum h hh
    (oddPellFunctionSupport f).card hq htwo).mp (Exists.intro f (And.intro hf rfl))
  have hsum : (T.image oddPellAtomDegree).sum Nat.totient=(oddPellFunctionSupport f).card := by
    rw [Finset.sum_image]
    . exact hT.2
    . intro i hi j hj heq
      exact oddPell_atomDegree_injective i j (hT.1 i hi) (hT.1 j hj) hq heq
  rw [<- hsum]
  apply Nat.oddTotient_support_necessary
  intro d hd
  choose i hi using Finset.mem_image.mp hd
  have hdata := oddPell_stable_atom_data p hp hq hpq i (hT.1 i hi.1)
  simpa only [hi.2] using hdata

theorem oddPell_stable_split_realize (h : F) (hh : Not (h=0)) (D : Finset Nat)
    (hD : forall d, Membership.mem D d ->
      Odd d /\ 1<d /\ Dvd.dvd d (Fintype.card F-1))
    (hq : 5<=Fintype.card F) (htwo : Not ((2 : F)=0)) :
    exists S : Finset Nat, exists a : Nat -> Real,
      oddPellFunctionSupport (fun c => oddPellSignedProbe h S a c)=
        (D.image (fun d => (Sum.inl d : Sum Nat Nat))).biUnion (oddPellShiftAtom h) /\
      (oddPellFunctionSupport (fun c => oddPellSignedProbe h S a c)).card=
        D.sum Nat.totient := by
  classical
  let T : Finset (Sum Nat Nat) := D.image (fun d => Sum.inl d)
  have hT : forall i, Membership.mem T i ->
      Membership.mem (oddPellAtomLabels (F:=F)) i := by
    intro i hi
    choose d hd using Finset.mem_image.mp hi
    rw [<- hd.2]
    apply (oddPell_atomLabels_left (F:=F) d).mpr
    have hdata := hD d hd.1
    apply And.intro (by omega)
    apply Finset.mem_filter.mpr
    apply And.intro
    . apply Nat.mem_divisors.mpr
      apply And.intro hdata.2.2
      change Not (Fintype.card F-1=0)
      omega
    . exact hdata.1
  choose f hf using (oddPell_probe_support_iff_union h hh
    (T.biUnion (oddPellShiftAtom h)) hq htwo).mpr (Exists.intro T (And.intro hT rfl))
  choose S a hpoly using (oddPell_mem_probeSpace h f).mp hf.1
  have hfun : (fun c => oddPellSignedProbe h S a c)=f := funext hpoly
  apply Exists.intro S
  apply Exists.intro a
  rw [hfun]
  apply And.intro hf.2
  rw [hf.2,oddPell_shiftAtom_union_card h hh T hT htwo]
  dsimp only [T]
  rw [Finset.sum_image]
  . rfl
  . intro d hd e he heq
    exact Sum.inl.inj heq

private theorem oddPell_stable_degree_packet (h : F) (hh : Not (h=0))
    (E : Finset Nat) (N : Nat) (hq : 5<=Fintype.card F) (htwo : Not ((2 : F)=0))
    (hE : forall d, Membership.mem E d ->
      Odd d /\ 1<d /\ Dvd.dvd d (Fintype.card F-1))
    (hchoose : exists D : Finset Nat, Membership.mem E.powerset D /\ D.sum Nat.totient=N) :
    oddPellSplitSupportWitness h E N := by
  choose D hD using hchoose
  choose S a hSa using oddPell_stable_split_realize h hh D
    (fun d hd => hE d ((Finset.mem_powerset.mp hD.1) hd)) hq htwo
  exact Exists.intro S (Exists.intro a (Exists.intro D
    (And.intro hD.1 (And.intro hSa.1 (hSa.2.trans hD.2)))))

theorem oddPell_stable_three_horizon (h : F) (hh : Not (h=0)) (N j : Nat)
    (hallowed : Nat.oddTotientSupportAllowed 3 N) (hcap : N+6<=310*5^j)
    (hcard : Fintype.card F=3^(720*5^j)) (htwo : Not ((2 : F)=0)) :
    oddPellSplitSupportWitness h (Nat.oddTotientThreeDegrees j) N := by
  have hm : 2<=720*5^j := by have hp := pow_pos (by decide : 0<(5 : Nat)) j; omega
  have hq : 5<=Fintype.card F := by
    have hb := (Nat.oddTotient_prime_power_card_bounds 3 (720*5^j) (by decide) hm).1
    rw [hcard]
    omega
  apply oddPell_stable_degree_packet h hh (Nat.oddTotientThreeDegrees j) N hq htwo
  . intro d hd
    have hx := Nat.oddTotient_three_data d j hd
    have hv := Nat.oddTotient_three_family_period j d hd
    exact And.intro hx.1 (And.intro hx.2.1 (by simpa only [hcard] using hv))
  . exact Nat.oddTotient_three_horizon_realize N j hallowed hcap

theorem oddPell_stable_five_horizon (h : F) (hh : Not (h=0)) (N j : Nat)
    (hallowed : Nat.oddTotientSupportAllowed 5 N) (hcap : N<=186*3^j+2)
    (hcard : Fintype.card F=5^(720*3^j)) (htwo : Not ((2 : F)=0)) :
    oddPellSplitSupportWitness h (Nat.oddTotientFiveDegrees j) N := by
  have hm : 2<=720*3^j := by have hp := pow_pos (by decide : 0<(3 : Nat)) j; omega
  have hq : 5<=Fintype.card F := by
    have hb := (Nat.oddTotient_prime_power_card_bounds 5 (720*3^j) (by decide) hm).1
    rw [hcard]
    omega
  apply oddPell_stable_degree_packet h hh (Nat.oddTotientFiveDegrees j) N hq htwo
  . intro d hd
    have hx := Nat.oddTotient_five_data d j hd
    have hv := Nat.oddTotient_five_family_period j d hd
    exact And.intro hx.1 (And.intro hx.2.1 (by simpa only [hcard] using hv))
  . exact Nat.oddTotient_five_horizon_realize N j hallowed hcap

theorem oddPell_stable_other_horizon (h : F) (hh : Not (h=0)) (p N j : Nat)
    (hp : Nat.Prime p) (hseven : 7<=p) (heven : Even N) (hcap : N+1<=21*3^j)
    (hcard : Fintype.card F=p^(12*3^j)) (htwo : Not ((2 : F)=0)) :
    oddPellSplitSupportWitness h (Nat.oddTotientOtherDegrees j) N := by
  have hcp3 : Nat.Coprime p 3 := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hd
    have hlo := Nat.le_of_dvd (by decide : 0<(3 : Nat)) hd
    omega
  have hcp5 : Nat.Coprime p 5 := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hd
    have hlo := Nat.le_of_dvd (by decide : 0<(5 : Nat)) hd
    omega
  have hm : 2<=12*3^j := by have ht := pow_pos (by decide : 0<(3 : Nat)) j; omega
  have hq : 5<=Fintype.card F := by
    have hb := (Nat.oddTotient_prime_power_card_bounds p (12*3^j) (by omega) hm).1
    rw [hcard]
    omega
  apply oddPell_stable_degree_packet h hh (Nat.oddTotientOtherDegrees j) N hq htwo
  . intro d hd
    have hx := Nat.oddTotient_other_data p d j hcp3 hcp5 hd
    have hv := Nat.oddTotient_other_family_period p j d hp.pos hcp3 hcp5 hd
    exact And.intro hx.1 (And.intro hx.2.1 (by simpa only [hcard] using hv))
  . exact Nat.oddTotient_other_horizon_realize N j heven hcap

theorem oddPell_stable_tower_realize (h : F) (hh : Not (h=0)) (p N j : Nat)
    (hp : Nat.Prime p) (hpo : Odd p) (hj : N<=j)
    (hallowed : Nat.oddTotientSupportAllowed p N)
    (hcard : Fintype.card F=p^(Nat.oddTotientTowerDegree p j))
    (htwo : Not ((2 : F)=0)) :
    oddPellSplitSupportWitness h (Nat.oddTotientTowerDegrees p j) N := by
  have hp3 : 3<=p := by
    have hm := Nat.odd_iff.mp hpo
    have hh := hp.two_le
    omega
  have hq : 5<=Fintype.card F := by
    have hb := (Nat.oddTotient_prime_power_card_bounds p (Nat.oddTotientTowerDegree p j)
      hp3 (by have hd := Nat.oddTotient_tower_degree_lower p j; omega)).1
    rw [hcard]
    omega
  apply oddPell_stable_degree_packet h hh (Nat.oddTotientTowerDegrees p j) N hq htwo
  . intro d hd
    have hx := Nat.oddTotient_tower_data p j d hp hpo hd
    exact And.intro hx.1 (And.intro hx.2.1 (by simpa only [hcard] using hx.2.2.2))
  . exact Nat.oddTotient_tower_eventual_realize p N j hallowed hj

theorem oddPell_stable_tower_spectrum (h : F) (hh : Not (h=0)) (p N j : Nat)
    (hp : Nat.Prime p) (hpo : Odd p) (hj : N<=j)
    (hcard : Fintype.card F=p^(Nat.oddTotientTowerDegree p j))
    (htwo : Not ((2 : F)=0)) :
    (exists S : Finset Nat, exists a : Nat -> Real,
      (oddPellFunctionSupport (fun c => oddPellSignedProbe h S a c)).card=N) <->
        Nat.oddTotientSupportAllowed p N := by
  have hp3 : 3<=p := by
    have hm := Nat.odd_iff.mp hpo
    have hh := hp.two_le
    omega
  have hb := Nat.oddTotient_prime_power_card_bounds p (Nat.oddTotientTowerDegree p j)
    hp3 (by have hd := Nat.oddTotient_tower_degree_lower p j; omega)
  have hq : 5<=Fintype.card F := by rw [hcard]; omega
  have hpq : Dvd.dvd p (Fintype.card F) := by simpa only [hcard] using hb.2
  constructor
  . intro hex
    choose S a hSa using hex
    have hmem : Membership.mem (oddPellProbeSpace h) (fun c => oddPellSignedProbe h S a c) :=
      (oddPell_mem_probeSpace h _).mpr (Exists.intro S (Exists.intro a (fun c => rfl)))
    have hnecess := oddPell_stable_support_necessary h hh p hp hq hpq htwo _ hmem
    simpa only [hSa] using hnecess
  . intro hallowed
    choose S a D hD using oddPell_stable_tower_realize h hh p N j hp hpo hj
      hallowed hcard htwo
    exact Exists.intro S (Exists.intro a hD.2.2)

end FiniteField
