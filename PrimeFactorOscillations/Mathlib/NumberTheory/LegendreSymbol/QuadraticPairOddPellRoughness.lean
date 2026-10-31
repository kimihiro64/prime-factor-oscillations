/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.ArithmeticFunction.TernaryExtensionOrder
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairOddPellPrimeExtension

/-!
# Extension-degree roughness and signed-probe delocalization

All extension degrees n>=2 are retained, independently of the odd-Pell
polynomial index. The full signed support minimum is controlled from both
sides by the least prime factor of n. Its divergence is exactly roughness of
the degrees; a fixed nontrivial divisor prevents divergence along any tower.
-/

set_option autoImplicit false
set_option Elab.async false

namespace FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] [DecidableEq F] in
private theorem oddPell_ternary_card_ge_five (n : Nat) (hn : 2<=n)
    (hcard : Fintype.card F=3^n) : 5<=Fintype.card F := by
  have hp : (9 : Nat)<=3^n :=
    Nat.pow_le_pow_right (n:=3) (i:=2) (j:=n) (by decide) hn
  rw [hcard]
  omega

omit [Field F] [DecidableEq F] in
private theorem oddPell_ternary_atom_data (n : Nat)
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
private theorem oddPell_ternary_prime_min_upper (n p : Nat) (hn : 2<=n)
    (hp : Nat.Prime p) (hpo : Odd p) (hcard : Fintype.card F=3^n)
    (hdiv : Dvd.dvd p (3^n-1) \/ Dvd.dvd p (3^n+1)) :
    oddPellMinSupport (F:=F)<=p-1 := by
  have hq := oddPell_ternary_card_ge_five n hn hcard
  have hhi : oddPellMinSupport (F:=F)<=p.totient := by
    cases hdiv with
    | inl hv =>
      have hi : Membership.mem (oddPellAtomLabels (F:=F)) (Sum.inl p) := by
        apply (oddPell_atomLabels_left (F:=F) p).mpr
        apply And.intro hp.ne_one
        apply Finset.mem_filter.mpr
        apply And.intro
        . apply Nat.mem_divisors.mpr
          apply And.intro
          . change Dvd.dvd p (Fintype.card F-1)
            simpa only [hcard] using hv
          . change Not (Fintype.card F-1=0)
            omega
        . exact hpo
      exact (oddPell_minSupport_spec (F:=F) hq).2 (Sum.inl p) hi
    | inr hv =>
      have hi : Membership.mem (oddPellAtomLabels (F:=F)) (Sum.inr p) := by
        apply (oddPell_atomLabels_right (F:=F) p).mpr
        apply And.intro hp.ne_one
        apply Finset.mem_filter.mpr
        apply And.intro
        . apply Nat.mem_divisors.mpr
          apply And.intro
          . change Dvd.dvd p (Fintype.card F+1)
            simpa only [hcard] using hv
          . change Not (Fintype.card F+1=0)
            omega
        . exact hpo
      exact (oddPell_minSupport_spec (F:=F) hq).2 (Sum.inr p) hi
  simpa only [Nat.totient_prime hp] using hhi

omit [Field F] [DecidableEq F] in
theorem oddPell_ternary_atom_totient_lower (n : Nat) (hn : 2<=n)
    (hcard : Fintype.card F=3^n) (i : Sum Nat Nat)
    (hi : Membership.mem (oddPellAtomLabels (F:=F)) i) :
    2*n.minFac<=(oddPellAtomDegree i).totient := by
  have hd := oddPell_ternary_atom_data n hcard i hi
  exact Nat.ternaryExtension_totient_lower n (oddPellAtomDegree i) hn
    hd.1 hd.2.1 hd.2.2

omit [Field F] [DecidableEq F] in
theorem oddPell_ternary_minSupport_lower (n : Nat) (hn : 2<=n)
    (hcard : Fintype.card F=3^n) :
    2*n.minFac<=oddPellMinSupport (F:=F) := by
  have hq := oddPell_ternary_card_ge_five n hn hcard
  choose i hi using (oddPell_minSupport_spec (F:=F) hq).1
  have hlo := oddPell_ternary_atom_totient_lower n hn hcard i hi.1
  simpa only [hi.2] using hlo

theorem oddPell_ternary_support_lower (h : F) (hh : Not (h=0))
    (n : Nat) (hn : 2<=n) (hcard : Fintype.card F=3^n)
    (htwo : Not ((2 : F)=0)) (f : F -> Real)
    (hf : Membership.mem (oddPellProbeSpace h) f) (hfn : Not (f=0)) :
    2*n.minFac<=(oddPellFunctionSupport f).card := by
  have hq := oddPell_ternary_card_ge_five n hn hcard
  exact Nat.le_trans (oddPell_ternary_minSupport_lower n hn hcard)
    ((oddPell_sharp_support_minimum h hh hq htwo).1 f hf hfn)

omit [Field F] [DecidableEq F] in
theorem oddPell_ternary_minSupport_eq_iff_prime (n : Nat) (hn : 2<=n)
    (hcard : Fintype.card F=3^n) :
    oddPellMinSupport (F:=F)=2*n.minFac <-> Nat.Prime (2*n.minFac+1) := by
  have hq := oddPell_ternary_card_ge_five n hn hcard
  constructor
  . intro heq
    choose i hi using (oddPell_minSupport_spec (F:=F) hq).1
    have hd := oddPell_ternary_atom_data n hcard i hi.1
    exact Nat.ternaryExtension_endpoint_prime n (oddPellAtomDegree i) hn
      hd.1 hd.2.1 hd.2.2 (hi.2.trans heq)
  . intro hp
    have hr : Nat.Prime n.minFac := Nat.minFac_prime (by omega)
    have hsupply := Nat.primeExtension_safePrime_factor n.minFac hr.two_le hp
    have hlift := Nat.ternaryExtension_primeFactor_lift n.minFac n (2*n.minFac+1)
      hp (Nat.minFac_dvd n) hsupply
    have ho : Odd (2*n.minFac+1) := Exists.intro n.minFac rfl
    have hhi := oddPell_ternary_prime_min_upper n (2*n.minFac+1) hn hp ho hcard hlift
    have hlo := oddPell_ternary_minSupport_lower n hn hcard
    omega

theorem oddPell_ternary_endpoint_iff_prime (h : F) (hh : Not (h=0))
    (n : Nat) (hn : 2<=n) (hcard : Fintype.card F=3^n)
    (htwo : Not ((2 : F)=0)) :
    (exists f : F -> Real, Membership.mem (oddPellProbeSpace h) f /\ Not (f=0) /\
      (oddPellFunctionSupport f).card=2*n.minFac) <-> Nat.Prime (2*n.minFac+1) := by
  have hq := oddPell_ternary_card_ge_five n hn hcard
  constructor
  . intro hf
    choose f hf using hf
    have hlo := oddPell_ternary_minSupport_lower n hn hcard
    have hhi := (oddPell_sharp_support_minimum h hh hq htwo).1 f hf.1 hf.2.1
    rw [hf.2.2] at hhi
    exact (oddPell_ternary_minSupport_eq_iff_prime n hn hcard).mp
      (Nat.le_antisymm hhi hlo)
  . intro hp
    have heq := (oddPell_ternary_minSupport_eq_iff_prime n hn hcard).mpr hp
    choose f hf using (oddPell_sharp_support_minimum h hh hq htwo).2
    exact Exists.intro f (And.intro hf.1 (And.intro hf.2.1 (hf.2.2.trans heq)))

omit [Field F] [DecidableEq F] in
theorem oddPell_ternary_minSupport_bound_of_degree_dvd (n d : Nat) (hn : 2<=n)
    (hd : 2<=d) (hcard : Fintype.card F=3^n) (hdn : Dvd.dvd d n) :
    oddPellMinSupport (F:=F)<=3^d+1 := by
  have hbase : Fintype.card (Fin (3^d))=3^d := Fintype.card_fin _
  have hq := oddPell_ternary_card_ge_five d hd hbase
  choose i hi using (oddPell_minSupport_spec (F:=Fin (3^d)) hq).1
  have he := oddPell_ternary_atom_data d hbase i hi.1
  have he1 : Not (oddPellAtomDegree i=1) := by have ht := he.2.1; omega
  choose p hp using Nat.exists_prime_and_dvd he1
  have hpo : Odd p := Odd.of_dvd_nat he.1 hp.2
  have hpdiv : Dvd.dvd p (3^d-1) \/ Dvd.dvd p (3^d+1) := by
    cases he.2.2 with
    | inl hv => exact Or.inl (Nat.dvd_trans hp.2 hv)
    | inr hv => exact Or.inr (Nat.dvd_trans hp.2 hv)
  have hlift := Nat.ternaryExtension_primeFactor_lift d n p hp.1 hdn hpdiv
  have hmin := oddPell_ternary_prime_min_upper n p hn hp.1 hpo hcard hlift
  have hep : 0<oddPellAtomDegree i := by have ht := he.2.1; omega
  have hpe := Nat.le_of_dvd hep hp.2
  have hqpos : 0<(3 : Nat)^d := pow_pos (by decide) _
  have hqge : 9<=3^d := Nat.pow_le_pow_right (n:=3) (i:=2) (j:=d) (by decide) hd
  have heup : oddPellAtomDegree i<=3^d+1 := by
    cases he.2.2 with
    | inl hv =>
      have hb := Nat.le_of_dvd (by omega : 0<3^d-1) hv
      omega
    | inr hv => exact Nat.le_of_dvd (by omega) hv
  omega

omit [Field F] [DecidableEq F] in
theorem oddPell_ternary_minSupport_upper (n : Nat) (hn : 2<=n)
    (hcard : Fintype.card F=3^n) :
    oddPellMinSupport (F:=F)<=3^n.minFac+1 := by
  have hr : Nat.Prime n.minFac := Nat.minFac_prime (by omega)
  exact oddPell_ternary_minSupport_bound_of_degree_dvd n n.minFac hn hr.two_le
    hcard (Nat.minFac_dvd n)

noncomputable def oddPellTernaryMinSupport (n : Nat) : Nat :=
  oddPellMinSupport (F:=Fin (3^n))

theorem oddPell_ternary_minSupport_bounds (n : Nat) (hn : 2<=n) :
    2*n.minFac<=oddPellTernaryMinSupport n /\
      oddPellTernaryMinSupport n<=3^n.minFac+1 := by
  have hc : Fintype.card (Fin (3^n))=3^n := Fintype.card_fin _
  exact And.intro (oddPell_ternary_minSupport_lower n hn hc)
    (oddPell_ternary_minSupport_upper n hn hc)

theorem oddPell_ternary_minSupport_tendsto_iff (a : Nat -> Nat)
    (ha : forall j : Nat, 2<=a j) :
    Filter.Tendsto (fun j => oddPellTernaryMinSupport (a j)) Filter.atTop Filter.atTop <->
      Filter.Tendsto (fun j => (a j).minFac) Filter.atTop Filter.atTop := by
  constructor
  . intro h
    apply Filter.tendsto_atTop_atTop.mpr
    intro b
    choose J hJ using (Filter.tendsto_atTop_atTop.mp h) (3^b+2)
    apply Exists.intro J
    intro j hj
    have hm := hJ j hj
    have hupper := (oddPell_ternary_minSupport_bounds (a j) (ha j)).2
    by_contra hbad
    have hb : (a j).minFac<=b := by omega
    have hp : 3^(a j).minFac<=3^b :=
      Nat.pow_le_pow_right (n:=3) (by decide) hb
    omega
  . intro h
    apply Filter.tendsto_atTop_mono (f:=fun j => (a j).minFac)
      (g:=fun j => oddPellTernaryMinSupport (a j))
    . intro j
      have hb := (oddPell_ternary_minSupport_bounds (a j) (ha j)).1
      omega
    . exact h

theorem oddPell_ternary_tower_bounded (a : Nat -> Nat) (d : Nat)
    (hd : 2<=d) (ha : forall j : Nat, 2<=a j)
    (hdiv : forall j : Nat, Dvd.dvd d (a j)) :
    forall j : Nat, oddPellTernaryMinSupport (a j)<=3^d+1 := by
  intro j
  have hc : Fintype.card (Fin (3^(a j)))=3^(a j) := Fintype.card_fin _
  exact oddPell_ternary_minSupport_bound_of_degree_dvd (a j) d (ha j) hd hc (hdiv j)

theorem oddPell_ternary_tower_not_tendsto (a : Nat -> Nat) (d : Nat)
    (hd : 2<=d) (ha : forall j : Nat, 2<=a j)
    (hdiv : forall j : Nat, Dvd.dvd d (a j)) :
    Not (Filter.Tendsto (fun j => oddPellTernaryMinSupport (a j))
      Filter.atTop Filter.atTop) := by
  intro h
  choose J hJ using (Filter.tendsto_atTop_atTop.mp h) (3^d+2)
  have hlo := hJ J (Nat.le_refl J)
  have hhi := oddPell_ternary_tower_bounded a d hd ha hdiv J
  omega

end FiniteField
