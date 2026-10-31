/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.ArithmeticFunction.OddDivisorProbe
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairOddPellStableSpectrum

/-!
# One integral odd-Pell probe across every late extension field

The finite polynomial indices and integer coefficients are chosen before
the extension stage, finite field and nonzero shift. The native class
weights are preserved and every unselected primitive degree vanishes.
This strengthens field-by-field support attainment without asserting
positive mass in an integer primality window.
-/

set_option autoImplicit false
set_option Elab.async false

namespace FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
open UniversalOddDivisorProbe

noncomputable def oddPellUniversalProbe (h : F) (D : Finset Nat) (c : F) : Real :=
  oddPellSignedProbe h (probeIndices D) (fun k => (probeCoefficients D k : Real)) c

theorem oddPell_universal_probe_expansion (h : F) (hh : Not (h = 0))
    (D : Finset Nat) (hD : forall d, Membership.mem D d -> Odd d /\ 0 < d)
    (hq : 5 <= Fintype.card F) (htwo : Not ((2 : F) = 0)) :
    (fun c => oddPellUniversalProbe h D c) =
      (oddPellAtomLabels (F:=F)).sum (fun i =>
        HSMul.hSMul (if Membership.mem D (oddPellAtomDegree i)
          then oddPellAtomWeight (F:=F) i else 0) (oddPellAtomIndicator h i)) := by
  classical
  unfold oddPellUniversalProbe
  rw [oddPell_probe_atom_expansion h hh _ _ hq htwo]
  apply Finset.sum_congr rfl
  intro i hi
  have ha := amplitude D hD (oddPellAtomDegree i) (oddPell_atomDegree_pos i hi)
  have hr : ((probeIndices D).filter (fun k =>
      Dvd.dvd (oddPellAtomDegree i) (2 * k + 1))).sum
        (fun k => (probeCoefficients D k : Real)) =
          if Membership.mem D (oddPellAtomDegree i) then 1 else 0 := by
    have hc := congrArg (fun z : Int => (z : Real)) ha
    simpa only [Int.cast_sum, apply_ite, Int.cast_one, Int.cast_zero] using hc
  rw [hr]
  by_cases hd : Membership.mem D (oddPellAtomDegree i)
  . simp only [ite_eq_left hd, mul_one]
  . simp only [ite_eq_right hd, mul_zero]

theorem oddPell_universal_probe_support (h : F) (hh : Not (h = 0))
    (D : Finset Nat) (hD : forall d, Membership.mem D d -> Odd d /\ 0 < d)
    (hq : 5 <= Fintype.card F) (htwo : Not ((2 : F) = 0)) :
    oddPellFunctionSupport (fun c => oddPellUniversalProbe h D c) =
      ((oddPellAtomLabels (F:=F)).filter
        (fun i => Membership.mem D (oddPellAtomDegree i))).biUnion (oddPellShiftAtom h) := by
  classical
  rw [oddPell_universal_probe_expansion h hh D hD hq htwo,
    oddPell_atom_sum_support h hh _ htwo]
  apply congrArg (fun T : Finset (Sum Nat Nat) => T.biUnion (oddPellShiftAtom h))
  apply Finset.filter_congr
  intro i hi
  by_cases hd : Membership.mem D (oddPellAtomDegree i)
  . simp [hd, ne_of_gt (oddPell_atomWeight_pos (F:=F) i hq)]
  . simp [hd]

omit [Field F] [DecidableEq F] in
private theorem oddPell_universal_split_label (D : Finset Nat)
    (hD : forall d, Membership.mem D d ->
      Odd d /\ 1 < d /\ Dvd.dvd d (Fintype.card F - 1))
    (hq : 5 <= Fintype.card F) (d : Nat) (hd : Membership.mem D d) :
    Membership.mem (oddPellAtomLabels (F:=F)) (Sum.inl d) := by
  have hdata := hD d hd
  apply (oddPell_atomLabels_left (F:=F) d).mpr
  apply And.intro (by omega)
  apply Finset.mem_filter.mpr
  apply And.intro
  . apply Nat.mem_divisors.mpr
    apply And.intro hdata.2.2
    change Not (Fintype.card F - 1 = 0)
    omega
  . exact hdata.1

omit [Field F] [DecidableEq F] in
theorem oddPell_universal_split_labels (D : Finset Nat)
    (hD : forall d, Membership.mem D d ->
      Odd d /\ 1 < d /\ Dvd.dvd d (Fintype.card F - 1))
    (hq : 5 <= Fintype.card F) :
    (oddPellAtomLabels (F:=F)).filter
      (fun i => Membership.mem D (oddPellAtomDegree i)) =
        D.image (fun d => (Sum.inl d : Sum Nat Nat)) := by
  classical
  apply Finset.ext
  intro i
  rw [Finset.mem_filter]
  constructor
  . intro hi
    have hj := oddPell_universal_split_label D hD hq (oddPellAtomDegree i) hi.2
    have he : i = Sum.inl (oddPellAtomDegree i) :=
      oddPell_atomDegree_injective i _ hi.1 hj hq rfl
    exact Finset.mem_image.mpr
      (Exists.intro (oddPellAtomDegree i) (And.intro hi.2 he.symm))
  . intro hi
    choose d hd using Finset.mem_image.mp hi
    rw [<- hd.2]
    exact And.intro (oddPell_universal_split_label D hD hq d hd.1) hd.1

theorem oddPell_universal_split_support (h : F) (hh : Not (h = 0))
    (D : Finset Nat) (hD : forall d, Membership.mem D d ->
      Odd d /\ 1 < d /\ Dvd.dvd d (Fintype.card F - 1))
    (hq : 5 <= Fintype.card F) (htwo : Not ((2 : F) = 0)) :
    oddPellFunctionSupport (fun c => oddPellUniversalProbe h D c) =
      (D.image (fun d => (Sum.inl d : Sum Nat Nat))).biUnion (oddPellShiftAtom h) /\
    (oddPellFunctionSupport (fun c => oddPellUniversalProbe h D c)).card =
      D.sum Nat.totient := by
  classical
  have hs := oddPell_universal_probe_support h hh D
    (fun d hd => And.intro (hD d hd).1 (by have hpos := (hD d hd).2.1; omega)) hq htwo
  rw [oddPell_universal_split_labels D hD hq] at hs
  apply And.intro hs
  have hT : forall i, Membership.mem
      (D.image (fun d => (Sum.inl d : Sum Nat Nat))) i ->
        Membership.mem (oddPellAtomLabels (F:=F)) i := by
    intro i hi
    choose d hd using Finset.mem_image.mp hi
    rw [<- hd.2]
    exact oddPell_universal_split_label D hD hq d hd.1
  rw [hs, oddPell_shiftAtom_union_card h hh _ hT htwo, Finset.sum_image]
  . rfl
  . intro d hd e he heq
    exact Sum.inl.inj heq

end FiniteField


namespace Nat

theorem oddTotient_tower_mono (p : Nat) : Monotone (oddTotientTowerDegrees p) := by
  apply monotone_nat_of_le_succ
  intro j
  by_cases hp3 : p = 3
  . simp only [oddTotientTowerDegrees, ite_eq_left hp3]
    exact Finset.subset_union_left
  by_cases hp5 : p = 5
  . simp only [oddTotientTowerDegrees, ite_eq_right hp3, ite_eq_left hp5]
    exact Finset.subset_union_left
  . simp only [oddTotientTowerDegrees, ite_eq_right hp3, ite_eq_right hp5]
    exact Finset.subset_union_left

end Nat

universe u

namespace FiniteField

open UniversalOddDivisorProbe

theorem oddPell_integral_stable_tower (p N : Nat) (hp : Nat.Prime p) (hpo : Odd p)
    (hallowed : Nat.oddTotientSupportAllowed p N) :
    exists S : Finset Nat, exists a : Nat -> Int,
      forall (j : Nat), N <= j ->
      forall (G : Type u) [Field G] [Fintype G] [DecidableEq G],
      Fintype.card G = p ^ (Nat.oddTotientTowerDegree p j) ->
      Not ((2 : G) = 0) ->
      forall (h : G), Not (h = 0) ->
        (oddPellFunctionSupport (fun c =>
          oddPellSignedProbe h S (fun k => (a k : Real)) c)).card = N := by
  classical
  choose D hD using Nat.oddTotient_tower_eventual_realize p N N hallowed (Nat.le_refl N)
  have hsub := Finset.mem_powerset.mp hD.1
  apply Exists.intro (probeIndices D)
  apply Exists.intro (probeCoefficients D)
  intro j hj G instGField instGFintype instGDec hcard htwo h hh
  have hin : forall d, Membership.mem D d ->
      Membership.mem (Nat.oddTotientTowerDegrees p j) d := by
    intro d hd
    exact Nat.oddTotient_tower_mono p hj (hsub hd)
  have hdata : forall d, Membership.mem D d ->
      Odd d /\ 1 < d /\ Dvd.dvd d (Fintype.card G - 1) := by
    intro d hd
    have hx := Nat.oddTotient_tower_data p j d hp hpo (hin d hd)
    apply And.intro hx.1
    apply And.intro hx.2.1
    simpa only [hcard] using hx.2.2.2
  have hp3 : 3 <= p := by
    have hp2 := hp.two_le
    have hodd := Nat.odd_iff.mp hpo
    omega
  have hdeg := Nat.oddTotient_tower_degree_lower p j
  have hq0 := Nat.oddTotient_prime_power_card_bounds p
    (Nat.oddTotientTowerDegree p j) hp3 (by omega)
  have hq : 5 <= Fintype.card G := by
    rw [hcard]
    exact Nat.le_trans (by decide : 5 <= 9) hq0.1
  have hs := oddPell_universal_split_support h hh D hdata hq htwo
  change (oddPellFunctionSupport (fun c => oddPellUniversalProbe h D c)).card = N
  exact hs.2.trans hD.2

end FiniteField

