/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelLabelAverage

/-!
# Exact label-phase projection of actual-prime ascent RH criteria

The finite phases act only on the residue of each actual sampled prime.
Their average equals the old odd-packet weight, including its zero extension.
The complete signed excess and its original sampling hypotheses are retained.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelLabelAscent

open CarmichaelLabelAverage CarmichaelSupportRigidity PrimeOrderReturnLaw
open Filter PrimeFactorUnimodality

abbrev BinaryPhaseFamily (q : Nat -> Nat) :=
  (X : Nat) ->
    returnImage (G := Units (ZMod (q X))) (Monoid.exponent (Units (ZMod (q X)))) 2 ->
      Units (ZMod (q X))

def BinaryPhaseSections (q : Nat -> Nat) (S : Nat -> Finset Nat.Primes)
    (v : BinaryPhaseFamily q) : Prop :=
  forall X,
    (forall r, (v X r) ^ (Monoid.exponent (Units (ZMod (q X))) / 2) = r.val) /\
    (forall r, forall p : Nat.Primes, Membership.mem ((S X).erase twoLabel) p ->
      (v X r) ^ (Monoid.exponent (Units (ZMod (q X))) / (p : Nat)) = 1)

theorem exists_binary_phase_sections (q : Nat -> Nat) [forall X, NeZero (q X)]
    (S : Nat -> Finset Nat.Primes)
    (hDiv : forall X, forall p : S X,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod (q X)))))
    (hTwo : forall X, Membership.mem (S X) twoLabel) :
    exists v : BinaryPhaseFamily q, BinaryPhaseSections q S v := by
  classical
  have h := fun X => exists_label_phase_section (S X) (hDiv X) twoLabel (hTwo X)
  choose v hCoord hFixed using h
  exact Exists.intro v (fun X => And.intro (hCoord X) (hFixed X))

def labelAveragedLocalAscentExcess (H : Nat) (m : Nat -> Nat)
    (a : (X : Nat) -> Fin (m X) -> Nat)
    (q : Nat -> Nat) [forall X, NeZero (q X)] (S : Nat -> Finset Nat.Primes)
    (v : BinaryPhaseFamily q) (X : Nat) : Real :=
  weightedLocalAscentExcess H m a
    (fun Y i => averagedPrimeWeight (q Y) (S Y) twoLabel (v Y) (primeAt (a Y i))) X

theorem labelAveragedLocalAscentExcess_eq_erased
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (q : Nat -> Nat) [forall X, NeZero (q X)] (S : Nat -> Finset Nat.Primes)
    (hDiv : forall X, forall p : S X,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod (q X)))))
    (hTwo : forall X, Membership.mem (S X) twoLabel)
    (v : BinaryPhaseFamily q) (hv : BinaryPhaseSections q S v) (X : Nat) :
    labelAveragedLocalAscentExcess H m a q S v X =
      carmichaelLocalAscentExcess H m a q (fun Y => (S Y).erase twoLabel) X := by
  unfold labelAveragedLocalAscentExcess carmichaelLocalAscentExcess
    weightedLocalAscentExcess carmichaelLocalAscentWeight
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun b : Real => b * localAscentPairExcess H X (a X i))
    (averagedPrimeWeight_eq_erased (q X) (S X) (hDiv X) twoLabel (hTwo X)
      (v X) (hv X).1 (hv X).2 (primeAt (a X i)))

theorem labelAveragedLocalAscentExcess_unbounded_of_not_RH
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalAscentSampling H m a)
    (q : Nat -> Nat) [forall X, NeZero (q X)] (S : Nat -> Finset Nat.Primes)
    (hDiv : forall X, forall p : S X,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod (q X)))))
    (hTwo : forall X, Membership.mem (S X) twoLabel)
    (v : BinaryPhaseFamily q) (hv : BinaryPhaseSections q S v)
    (hBudget : Filter.Eventually (fun X : Nat => q X <= X ^ (m X / 2)) atTop)
    (hNotRH : Not RiemannHypothesis) (C X0 : Real) (hC : 0 < C) :
    exists n : Nat, X0 < (n : Real) /\
      C * (n : Real) ^ (7 / 10 : Real) < labelAveragedLocalAscentExcess H m a q S v n := by
  have hErase : forall X, forall p : (S X).erase twoLabel,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod (q X)))) := by
    intro X p
    exact hDiv X (Subtype.mk p.val (Finset.mem_erase.mp p.property).2)
  have hOdd : forall X, forall p : (S X).erase twoLabel, Not ((p.val : Nat) = 2) := by
    intro X p hEq
    have hp : p.val = twoLabel := Subtype.ext hEq
    exact (Finset.mem_erase.mp p.property).1 hp
  choose n hn hEx using carmichaelLocalAscentExcess_unbounded_of_not_RH
    H m a hs q (fun X => (S X).erase twoLabel) hErase hOdd hBudget hNotRH C X0 hC
  refine Exists.intro n (And.intro hn ?_)
  rw [labelAveragedLocalAscentExcess_eq_erased H m a q S hDiv hTwo v hv]
  exact hEx

theorem riemannHypothesis_iff_labelAveragedLocalAscentExcess_nonpos
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalAscentSampling H m a)
    (q : Nat -> Nat) [forall X, NeZero (q X)] (S : Nat -> Finset Nat.Primes)
    (hDiv : forall X, forall p : S X,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod (q X)))))
    (hTwo : forall X, Membership.mem (S X) twoLabel)
    (v : BinaryPhaseFamily q) (hv : BinaryPhaseSections q S v)
    (hBudget : Filter.Eventually (fun X : Nat => q X <= X ^ (m X / 2)) atTop) :
    RiemannHypothesis <-> Filter.Eventually
      (fun X : Nat => labelAveragedLocalAscentExcess H m a q S v X <= 0) atTop := by
  have hErase : forall X, forall p : (S X).erase twoLabel,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod (q X)))) := by
    intro X p
    exact hDiv X (Subtype.mk p.val (Finset.mem_erase.mp p.property).2)
  have hOdd : forall X, forall p : (S X).erase twoLabel, Not ((p.val : Nat) = 2) := by
    intro X p hEq
    have hp : p.val = twoLabel := Subtype.ext hEq
    exact (Finset.mem_erase.mp p.property).1 hp
  have h := riemannHypothesis_iff_eventually_carmichaelLocalAscentExcess_nonpos
    H m a hs q (fun X => (S X).erase twoLabel) hErase hOdd hBudget
  simpa only [labelAveragedLocalAscentExcess_eq_erased H m a q S hDiv hTwo v hv] using h

theorem riemannHypothesis_iff_labelAveragedLocalAscentExcess_power_upper
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalAscentSampling H m a)
    (q : Nat -> Nat) [forall X, NeZero (q X)] (S : Nat -> Finset Nat.Primes)
    (hDiv : forall X, forall p : S X,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod (q X)))))
    (hTwo : forall X, Membership.mem (S X) twoLabel)
    (v : BinaryPhaseFamily q) (hv : BinaryPhaseSections q S v)
    (hBudget : Filter.Eventually (fun X : Nat => q X <= X ^ (m X / 2)) atTop) :
    RiemannHypothesis <-> exists C : Real, 0 < C /\ Filter.Eventually
      (fun X : Nat => labelAveragedLocalAscentExcess H m a q S v X <=
        C * (X : Real) ^ (7 / 10 : Real)) atTop := by
  have hErase : forall X, forall p : (S X).erase twoLabel,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod (q X)))) := by
    intro X p
    exact hDiv X (Subtype.mk p.val (Finset.mem_erase.mp p.property).2)
  have hOdd : forall X, forall p : (S X).erase twoLabel, Not ((p.val : Nat) = 2) := by
    intro X p hEq
    have hp : p.val = twoLabel := Subtype.ext hEq
    exact (Finset.mem_erase.mp p.property).1 hp
  have h := riemannHypothesis_iff_eventually_carmichaelLocalAscentExcess_power_upper
    H m a hs q (fun X => (S X).erase twoLabel) hErase hOdd hBudget
  simpa only [labelAveragedLocalAscentExcess_eq_erased H m a q S hDiv hTwo v hv] using h

end PrimeFactorOscillations.CarmichaelLabelAscent
