import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.LiminfLimsup
import PrimeFactorUnimodality.Helpers.PrimeSequence.Basic

/-! # Actual consecutive-prime-gap frequencies and their growth exponents -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open PrimeFactorUnimodality

noncomputable section

/-- Consecutive gaps at most H with lower prime at most X.
The ambient range is finite and loses no prime index because p_i>=i+2. -/
def primeGapFrequencyCount (H X : Nat) : Nat :=
  ((Finset.range X).filter (fun i => primeAt i <= X /\ primeGap i <= H)).card

/-- The stretched-logarithmic upper growth exponent of the actual gap count.
The variable X tends to infinity with H fixed. The shift handles empty counts. -/
def primeGapFrequencyExponent (H : Nat) : Real :=
  Filter.limsup
    (fun X : Nat => Real.log (Real.log (3 + (primeGapFrequencyCount H X : Real))) /
      Real.log (Real.log (X : Real))) Filter.atTop

/-- The count is bounded by the ambient number of integers, uniformly in H. -/
theorem primeGapFrequencyCount_le (H X : Nat) : primeGapFrequencyCount H X <= X := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range X)

/-- Enlarging the endpoint only adds eligible actual prime gaps. -/
theorem primeGapFrequencyCount_mono_endpoint (H : Nat) :
    Monotone (primeGapFrequencyCount H) := by
  intro X Y hXY
  apply Finset.card_le_card
  intro i hi
  have hmem := Finset.mem_filter.mp hi
  have hindex := Finset.mem_range.mp hmem.1
  exact Finset.mem_filter.mpr (And.intro
    (Finset.mem_range.mpr (hindex.trans_le hXY))
    (And.intro (hmem.2.1.trans hXY) hmem.2.2))

/-- Enlarging the allowed gap only adds eligible actual prime gaps. -/
theorem primeGapFrequencyCount_mono_gap (X : Nat) :
    Monotone (fun H => primeGapFrequencyCount H X) := by
  intro H J hHJ
  apply Finset.card_le_card
  intro i hi
  have hmem := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr
    (And.intro hmem.1 (And.intro hmem.2.1 (hmem.2.2.trans hHJ)))

/-- Exact membership can be tested by the prime value and gap alone; the
finite index cutoff is not an additional mathematical restriction. -/
theorem mem_primeGapFrequency_filter_iff (H X i : Nat) :
    Membership.mem ((Finset.range X).filter
      (fun i => primeAt i <= X /\ primeGap i <= H)) i <->
      primeAt i <= X /\ primeGap i <= H := by
  constructor
  next =>
    intro hi
    exact (Finset.mem_filter.mp hi).2
  next =>
    intro hi
    have hbase : i + 2 <= primeAt i := Nat.add_two_le_nth_prime i
    exact Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr (by omega)) hi)

end

end PrimeFactorOscillations
