/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.CyclotomicSampling
import PrimeFactorOscillations.Mathlib.NumberTheory.Primes.FibonacciGoldenCarrier

/-!
# Exact joint law for Fibonacci carrier primes

Labels are odd index primes. Uniform scalar indices modulo their product
give the full Bernoulli law with success probability 1/l. The existing CRT
equivalence is reused; carrier magnitudes never determine the cutoff.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.FibonacciProbability

local instance (p : Nat.Primes) : NeZero (p : Nat) :=
  NeZero.mk p.property.ne_zero

local instance (S : Finset Nat.Primes) :
    NeZero (CyclotomicProbability.sampleModulus S) :=
  NeZero.mk (by
    unfold CyclotomicProbability.sampleModulus
    apply Finset.prod_ne_zero_iff.mpr
    intro p _
    exact p.val.property.ne_zero)

/-- A local index-divisibility outcome, including failure. -/
def patternSet (p : Nat.Primes) (bit : Bool) : Finset (ZMod (p : Nat)) := by
  classical
  exact if bit then {0} else Finset.univ.erase 0

theorem patternSet_mem (p : Nat.Primes) (bit : Bool) (x : ZMod (p : Nat)) :
    Membership.mem (patternSet p bit) x <-> if bit then x = 0 else Not (x = 0) := by
  classical
  cases bit <;> simp [patternSet]

theorem patternSet_card (p : Nat.Primes) (bit : Bool) :
    (patternSet p bit).card = if bit then 1 else (p : Nat) - 1 := by
  classical
  cases bit <;> simp [patternSet, Finset.card_univ, ZMod.card]

/-- Complete scalar outcome set for a prescribed finite binary pattern. -/
def jointSet (S : Finset Nat.Primes) (bits : S -> Bool) :
    Finset (ZMod (CyclotomicProbability.sampleModulus S)) := by
  classical
  exact (Fintype.piFinset (fun p : S => patternSet p.val (bits p))).map
    (CyclotomicProbability.residueEquiv S).symm.toEquiv.toEmbedding

theorem jointSet_mem (S : Finset Nat.Primes) (bits : S -> Bool)
    (u : ZMod (CyclotomicProbability.sampleModulus S)) :
    Membership.mem (jointSet S bits) u <->
      forall p : S, Membership.mem (patternSet p.val (bits p))
        (CyclotomicProbability.residueEquiv S u p) := by
  classical
  constructor
  { intro hu
    choose v hv using Finset.mem_map.mp hu
    intro p
    have heq : CyclotomicProbability.residueEquiv S u p = v p := by
      rw [<- hv.2]
      exact congrFun ((CyclotomicProbability.residueEquiv S).apply_symm_apply v) p
    rw [heq]
    exact Fintype.mem_piFinset.mp hv.1 p }
  { intro hu
    exact Finset.mem_map.mpr (Exists.intro (CyclotomicProbability.residueEquiv S u)
      (And.intro (Fintype.mem_piFinset.mpr hu)
        ((CyclotomicProbability.residueEquiv S).symm_apply_apply u))) }

/-- This residue law is the actual Fibonacci carrier event at every integer index. -/
theorem jointSet_natCast_mem (S : Finset Nat.Primes)
    (hodd : forall p, Membership.mem S p -> 3 <= (p : Nat))
    (bits : S -> Bool) (n : Nat) :
    Membership.mem (jointSet S bits)
      (n : ZMod (CyclotomicProbability.sampleModulus S)) <->
      forall p : S, if bits p then
        Dvd.dvd (Nat.fibonacciPrimeCarrier (p.val : Nat)) (Nat.fib n)
      else Not (Dvd.dvd (Nat.fibonacciPrimeCarrier (p.val : Nat)) (Nat.fib n)) := by
  classical
  rw [jointSet_mem]
  apply forall_congr'
  intro p
  rw [CyclotomicProbability.residueEquiv_natCast, patternSet_mem]
  have hz : (n : ZMod (p.val : Nat)) = 0 <-> Dvd.dvd (p.val : Nat) n :=
    CharP.cast_eq_zero_iff (ZMod (p.val : Nat)) (p.val : Nat) n
  have hc := Nat.fibonacciPrimeCarrier_dvd_iff (p.val : Nat) n p.val.property
    (hodd p.val p.property)
  cases bits p
  { change Not ((n : ZMod (p.val : Nat)) = 0) <->
      Not (Dvd.dvd (Nat.fibonacciPrimeCarrier (p.val : Nat)) (Nat.fib n))
    exact not_congr (hz.trans hc.symm) }
  { exact hz.trans hc.symm }

theorem jointSet_card (S : Finset Nat.Primes) (bits : S -> Bool) :
    (jointSet S bits).card =
      Finset.prod Finset.univ (fun p : S => if bits p then 1 else (p.val : Nat) - 1) := by
  classical
  unfold jointSet
  rw [Finset.card_map, Fintype.card_piFinset]
  apply Finset.prod_congr rfl
  intro p _
  exact patternSet_card p.val (bits p)

/-- Uniform sampling over one full scalar index period. -/
def jointProbability (S : Finset Nat.Primes) (bits : S -> Bool) : Real :=
  ((jointSet S bits).card : Real) / CyclotomicProbability.sampleModulus S

/-- Exact Bernoulli independence at all fixed finite label supports. -/
theorem jointProbability_eq_product (S : Finset Nat.Primes) (bits : S -> Bool) :
    jointProbability S bits =
      Finset.prod Finset.univ (fun p : S =>
        if bits p then 1 / ((p.val : Nat) : Real)
        else 1 - 1 / ((p.val : Nat) : Real)) := by
  classical
  unfold jointProbability
  rw [jointSet_card]
  simp only [CyclotomicProbability.sampleModulus, Nat.cast_prod]
  rw [<- Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p _
  cases bits p
  { change (((p.val : Nat) - 1 : Nat) : Real) / ((p.val : Nat) : Real) =
      1 - 1 / ((p.val : Nat) : Real)
    rw [Nat.cast_sub p.val.property.one_lt.le, Nat.cast_one, sub_div]
    have hp : Not (((p.val : Nat) : Real) = 0) := by
      exact_mod_cast p.val.property.ne_zero
    rw [div_self hp] }
  { simp only [ite_true, Nat.cast_one] }

end PrimeFactorOscillations.FibonacciProbability
