/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.GeneralPolynomialDetector
import PrimeFactorOscillations.Mathlib.FieldTheory.Finite.Cyclotomic

/-!
# Cyclotomic polynomial probability laws

For the scalar polynomial input u in Phi_q(u), the local divisor probability
at an unramified prime p is totient(q)/p on p = 1 modulo q and zero otherwise.
The modulus q is fixed; it is not the sampled scalar input or a divisor cutoff.
Primes dividing q are explicitly depleted. The resulting bounded-root law is
a PrimeClockLaw, with its own character-dependent clock and profile.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CyclotomicProbability

local instance (p : Nat.Primes) : NeZero (p : Nat) :=
  NeZero.mk p.property.ne_zero

/-- Exact local root count away from the ramified primes. -/
theorem polynomial_rootCount (q : Nat) (p : Nat.Primes)
    (hpq : Not (Dvd.dvd (p : Nat) q)) :
    GeneralPolynomialLaw.rootCount (Polynomial.cyclotomic q Int) p =
      if Dvd.dvd q ((p : Nat) - 1) then Nat.totient q else 0 := by
  classical
  let : Fact (Nat.Prime (p : Nat)) := Fact.mk p.property
  let : NeZero (q : ZMod (p : Nat)) := NeZero.mk (fun hz =>
    hpq ((CharP.cast_eq_zero_iff (ZMod (p : Nat)) (p : Nat) q).mp hz))
  have hr := FiniteField.card_cyclotomic_root_filter (K := ZMod (p : Nat)) q
  have hs : GeneralPolynomialLaw.rootSet (Polynomial.cyclotomic q Int) p =
      Finset.univ.filter
        (fun x : ZMod (p : Nat) => (Polynomial.cyclotomic q (ZMod (p : Nat))).IsRoot x) := by
    ext x
    simp only [GeneralPolynomialLaw.rootSet, GeneralPolynomialLaw.reduction,
      Polynomial.map_cyclotomic_int, Polynomial.IsRoot, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    { intro hx
      exact Finset.mem_filter.mpr (And.intro (Finset.mem_univ x) hx) }
    { intro hx
      exact (Finset.mem_filter.mp hx).2 }
  change (GeneralPolynomialLaw.rootSet (Polynomial.cyclotomic q Int) p).card = _
  rw [hs]
  simpa only [ZMod.card] using hr

/-- The finite exceptional set of primes dividing q is omitted explicitly. -/
def count (q : Nat) (p : Nat.Primes) : Nat :=
  if Dvd.dvd (p : Nat) q then 0
  else GeneralPolynomialLaw.rootCount (Polynomial.cyclotomic q Int) p

/-- Complete root-count formula, including every depleted prime. -/
theorem count_formula (q : Nat) (p : Nat.Primes) :
    count q p =
      if Dvd.dvd (p : Nat) q then 0
      else if Dvd.dvd q ((p : Nat) - 1) then Nat.totient q else 0 := by
  classical
  by_cases hpq : Dvd.dvd (p : Nat) q
  { simp only [count, hpq, ite_eq_left] }
  { rw [count, ite_eq_right hpq, polynomial_rootCount q p hpq,
      ite_eq_right hpq] }

/-- The degree bound is valid also before the nonramification restriction. -/
theorem count_le_totient (q : Nat) (p : Nat.Primes) :
    count q p <= Nat.totient q := by
  classical
  rw [count_formula]
  split_ifs <;> omega

/-- The depleted local success probability is strictly below one. -/
theorem count_lt_prime (q : Nat) (p : Nat.Primes) :
    count q p < (p : Nat) := by
  classical
  rw [count_formula]
  by_cases hpq : Dvd.dvd (p : Nat) q
  { rw [ite_eq_left hpq]
    exact p.property.pos }
  { rw [ite_eq_right hpq]
    by_cases hqp : Dvd.dvd q ((p : Nat) - 1)
    { rw [ite_eq_left hqp]
      have hpred : 0 < (p : Nat) - 1 := Nat.sub_pos_of_lt p.property.one_lt
      have hqle := Nat.le_of_dvd hpred hqp
      exact (Nat.totient_le q).trans_lt
        (hqle.trans_lt (Nat.sub_lt p.property.pos Nat.one_pos)) }
    { rw [ite_eq_right hqp]
      exact p.property.pos } }

/-- Every prime up to q is either depleted or absent from the identity class. -/
theorem count_eq_zero_of_le (q : Nat) (p : Nat.Primes)
    (hp : (p : Nat) <= q) : count q p = 0 := by
  classical
  rw [count_formula]
  by_cases hpq : Dvd.dvd (p : Nat) q
  { exact ite_eq_left hpq }
  { rw [ite_eq_right hpq]
    apply ite_eq_right
    intro hqp
    have hpred : 0 < (p : Nat) - 1 := Nat.sub_pos_of_lt p.property.one_lt
    have hqle := Nat.le_of_dvd hpred hqp
    omega }

/-- Local success probability for uniformly sampled integer inputs. -/
def probability (q : Nat) (p : Nat.Primes) : Real :=
  (count q p : Real) / (p : Nat)

theorem probability_nonneg (q : Nat) (p : Nat.Primes) :
    0 <= probability q p :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem probability_lt_one (q : Nat) (p : Nat.Primes) :
    probability q p < 1 := by
  have hp : (0 : Real) < (p : Nat) := by exact_mod_cast p.property.pos
  exact (div_lt_one hp).mpr (by exact_mod_cast count_lt_prime q p)

/-- The character-dependent cyclotomic family fits the proved general
bounded-root probability law, without a quadratic reference-law assertion. -/
def law (q : Nat) (hq : 2 <= q) : PrimeClockLaw :=
  PrimeClockLaw.ofRootCounts (count q) (fun p => (p : Nat))
    (Nat.totient q) (Nat.totient_pos.mpr (by omega))
    (fun p => (count_lt_prime q p).le)
    (count_le_totient q) (fun p => Nat.sub_le _ _)

/-- Explicit odds, with a positive denominator supplied by count_lt_prime. -/
theorem law_weight (q : Nat) (hq : 2 <= q) (p : Nat.Primes) :
    (law q hq).weight p =
      (count q p : Real) / ((p : Nat) - count q p) := rfl

/-- The existing uniform coefficient comparison applies to this actual law. -/
theorem law_comparison (q : Nat) (hq : 2 <= q) (b : Real) (hb : 0 < b) :
    PowerPolynomialLaw.ComparisonClaim (law q hq) b :=
  (law q hq).exists_densityRatio_linearization b hb

end PrimeFactorOscillations.CyclotomicProbability
