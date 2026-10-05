/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.PSeries
import Mathlib.Order.Filter.AtTopBot.Finset
import PrimeFactorOscillations.Definitions.PrimeProfile

/-!
# Analytic construction of the prime profile

Square-summable prime weights give an entire function. Products over the exact
inclusive cutoffs converge uniformly on each closed complex disk. No prime-gap
or Riemann-hypothesis assumption is used.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

theorem primeProfileWeight_nonneg (p : Nat) : 0 <= primeProfileWeight p := by
  unfold primeProfileWeight
  positivity

theorem primeProfileWeight_le_one (p : Nat.Primes) :
    primeProfileWeight (p : Nat) <= 1 := by
  have hn : 1 <= (p : Nat) - 1 := Nat.le_sub_one_of_lt p.property.one_lt
  have hr : (1 : Real) <= (((p : Nat) - 1 : Nat) : Real) := by exact_mod_cast hn
  have h := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1) hr
  simpa only [primeProfileWeight, div_one] using h

theorem summable_primeProfileWeight_sq :
    Summable (fun p : Nat.Primes => (primeProfileWeight (p : Nat)) ^ 2) := by
  have hb : Summable (fun n : Nat => 1 / (n : Real) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by decide)
  have hi : Function.Injective (fun p : Nat.Primes => (p : Nat) - 1) := by
    intro p q hpq
    apply Nat.Primes.coe_nat_injective
    calc
      (p : Nat) = ((p : Nat) - 1) + 1 :=
        (Nat.sub_add_cancel p.property.one_lt.le).symm
      _ = ((q : Nat) - 1) + 1 := congrArg (fun n : Nat => n + 1) hpq
      _ = (q : Nat) := Nat.sub_add_cancel q.property.one_lt.le
  simpa only [primeProfileWeight, div_pow, one_pow, Function.comp_def] using
    hb.comp_injective hi

theorem hasProdUniformlyOn_primeProfile (R : Real) (hR : 0 <= R) :
    HasProdUniformlyOn
      (fun p : Nat.Primes => fun z =>
        Complex.normalizedLinearFactor (primeProfileWeight (p : Nat)) z)
      primeProfile (Metric.closedBall (0 : Complex) R) :=
  Complex.hasProdUniformlyOn_normalizedLinearFactor
    (fun p : Nat.Primes => primeProfileWeight (p : Nat))
    (fun p => primeProfileWeight_nonneg (p : Nat))
    primeProfileWeight_le_one summable_primeProfileWeight_sq R hR

theorem differentiable_primeProfile : Differentiable Complex primeProfile :=
  Complex.differentiable_tprod_normalizedLinearFactor
    (fun p : Nat.Primes => primeProfileWeight (p : Nat))
    (fun p => primeProfileWeight_nonneg (p : Nat))
    primeProfileWeight_le_one summable_primeProfileWeight_sq

@[simp] theorem primeProfile_zero : primeProfile 0 = 1 := by
  simp [primeProfile]

@[simp] theorem primeProfile_one : primeProfile 1 = 1 := by
  simp [primeProfile, Complex.normalizedLinearFactor_one,
    primeProfileWeight_nonneg]

@[simp] theorem mem_primeProfilePrefixSet (p : Nat.Primes) (N : Nat) :
    Membership.mem (primeProfilePrefixSet N) p <-> (p : Nat) <= N := by
  exact (Finset.mem_subtype (p := Nat.Prime) (s := Finset.range (N + 1))
    (a := p)).trans (Finset.mem_range.trans Nat.lt_succ_iff)

theorem monotone_primeProfilePrefixSet : Monotone primeProfilePrefixSet := by
  intro m n hmn p hp
  exact (mem_primeProfilePrefixSet p n).mpr
    (((mem_primeProfilePrefixSet p m).mp hp).trans hmn)

theorem tendsto_primeProfilePrefixSet :
    Filter.Tendsto primeProfilePrefixSet Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_finset_of_monotone monotone_primeProfilePrefixSet
  intro p
  exact Exists.intro (p : Nat) ((mem_primeProfilePrefixSet p (p : Nat)).mpr le_rfl)

theorem tendstoUniformlyOn_primePrefixProfile (R : Real) (hR : 0 <= R) :
    TendstoUniformlyOn primePrefixProfile primeProfile Filter.atTop
      (Metric.closedBall (0 : Complex) R) := by
  have hp := (hasProdUniformlyOn_primeProfile R hR).tendstoUniformlyOn
  intro u hu
  exact tendsto_primeProfilePrefixSet.eventually (hp u hu)

theorem differentiable_primePrefixProfile (N : Nat) :
    Differentiable Complex (primePrefixProfile N) := by
  unfold primePrefixProfile Complex.normalizedLinearFactor
  fun_prop

@[simp] theorem primePrefixProfile_zero (N : Nat) : primePrefixProfile N 0 = 1 := by
  simp [primePrefixProfile]

@[simp] theorem primePrefixProfile_one (N : Nat) : primePrefixProfile N 1 = 1 := by
  simp [primePrefixProfile, Complex.normalizedLinearFactor_one,
    primeProfileWeight_nonneg]

end PrimeFactorOscillations

