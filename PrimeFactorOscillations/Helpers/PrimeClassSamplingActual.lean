/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassSamplingModel

/-!
# Uniform finite-prefix sampling for the literal prime class

A prime cutoff Y at least N contains every prime divisor in the full integer
sample from one through N. Its empirical coefficients are exactly the actual
sampleCount values. The finite Bernoulli error bound therefore applies uniformly
throughout this complete two-parameter domain, with its local budget retained.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open PrimeFactorOscillations.PrimeClassDecoder

theorem coeff_finiteEmpiricalPolynomial (s : Finset Nat) (N k : Nat) :
    (finiteEmpiricalPolynomial s N).coeff k =
      (1 / (N : Real)) *
        (((Finset.Icc 1 N).filter (fun m =>
          (s.filter (fun p => Dvd.dvd p m)).card = k)).card : Real) := by
  classical
  simp [finiteEmpiricalPolynomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Finset.sum_boole, eq_comm]

noncomputable def primeClassPrefix (P : Set Nat) (Y : Nat) : Finset Nat := by
  classical
  exact (Finset.Icc 2 Y).filter (fun p => And (Nat.Prime p) (Membership.mem P p))

theorem primeClassPrefix_prime (P : Set Nat) (Y p : Nat)
    (hp : Membership.mem (primeClassPrefix P Y) p) : Nat.Prime p := by
  classical
  exact (Finset.mem_filter.mp hp).2.1

theorem primeClassPrefix_factorCount_eq (P : Set Nat) (Y m : Nat)
    (hm : 0 < m) (hmY : m <= Y) :
    ((primeClassPrefix P Y).filter (fun p => Dvd.dvd p m)).card =
      primeDivisorCount P m := by
  classical
  unfold primeDivisorCount
  apply congrArg Finset.card
  apply Finset.ext
  intro p
  constructor
  case mp =>
    intro hp
    have hdivdata := Finset.mem_filter.mp hp
    have hprefix := Finset.mem_filter.mp hdivdata.1
    have hinterval := Finset.mem_Icc.mp hprefix.1
    have hpm : p <= m := Nat.le_of_dvd hm hdivdata.2
    exact Finset.mem_filter.mpr (And.intro
      (Finset.mem_Icc.mpr (And.intro hinterval.1 hpm))
      (And.intro hprefix.2.1 (And.intro hdivdata.2 hprefix.2.2)))
  case mpr =>
    intro hp
    have hsample := Finset.mem_filter.mp hp
    have hinterval := Finset.mem_Icc.mp hsample.1
    apply Finset.mem_filter.mpr
    exact And.intro
      (Finset.mem_filter.mpr (And.intro
        (Finset.mem_Icc.mpr (And.intro hinterval.1 (hinterval.2.trans hmY)))
        (And.intro hsample.2.1 hsample.2.2.2)))
      hsample.2.2.1

theorem coeff_finiteEmpirical_primeClassPrefix
    (P : Set Nat) (N Y k : Nat) (hNY : N <= Y) :
    (finiteEmpiricalPolynomial (primeClassPrefix P Y) N).coeff k =
      (sampleCount P N k : Real) / (N : Real) := by
  classical
  rw [coeff_finiteEmpiricalPolynomial]
  have hcounts :
      ((Finset.Icc 1 N).filter (fun m =>
        ((primeClassPrefix P Y).filter (fun p => Dvd.dvd p m)).card = k)).card =
        sampleCount P N k := by
    unfold sampleCount
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro m hm
    have hinterval := Finset.mem_Icc.mp hm
    have hmpos : 0 < m := Nat.lt_of_lt_of_le Nat.zero_lt_one hinterval.1
    rw [primeClassPrefix_factorCount_eq P Y m hmpos (hinterval.2.trans hNY)]
  rw [hcounts]
  ring

theorem actualSample_coefficient_error_le
    (P : Set Nat) (N Y : Nat) (hNY : N <= Y) (hN : 0 < N)
    (sigma : Real) (hs0 : 0 <= sigma) (hs1 : sigma <= 1) :
    (Finset.range ((primeClassPrefix P Y).card + 1)).sum (fun k =>
      abs ((sampleCount P N k : Real) / (N : Real) -
        (finiteReferencePolynomial (primeClassPrefix P Y)).coeff k)) <=
      (N : Real) ^ (sigma - 1) *
        (primeClassPrefix P Y).prod (fun p => 1 + 2 * (p : Real) ^ (-sigma)) := by
  have h := finiteEmpirical_coefficient_error_le (primeClassPrefix P Y)
    (fun p hp => primeClassPrefix_prime P Y p hp) N hN sigma hs0 hs1
  simpa only [Polynomial.coeff_sub, coeff_finiteEmpirical_primeClassPrefix P N Y _ hNY] using h

end PrimeFactorOscillations.PrimeClassSampling
