/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PrimeProfileSquareFilter
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.QuadraticReciprocalFilter

/-!
# Accelerated finite-moment recovery of exact prime transport

An explicit quadratic filter replaces the half-ratio geometric remainder by
64 to the negative k using degree at most 4k. The same fixed observation-noise
allowance recovers the exact even transport throughout the full budget window.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimeProfileRigidity

/-- Use the kth power of the explicit normalized quadratic as the square filter. -/
def primePrefixQuadraticFilterTransport (k : Nat) (e : Equiv.Perm Nat) (n : Nat) : Real :=
  primePrefixSquareFilterTransport (Polynomial.reciprocalWindowQuadratic ^ k) e n

/-- The accelerated observable genuinely uses probability moments of degree at most 4k. -/
theorem primePrefixQuadraticFilterTransport_polynomial
    (k : Nat) (e : Equiv.Perm Nat) (n : Nat) :
    exists G : Polynomial Real,
      G.natDegree <= 4 * k /\
      primePrefixQuadraticFilterTransport k e n =
        (PrimeFactorUnimodality.primeAt n : Real) *
          Finset.prefixDefect (fun j => Polynomial.eval
            ((PrimeFactorUnimodality.primeAt n : Real) /
              PrimeFactorUnimodality.primeAt j) G) e (n + 1) := by
  have hex := primePrefixSquareFilterTransport_polynomial
    (Polynomial.reciprocalWindowQuadratic ^ k)
    (Polynomial.eval_zero_reciprocalWindowQuadratic_pow k) e n
  let G := Classical.choose hex
  have hG := Classical.choose_spec hex
  have hdegree := Nat.mul_le_mul_left 2
    (Polynomial.natDegree_reciprocalWindowQuadratic_pow_le k)
  refine Exists.intro G (And.intro ?_ hG.2)
  apply le_trans hG.1
  omega

/-- A universal exponential error bound for the complete signed observable. -/
theorem primePrefixQuadraticFilterTransport_error
    (k : Nat) (e : Equiv.Perm Nat) (t : Nat -> Real) (n : Nat) (C : Real)
    (ht : 0 < t n) (hC0 : 0 <= C)
    (hC : C < (PrimeFactorUnimodality.primeAt n : Real) / 4)
    (hcost : normalizedPrimePrefixDefect e t n <= C) :
    0 <= Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) - primePrefixQuadraticFilterTransport k e n /\
      (Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) - primePrefixQuadraticFilterTransport k e n <=
          (1 / 64 : Real) ^ k *
            Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
              e (n + 1)) /\
      (Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) - primePrefixQuadraticFilterTransport k e n <=
          4 * C * (1 / 64 : Real) ^ k) := by
  have he := primePrefixSquareFilterTransport_error
    (Polynomial.reciprocalWindowQuadratic ^ k) ((25 / 217 : Real) ^ k)
    (Polynomial.abs_eval_reciprocalWindowQuadratic_pow_le k) e t n C ht hC0 hC hcost
  have hS0 := prime_prefix_transport_nonneg e n
  have hm := mul_le_mul_of_nonneg_right (Polynomial.reciprocalWindowQuadratic_rate k) hS0
  have hmc := mul_le_mul_of_nonneg_left (Polynomial.reciprocalWindowQuadratic_rate k)
    (by linarith only [hC0] : 0 <= 4 * C)
  exact And.intro he.1 (And.intro (he.2.1.trans hm) (he.2.2.trans hmc))

/-- An explicit smaller logarithmic degree retains the same half-unit noise allowance. -/
theorem primePrefixQuadraticFilterTransport_noisy_readout
    (e : Equiv.Perm Nat) (t : Nat -> Real) (n : Nat) (C : Real)
    (ht : 0 < t n) (hC0 : 0 <= C)
    (hp3 : (3 : Real) <= PrimeFactorUnimodality.primeAt n)
    (hC : C < (PrimeFactorUnimodality.primeAt n : Real) / 4)
    (hcost : normalizedPrimePrefixDefect e t n <= C) :
    let k : Nat := Nat.log 64 (2 * PrimeFactorUnimodality.primeAt n) + 1
    exists K : Nat,
      Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) = 2 * (K : Real) /\
      (forall y : Real, abs (y - primePrefixQuadraticFilterTransport k e n) < (1 / 2 : Real) ->
        abs (y - 2 * (K : Real)) < 1 /\
        (forall j : Nat, abs (y - 2 * (j : Real)) < 1 -> j = K)) := by
  let r : Real := PrimeFactorUnimodality.primeAt n
  let k : Nat := Nat.log 64 (2 * PrimeFactorUnimodality.primeAt n) + 1
  have hr3 : 3 <= r := hp3
  have hbudget : 4 * C < r := by linarith only [hC]
  have hsmall : 2 < r - C := by linarith only [hC, hr3]
  have heven := prime_prefix_transport_even_of_cost_le e t n C
    ht hC0 hC hcost hsmall
  let K := Classical.choose heven
  have hK : Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
      e (n + 1) = 2 * (K : Real) := Classical.choose_spec heven
  have hdNat : 2 * PrimeFactorUnimodality.primeAt n <
      64 ^ (Nat.log 64 (2 * PrimeFactorUnimodality.primeAt n) + 1) :=
    Nat.lt_pow_succ_log_self (by decide) (2 * PrimeFactorUnimodality.primeAt n)
  have hd : 2 * r < (64 : Real) ^ k := by
    dsimp only [r, k]
    exact_mod_cast hdNat
  have hpower : (1 / 64 : Real) ^ k * (64 : Real) ^ k = 1 := by
    rw [<- mul_pow]
    norm_num
  have hcancel : (4 * C * (1 / 64 : Real) ^ k) * (64 : Real) ^ k = 4 * C := by
    calc
      _ = 4 * C * ((1 / 64 : Real) ^ k * (64 : Real) ^ k) := by ring
      _ = _ := by rw [hpower, mul_one]
  have hprecision : 4 * C * (1 / 64 : Real) ^ k < (1 / 2 : Real) := by
    by_contra hn
    have hm := mul_le_mul_of_nonneg_right (le_of_not_gt hn)
      (by positivity : 0 <= (64 : Real) ^ k)
    rw [hcancel] at hm
    linarith only [hm, hd, hbudget]
  have he := primePrefixQuadraticFilterTransport_error k e t n C ht hC0 hC hcost
  rw [hK] at he
  have herror : 2 * (K : Real) - primePrefixQuadraticFilterTransport k e n < (1 / 2 : Real) :=
    he.2.2.trans_lt hprecision
  refine Exists.intro K (And.intro hK ?_)
  intro y hy
  change abs (y - primePrefixQuadraticFilterTransport k e n) < (1 / 2 : Real) at hy
  have hybounds := abs_lt.mp hy
  have hread : abs (y - 2 * (K : Real)) < 1 := by
    apply abs_lt.mpr
    constructor <;> linarith only [hybounds.1, hybounds.2, he.1, herror]
  refine And.intro hread ?_
  intro j hj
  have hKb := abs_lt.mp hread
  have hjb := abs_lt.mp hj
  have hjK : (j : Real) < (K : Real) + 1 := by linarith only [hjb.1, hKb.2]
  have hKj : (K : Real) < (j : Real) + 1 := by linarith only [hKb.1, hjb.2]
  have hjKn : j < K + 1 := by exact_mod_cast hjK
  have hKjn : K < j + 1 := by exact_mod_cast hKj
  omega

end PrimeFactorOscillations.PrimeProfileRigidity
