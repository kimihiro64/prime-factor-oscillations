/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PrimeProfileSquareFilter
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.ReciprocalChebyshevFilter

/-!
# All-order Chebyshev recovery of exact prime-profile transport

The complete signed error is at most 4*16^(-k)*S using degree at most 2k.
An explicit integer-logarithm order retains the fixed half-unit noise allowance
throughout the full localization budget window.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimeProfileRigidity

/-- The complete profile observable for the all-order normalized polynomial filter. -/
def primePrefixChebyshevTransport (k : Nat) (e : Equiv.Perm Nat) (n : Nat) : Real :=
  primePrefixSquareFilterTransport (Polynomial.reciprocalChebyshevFilter k) e n

/-- All-order filtering genuinely uses probability moments of degree at most 2k. -/
theorem primePrefixChebyshevTransport_polynomial
    (k : Nat) (e : Equiv.Perm Nat) (n : Nat) :
    exists G : Polynomial Real,
      G.natDegree <= 2 * k /\
      primePrefixChebyshevTransport k e n =
        (PrimeFactorUnimodality.primeAt n : Real) *
          Finset.prefixDefect (fun j => Polynomial.eval
            ((PrimeFactorUnimodality.primeAt n : Real) /
              PrimeFactorUnimodality.primeAt j) G) e (n + 1) := by
  have hex := primePrefixSquareFilterTransport_polynomial
    (Polynomial.reciprocalChebyshevFilter k)
    (Polynomial.eval_zero_reciprocalChebyshevFilter k) e n
  let G := Classical.choose hex
  have hG := Classical.choose_spec hex
  have hdegree := Nat.mul_le_mul_left 2
    (Polynomial.natDegree_reciprocalChebyshevFilter_le k)
  exact Exists.intro G (And.intro (le_trans hG.1 hdegree) hG.2)

/-- The full signed consumer retains the principal coefficient and all filter remainders. -/
theorem primePrefixChebyshevTransport_error
    (k : Nat) (e : Equiv.Perm Nat) (t : Nat -> Real) (n : Nat) (C : Real)
    (ht : 0 < t n) (hC0 : 0 <= C)
    (hC : C < (PrimeFactorUnimodality.primeAt n : Real) / 4)
    (hcost : normalizedPrimePrefixDefect e t n <= C) :
    0 <= Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) - primePrefixChebyshevTransport k e n /\
      (Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) - primePrefixChebyshevTransport k e n <=
          4 * (1 / 16 : Real) ^ k *
            Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
              e (n + 1)) /\
      (Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) - primePrefixChebyshevTransport k e n <=
          16 * C * (1 / 16 : Real) ^ k) := by
  have he := primePrefixSquareFilterTransport_error
    (Polynomial.reciprocalChebyshevFilter k) (2 * (1 / 4 : Real) ^ k)
    (Polynomial.abs_eval_reciprocalChebyshevFilter_le k) e t n C ht hC0 hC hcost
  rw [Polynomial.reciprocalChebyshevFilter_rate] at he
  refine And.intro he.1 (And.intro he.2.1 ?_)
  calc
    _ <= 4 * C * (4 * (1 / 16 : Real) ^ k) := he.2.2
    _ = 16 * C * (1 / 16 : Real) ^ k := by ring

/-- The explicit degree has half the original leading logarithmic moment count. -/
theorem primePrefixChebyshevTransport_noisy_readout
    (e : Equiv.Perm Nat) (t : Nat -> Real) (n : Nat) (C : Real)
    (ht : 0 < t n) (hC0 : 0 <= C)
    (hp3 : (3 : Real) <= PrimeFactorUnimodality.primeAt n)
    (hC : C < (PrimeFactorUnimodality.primeAt n : Real) / 4)
    (hcost : normalizedPrimePrefixDefect e t n <= C) :
    let k : Nat := Nat.log 16 (8 * PrimeFactorUnimodality.primeAt n) + 1
    exists K : Nat,
      Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) = 2 * (K : Real) /\
      (forall y : Real, abs (y - primePrefixChebyshevTransport k e n) < (1 / 2 : Real) ->
        abs (y - 2 * (K : Real)) < 1 /\
        (forall j : Nat, abs (y - 2 * (j : Real)) < 1 -> j = K)) := by
  let r : Real := PrimeFactorUnimodality.primeAt n
  let k : Nat := Nat.log 16 (8 * PrimeFactorUnimodality.primeAt n) + 1
  have hr3 : 3 <= r := hp3
  have hbudget : 16 * C < 4 * r := by linarith only [hC]
  have hsmall : 2 < r - C := by linarith only [hC, hr3]
  have heven := prime_prefix_transport_even_of_cost_le e t n C
    ht hC0 hC hcost hsmall
  let K := Classical.choose heven
  have hK : Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
      e (n + 1) = 2 * (K : Real) := Classical.choose_spec heven
  have hdNat : 8 * PrimeFactorUnimodality.primeAt n <
      16 ^ (Nat.log 16 (8 * PrimeFactorUnimodality.primeAt n) + 1) :=
    Nat.lt_pow_succ_log_self (by decide) (8 * PrimeFactorUnimodality.primeAt n)
  have hd : 8 * r < (16 : Real) ^ k := by
    dsimp only [r, k]
    exact_mod_cast hdNat
  have hpower : (1 / 16 : Real) ^ k * (16 : Real) ^ k = 1 := by
    rw [<- mul_pow]
    norm_num
  have hcancel : (16 * C * (1 / 16 : Real) ^ k) * (16 : Real) ^ k = 16 * C := by
    calc
      _ = 16 * C * ((1 / 16 : Real) ^ k * (16 : Real) ^ k) := by ring
      _ = _ := by rw [hpower, mul_one]
  have hprecision : 16 * C * (1 / 16 : Real) ^ k < (1 / 2 : Real) := by
    by_contra hn
    have hm := mul_le_mul_of_nonneg_right (le_of_not_gt hn)
      (by positivity : 0 <= (16 : Real) ^ k)
    rw [hcancel] at hm
    linarith only [hm, hd, hbudget]
  have he := primePrefixChebyshevTransport_error k e t n C ht hC0 hC hcost
  rw [hK] at he
  have herror : 2 * (K : Real) - primePrefixChebyshevTransport k e n < (1 / 2 : Real) :=
    he.2.2.trans_lt hprecision
  refine Exists.intro K (And.intro hK ?_)
  intro y hy
  change abs (y - primePrefixChebyshevTransport k e n) < (1 / 2 : Real) at hy
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

/-- The complete characteristic denominator sharpens the same signed error. -/
theorem primePrefixChebyshevTransport_exact_error
    (k : Nat) (e : Equiv.Perm Nat) (t : Nat -> Real) (n : Nat) (C : Real)
    (ht : 0 < t n) (hC0 : 0 <= C)
    (hC : C < (PrimeFactorUnimodality.primeAt n : Real) / 4)
    (hcost : normalizedPrimePrefixDefect e t n <= C) :
    0 <= Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) - primePrefixChebyshevTransport k e n /\
      (Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) - primePrefixChebyshevTransport k e n <=
          (4 / (Polynomial.reciprocalChebyshevDenominator k) ^ 2) *
            Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
              e (n + 1)) /\
      (Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) - primePrefixChebyshevTransport k e n <=
          16 * C / (Polynomial.reciprocalChebyshevDenominator k) ^ 2) := by
  have he := primePrefixSquareFilterTransport_error
    (Polynomial.reciprocalChebyshevFilter k)
    (2 / Polynomial.reciprocalChebyshevDenominator k)
    (Polynomial.abs_eval_reciprocalChebyshevFilter_le_exact k) e t n C ht hC0 hC hcost
  rw [Polynomial.reciprocalChebyshevFilter_exact_rate] at he
  refine And.intro he.1 (And.intro he.2.1 ?_)
  calc
    _ <= 4 * C * (4 / (Polynomial.reciprocalChebyshevDenominator k) ^ 2) := he.2.2
    _ = 16 * C / (Polynomial.reciprocalChebyshevDenominator k) ^ 2 := by ring

/-- A cost-adaptive exact spectral condition suffices for the same stable even readout. -/
theorem primePrefixChebyshevTransport_exact_noisy_readout
    (k : Nat) (e : Equiv.Perm Nat) (t : Nat -> Real) (n : Nat) (C : Real)
    (ht : 0 < t n) (hC0 : 0 <= C)
    (hp3 : (3 : Real) <= PrimeFactorUnimodality.primeAt n)
    (hC : C < (PrimeFactorUnimodality.primeAt n : Real) / 4)
    (hcost : normalizedPrimePrefixDefect e t n <= C)
    (hprecision : 32 * C < (Polynomial.reciprocalChebyshevDenominator k) ^ 2) :
    exists K : Nat,
      Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) = 2 * (K : Real) /\
      (forall y : Real, abs (y - primePrefixChebyshevTransport k e n) < (1 / 2 : Real) ->
        abs (y - 2 * (K : Real)) < 1 /\
        (forall j : Nat, abs (y - 2 * (j : Real)) < 1 -> j = K)) := by
  have hsmall : 2 < (PrimeFactorUnimodality.primeAt n : Real) - C := by
    linarith only [hC, hp3]
  have heven := prime_prefix_transport_even_of_cost_le e t n C
    ht hC0 hC hcost hsmall
  let K := Classical.choose heven
  have hK : Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
      e (n + 1) = 2 * (K : Real) := Classical.choose_spec heven
  have hW := Polynomial.reciprocalChebyshevDenominator_pos k
  have hWsq : 0 < (Polynomial.reciprocalChebyshevDenominator k) ^ 2 := pow_pos hW 2
  have hcancel : (16 * C / (Polynomial.reciprocalChebyshevDenominator k) ^ 2) *
      (Polynomial.reciprocalChebyshevDenominator k) ^ 2 = 16 * C := by
    field_simp [pow_ne_zero 2 hW.ne']
  have hprec : 16 * C / (Polynomial.reciprocalChebyshevDenominator k) ^ 2 <
      (1 / 2 : Real) := by
    by_contra hn
    have hm := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hWsq.le
    rw [hcancel] at hm
    linarith only [hm, hprecision]
  have he := primePrefixChebyshevTransport_exact_error k e t n C ht hC0 hC hcost
  rw [hK] at he
  have herror : 2 * (K : Real) - primePrefixChebyshevTransport k e n < (1 / 2 : Real) :=
    he.2.2.trans_lt hprec
  refine Exists.intro K (And.intro hK ?_)
  intro y hy
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
