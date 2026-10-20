/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PrimeProfileNonlinearCoercivity
import PrimeFactorOscillations.Helpers.PrimeProfileReciprocalWindow
import PrimeFactorOscillations.Helpers.PrimeProfileSupportedFilter
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.ReciprocalSevenFilter

/-!
# Exact rational characteristic readout of prime-profile transport

Integrated boundary costs imply a tighter retained window. Its characteristic
roots seven and one seventh give degree-2k exact recovery with fixed noise.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimeProfileRigidity

/-- The complete signed profile observable using the rational characteristic filter. -/
def primePrefixSevenTransport (k : Nat) (e : Equiv.Perm Nat) (n : Nat) : Real :=
  primePrefixSquareFilterTransport (Polynomial.reciprocalSevenFilter k) e n

/-- The rational filter uses probability moments of degree at most twice its order. -/
theorem primePrefixSevenTransport_polynomial (k : Nat) (e : Equiv.Perm Nat) (n : Nat) :
    exists G : Polynomial Real, G.natDegree <= 2 * k /\
      primePrefixSevenTransport k e n = (PrimeFactorUnimodality.primeAt n : Real) *
        Finset.prefixDefect (fun j => Polynomial.eval
          ((PrimeFactorUnimodality.primeAt n : Real) /
            PrimeFactorUnimodality.primeAt j) G) e (n + 1) := by
  have hex := primePrefixSquareFilterTransport_polynomial
    (Polynomial.reciprocalSevenFilter k) (Polynomial.eval_zero_reciprocalSevenFilter k) e n
  let G := Classical.choose hex
  have hG := Classical.choose_spec hex
  have hdegree := Nat.mul_le_mul_left 2 (Polynomial.natDegree_reciprocalSevenFilter_le k)
  exact Exists.intro G (And.intro (le_trans hG.1 hdegree) hG.2)

/-- The exact two-branch denominator controls the full signed error. -/
theorem primePrefixSevenTransport_exact_error
    (k : Nat) (e : Equiv.Perm Nat) (t : Nat -> Real) (n : Nat) (C : Real)
    (ht : 0 < t n) (hC0 : 0 <= C)
    (hC : C < (PrimeFactorUnimodality.primeAt n : Real) / 4)
    (hcost : normalizedPrimePrefixDefect e t n <= C) :
    0 <= Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) - primePrefixSevenTransport k e n /\
      (Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) - primePrefixSevenTransport k e n <=
          (4 / (Polynomial.reciprocalSevenDenominator k) ^ 2) *
            Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
              e (n + 1)) /\
      (Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) - primePrefixSevenTransport k e n <=
          16 * C / (Polynomial.reciprocalSevenDenominator k) ^ 2) := by
  have hlocal := prime_prefix_integrated_reciprocal_window e t n C ht hC hcost
  have he := primePrefixSquareFilterTransport_supported_error
    (Polynomial.reciprocalSevenFilter k) (2 / Polynomial.reciprocalSevenDenominator k)
    e n (by
      intro j hj
      have hw := hj.elim (hlocal.1 j) (hlocal.2 j)
      exact Polynomial.abs_eval_reciprocalSevenFilter_le_exact k _ hw.1 hw.2)
  rw [Polynomial.reciprocalSevenFilter_exact_rate] at he
  have hSC := prime_prefix_transport_le_four_mul_cost e t n C ht hC0 hC hcost
  have hm := mul_le_mul_of_nonneg_left hSC
    (by positivity : 0 <= 4 / (Polynomial.reciprocalSevenDenominator k) ^ 2)
  refine And.intro he.1 (And.intro he.2 ?_)
  calc
    _ <= (4 / (Polynomial.reciprocalSevenDenominator k) ^ 2) * (4 * C) :=
      he.2.trans hm
    _ = 16 * C / (Polynomial.reciprocalSevenDenominator k) ^ 2 := by ring

/-- The same degree gives a geometric forty-nine rate on the full signed consumer. -/
theorem primePrefixSevenTransport_error
    (k : Nat) (e : Equiv.Perm Nat) (t : Nat -> Real) (n : Nat) (C : Real)
    (ht : 0 < t n) (hC0 : 0 <= C)
    (hC : C < (PrimeFactorUnimodality.primeAt n : Real) / 4)
    (hcost : normalizedPrimePrefixDefect e t n <= C) :
    0 <= Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) - primePrefixSevenTransport k e n /\
      (Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) - primePrefixSevenTransport k e n <=
          4 * (1 / 49 : Real) ^ k *
            Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
              e (n + 1)) /\
      (Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) - primePrefixSevenTransport k e n <= 16 * C * (1 / 49 : Real) ^ k) := by
  have he := primePrefixSevenTransport_exact_error k e t n C ht hC0 hC hcost
  have hS := (primePrefixDefect_nonlinear_coercivity e t n ht).1
  have hnorm := Polynomial.reciprocalSeven_filter_norm_rate k
  have hleft : 0 <= 2 / Polynomial.reciprocalSevenDenominator k :=
    div_nonneg (by norm_num) (Polynomial.reciprocalSevenDenominator_pos k).le
  have hright : 0 <= 2 * (1 / 7 : Real) ^ k := by positivity
  have hsquare : (2 / Polynomial.reciprocalSevenDenominator k) ^ 2 <=
      (2 * (1 / 7 : Real) ^ k) ^ 2 := by
    nlinarith only [hnorm, hleft, hright]
  rw [Polynomial.reciprocalSevenFilter_exact_rate, Polynomial.reciprocalSevenFilter_rate] at hsquare
  have hm := mul_le_mul_of_nonneg_right hsquare hS
  have hSC := prime_prefix_transport_le_four_mul_cost e t n C ht hC0 hC hcost
  have hCmul := mul_le_mul_of_nonneg_left hSC
    (by positivity : 0 <= 4 * (1 / 49 : Real) ^ k)
  refine And.intro he.1 (And.intro (he.2.1.trans hm) ?_)
  calc
    _ <= (4 * (1 / 49 : Real) ^ k) * (4 * C) := (he.2.1.trans hm).trans hCmul
    _ = 16 * C * (1 / 49 : Real) ^ k := by ring

/-- A cost-adaptive exact spectral condition suffices for the same stable even readout. -/
theorem primePrefixSevenTransport_exact_noisy_readout
    (k : Nat) (e : Equiv.Perm Nat) (t : Nat -> Real) (n : Nat) (C : Real)
    (ht : 0 < t n) (hC0 : 0 <= C)
    (hp3 : (3 : Real) <= PrimeFactorUnimodality.primeAt n)
    (hC : C < (PrimeFactorUnimodality.primeAt n : Real) / 4)
    (hcost : normalizedPrimePrefixDefect e t n <= C)
    (hprecision : 32 * C < (Polynomial.reciprocalSevenDenominator k) ^ 2) :
    exists K : Nat,
      Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) = 2 * (K : Real) /\
      (forall y : Real, abs (y - primePrefixSevenTransport k e n) < (1 / 2 : Real) ->
        abs (y - 2 * (K : Real)) < 1 /\
        (forall j : Nat, abs (y - 2 * (j : Real)) < 1 -> j = K)) := by
  have hsmall : 2 < (PrimeFactorUnimodality.primeAt n : Real) - C := by
    linarith only [hC, hp3]
  have heven := prime_prefix_transport_even_of_cost_le e t n C
    ht hC0 hC hcost hsmall
  let K := Classical.choose heven
  have hK : Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
      e (n + 1) = 2 * (K : Real) := Classical.choose_spec heven
  have hW := Polynomial.reciprocalSevenDenominator_pos k
  have hWsq : 0 < (Polynomial.reciprocalSevenDenominator k) ^ 2 := pow_pos hW 2
  have hcancel : (16 * C / (Polynomial.reciprocalSevenDenominator k) ^ 2) *
      (Polynomial.reciprocalSevenDenominator k) ^ 2 = 16 * C := by
    field_simp [pow_ne_zero 2 hW.ne']
  have hprec : 16 * C / (Polynomial.reciprocalSevenDenominator k) ^ 2 <
      (1 / 2 : Real) := by
    by_contra hn
    have hm := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hWsq.le
    rw [hcancel] at hm
    linarith only [hm, hprecision]
  have he := primePrefixSevenTransport_exact_error k e t n C ht hC0 hC hcost
  rw [hK] at he
  have herror : 2 * (K : Real) - primePrefixSevenTransport k e n < (1 / 2 : Real) :=
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

/-- A closed integer-log order preserves the same half-unit combined-noise allowance. -/
theorem primePrefixSevenTransport_noisy_readout
    (e : Equiv.Perm Nat) (t : Nat -> Real) (n : Nat) (C : Real)
    (ht : 0 < t n) (hC0 : 0 <= C)
    (hp3 : (3 : Real) <= PrimeFactorUnimodality.primeAt n)
    (hC : C < (PrimeFactorUnimodality.primeAt n : Real) / 4)
    (hcost : normalizedPrimePrefixDefect e t n <= C) :
    let k : Nat := Nat.log 49 (8 * PrimeFactorUnimodality.primeAt n) + 1
    exists K : Nat,
      Finset.prefixDefect (fun j => (PrimeFactorUnimodality.primeAt j : Real))
        e (n + 1) = 2 * (K : Real) /\
      (forall y : Real, abs (y - primePrefixSevenTransport k e n) < (1 / 2 : Real) ->
        abs (y - 2 * (K : Real)) < 1 /\
        (forall j : Nat, abs (y - 2 * (j : Real)) < 1 -> j = K)) := by
  let r : Real := PrimeFactorUnimodality.primeAt n
  let k : Nat := Nat.log 49 (8 * PrimeFactorUnimodality.primeAt n) + 1
  have hdNat : 8 * PrimeFactorUnimodality.primeAt n <
      49 ^ (Nat.log 49 (8 * PrimeFactorUnimodality.primeAt n) + 1) :=
    Nat.lt_pow_succ_log_self (by decide) (8 * PrimeFactorUnimodality.primeAt n)
  have hd : 8 * r < (49 : Real) ^ k := by
    dsimp only [r, k]
    exact_mod_cast hdNat
  have hW := Polynomial.reciprocalSevenDenominator_pos k
  have hmajor : (7 : Real) ^ k <= Polynomial.reciprocalSevenDenominator k := by
    dsimp only [Polynomial.reciprocalSevenDenominator]
    have hp : 0 <= (1 / 7 : Real) ^ k := by positivity
    linarith only [hp]
  have hsq : ((7 : Real) ^ k) ^ 2 <= (Polynomial.reciprocalSevenDenominator k) ^ 2 := by
    have hp : 0 <= (7 : Real) ^ k := by positivity
    nlinarith only [hmajor, hp, hW]
  have hid : ((7 : Real) ^ k) ^ 2 = (49 : Real) ^ k := by
    rw [<- pow_mul, Nat.mul_comm k 2, pow_mul]
    norm_num
  rw [hid] at hsq
  have hprecision : 32 * C < (Polynomial.reciprocalSevenDenominator k) ^ 2 := by
    have hbudget : 32 * C < 8 * r := by linarith only [hC]
    exact hbudget.trans (hd.trans_le hsq)
  exact primePrefixSevenTransport_exact_noisy_readout k e t n C ht hC0 hp3 hC hcost hprecision

end PrimeFactorOscillations.PrimeProfileRigidity
