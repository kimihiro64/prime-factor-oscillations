/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimePrefixClockContinuity

/-!
# Signed root brackets at consecutive prime prefixes

The exact one-prime increment and uniform coefficient sign tests bound
the reference root between the two neighboring logarithmic clocks.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Filter

theorem primeProfilePrefixSet_next_prime (i : Nat) :
    primeProfilePrefixSet (PrimeFactorUnimodality.primeAt (i + 1) - 1) =
      @insert Nat.Primes (Finset Nat.Primes) inferInstance
        (Subtype.mk (PrimeFactorUnimodality.primeAt i)
        (PrimeFactorUnimodality.prime_primeAt i))
        (primeProfilePrefixSet (PrimeFactorUnimodality.primeAt i - 1)) := by
  classical
  let p := PrimeFactorUnimodality.primeAt i
  let q := PrimeFactorUnimodality.primeAt (i + 1)
  have hp2 := (PrimeFactorUnimodality.prime_primeAt i).two_le
  have hq2 := (PrimeFactorUnimodality.prime_primeAt (i + 1)).two_le
  have hpq : p < q := PrimeFactorUnimodality.primeAt_strictMono (Nat.lt_succ_self i)
  ext a
  have hm (N : Nat) := mem_primeProfilePrefixSet a N
  have hi : (a = (Subtype.mk (PrimeFactorUnimodality.primeAt i)
      (PrimeFactorUnimodality.prime_primeAt i) : Nat.Primes) \/
      Membership.mem (primeProfilePrefixSet (PrimeFactorUnimodality.primeAt i - 1)) a) <->
      Membership.mem (@insert Nat.Primes (Finset Nat.Primes) inferInstance
        (Subtype.mk (PrimeFactorUnimodality.primeAt i)
          (PrimeFactorUnimodality.prime_primeAt i))
        (primeProfilePrefixSet (PrimeFactorUnimodality.primeAt i - 1))) a :=
    Finset.mem_insert.symm
  apply (hm _).trans
  apply Iff.trans _ hi
  rw [hm]
  constructor
  . intro ha
    by_cases hap : (a : Nat) < p
    . exact Or.inr (by dsimp [p] at hap; omega)
    . have hap' : p <= (a : Nat) := Nat.le_of_not_gt hap
      let j := Nat.count Nat.Prime (a : Nat)
      have hj : PrimeFactorUnimodality.primeAt j = (a : Nat) := Nat.nth_count a.property
      have hij : i <= j := by
        by_contra h
        have hlt := PrimeFactorUnimodality.primeAt_strictMono (Nat.lt_of_not_ge h)
        rw [hj] at hlt
        exact not_lt_of_ge hap' hlt
      have hji : j <= i := by
        by_contra h
        have hle := PrimeFactorUnimodality.primeAt_strictMono.monotone
          (show i + 1 <= j by omega)
        rw [hj] at hle
        dsimp [q] at *
        omega
      have heq : j = i := le_antisymm hji hij
      left
      apply Subtype.ext
      simpa only [heq] using hj.symm
  . intro ha
    rcases ha with ha | ha
    . have hv := congrArg (fun a : Nat.Primes => (a : Nat)) ha
      simp only [Subtype.coe_mk] at hv
      rw [hv]
      exact Nat.le_pred_of_lt hpq
    . dsimp [p, q] at hpq
      omega

theorem primePrefixLogSum_prime_step (i : Nat) :
    primePrefixLogSum (PrimeFactorUnimodality.primeAt (i + 1) - 1) -
      primePrefixLogSum (PrimeFactorUnimodality.primeAt i - 1) =
        Real.log (1 + primeProfileWeight (PrimeFactorUnimodality.primeAt i)) := by
  classical
  let p : Nat.Primes := Subtype.mk (PrimeFactorUnimodality.primeAt i)
    (PrimeFactorUnimodality.prime_primeAt i)
  have hnot : Not (Membership.mem
      (primeProfilePrefixSet (PrimeFactorUnimodality.primeAt i - 1)) p) := by
    rw [mem_primeProfilePrefixSet]
    have hpos := (PrimeFactorUnimodality.prime_primeAt i).pos
    dsimp [p]
    omega
  unfold primePrefixLogSum
  rw [primeProfilePrefixSet_next_prime, Finset.sum_insert hnot]
  ring

theorem primePrefixLogSum_prime_step_bounds (i : Nat) :
    0 <= primePrefixLogSum (PrimeFactorUnimodality.primeAt (i + 1) - 1) -
      primePrefixLogSum (PrimeFactorUnimodality.primeAt i - 1) /\
    primePrefixLogSum (PrimeFactorUnimodality.primeAt (i + 1) - 1) -
      primePrefixLogSum (PrimeFactorUnimodality.primeAt i - 1) <=
        1 / ((PrimeFactorUnimodality.primeAt i - 1 : Nat) : Real) := by
  rw [primePrefixLogSum_prime_step]
  have hw := primeProfileWeight_nonneg (PrimeFactorUnimodality.primeAt i)
  refine And.intro (Real.log_nonneg (by linarith)) ?_
  have h := Real.log_le_sub_one_of_pos
    (by linarith : 0 < 1 + primeProfileWeight (PrimeFactorUnimodality.primeAt i))
  simpa only [add_sub_cancel_left, primeProfileWeight] using h

theorem exists_primePrefix_cutoff_clock_bracket (a b : Real) (ha : 0 < a) (hab : a <= b) :
    exists r0 N0 : Nat, exists K : Real, 0 < r0 /\ 1 <= N0 /\ 0 < K /\
      forall r i : Nat, r0 <= r -> N0 <= PrimeFactorUnimodality.primeAt i - 1 ->
      forall u s : Real,
      (forall j : Nat, j = i \/ j = i + 1 ->
        forall v : Real, Set.Icc
          (min (primePrefixLogSum (PrimeFactorUnimodality.primeAt j - 1)) u)
          (max (primePrefixLogSum (PrimeFactorUnimodality.primeAt j - 1)) u) v ->
          0 < v /\ a <= (r : Real) / v /\ (r : Real) / v <= b) ->
      Nat.factorialConvolution primeProfileRealCoefficient (r - 1) u /
        Nat.factorialConvolution primeProfileRealCoefficient r u = s ->
      s < (PrimeFactorUnimodality.densityRatio
        (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt i)) r : Real) ->
      (PrimeFactorUnimodality.densityRatio
        (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt (i + 1))) r : Real) <= s ->
      abs (primePrefixLogSum (PrimeFactorUnimodality.primeAt i - 1) - u) <=
        K / ((PrimeFactorUnimodality.primeAt i - 1 : Nat) : Real) := by
  choose r0 N0 C hr0 hN0 hC hSign using exists_primePrefixProfile_clock_sign_transfer a b ha hab
  refine Exists.intro r0 (Exists.intro N0 (Exists.intro (C + 1)
    (And.intro hr0 (And.intro hN0 (And.intro (by linarith) ?_)))))
  intro r i hr hn u s hBand hRoot hBefore hAfter
  let N := PrimeFactorUnimodality.primeAt i - 1
  let M := PrimeFactorUnimodality.primeAt (i + 1) - 1
  let B := primePrefixLogSum N
  let D := primePrefixLogSum M
  have hNM : N <= M := Nat.sub_le_sub_right
    (PrimeFactorUnimodality.primeAt_strictMono.monotone (Nat.le_succ i)) 1
  have hNr : (0 : Real) < N := by exact_mod_cast (show 0 < N by omega)
  have hMr : (0 : Real) < M := hNr.trans_le (by exact_mod_cast hNM)
  have hCScale : C / (M : Real) <= C / (N : Real) :=
    div_le_div_of_nonneg_left hC hNr (by exact_mod_cast hNM)
  have hNatural (j : Nat) : j = i \/ j = i + 1 ->
      (PrimeFactorUnimodality.densityRatio
        (PrimeFactorUnimodality.primesBelow (PrimeFactorUnimodality.primeAt j)) r : Real) =
      Nat.factorialConvolution
        (fun k => (BombieriVinogradov.ComplexAnalysis.taylorCoefficient
          (primePrefixProfile (PrimeFactorUnimodality.primeAt j - 1)) 0 k).re) (r - 1)
          (primePrefixLogSum (PrimeFactorUnimodality.primeAt j - 1)) /
      Nat.factorialConvolution
        (fun k => (BombieriVinogradov.ComplexAnalysis.taylorCoefficient
          (primePrefixProfile (PrimeFactorUnimodality.primeAt j - 1)) 0 k).re) r
          (primePrefixLogSum (PrimeFactorUnimodality.primeAt j - 1)) := by
    intro hj
    have hp := (PrimeFactorUnimodality.prime_primeAt j).one_lt.le
    simpa only [Nat.sub_add_cancel hp, primePrefixLogSum] using
      densityRatio_eq_primePrefixProfile_factorialConvolution
        (PrimeFactorUnimodality.primeAt j - 1) r
  have hFirst := hSign r hr N hn B u (hBand i (Or.inl rfl))
  have hSecond := hSign r hr M (hn.trans hNM) D u (hBand (i + 1) (Or.inr rfl))
  have hLeft : B - u <= C / (N : Real) := by
    by_contra hn'
    have hh := hFirst.2.2.2 (by
      rw [neg_div]
      linarith [lt_of_not_ge hn'] : u - B < -C / (N : Real))
    rw [hRoot, <- hNatural i (Or.inl rfl)] at hh
    exact not_lt_of_ge hh.le hBefore
  have hRight : u - D <= C / (M : Real) := by
    by_contra hn'
    have hh := hSecond.2.2.1 (lt_of_not_ge hn')
    rw [hRoot, <- hNatural (i + 1) (Or.inr rfl)] at hh
    exact not_lt_of_ge hAfter hh
  have hStep : D - B <= 1 / (N : Real) := (primePrefixLogSum_prime_step_bounds i).2
  have hDivide : (C + 1) / (N : Real) = C / (N : Real) + 1 / (N : Real) := by ring
  rw [hDivide]
  apply abs_le.mpr
  have hi : 0 <= 1 / (N : Real) := by positivity
  constructor <;> linarith

end PrimeFactorOscillations
