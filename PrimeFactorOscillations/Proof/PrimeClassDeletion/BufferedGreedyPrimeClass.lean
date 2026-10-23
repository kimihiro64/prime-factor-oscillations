/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.BufferedPrimeClass
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyClockTermination

/-!
# Buffered greedy prime classes and their exact finiteness criterion

The complement mass is coupled to the complete theta excess before
the stopping criterion is applied. A nonnegative monotone buffer gives
the advertised capacity. Finiteness is equivalent to bounded excess
for arbitrary buffers, without any zero-free or RH hypothesis.
-/

set_option autoImplicit false
set_option Elab.async false

open PrimeFactorUnimodality
open PrimeFactorOscillations.PrimeClassSampling

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def bufferedPrimeIndices (B : Nat -> Real) : Nat -> Prop :=
  greedySelection primeLogWeight (fun i => (primeAt i : Real) + B (primeAt i))

noncomputable def bufferedGreedyPrimeClass (B : Nat -> Real) : Set Nat :=
  fun p => And (Nat.Prime p) (bufferedPrimeIndices B (Nat.count Nat.Prime p))

noncomputable def bufferedGreedyDeletedPrimeClass (B : Nat -> Real) : Set Nat :=
  fun p => And (Nat.Prime p) (Not (bufferedPrimeIndices B (Nat.count Nat.Prime p)))

noncomputable def bufferedPrimeClockError (B : Nat -> Real) (n : Nat) : Real :=
  primeClockError n - B (primeAt n)

theorem classPrimeIndices_bufferedGreedyPrimeClass (B : Nat -> Real) :
    classPrimeIndices (bufferedGreedyPrimeClass B) = bufferedPrimeIndices B := by
  funext i
  apply propext
  change And (Nat.Prime (primeAt i))
    (bufferedPrimeIndices B (Nat.count Nat.Prime (primeAt i))) <-> bufferedPrimeIndices B i
  rw [primeCount_primeAt]
  exact and_iff_right (prime_primeAt i)

theorem classPrimeIndices_bufferedGreedyDeletedPrimeClass (B : Nat -> Real) :
    classPrimeIndices (bufferedGreedyDeletedPrimeClass B) =
      fun i => Not (bufferedPrimeIndices B i) := by
  funext i
  apply propext
  change And (Nat.Prime (primeAt i))
    (Not (bufferedPrimeIndices B (Nat.count Nat.Prime (primeAt i)))) <->
      Not (bufferedPrimeIndices B i)
  rw [primeCount_primeAt]
  exact and_iff_right (prime_primeAt i)

theorem bufferedPrimeDeletedMass_eq_clock (B : Nat -> Real) (n : Nat) :
    selectionCost (fun i => Not (bufferedPrimeIndices B i)) primeLogWeight n =
      clockDeletedMass (bufferedPrimeClockError B) primeLogWeight n := by
  classical
  induction n with
  | zero => rfl
  | succ n ih =>
      have hTotal :
          greedySelectionCost primeLogWeight
              (fun i => (primeAt i : Real) + B (primeAt i)) n +
            selectionCost (fun i => Not (bufferedPrimeIndices B i)) primeLogWeight n =
              primeFullPrefixCost n := by
        simpa only [bufferedPrimeIndices, selectionCost_greedySelection, primeFullPrefixCost]
          using selectionCost_add_complement (bufferedPrimeIndices B) primeLogWeight n
      have hTest :
          bufferedPrimeClockError B n <=
              selectionCost (fun i => Not (bufferedPrimeIndices B i)) primeLogWeight n <->
            bufferedPrimeIndices B n := by
        change primeFullPrefixCost (n + 1) - (primeAt n : Real) - B (primeAt n) <=
          selectionCost (fun i => Not (bufferedPrimeIndices B i)) primeLogWeight n <->
          greedySelectionCost primeLogWeight
              (fun i => (primeAt i : Real) + B (primeAt i)) n + primeLogWeight n <=
            (primeAt n : Real) + B (primeAt n)
        rw [primeFullPrefixCost_succ]
        constructor <;> intro h <;> linarith only [hTotal, h]
      simp only [selectionCost, clockDeletedMass]
      rw [<- ih]
      unfold deletionStep
      by_cases h : bufferedPrimeIndices B n
      case pos =>
        have he := hTest.mpr h
        simp only [h, not_true_eq_false, ite_false, ite_eq_left he, add_zero]
      case neg =>
        have he : Not (bufferedPrimeClockError B n <=
            selectionCost (fun i => Not (bufferedPrimeIndices B i)) primeLogWeight n) :=
          fun he => h (hTest.mp he)
        simp only [ite_eq_left h, ite_eq_right he]

theorem bufferedPrimeIndices_iff_clock_accept (B : Nat -> Real) (n : Nat) :
    bufferedPrimeIndices B n <->
      bufferedPrimeClockError B n <=
        clockDeletedMass (bufferedPrimeClockError B) primeLogWeight n := by
  have hTotal := selectionCost_add_complement (bufferedPrimeIndices B) primeLogWeight n
  rw [bufferedPrimeDeletedMass_eq_clock] at hTotal
  have hKeep : selectionCost (bufferedPrimeIndices B) primeLogWeight n =
      greedySelectionCost primeLogWeight
        (fun i => (primeAt i : Real) + B (primeAt i)) n :=
    selectionCost_greedySelection _ _ _
  rw [hKeep] at hTotal
  change _ + _ = primeFullPrefixCost n at hTotal
  change greedySelectionCost primeLogWeight
      (fun i => (primeAt i : Real) + B (primeAt i)) n + primeLogWeight n <=
      (primeAt n : Real) + B (primeAt n) <->
    primeFullPrefixCost (n + 1) - (primeAt n : Real) - B (primeAt n) <= _
  rw [primeFullPrefixCost_succ]
  constructor <;> intro h <;> linarith only [hTotal, h]

theorem clockRejected_bufferedPrimeClockError (B : Nat -> Real) :
    clockRejected (bufferedPrimeClockError B) primeLogWeight =
      fun i => Not (bufferedPrimeIndices B i) := by
  funext i
  apply propext
  change Not (bufferedPrimeClockError B i <=
    clockDeletedMass (bufferedPrimeClockError B) primeLogWeight i) <->
      Not (bufferedPrimeIndices B i)
  exact not_congr (bufferedPrimeIndices_iff_clock_accept B i).symm

theorem greedySelectionCost_le_monotone_capacity (w b : Nat -> Real)
    (hb : Monotone b) (hb0 : 0 <= b 0) (n : Nat) :
    greedySelectionCost w b (n + 1) <= b n := by
  classical
  induction n with
  | zero =>
      change (if 0 + w 0 <= b 0 then 0 + w 0 else 0) <= b 0
      split_ifs with h
      case pos => exact h
      case neg => exact hb0
  | succ n ih =>
      change (if greedySelectionCost w b (n + 1) + w (n + 1) <= b (n + 1)
        then greedySelectionCost w b (n + 1) + w (n + 1)
        else greedySelectionCost w b (n + 1)) <= b (n + 1)
      split_ifs with h
      case pos => exact h
      case neg => exact ih.trans (hb (Nat.le_succ n))

theorem bufferedGreedyPrimeClass_theta_le
    (B : Nat -> Real) (hB : Monotone B) (hB0 : forall n, 0 <= B n) (X : Nat) :
    primeClassTheta (bufferedGreedyPrimeClass B) X <= (X : Real) + B X := by
  have hCapacity : Monotone (fun i => (primeAt i : Real) + B (primeAt i)) := by
    intro i j hij
    have hp := primeAt_strictMono.monotone hij
    exact add_le_add (Nat.cast_le.mpr hp) (hB hp)
  have hInitial : 0 <= (primeAt 0 : Real) + B (primeAt 0) :=
    add_nonneg (Nat.cast_nonneg _) (hB0 _)
  unfold primeClassTheta
  rw [primeClassPrefix_logSum_eq_selectionCost, classPrimeIndices_bufferedGreedyPrimeClass,
    show selectionCost (bufferedPrimeIndices B) primeLogWeight (primeCutoffLength X) =
      greedySelectionCost primeLogWeight
        (fun i => (primeAt i : Real) + B (primeAt i)) (primeCutoffLength X) from
      selectionCost_greedySelection _ _ _]
  cases hN : primeCutoffLength X with
  | zero =>
      exact add_nonneg (Nat.cast_nonneg X) (hB0 X)
  | succ n =>
      have hp : primeAt n <= X := (primeAt_le_cutoff_iff n X).mpr (by
        rw [hN]
        exact Nat.lt_succ_self n)
      exact (greedySelectionCost_le_monotone_capacity primeLogWeight
        (fun i => (primeAt i : Real) + B (primeAt i)) hCapacity hInitial n).trans
          (add_le_add (Nat.cast_le.mpr hp) (hB hp))

theorem bufferedGreedyDeletedPrimeClass_count_le_excess_bound
    (B : Nat -> Real) (X : Nat) (C : Real) (hC : 0 <= C)
    (he : forall p : Nat, Nat.Prime p -> p <= X ->
      primeClassTheta Set.univ p - (p : Real) - B p <= C) :
    ((primeClassPrefix (bufferedGreedyDeletedPrimeClass B) X).card : Real) *
      Real.log 2 <= C + Real.log 2 := by
  rw [primeClassPrefix_card_eq_selectionCount,
    classPrimeIndices_bufferedGreedyDeletedPrimeClass,
    <- clockRejected_bufferedPrimeClockError]
  have hWeight : forall n, Real.log 2 <= primeLogWeight n := by
    intro n
    change Real.log 2 <= Real.log (primeAt n : Real)
    exact Real.log_le_log (by norm_num) (Nat.cast_le.mpr (prime_primeAt n).two_le)
  apply clockRejected_count_le_prefix_bound
    (bufferedPrimeClockError B) primeLogWeight (Real.log 2) C
    (Real.log_nonneg (by norm_num)) hC hWeight
  intro i hi
  change primeClockError i - B (primeAt i) <= C
  rw [primeClockError_eq_theta]
  exact he (primeAt i) (prime_primeAt i) ((primeAt_le_cutoff_iff i X).mpr hi)

theorem bufferedPrimeIndices_eventually_all_iff_bounded_excess (B : Nat -> Real) :
    (Exists fun N : Nat => forall n, N <= n -> bufferedPrimeIndices B n) <->
      (Exists fun C : Real => And (0 <= C)
        (forall n, primeClockError n <= B (primeAt n) + C)) := by
  classical
  have hWeight : forall n, Real.log 2 <= primeLogWeight n := by
    intro n
    change Real.log 2 <= Real.log (primeAt n : Real)
    exact Real.log_le_log (by norm_num) (Nat.cast_le.mpr (prime_primeAt n).two_le)
  have hTerm := greedyClock_eventually_no_rejections_iff_bounded_excess
    (bufferedPrimeClockError B) primeLogWeight (Real.log 2)
    (Real.log_pos (by norm_num)) hWeight
  constructor
  case mp =>
    intro h
    choose N hN using h
    have hNo : Exists fun N : Nat => forall n, N <= n ->
        Not (clockRejected (bufferedPrimeClockError B) primeLogWeight n) := by
      refine Exists.intro N ?_
      intro n hn
      have hAccept := (bufferedPrimeIndices_iff_clock_accept B n).mp (hN n hn)
      exact not_not.mpr hAccept
    choose C hC he using hTerm.mp hNo
    refine Exists.intro C (And.intro hC ?_)
    intro n
    have h := he n
    change primeClockError n - B (primeAt n) <= C at h
    linarith only [h]
  case mpr =>
    intro h
    choose C hC he using h
    have hBound : Exists fun C : Real => And (0 <= C)
        (forall n, bufferedPrimeClockError B n <= C) := by
      refine Exists.intro C (And.intro hC ?_)
      intro n
      change primeClockError n - B (primeAt n) <= C
      linarith only [he n]
    choose N hN using hTerm.mpr hBound
    refine Exists.intro N ?_
    intro n hn
    apply (bufferedPrimeIndices_iff_clock_accept B n).mpr
    exact not_not.mp (hN n hn)

theorem primeAt_ge_index (n : Nat) : n <= primeAt n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
      have h := primeAt_strictMono (Nat.lt_succ_self n)
      exact (Nat.succ_le_succ ih).trans (Nat.succ_le_of_lt h)

theorem bufferedGreedyDeletedPrimeClass_finite_iff_eventual_accept
    (B : Nat -> Real) :
    Set.Finite (bufferedGreedyDeletedPrimeClass B) <->
      (Exists fun N : Nat => forall n, N <= n -> bufferedPrimeIndices B n) := by
  classical
  constructor
  case mp =>
    intro hFinite
    choose M hM using hFinite.bddAbove
    refine Exists.intro (M + 1) ?_
    intro n hn
    by_contra hReject
    have hMember : Membership.mem (bufferedGreedyDeletedPrimeClass B) (primeAt n) := by
      change And (Nat.Prime (primeAt n))
        (Not (bufferedPrimeIndices B (Nat.count Nat.Prime (primeAt n))))
      rw [primeCount_primeAt]
      exact And.intro (prime_primeAt n) hReject
    have hUpper := hM hMember
    have hLower := primeAt_ge_index n
    omega
  case mpr =>
    intro h
    choose N hN using h
    apply (Finset.finite_toSet ((Finset.range N).image primeAt)).subset
    intro p hp
    have hPrime : Nat.Prime p := hp.1
    let i := Nat.count Nat.Prime p
    have hi : i < N := by
      by_contra hFail
      have hAccept := hN i (le_of_not_gt hFail)
      exact hp.2 hAccept
    have hEq : primeAt i = p := primeAt_count_prime p hPrime
    exact Finset.mem_image.mpr
      (Exists.intro i (And.intro (Finset.mem_range.mpr hi) hEq))

theorem bufferedGreedyDeletedPrimeClass_finite_iff_bounded_excess
    (B : Nat -> Real) :
    Set.Finite (bufferedGreedyDeletedPrimeClass B) <->
      (Exists fun C : Real => And (0 <= C)
        (forall n, primeClockError n <= B (primeAt n) + C)) := by
  exact (bufferedGreedyDeletedPrimeClass_finite_iff_eventual_accept B).trans
    (bufferedPrimeIndices_eventually_all_iff_bounded_excess B)

end PrimeFactorOscillations.PrimeClassDeletion
