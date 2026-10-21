/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyPrimeClass
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyRegulator

/-!
# The actual greedy prime mass and its exact record regulator

The complement cost is coupled to the retained cost before the actual
rejection test is converted to the clock recursion. The final bound uses
the last included prime weight, rather than the next prime's logarithm.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open PrimeFactorUnimodality
open PrimeFactorOscillations.PrimeClassSampling

theorem selectionCost_add_complement (a : Nat -> Prop) (w : Nat -> Real) (n : Nat) :
    selectionCost a w n + selectionCost (fun i => Not (a i)) w n =
      selectionCost (fun _ => True) w n := by
  classical
  induction n with
  | zero => simp only [selectionCost, zero_add]
  | succ n ih =>
      by_cases h : a n
      all_goals (simp [selectionCost, h]; linarith only [ih])

noncomputable def primeFullPrefixCost (n : Nat) : Real :=
  selectionCost (fun _ => True) primeLogWeight n

noncomputable def primeClockError (n : Nat) : Real :=
  primeFullPrefixCost (n + 1) - (primeAt n : Real)

noncomputable def greedyPrimeRegulator (X : Nat) : Real :=
  clockRecord primeClockError (primeCutoffLength X)

theorem primeFullPrefixCost_succ (n : Nat) :
    primeFullPrefixCost (n + 1) = primeFullPrefixCost n + primeLogWeight n := by
  simp only [primeFullPrefixCost, selectionCost, ite_true]

theorem primeClassTheta_univ_at_primeAt (n : Nat) :
    primeClassTheta Set.univ (primeAt n) = primeFullPrefixCost (n + 1) := by
  unfold primeClassTheta
  rw [primeClassPrefix_logSum_eq_selectionCost]
  have hlength : primeCutoffLength (primeAt n) = n + 1 :=
    Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime n
  rw [hlength]
  rfl

theorem primeClockError_eq_theta (n : Nat) :
    primeClockError n = primeClassTheta Set.univ (primeAt n) - (primeAt n : Real) := by
  rw [primeClassTheta_univ_at_primeAt]
  rfl

theorem greedyPrimeDeletedMass_eq_clock (n : Nat) :
    selectionCost (fun i => Not (greedyPrimeIndices i)) primeLogWeight n =
      clockDeletedMass primeClockError primeLogWeight n := by
  classical
  induction n with
  | zero => rfl
  | succ n ih =>
      have htotal :
          greedySelectionCost primeLogWeight (fun i => (primeAt i : Real)) n +
            selectionCost (fun i => Not (greedyPrimeIndices i)) primeLogWeight n =
              primeFullPrefixCost n := by
        simpa only [greedyPrimeIndices, selectionCost_greedySelection, primeFullPrefixCost] using
          selectionCost_add_complement greedyPrimeIndices primeLogWeight n
      have htest :
          primeClockError n <=
              selectionCost (fun i => Not (greedyPrimeIndices i)) primeLogWeight n <->
            greedyPrimeIndices n := by
        change primeFullPrefixCost (n + 1) - (primeAt n : Real) <=
          selectionCost (fun i => Not (greedyPrimeIndices i)) primeLogWeight n <->
          greedySelectionCost primeLogWeight (fun i => (primeAt i : Real)) n +
            primeLogWeight n <= (primeAt n : Real)
        rw [primeFullPrefixCost_succ]
        constructor <;> intro h <;> linarith only [htotal, h]
      simp only [selectionCost, clockDeletedMass]
      rw [<- ih]
      unfold deletionStep
      by_cases hg : greedyPrimeIndices n
      case pos =>
        have he := htest.mpr hg
        simp only [hg, not_true_eq_false, ite_false, ite_eq_left he, add_zero]
      case neg =>
        have he : Not (primeClockError n <=
            selectionCost (fun i => Not (greedyPrimeIndices i)) primeLogWeight n) :=
          fun h => hg (htest.mp h)
        simp only [ite_eq_left hg, ite_eq_right he]

theorem primeClockError_initial : primeClockError 0 <= primeLogWeight 0 := by
  have hp : (0 : Real) <= (primeAt 0 : Real) := Nat.cast_nonneg _
  simp only [primeClockError, primeFullPrefixCost, selectionCost, ite_true, zero_add]
  linarith only [hp]

theorem primeClockError_increment (n : Nat) :
    primeClockError (n + 1) <= primeClockError n + primeLogWeight (n + 1) := by
  have hp : (primeAt n : Real) <= (primeAt (n + 1) : Real) :=
    Nat.cast_le.mpr (primeAt_strictMono.monotone (Nat.le_succ n))
  unfold primeClockError
  rw [primeFullPrefixCost_succ (n + 1)]
  linarith only [hp]

theorem clockDeletedMass_record_bounds_sharp
    (e w : Nat -> Real) (hw0 : 0 <= w 0) (hw : Monotone w)
    (hinit : e 0 <= w 0)
    (hclock : forall n, e (n + 1) <= e n + w (n + 1)) (n : Nat) :
    And (clockRecord e (n + 1) <= clockDeletedMass e w (n + 1))
      (clockDeletedMass e w (n + 1) <= clockRecord e (n + 1) + w n) := by
  have hprefix := clockDeletedMass_record_bounds e w hw0 hw hinit hclock n
  have hpre : e n <= clockDeletedMass e w n + w n := by
    cases n with
    | zero => simpa only [clockDeletedMass, zero_add] using hinit
    | succ k =>
        have hc := hclock k
        have hr := (clockRecord_contains e k).trans hprefix.1
        linarith only [hc, hr]
  exact deletionStep_record_bounds (e n) (w n) (clockDeletedMass e w n)
    (clockRecord e n) hprefix.1 hprefix.2 hpre

theorem greedyDeletedPrimeClass_theta_eq_clock (X : Nat) :
    primeClassTheta greedyDeletedPrimeClass X =
      clockDeletedMass primeClockError primeLogWeight (primeCutoffLength X) := by
  unfold primeClassTheta
  rw [primeClassPrefix_logSum_eq_selectionCost, classPrimeIndices_greedyDeletedPrimeClass,
    greedyPrimeDeletedMass_eq_clock]

theorem greedyDeletedPrimeClass_record_bounds (X : Nat) (hX : 2 <= X) :
    And (greedyPrimeRegulator X <= primeClassTheta greedyDeletedPrimeClass X)
      (primeClassTheta greedyDeletedPrimeClass X <=
        greedyPrimeRegulator X + Real.log (X : Real)) := by
  rw [greedyDeletedPrimeClass_theta_eq_clock]
  unfold greedyPrimeRegulator
  cases hN : primeCutoffLength X with
  | zero =>
      have hlog : 0 <= Real.log (X : Real) := by
        apply Real.log_nonneg
        exact_mod_cast (show 1 <= X by omega)
      exact And.intro (le_refl 0) (by
        simpa only [clockDeletedMass, clockRecord, zero_add] using hlog)
  | succ n =>
      have hp : primeAt n <= X := (primeAt_le_cutoff_iff n X).mpr (by
        rw [hN]
        exact Nat.lt_succ_self n)
      have hw : primeLogWeight n <= Real.log (X : Real) :=
        Real.log_le_log (Nat.cast_pos.mpr (prime_primeAt n).pos) (Nat.cast_le.mpr hp)
      have hsharp := clockDeletedMass_record_bounds_sharp primeClockError primeLogWeight
        (primeLogWeight_nonneg 0) primeLogWeight_monotone primeClockError_initial
        primeClockError_increment n
      exact And.intro hsharp.1 (by linarith only [hsharp.2, hw])

theorem selectionCost_monotone_of_nonneg (a : Nat -> Prop) (w : Nat -> Real)
    (hw : forall i, 0 <= w i) : Monotone (selectionCost a w) := by
  classical
  apply monotone_nat_of_le_succ
  intro n
  simp only [selectionCost]
  by_cases ha : a n
  case pos =>
    rw [ite_eq_left ha]
    linarith only [hw n]
  case neg => simp only [ite_eq_right ha, add_zero, le_refl]

theorem clockRecord_le_of_bounds (e : Nat -> Real) (n : Nat) (c : Real)
    (hc : 0 <= c) (he : forall i, i < n -> e i <= c) : clockRecord e n <= c := by
  revert he
  induction n with
  | zero => intro _; exact hc
  | succ n ih =>
      intro he
      exact max_le (ih (fun i hi => he i (hi.trans (Nat.lt_succ_self n))))
        (he n (Nat.lt_succ_self n))

theorem clockRecord_attained (e : Nat -> Real) (n : Nat) :
    Or (clockRecord e n = 0)
      (exists i : Nat, And (i < n) (clockRecord e n = e i)) := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
      by_cases h : clockRecord e n <= e n
      case pos =>
        exact Or.inr (Exists.intro n (And.intro (Nat.lt_succ_self n)
          (by simp only [clockRecord, max_eq_right h])))
      case neg =>
        have hmax : max (clockRecord e n) (e n) = clockRecord e n :=
          max_eq_left (le_of_lt (lt_of_not_ge h))
        cases ih with
        | inl hz => exact Or.inl (by simpa only [clockRecord, hmax] using hz)
        | inr hi =>
            choose i hi using hi
            exact Or.inr (Exists.intro i (And.intro (hi.1.trans (Nat.lt_succ_self n))
              (by simpa only [clockRecord, hmax] using hi.2)))

theorem primeClassTheta_complement_sum (P : Set Nat) (X : Nat) :
    primeClassTheta P X + primeClassTheta (fun p => Not (Membership.mem P p)) X =
      primeClassTheta Set.univ X := by
  unfold primeClassTheta
  rw [primeClassPrefix_logSum_eq_selectionCost P X,
    primeClassPrefix_logSum_eq_selectionCost (fun p => Not (Membership.mem P p)) X,
    primeClassPrefix_logSum_eq_selectionCost Set.univ X]
  exact selectionCost_add_complement (classPrimeIndices P) primeLogWeight (primeCutoffLength X)

theorem greedyPrimeClass_theta_partition (X : Nat) :
    primeClassTheta greedyPrimeClass X + primeClassTheta greedyDeletedPrimeClass X =
      primeClassTheta Set.univ X := by
  unfold primeClassTheta
  rw [primeClassPrefix_logSum_eq_selectionCost greedyPrimeClass X,
    primeClassPrefix_logSum_eq_selectionCost greedyDeletedPrimeClass X,
    primeClassPrefix_logSum_eq_selectionCost Set.univ X,
    classPrimeIndices_greedyPrimeClass, classPrimeIndices_greedyDeletedPrimeClass]
  exact selectionCost_add_complement greedyPrimeIndices primeLogWeight (primeCutoffLength X)

theorem primeClass_complementMass_dominates_record
    (P : Set Nat) (hP : forall X : Nat, primeClassTheta P X <= (X : Real)) (X : Nat) :
    greedyPrimeRegulator X <= primeClassTheta (fun p => Not (Membership.mem P p)) X := by
  have hmono := selectionCost_monotone_of_nonneg
    (fun i => Not (classPrimeIndices P i)) primeLogWeight primeLogWeight_nonneg
  have hrec : clockRecord primeClockError (primeCutoffLength X) <=
      selectionCost (fun i => Not (classPrimeIndices P i)) primeLogWeight (primeCutoffLength X) := by
    apply clockRecord_le_of_bounds
    case hc => simpa only [selectionCost] using hmono (Nat.zero_le (primeCutoffLength X))
    case he =>
      intro i hi
      have hcap := hP (primeAt i)
      have hlength : primeCutoffLength (primeAt i) = i + 1 :=
        Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime i
      unfold primeClassTheta at hcap
      rw [primeClassPrefix_logSum_eq_selectionCost P (primeAt i), hlength] at hcap
      have htotal := selectionCost_add_complement (classPrimeIndices P) primeLogWeight (i + 1)
      have he : primeClockError i <=
          selectionCost (fun j => Not (classPrimeIndices P j)) primeLogWeight (i + 1) := by
        unfold primeClockError primeFullPrefixCost
        linarith only [htotal, hcap]
      exact he.trans (hmono (Nat.succ_le_of_lt hi))
  unfold greedyPrimeRegulator primeClassTheta
  rw [primeClassPrefix_logSum_eq_selectionCost (fun p => Not (Membership.mem P p)) X]
  exact hrec

theorem greedyDeletedPrimeClass_mass_optimal
    (P : Set Nat) (hP : forall X : Nat, primeClassTheta P X <= (X : Real))
    (X : Nat) (hX : 2 <= X) :
    primeClassTheta greedyDeletedPrimeClass X <=
      primeClassTheta (fun p => Not (Membership.mem P p)) X + Real.log (X : Real) := by
  have hmass := (greedyDeletedPrimeClass_record_bounds X hX).2
  have hrecord := primeClass_complementMass_dominates_record P hP X
  linarith only [hmass, hrecord]

end PrimeFactorOscillations.PrimeClassDeletion
