/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Proof.PrimeClassDeletion.ClockRecordProduct
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeRecordIntegral

/-! # Full actual signed prime-record energy

The prime supply and the actual ordinary integral remain coupled.
The terminal correction is retained at every real cutoff and vanishes
only under the stated record condition. These are exact identities,
not an independent estimate for the signed energy.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

open Filter
open PrimeFactorUnimodality
open PrimeFactorOscillations.PrimeClassSampling

noncomputable def primeRecordPrimeSupply (x : Real) : Real :=
  (primeClassPrefix Set.univ (Nat.floor x)).sum
    (fun p => greedyPrimeRegulator (p - 1) * Real.log (p : Real))

noncomputable def primeRecordPositionJumps (x : Real) : Real :=
  (primeClassPrefix Set.univ (Nat.floor x)).sum
    (fun p => (p : Real) * primeRecordJump p)

noncomputable def primeRecordSignedEnergy (x : Real) : Real :=
  primeRecordPrimeSupply x -
    intervalIntegral greedyPrimeRegulatorReal 2 x MeasureTheory.volume

theorem greedyPrimeRegulator_before_primeAt (i : Nat) :
    greedyPrimeRegulator (primeAt i - 1) = clockRecord primeClockError i := by
  unfold greedyPrimeRegulator primeCutoffLength
  rw [Nat.sub_add_cancel (prime_primeAt i).one_lt.le, primeCount_primeAt]

theorem primeRecordPrimeSupply_eq_index (x : Real) :
    primeRecordPrimeSupply x =
      (Finset.range (primeCutoffLength (Nat.floor x))).sum
        (fun i => clockRecord primeClockError i * primeLogWeight i) := by
  rw [primeRecordPrimeSupply, primeFullPrefix_sum_eq_index]
  apply Finset.sum_congr rfl
  intro i _
  rw [greedyPrimeRegulator_before_primeAt]
  rfl

theorem primeRecordPositionJumps_eq_index (x : Real) :
    primeRecordPositionJumps x =
      (Finset.range (primeCutoffLength (Nat.floor x))).sum
        (fun i => (primeAt i : Real) * clockRecordIncrement primeClockError i) := by
  rw [primeRecordPositionJumps, primeFullPrefix_sum_eq_index]
  simp only [primeRecordJump, primeCount_primeAt]

theorem primeClassTheta_univ_eq_fullCost (X : Nat) :
    primeClassTheta Set.univ X = primeFullPrefixCost (primeCutoffLength X) := by
  unfold primeClassTheta
  rw [primeClassPrefix_logSum_eq_selectionCost]
  rfl

theorem primeRecord_product_ledger (x : Real) :
    greedyPrimeRegulatorReal x * primeClassThetaReal Set.univ x =
      primeRecordPrimeSupply x + primeRecordPositionJumps x +
        (Finset.range (primeCutoffLength (Nat.floor x))).sum
          (fun i => clockRecord primeClockError (i + 1) *
            clockRecordIncrement primeClockError i) := by
  let n := primeCutoffLength (Nat.floor x)
  have hsupply :
      (Finset.range n).sum
        (fun i => clockRecord primeClockError i *
          (primeFullPrefixCost (i + 1) - primeFullPrefixCost i)) =
        primeRecordPrimeSupply x := by
    rw [primeRecordPrimeSupply_eq_index]
    apply Finset.sum_congr rfl
    intro i _
    rw [primeFullPrefixCost_succ]
    ring
  have hsecond :
      (Finset.range n).sum
        (fun i => primeFullPrefixCost (i + 1) * clockRecordIncrement primeClockError i) =
      primeRecordPositionJumps x +
        (Finset.range n).sum
          (fun i => clockRecord primeClockError (i + 1) *
            clockRecordIncrement primeClockError i) := by
    rw [primeRecordPositionJumps_eq_index, <- Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hcomp := clockRecordIncrement_complementarity primeClockError i
    have heq : primeClockError i =
        primeFullPrefixCost (i + 1) - (primeAt i : Real) := rfl
    rw [heq] at hcomp
    nlinarith only [hcomp]
  have h := clockRecord_product_ledger primeClockError primeFullPrefixCost n
  rw [hsupply, hsecond] at h
  simpa only [greedyPrimeRegulatorReal, greedyPrimeRegulator, primeClassThetaReal,
    primeClassTheta_univ_eq_fullCost, add_assoc, n] using h

theorem greedyPrimeRegulatorReal_integral_signed (x : Real) (hx : 2 <= x) :
    intervalIntegral greedyPrimeRegulatorReal 2 x MeasureTheory.volume =
      x * greedyPrimeRegulatorReal x - primeRecordPositionJumps x := by
  classical
  calc
    intervalIntegral greedyPrimeRegulatorReal 2 x MeasureTheory.volume =
        (primeClassPrefix Set.univ (Nat.floor x)).sum
          (fun p => x * primeRecordJump p - (p : Real) * primeRecordJump p) := by
      rw [greedyPrimeRegulatorReal_integral x hx]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, <- Finset.mul_sum, primeRecordJump_sum]
      rfl

theorem primeRecordEnergy_identity (x : Real) (hx : 2 <= x) :
    (greedyPrimeRegulatorReal x) ^ 2 = 2 * primeRecordSignedEnergy x +
      2 * greedyPrimeRegulatorReal x *
        (greedyPrimeRegulatorReal x - (primeClassThetaReal Set.univ x - x)) +
          primeRecordQuadraticVariation x := by
  have hproduct := primeRecord_product_ledger x
  have hintegral := greedyPrimeRegulatorReal_integral_signed x hx
  have hjump := clockRecord_right_jump_energy primeClockError
    (primeCutoffLength (Nat.floor x))
  have hjump' :
      2 * (Finset.range (primeCutoffLength (Nat.floor x))).sum
          (fun i => clockRecord primeClockError (i + 1) *
            clockRecordIncrement primeClockError i) =
        (greedyPrimeRegulatorReal x) ^ 2 + primeRecordQuadraticVariation x := by
    simpa only [greedyPrimeRegulatorReal, greedyPrimeRegulator,
      primeRecordQuadraticVariation_eq_clock] using hjump
  unfold primeRecordSignedEnergy
  nlinarith only [hproduct, hintegral, hjump']

theorem primeRecordEnergy_at_record (x : Real) (hx : 2 <= x)
    (hrecord : greedyPrimeRegulatorReal x = primeClassThetaReal Set.univ x - x) :
    And ((greedyPrimeRegulatorReal x) ^ 2 =
      2 * primeRecordSignedEnergy x + primeRecordQuadraticVariation x)
      (And (0 <= primeRecordQuadraticVariation x)
        (primeRecordQuadraticVariation x <= greedyPrimeRegulatorReal x * Real.log x)) := by
  refine And.intro ?_ (primeRecordQuadraticVariation_bounds x hx)
  have h := primeRecordEnergy_identity x hx
  rw [<- hrecord] at h
  simpa only [sub_self, mul_zero, add_zero] using h

theorem greedyPrimeRegulator_at_primeAt (i : Nat) :
    greedyPrimeRegulator (primeAt i) = clockRecord primeClockError (i + 1) := by
  have h : primeCutoffLength (primeAt i) = i + 1 :=
    Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime i
  simp only [greedyPrimeRegulator, h]

theorem primeRecordRightJump_sum (x : Real) :
    (primeClassPrefix Set.univ (Nat.floor x)).sum
        (fun p => greedyPrimeRegulator p * primeRecordJump p) =
      (Finset.range (primeCutoffLength (Nat.floor x))).sum
        (fun i => clockRecord primeClockError (i + 1) *
          clockRecordIncrement primeClockError i) := by
  rw [primeFullPrefix_sum_eq_index]
  simp only [greedyPrimeRegulator_at_primeAt, primeRecordJump, primeCount_primeAt]

theorem primeRecord_error_product (x : Real) (hx : 2 <= x) :
    greedyPrimeRegulatorReal x * (primeClassThetaReal Set.univ x - x) =
      primeRecordSignedEnergy x +
        (primeClassPrefix Set.univ (Nat.floor x)).sum
          (fun p => greedyPrimeRegulator p * primeRecordJump p) := by
  rw [primeRecordRightJump_sum]
  have hproduct := primeRecord_product_ledger x
  have hintegral := greedyPrimeRegulatorReal_integral_signed x hx
  unfold primeRecordSignedEnergy
  nlinarith only [hproduct, hintegral]

theorem primeRecord_jump_energy (x : Real) :
    2 * (primeClassPrefix Set.univ (Nat.floor x)).sum
        (fun p => greedyPrimeRegulator p * primeRecordJump p) =
      (greedyPrimeRegulatorReal x) ^ 2 + primeRecordQuadraticVariation x := by
  rw [primeRecordRightJump_sum]
  simpa only [greedyPrimeRegulatorReal, greedyPrimeRegulator,
    primeRecordQuadraticVariation_eq_clock] using
      clockRecord_right_jump_energy primeClockError (primeCutoffLength (Nat.floor x))

noncomputable def primeRecordCenteredEnergy (y x : Real) : Real :=
  primeRecordSignedEnergy x - primeRecordSignedEnergy y -
    greedyPrimeRegulatorReal y *
      ((primeClassThetaReal Set.univ x - x) - (primeClassThetaReal Set.univ y - y))

theorem primeRecordCenteredEnergy_identity (y x : Real) (hy : 2 <= y) (hx : 2 <= x) :
    (greedyPrimeRegulatorReal x - greedyPrimeRegulatorReal y) ^ 2 =
      2 * primeRecordCenteredEnergy y x +
        2 * (greedyPrimeRegulatorReal x - greedyPrimeRegulatorReal y) *
          (greedyPrimeRegulatorReal x - (primeClassThetaReal Set.univ x - x)) +
        (primeRecordQuadraticVariation x - primeRecordQuadraticVariation y) := by
  have hnx := primeRecordEnergy_identity x hx
  have hny := primeRecordEnergy_identity y hy
  dsimp only [primeRecordCenteredEnergy]
  nlinarith only [hnx, hny]

theorem primeRecordCenteredEnergy_at_record
    (y x : Real) (hy : 2 <= y) (hx : 2 <= x)
    (hrecord : greedyPrimeRegulatorReal x = primeClassThetaReal Set.univ x - x) :
    (greedyPrimeRegulatorReal x - greedyPrimeRegulatorReal y) ^ 2 =
      2 * primeRecordCenteredEnergy y x +
        (primeRecordQuadraticVariation x - primeRecordQuadraticVariation y) := by
  have h := primeRecordCenteredEnergy_identity y x hy hx
  rw [<- hrecord] at h
  simpa only [sub_self, mul_zero, add_zero] using h

theorem greedyPrimeRegulator_balanced_records
    (hUnbounded : forall B : Real, Exists fun n : Nat => B < greedyPrimeRegulator n)
    (N : Nat) :
    Exists fun p : Nat => And (N <= p) (And (Nat.Prime p)
      (And (greedyPrimeRegulator (p - 1) < greedyPrimeRegulator p)
        (greedyPrimeRegulator p - Real.log (p : Real) <=
          2 * greedyPrimeRegulator (p / 2)))) := by
  have hr : Monotone greedyPrimeRegulator := by
    intro m n hmn
    have hn := (greedyPrimeRegulator_le_iff n (greedyPrimeRegulator n)).mp le_rfl
    apply (greedyPrimeRegulator_le_iff m (greedyPrimeRegulator n)).mpr
    exact And.intro hn.1 (fun p hp hpm => hn.2 p hp (hpm.trans hmn))
  have hSublinear : forall c : Real, 0 < c -> Exists fun M : Nat =>
      forall n : Nat, M <= n -> greedyPrimeRegulator n <= c * (n : Real) := by
    intro c hc
    have hEvent : Filter.Eventually (fun n : Nat =>
        primeClassTheta greedyDeletedPrimeClass n / (n : Real) < c) atTop :=
      greedyDeletedPrimeClass_mass_div_tendsto_zero.eventually (eventually_lt_nhds hc)
    choose M hM using eventually_atTop.mp hEvent
    apply Exists.intro (max M 2)
    intro n hn
    have hnTwo : 2 <= n := (le_max_right M 2).trans hn
    have hnPos : (0 : Real) < (n : Real) := by exact_mod_cast (by omega : 0 < n)
    have hRatio := hM n ((le_max_left M 2).trans hn)
    have hCancel : (primeClassTheta greedyDeletedPrimeClass n / (n : Real)) *
        (n : Real) = primeClassTheta greedyDeletedPrimeClass n := by
      field_simp [hnPos.ne']
    have hMass : primeClassTheta greedyDeletedPrimeClass n < c * (n : Real) := by
      have hScaled := mul_lt_mul_of_pos_right hRatio hnPos
      rw [hCancel] at hScaled
      exact hScaled
    exact (greedyDeletedPrimeClass_record_bounds n hnTwo).1.trans hMass.le
  let w : Nat -> Real := fun n => greedyPrimeRegulator n - greedyPrimeRegulator (n - 1)
  have hGood := sublinearClock_balanced_records greedyPrimeRegulator w hr hUnbounded
    (fun _ _ => le_rfl) hSublinear N
  choose p hp using hGood
  have hrec := hp.2.1
  have hprime : Nat.Prime p := by
    by_contra hnot
    have hSelf := (greedyPrimeRegulator_le_iff (p - 1)
      (greedyPrimeRegulator (p - 1))).mp le_rfl
    have hNoRise : greedyPrimeRegulator p <= greedyPrimeRegulator (p - 1) := by
      apply (greedyPrimeRegulator_le_iff p (greedyPrimeRegulator (p - 1))).mpr
      apply And.intro hSelf.1
      intro q hq hqp
      have hNe : Not (q = p) := by
        intro heq
        apply hnot
        rw [<- heq]
        exact hq
      exact hSelf.2 q hq (by omega)
    exact (not_le_of_gt hrec) hNoRise
  have hJump : greedyPrimeRegulator p - greedyPrimeRegulator (p - 1) <=
      Real.log (p : Real) := by
    rw [<- primeRecordJump_eq_regulator_sub p hprime]
    exact primeRecordJump_le_log p hprime
  have hBalance := hp.2.2
  dsimp only [w] at hBalance
  apply Exists.intro p
  apply And.intro hp.1
  apply And.intro hprime
  exact And.intro hrec (by linarith only [hBalance, hJump])

theorem greedyPrimeRegulator_balanced_records_or_bounded :
    Or (Exists fun B : Real => forall n : Nat, greedyPrimeRegulator n <= B)
      (forall N : Nat, Exists fun p : Nat => And (N <= p) (And (Nat.Prime p)
        (And (greedyPrimeRegulator (p - 1) < greedyPrimeRegulator p)
          (greedyPrimeRegulator p - Real.log (p : Real) <=
            2 * greedyPrimeRegulator (p / 2))))) := by
  classical
  by_cases hUnbounded : forall B : Real, Exists fun n : Nat => B < greedyPrimeRegulator n
  case pos =>
    exact Or.inr (greedyPrimeRegulator_balanced_records hUnbounded)
  case neg =>
    choose B hB using not_forall.mp hUnbounded
    apply Or.inl
    apply Exists.intro B
    intro n
    exact le_of_not_gt (fun h => hB (Exists.intro n h))


/-! The psi clock is evaluated at the same successive actual primes.
The prime-power correction uses this same adaptive record weight. -/

noncomputable def primePsiClockError (i : Nat) : Real :=
  Chebyshev.psi (primeAt i : Real) - (primeAt i : Real)

noncomputable def primePowerClockError (i : Nat) : Real :=
  Chebyshev.psi (primeAt i : Real) - Chebyshev.theta (primeAt i : Real)

noncomputable def primeRecordPsiWork (m n : Nat) : Real :=
  clockRecordCenteredCrossEnergy primeClockError primePsiClockError m n

noncomputable def primeRecordPrimePowerWork (m n : Nat) : Real :=
  clockRecordCenteredCrossEnergy primeClockError primePowerClockError m n

theorem primePsiClockError_eq_theta_add_primePower :
    primePsiClockError = fun i => primeClockError i + primePowerClockError i := by
  funext i
  rw [primeClockError_eq_theta, primeClassTheta_univ_eq_chebyshev]
  unfold primePsiClockError primePowerClockError
  ring

/-- Every endpoint and record-jump cross term of the prime-power work. -/
theorem primeRecordPrimePowerWork_product (m n : Nat) :
    primeRecordPrimePowerWork m n =
      (clockRecord primeClockError n - clockRecord primeClockError m) *
        clockPreviousError primePowerClockError n -
      ((Finset.range n).sum
          (fun i => primePowerClockError i * clockRecordIncrement primeClockError i) -
        (Finset.range m).sum
          (fun i => primePowerClockError i * clockRecordIncrement primeClockError i)) :=
  clockRecordCenteredCrossEnergy_product primeClockError primePowerClockError m n

theorem primeRecordPsiWork_product (m n : Nat) :
    primeRecordPsiWork m n =
      (clockRecord primeClockError n - clockRecord primeClockError m) *
        clockPreviousError primePsiClockError n -
      ((Finset.range n).sum
          (fun i => primePsiClockError i * clockRecordIncrement primeClockError i) -
        (Finset.range m).sum
          (fun i => primePsiClockError i * clockRecordIncrement primeClockError i)) :=
  clockRecordCenteredCrossEnergy_product primeClockError primePsiClockError m n

/-- Prime-square damping is contained inside the psi work as well as in
its compensation. The retained term is exactly the record self-work. -/
theorem primeRecordPsiWork_compensated (m n : Nat)
    (hrecord : clockPreviousError primeClockError n = clockRecord primeClockError n) :
    2 * (primeRecordPsiWork m n - primeRecordPrimePowerWork m n) =
      (clockRecord primeClockError n - clockRecord primeClockError m) ^ 2 -
        (clockRecordQuadraticVariation primeClockError n -
          clockRecordQuadraticVariation primeClockError m) := by
  unfold primeRecordPsiWork primeRecordPrimePowerWork
  rw [primePsiClockError_eq_theta_add_primePower]
  exact clockRecordCenteredCrossEnergy_compensated
    primeClockError primePowerClockError m n hrecord

/-- Once the new record dominates one jump, the compensated work retains
a positive quadratic signal. This is a lower bound, not a root-scale upper bound. -/
theorem primeRecordPsiWork_retained_self_work
    (m n : Nat) (W : Real) (hmn : m <= n)
    (hrecord : clockPreviousError primeClockError n = clockRecord primeClockError n)
    (hInc : forall i : Nat, m <= i -> i < n ->
      clockRecordIncrement primeClockError i <= W)
    (hW : 0 <= W)
    (hk : 2 * W <= clockRecord primeClockError n - clockRecord primeClockError m) :
    (clockRecord primeClockError n - clockRecord primeClockError m) ^ 2 <=
      4 * (primeRecordPsiWork m n - primeRecordPrimePowerWork m n) := by
  have hid := primeRecordPsiWork_compensated m n hrecord
  have hq := clockRecordQuadraticVariation_interval_le primeClockError m n W hmn hInc
  have hk0 : 0 <= clockRecord primeClockError n - clockRecord primeClockError m := by
    linarith only [hW, hk]
  have hprod := mul_nonneg hk0
    (show 0 <= clockRecord primeClockError n - clockRecord primeClockError m - 2 * W by
      linarith only [hk])
  nlinarith only [hid, hq, hprod]



noncomputable def properPrimePowerWeight (n : Nat) : Real :=
  ArithmeticFunction.vonMangoldt n - (if Nat.Prime n then Real.log (n : Real) else 0)

theorem properPrimePowerWeight_nonneg (n : Nat) : 0 <= properPrimePowerWeight n := by
  classical
  by_cases hp : Nat.Prime n
  case pos => simp only [properPrimePowerWeight, ite_eq_left hp,
    ArithmeticFunction.vonMangoldt_apply_prime hp, sub_self, le_refl]
  case neg => simp only [properPrimePowerWeight, ite_eq_right hp, sub_zero]
              exact ArithmeticFunction.vonMangoldt_nonneg

theorem primePowerClockError_eq_sum (i : Nat) :
    primePowerClockError i =
      (Finset.Ioc 0 (primeAt i)).sum properPrimePowerWeight := by
  classical
  unfold primePowerClockError Chebyshev.psi Chebyshev.theta properPrimePowerWeight
  simp only [Nat.floor_natCast, Finset.sum_filter, Finset.sum_sub_distrib]

theorem primePowerClockError_monotone : Monotone primePowerClockError := by
  intro i j hij
  rw [primePowerClockError_eq_sum, primePowerClockError_eq_sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  . intro k hk
    have h := Finset.mem_Ioc.mp hk
    exact Finset.mem_Ioc.mpr
      (And.intro h.1 (h.2.trans (primeAt_strictMono.monotone hij)))
  . intro k _ _
    exact properPrimePowerWeight_nonneg k

theorem primePowerClockError_increment_nonneg (i : Nat) :
    0 <= primePowerClockError i - clockPreviousError primePowerClockError i := by
  cases i with
  | zero =>
      change 0 <= primePowerClockError 0 - 0
      rw [sub_zero, primePowerClockError_eq_sum]
      exact Finset.sum_nonneg (fun j _ => properPrimePowerWeight_nonneg j)
  | succ i =>
      change 0 <= primePowerClockError (i + 1) - primePowerClockError i
      exact sub_nonneg.mpr (primePowerClockError_monotone (Nat.le_succ i))

theorem primeRecordPrimePowerWork_bounds (m n : Nat) (hmn : m <= n) :
    And (0 <= primeRecordPrimePowerWork m n)
      (primeRecordPrimePowerWork m n <=
        (clockRecord primeClockError n - clockRecord primeClockError m) *
          (clockPreviousError primePowerClockError n -
            clockPreviousError primePowerClockError m)) :=
  clockRecordCenteredCrossEnergy_bounds primeClockError primePowerClockError m n hmn
    primePowerClockError_increment_nonneg

/-- Two-sided signed control after the exact cross terms are retained.
The prime powers add positive work; no main term is bounded by its norm. -/
theorem primeRecordPsiWork_signed_bounds
    (m n : Nat) (W : Real) (hmn : m <= n)
    (hrecord : clockPreviousError primeClockError n = clockRecord primeClockError n)
    (hInc : forall i : Nat, m <= i -> i < n ->
      clockRecordIncrement primeClockError i <= W) :
    And
      (((clockRecord primeClockError n - clockRecord primeClockError m) ^ 2 -
        W * (clockRecord primeClockError n - clockRecord primeClockError m)) / 2 <=
          primeRecordPsiWork m n)
      (primeRecordPsiWork m n <=
        (clockRecord primeClockError n - clockRecord primeClockError m) ^ 2 / 2 +
          (clockRecord primeClockError n - clockRecord primeClockError m) *
            (clockPreviousError primePowerClockError n -
              clockPreviousError primePowerClockError m)) := by
  have hid := primeRecordPsiWork_compensated m n hrecord
  have hp := primeRecordPrimePowerWork_bounds m n hmn
  have hq := clockRecordQuadraticVariation_interval_le primeClockError m n W hmn hInc
  have hq0 : 0 <= clockRecordQuadraticVariation primeClockError n -
      clockRecordQuadraticVariation primeClockError m := by
    apply sub_nonneg.mpr
    unfold clockRecordQuadraticVariation
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
    intro i _ _
    exact sq_nonneg (clockRecordIncrement primeClockError i)
  constructor
  . linarith only [hid, hp.1, hq]
  . linarith only [hid, hp.2, hq0]



/-- The finite pairing formed from midpoint values at every prime,
including the final prime endpoint. No infinite Abel limit is assumed. -/
noncomputable def primeRecordPsiMidpointPairing (m n : Nat) : Real :=
  (clockRecord primeClockError n - clockRecord primeClockError m) *
    (clockPreviousError primePsiClockError n - clockPreviousError primeLogWeight n / 2) -
  ((Finset.range n).sum (fun i =>
      (primePsiClockError i - primeLogWeight i / 2) * clockRecordIncrement primeClockError i) -
    (Finset.range m).sum (fun i =>
      (primePsiClockError i - primeLogWeight i / 2) * clockRecordIncrement primeClockError i))

noncomputable def primeRecordLogJumpCross (n : Nat) : Real :=
  (Finset.range n).sum (fun i => primeLogWeight i * clockRecordIncrement primeClockError i)

theorem primeRecordPsiMidpointPairing_correction (m n : Nat) :
    primeRecordPsiMidpointPairing m n =
      primeRecordPsiWork m n -
        (clockRecord primeClockError n - clockRecord primeClockError m) *
          clockPreviousError primeLogWeight n / 2 +
        (primeRecordLogJumpCross n - primeRecordLogJumpCross m) / 2 := by
  have hsum (s : Finset Nat) :
      s.sum (fun i => (primePsiClockError i - primeLogWeight i / 2) *
        clockRecordIncrement primeClockError i) =
      s.sum (fun i => primePsiClockError i * clockRecordIncrement primeClockError i) -
        s.sum (fun i => primeLogWeight i * clockRecordIncrement primeClockError i) / 2 := by
    calc
      _ = s.sum (fun i => primePsiClockError i * clockRecordIncrement primeClockError i -
          (primeLogWeight i * clockRecordIncrement primeClockError i) / 2) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [Finset.sum_sub_distrib, <- Finset.sum_div]
  rw [primeRecordPsiWork_product]
  unfold primeRecordPsiMidpointPairing primeRecordLogJumpCross
  rw [hsum, hsum]
  ring

theorem primeRecordPsiMidpointPairing_compensated (m n : Nat)
    (hrecord : clockPreviousError primeClockError n = clockRecord primeClockError n) :
    2 * (primeRecordPsiMidpointPairing m n - primeRecordPrimePowerWork m n) =
      (clockRecord primeClockError n - clockRecord primeClockError m) ^ 2 -
        (clockRecordQuadraticVariation primeClockError n -
          clockRecordQuadraticVariation primeClockError m) -
        (clockRecord primeClockError n - clockRecord primeClockError m) *
          clockPreviousError primeLogWeight n +
        (primeRecordLogJumpCross n - primeRecordLogJumpCross m) := by
  rw [primeRecordPsiMidpointPairing_correction]
  have h := primeRecordPsiWork_compensated m n hrecord
  linarith only [h]



/-- Each actual retained prime and the complete elapsed prime gap are present. -/
theorem primeClock_retained_source_step (i : Nat) :
    (primeClockError i - clockPreviousError primeClockError i) -
        clockDeletedIncrement primeClockError primeLogWeight i =
      (@ite Real (greedyPrimeIndices i) (Classical.propDecidable _) (primeLogWeight i) 0) -
        ((primeAt i : Real) -
          clockPreviousError (fun j => (primeAt j : Real)) i) := by
  classical
  have hd : clockDeletedIncrement primeClockError primeLogWeight i =
      if greedyPrimeIndices i then 0 else primeLogWeight i := by
    unfold clockDeletedIncrement
    rw [<- greedyPrimeDeletedMass_eq_clock, <- greedyPrimeDeletedMass_eq_clock]
    simp only [selectionCost]
    by_cases h : greedyPrimeIndices i <;> simp [h]
  have he : primeClockError i - clockPreviousError primeClockError i =
      primeLogWeight i - ((primeAt i : Real) -
        clockPreviousError (fun j => (primeAt j : Real)) i) := by
    cases i with
    | zero =>
        simp only [primeClockError, primeFullPrefixCost, selectionCost,
          clockPreviousError, ite_true]
        ring
    | succ k =>
        change primeClockError (k + 1) - primeClockError k =
          primeLogWeight (k + 1) - ((primeAt (k + 1) : Real) - (primeAt k : Real))
        unfold primeClockError
        rw [primeFullPrefixCost_succ (k + 1)]
        ring
  rw [he, hd]
  by_cases h : greedyPrimeIndices i <;> simp [h]

theorem primeClock_pre_deletion_budget (i : Nat) :
    primeClockError i <=
      clockDeletedMass primeClockError primeLogWeight i + primeLogWeight i := by
  cases i with
  | zero =>
      simpa only [clockDeletedMass, zero_add] using primeClockError_initial
  | succ k =>
      have hb := clockDeletedMass_record_bounds primeClockError primeLogWeight
        (primeLogWeight_nonneg 0) primeLogWeight_monotone primeClockError_initial
        primeClockError_increment (k + 1)
      have he := (clockRecord_contains primeClockError k).trans hb.1
      have hi := primeClockError_increment k
      linarith only [he, hi]

theorem primeRetainedSignedWork_feedback_bounds (n : Nat) :
    And
      (-clockDeletedMass primeClockError primeLogWeight n *
          clockRetainedHeadroom primeClockError primeLogWeight n <=
        clockRetainedSignedWork primeClockError primeLogWeight n)
      (clockRetainedSignedWork primeClockError primeLogWeight n <=
        -clockDeletedMass primeClockError primeLogWeight n *
            clockRetainedHeadroom primeClockError primeLogWeight n +
          clockDeletedJumpBudget primeClockError primeLogWeight n) :=
  clockRetainedSignedWork_bounds primeClockError primeLogWeight n
    primeLogWeight_nonneg primeClock_pre_deletion_budget

theorem primeFullSignedWork_feedback_bounds (n : Nat) :
    And
      (-clockDeletedJumpBudget primeClockError primeLogWeight n / 2 <=
        clockFullSignedWork primeClockError primeLogWeight n -
          (clockDeletedMass primeClockError primeLogWeight n) ^ 2 / 2 +
          clockDeletedMass primeClockError primeLogWeight n *
            clockRetainedHeadroom primeClockError primeLogWeight n)
      (clockFullSignedWork primeClockError primeLogWeight n -
          (clockDeletedMass primeClockError primeLogWeight n) ^ 2 / 2 +
          clockDeletedMass primeClockError primeLogWeight n *
            clockRetainedHeadroom primeClockError primeLogWeight n <=
        clockDeletedJumpBudget primeClockError primeLogWeight n / 2) :=
  clockFullSignedWork_feedback_bounds primeClockError primeLogWeight n
    primeLogWeight_nonneg primeClock_pre_deletion_budget


end PrimeFactorOscillations.PrimeClassDeletion
