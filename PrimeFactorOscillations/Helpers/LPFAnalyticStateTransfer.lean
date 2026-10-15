/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFPrimeRowWeights
import PrimeFactorOscillations.Helpers.LPFStateResidueEnergy

/-!
# The audited analytic input in the complete actual-state lower bound

Both prime rows retain their positive projected mass. The 3r row is evaluated
on multiplied unit classes, including nonunit output classes. The remaining
joint centered energy is displayed rather than assumed to be small.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem sum_odd_frontier_eq_rows (f : Nat -> Real) (M : Nat) (hM : 3 <= M) :
    Finset.sum ((oddInterval M).filter (fun n => M < Nat.largestPrimeFactor n)) f =
      Finset.sum (Nat.largestPrimeFactorRow (4 * M - 1) M 1) f +
      Finset.sum (Nat.largestPrimeFactorRow (4 * M - 1) M 3) (fun r => f (3 * r)) := by
  let g : Nat -> Real := fun n => if n % 2 = 1 then f n else 0
  have hEven : forall n, g (2 * n) = 0 := by
    intro n
    have hMod : (2 * n) % 2 = 0 := by omega
    simp [g, hMod]
  have hLeft : Finset.sum ((Finset.Icc 1 (4 * M - 1)).filter
      (fun n => M < Nat.largestPrimeFactor n)) g =
      Finset.sum ((oddInterval M).filter (fun n => M < Nat.largestPrimeFactor n)) f := by
    unfold oddInterval
    simp only [Finset.sum_filter, g]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hOdd : n % 2 = 1
    next => simp [hOdd]
    next => simp [hOdd]
  have hOne : Nat.largestPrimeFactorRow (4 * M - 1) M 1 =
      (Finset.Icc (M + 1) (4 * M - 1)).filter Nat.Prime := by
    simp [Nat.largestPrimeFactorRow, Nat.largestPrimeFactor]
  have hThree : Nat.largestPrimeFactorRow (4 * M - 1) M 3 =
      (Finset.Icc (M + 1) ((4 * M - 1) / 3)).filter Nat.Prime := by
    unfold Nat.largestPrimeFactorRow
    rw [Nat.largestPrimeFactor_of_prime (by decide : Nat.Prime 3),
      max_eq_left (by omega : 3 <= M + 1)]
  have hFirst : Finset.sum (Nat.largestPrimeFactorRow (4 * M - 1) M 1) g =
      Finset.sum (Nat.largestPrimeFactorRow (4 * M - 1) M 1) f := by
    apply Finset.sum_congr rfl
    intro r hr
    have hp := (Nat.mem_largestPrimeFactorRow (by decide : 0 < 1)).mp hr
    have ho : r % 2 = 1 := hp.1.eq_two_or_odd.resolve_left (by omega)
    simp [g, ho]
  have hSecond : Finset.sum (Nat.largestPrimeFactorRow (4 * M - 1) M 3) (fun r => g (3 * r)) =
      Finset.sum (Nat.largestPrimeFactorRow (4 * M - 1) M 3) (fun r => f (3 * r)) := by
    apply Finset.sum_congr rfl
    intro r hr
    have hp := (Nat.mem_largestPrimeFactorRow (by decide : 0 < 3)).mp hr
    have ho : r % 2 = 1 := hp.1.eq_two_or_odd.resolve_left (by omega)
    have hmo : (3 * r) % 2 = 1 := by omega
    simp [g, hmo]
  have h := Nat.sum_largestPrimeFactor_frontier_eq_two_rows g hEven M hM
  rw [hLeft, <- hOne, <- hThree, hFirst, hSecond] at h
  exact h

noncomputable def stateResidueMean (S : Finset Nat) (M Q : Nat) (a : ZMod Q) : Real :=
  Finset.fiberMean (oddInterval M) (fun n => n % Q) (fun n => (pairWeight S n : Real)) a.val

theorem stateResidueMean_nonneg (S : Finset Nat) (M Q : Nat) (a : ZMod Q) :
    0 <= stateResidueMean S M Q a := by
  unfold stateResidueMean Finset.fiberMean
  apply div_nonneg
  next => exact Finset.sum_nonneg (fun n hn => Nat.cast_nonneg _)
  next => exact Nat.cast_nonneg _

noncomputable def projectedRowMass (S : Finset Nat) (M Q m : Nat) [NeZero Q] : Real :=
  Finset.sum (Finset.univ : Finset (Units (ZMod Q)))
    (fun a => stateResidueMean S M Q ((m : ZMod Q) * (a : ZMod Q)))

noncomputable def modeledProjection (S : Finset Nat) (M Q : Nat) [NeZero Q] : Real :=
  ((Nat.largestPrimeFactorRow (4 * M - 1) M 1).card : Real) / (Q.totient : Real) *
    projectedRowMass S M Q 1 +
  ((Nat.largestPrimeFactorRow (4 * M - 1) M 3).card : Real) / (Q.totient : Real) *
    projectedRowMass S M Q 3

noncomputable def projectedRowError (C : Real) (S : Finset Nat) (M Q : Nat) [NeZero Q] : Real :=
  C * ((4 * M - 1 : Nat) : Real) ^ (7 / 8 : Real) *
    (1 + Real.log Q + Real.log (((4 * M - 1 : Nat) : Real) + 2)) ^ 2 *
    (projectedRowMass S M Q 1 + projectedRowMass S M Q 3)

theorem residueProjection_eq_two_weighted_rows (S : Finset Nat) (M Q : Nat) [NeZero Q]
    (hM : 3 <= M) :
    residueProjection S M Q =
      Finset.sum (Nat.largestPrimeFactorRow (4 * M - 1) M 1)
        (fun r => stateResidueMean S M Q (r : ZMod Q)) +
      Finset.sum (Nat.largestPrimeFactorRow (4 * M - 1) M 3)
        (fun r => stateResidueMean S M Q (3 * (r : ZMod Q))) := by
  have hProjection := Finset.sum_fiberMean_mul_eq_projection
    (oddInterval M) (fun n => n % Q) (fun n => (pairWeight S n : Real)) (frontierIndicator M)
  have hEq : residueProjection S M Q =
      Finset.sum ((oddInterval M).filter (fun n => M < Nat.largestPrimeFactor n))
        (fun n => stateResidueMean S M Q (n : ZMod Q)) := by
    change _ = _
    rw [show residueProjection S M Q = _ from hProjection.symm]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    simp [stateResidueMean, ZMod.val_natCast, frontierIndicator, mul_ite]
  rw [hEq, sum_odd_frontier_eq_rows _ M hM]
  simp only [Nat.cast_mul, Nat.cast_ofNat]

theorem exists_uniform_actual_state_lower_bound :
    exists C : Real, And (0 < C)
      (forall {Q : Nat} [NeZero Q] (S : Finset Nat) (M : Nat), 3 <= M ->
        Nat.largestPrimeFactor Q <= M ->
        (forall p, Membership.mem S p -> p <= M) ->
        modeledProjection S M Q - projectedRowError C S M Q -
          Real.sqrt (pairResidueEnergy S M Q * frontierResidueEnergy M Q) <=
          (frontierCount S M : Real)) := by
  let C : Real := Classical.choose exists_uniform_weighted_prime_row_lower_bound
  have hC := Classical.choose_spec exists_uniform_weighted_prime_row_lower_bound
  refine Exists.intro C (And.intro hC.1 ?_)
  intro Q inst S M hM hQ hBound
  have hOne := hC.2 (4 * M - 1) M 1 (by decide) hQ
    (fun a => stateResidueMean S M Q ((1 : ZMod Q) * a))
    (fun a => stateResidueMean_nonneg S M Q _)
  have hThree := hC.2 (4 * M - 1) M 3 (by decide) hQ
    (fun a => stateResidueMean S M Q ((3 : ZMod Q) * a))
    (fun a => stateResidueMean_nonneg S M Q _)
  have hAnalytic : modeledProjection S M Q - projectedRowError C S M Q <=
      residueProjection S M Q := by
    rw [residueProjection_eq_two_weighted_rows S M Q hM]
    unfold modeledProjection projectedRowError projectedRowMass
    simp only [one_mul] at hOne
    simp only [Nat.cast_one, one_mul]
    linarith
  have hJoint := residue_projection_lower_bound S M Q hBound
  linarith

theorem exists_uniform_actual_state_growth_criterion :
    exists C : Real, And (0 < C)
      (forall {Q : Nat} [NeZero Q] (S : Finset Nat) (M : Nat), 3 <= M ->
        Nat.largestPrimeFactor Q <= M ->
        (forall p, Membership.mem S p -> p <= M) ->
        projectedRowError C S M Q +
            Real.sqrt (pairResidueEnergy S M Q * frontierResidueEnergy M Q) <
          modeledProjection S M Q ->
        Not (step S = S)) := by
  let C : Real := Classical.choose exists_uniform_actual_state_lower_bound
  have hC := Classical.choose_spec exists_uniform_actual_state_lower_bound
  refine Exists.intro C (And.intro hC.1 ?_)
  intro Q inst S M hM hQ hBound hSurplus
  have h := hC.2 S M hM hQ hBound
  have hPos : (0 : Real) < (frontierCount S M : Real) := by linarith
  apply not_closed_of_frontierCount_pos S M hBound
  exact_mod_cast hPos

end PrimeFactorOscillations.LPF
