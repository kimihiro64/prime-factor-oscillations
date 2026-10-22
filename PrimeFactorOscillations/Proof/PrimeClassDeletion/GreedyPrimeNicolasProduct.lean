/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeClassNicolasTail

/-!
# The calibrated greedy Nicolas error and its complete missing-product tail

Split the actual convergent Euler cost into its complete finite prefix and
infinite tail. The comparison with Nicolas's original full-prime logarithm
retains both the theta-height correction and every missing prime beyond x.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter MeasureTheory
open PrimeFactorOscillations.PrimeClassSampling
open Robin1984

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def primeClassMissingWeightTail (P : Set Nat) (w : Nat -> Real)
    (x : Real) : Nat -> Real := by
  classical
  exact fun p => if x < (p : Real) then primeClassMissingWeight P w p else 0

theorem primeClassMissingWeight_tsum_split (P : Set Nat) (w : Nat -> Real)
    (hw : forall p : Nat, Nat.Prime p -> 0 <= w p)
    (hs : Summable (primeClassMissingWeight P w)) (x : Real) (hx : 0 <= x) :
    tsum (primeClassMissingWeight P w) =
      (primeClassPrefix (fun p => Not (Membership.mem P p)) (Nat.floor x)).sum w +
        tsum (primeClassMissingWeightTail P w x) := by
  classical
  let S := primeClassPrefix (fun p => Not (Membership.mem P p)) (Nat.floor x)
  let low : Nat -> Real := fun p => if Membership.mem S p then w p else 0
  have hHigh0 (p : Nat) : 0 <= primeClassMissingWeightTail P w x p := by
    dsimp only [primeClassMissingWeightTail]
    split_ifs
    case pos => exact primeClassMissingWeight_nonneg P w hw p
    case neg => exact le_refl 0
  have hHighLe (p : Nat) :
      primeClassMissingWeightTail P w x p <= primeClassMissingWeight P w p := by
    dsimp only [primeClassMissingWeightTail]
    split_ifs
    case pos => exact le_refl _
    case neg => exact primeClassMissingWeight_nonneg P w hw p
  have hsHigh : Summable (primeClassMissingWeightTail P w x) :=
    Summable.of_nonneg_of_le hHigh0 hHighLe hs
  have hLow0 (p : Nat) : 0 <= low p := by
    dsimp only [low]
    split_ifs with hp
    case neg => exact le_refl 0
    case pos =>
      exact hw p ((primeClassPrefix_mem_iff _ (Nat.floor x) p).mp hp).2.2.1
  have hEach (p : Nat) :
      primeClassMissingWeight P w p = low p + primeClassMissingWeightTail P w x p := by
    by_cases hp : And (Nat.Prime p) (Not (Membership.mem P p))
    case neg =>
      have hnotS : Not (Membership.mem S p) := by
        intro hIn
        exact hp ((primeClassPrefix_mem_iff _ (Nat.floor x) p).mp hIn).2.2
      simp only [primeClassMissingWeight, ite_eq_right hp, low, ite_eq_right hnotS,
        primeClassMissingWeightTail]
      split_ifs <;> norm_num
    case pos =>
      by_cases hpx : (p : Real) <= x
      case pos =>
        have hIn : Membership.mem S p :=
          (primeClassPrefix_mem_iff _ (Nat.floor x) p).mpr
            (And.intro hp.1.two_le (And.intro (Nat.le_floor hpx) hp))
        have hNot : Not (x < (p : Real)) := not_lt.mpr hpx
        simp only [primeClassMissingWeight, ite_eq_left hp, low, ite_eq_left hIn,
          primeClassMissingWeightTail, ite_eq_right hNot, add_zero]
      case neg =>
        have hxp : x < (p : Real) := lt_of_not_ge hpx
        have hnotS : Not (Membership.mem S p) := by
          intro hIn
          have hm := (primeClassPrefix_mem_iff _ (Nat.floor x) p).mp hIn
          exact hpx ((Nat.cast_le.mpr hm.2.1).trans (Nat.floor_le hx))
        simp only [primeClassMissingWeight, ite_eq_left hp, low, ite_eq_right hnotS,
          primeClassMissingWeightTail, ite_eq_left hxp, zero_add]
  have hsLow : Summable low := by
    apply Summable.of_nonneg_of_le hLow0 _ hs
    intro p
    rw [hEach]
    exact le_add_of_nonneg_right (hHigh0 p)
  have hLowTotal : tsum low = S.sum w := by
    calc
      _ = S.sum low := tsum_eq_sum (fun p hp => by simp only [ite_eq_right hp])
      _ = _ := by
        apply Finset.sum_congr rfl
        intro p hp
        simp only [low, ite_eq_left hp]
  calc
    _ = tsum (fun p => low p + primeClassMissingWeightTail P w x p) := tsum_congr hEach
    _ = tsum low + tsum (primeClassMissingWeightTail P w x) := hsLow.tsum_add hsHigh
    _ = _ := by rw [hLowTotal]

noncomputable def greedyPrimeMissingEulerConstant : Real :=
  tsum (primeClassMissingWeight greedyPrimeClass primeEulerLogWeight)

noncomputable def greedyPrimeCalibratedError (x : Real) : Real :=
  Real.eulerMascheroniConstant - greedyPrimeMissingEulerConstant +
    Real.log (Real.log (primeClassThetaReal greedyPrimeClass x)) -
      (primeClassPrefix greedyPrimeClass (Nat.floor x)).sum primeEulerLogWeight

theorem nicolasLogMertensOscillation_eq_primeClassEulerCost
    (x : Real) (hx : 3 <= x) :
    nicolasLogMertensOscillation x =
      Real.eulerMascheroniConstant + Real.log (Real.log (Chebyshev.theta x)) -
        (primeClassPrefix Set.univ (Nat.floor x)).sum primeEulerLogWeight := by
  classical
  have hPrefix : primeClassPrefix Set.univ (Nat.floor x) = Nat.primesLE (Nat.floor x) := by
    ext p
    simp only [primeClassPrefix, Finset.mem_filter, Finset.mem_Icc, Set.mem_univ,
      and_true, Nat.mem_primesLE]
    constructor
    case mp =>
      intro hp
      exact And.intro hp.1.2 hp.2
    case mpr =>
      intro hp
      exact And.intro (And.intro hp.2.two_le hp.1) hp.2
  have hFactors (p : Nat) (hp : Membership.mem (Nat.primesLE (Nat.floor x)) p) :
      Not (1 - 1 / (p : Real) = 0) := by
    have hPrime := Nat.prime_of_mem_primesLE hp
    have hp0 : (0 : Real) < p := Nat.cast_pos.mpr hPrime.pos
    have hp1 : (1 : Real) < p := by exact_mod_cast hPrime.one_lt
    have hFrac := (div_lt_one hp0).mpr hp1
    linarith only [hFrac]
  have hLogProduct : Real.log (nicolasMertensProduct x) =
      -(primeClassPrefix Set.univ (Nat.floor x)).sum primeEulerLogWeight := by
    unfold nicolasMertensProduct
    rw [Real.log_prod hFactors, <- hPrefix]
    change (primeClassPrefix Set.univ (Nat.floor x)).sum
      (fun p => Real.log (1 - 1 / (p : Real))) =
        -(primeClassPrefix Set.univ (Nat.floor x)).sum
          (fun p => -Real.log (1 - 1 / (p : Real)))
    rw [Finset.sum_neg_distrib, neg_neg]
  have hLogTheta : 0 < Real.log (Chebyshev.theta x) :=
    Real.log_pos (one_lt_chebyshevTheta_of_three_le hx)
  have hProduct : 0 < nicolasMertensProduct x := nicolasMertensProduct_pos x
  unfold nicolasLogMertensOscillation nicolasFunction
  rw [Real.log_mul (mul_ne_zero (Real.exp_pos _).ne' hLogTheta.ne') hProduct.ne',
    Real.log_mul (Real.exp_pos _).ne' hLogTheta.ne', Real.log_exp, hLogProduct]
  ring

theorem greedyPrimeCalibratedError_difference (x : Real) (hx : 3 <= x) :
    nicolasLogMertensOscillation x - greedyPrimeCalibratedError x =
      Real.log (Real.log (Chebyshev.theta x)) -
        Real.log (Real.log (primeClassThetaReal greedyPrimeClass x)) +
          tsum (primeClassMissingWeightTail greedyPrimeClass primeEulerLogWeight x) := by
  have hSplit := primeClassMissingWeight_tsum_split greedyPrimeClass primeEulerLogWeight
    primeEulerLogWeight_nonneg greedyPrimeClass_missing_logEulerCost_summable x
      (by linarith only [hx])
  have hPartition := primeClassPrefix_complement_weight_sum greedyPrimeClass
    primeEulerLogWeight (Nat.floor x)
  rw [nicolasLogMertensOscillation_eq_primeClassEulerCost x hx]
  dsimp only [greedyPrimeCalibratedError, greedyPrimeMissingEulerConstant]
  linarith only [hSplit, hPartition]

theorem greedyPrimeCalibratedError_difference_nonneg
    (x : Real) (hx : 3 <= x) (hS : 1 < primeClassThetaReal greedyPrimeClass x) :
    And
      (0 <= Real.log (Real.log (Chebyshev.theta x)) -
        Real.log (Real.log (primeClassThetaReal greedyPrimeClass x)))
      (And
        (0 <= tsum (primeClassMissingWeightTail greedyPrimeClass primeEulerLogWeight x))
        (greedyPrimeCalibratedError x <= nicolasLogMertensOscillation x)) := by
  classical
  have hTheta : primeClassThetaReal greedyPrimeClass x <= Chebyshev.theta x := by
    rw [<- primeClassThetaReal_univ_eq_chebyshev x]
    unfold primeClassThetaReal primeClassTheta
    apply Finset.sum_le_sum_of_subset_of_nonneg
    case h =>
      intro p hp
      have hm := (primeClassPrefix_mem_iff greedyPrimeClass (Nat.floor x) p).mp hp
      exact (primeClassPrefix_mem_iff Set.univ (Nat.floor x) p).mpr
        (And.intro hm.1 (And.intro hm.2.1 (And.intro hm.2.2.1 (Set.mem_univ p))))
    case hf =>
      intro p hp _
      exact Real.log_nonneg
        (by exact_mod_cast (primeClassPrefix_prime Set.univ (Nat.floor x) p hp).one_le)
  have hHeight : 0 <= Real.log (Real.log (Chebyshev.theta x)) -
      Real.log (Real.log (primeClassThetaReal greedyPrimeClass x)) :=
    sub_nonneg.mpr (Real.log_le_log (Real.log_pos hS)
      (Real.log_le_log (lt_trans zero_lt_one hS) hTheta))
  have hTail : 0 <= tsum
      (primeClassMissingWeightTail greedyPrimeClass primeEulerLogWeight x) := by
    apply tsum_nonneg
    intro p
    dsimp only [primeClassMissingWeightTail]
    split_ifs
    case pos =>
      exact primeClassMissingWeight_nonneg greedyPrimeClass primeEulerLogWeight
        primeEulerLogWeight_nonneg p
    case neg => exact le_refl 0
  refine And.intro hHeight (And.intro hTail ?_)
  have hDiff := greedyPrimeCalibratedError_difference x hx
  linarith only [hDiff, hHeight, hTail]

end PrimeFactorOscillations.PrimeClassDeletion
