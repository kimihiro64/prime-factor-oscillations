/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyPrimeNicolasProduct

/-!
# The unconditional selected theta-error integral

The literal selected and deleted prime masses partition the full theta
function. Their independently proved tail integrability justifies the
signed subtraction before the actual pointwise cap supplies its sign.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter MeasureTheory
open PrimeFactorOscillations.PrimeClassSampling
open Robin1984

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem greedyPrimeClass_thetaReal_add_deleted (t : Real) :
    primeClassThetaReal greedyPrimeClass t +
      primeClassThetaReal greedyDeletedPrimeClass t = Chebyshev.theta t := by
  classical
  have hComplement :
      primeClassPrefix (fun p => Not (Membership.mem greedyPrimeClass p)) (Nat.floor t) =
        primeClassPrefix greedyDeletedPrimeClass (Nat.floor t) := by
    apply Finset.ext
    intro p
    constructor
    case mp =>
      intro h
      have hm := (primeClassPrefix_mem_iff
        (fun q => Not (Membership.mem greedyPrimeClass q)) (Nat.floor t) p).mp h
      apply (primeClassPrefix_mem_iff greedyDeletedPrimeClass (Nat.floor t) p).mpr
      refine And.intro hm.1 (And.intro hm.2.1 (And.intro hm.2.2.1 ?_))
      change And (Nat.Prime p) (Not (greedyPrimeIndices (Nat.count Nat.Prime p)))
      refine And.intro hm.2.2.1 ?_
      intro hi
      exact hm.2.2.2 (And.intro hm.2.2.1 hi)
    case mpr =>
      intro h
      have hm := (primeClassPrefix_mem_iff greedyDeletedPrimeClass (Nat.floor t) p).mp h
      apply (primeClassPrefix_mem_iff
        (fun q => Not (Membership.mem greedyPrimeClass q)) (Nat.floor t) p).mpr
      have hDeleted := hm.2.2.2
      change And (Nat.Prime p) (Not (greedyPrimeIndices (Nat.count Nat.Prime p))) at hDeleted
      refine And.intro hm.1 (And.intro hm.2.1 (And.intro hm.2.2.1 ?_))
      intro hSelected
      change And (Nat.Prime p) (greedyPrimeIndices (Nat.count Nat.Prime p)) at hSelected
      exact hDeleted.2 hSelected.2
  have h := primeClassPrefix_complement_weight_sum greedyPrimeClass
    (fun p => Real.log (p : Real)) (Nat.floor t)
  rw [hComplement] at h
  change primeClassThetaReal greedyPrimeClass t +
    primeClassThetaReal greedyDeletedPrimeClass t = primeClassThetaReal Set.univ t at h
  simpa only [primeClassThetaReal_univ_eq_chebyshev] using h

noncomputable def greedyPrimeNicolasIntegral (x : Real) : Real :=
  integral (volume.restrict (Set.Ioi x))
    (fun t => (primeClassThetaReal greedyPrimeClass t - t) * nicolasTailKernel t)

theorem greedyPrimeNicolas_integrand_eq (t : Real) :
    (primeClassThetaReal greedyPrimeClass t - t) * nicolasTailKernel t =
      nicolasThetaError t * nicolasTailKernel t -
        primeClassThetaReal greedyDeletedPrimeClass t * nicolasTailKernel t := by
  unfold nicolasThetaError
  rw [<- greedyPrimeClass_thetaReal_add_deleted t]
  ring

theorem greedyPrimeNicolasIntegral_integrable (x : Real) (hx : 2 <= x) :
    IntegrableOn
      (fun t => (primeClassThetaReal greedyPrimeClass t - t) * nicolasTailKernel t)
      (Set.Ioi x) := by
  have hF : IntegrableOn (fun t => nicolasThetaError t * nicolasTailKernel t)
      (Set.Ioi x) :=
    nicolasThetaTail_integrableOn_Ioi_two.mono_set (fun _ ht => lt_of_le_of_lt hx ht)
  have hD := (greedyDeletedPrimeClass_nicolas_tail x (by linarith only [hx])).1
  exact (hF.sub hD).congr (Filter.Eventually.of_forall
    (fun t => (greedyPrimeNicolas_integrand_eq t).symm))

theorem greedyPrimeNicolasIntegral_eq_K_sub_tail (x : Real) (hx : 2 <= x) :
    greedyPrimeNicolasIntegral x = nicolasK x -
      (primeClassThetaReal greedyDeletedPrimeClass x / (x * Real.log x) +
        tsum (primeClassReciprocalTail greedyDeletedPrimeClass x)) := by
  have hx1 : 1 < x := by linarith only [hx]
  have hF : IntegrableOn (fun t => nicolasThetaError t * nicolasTailKernel t)
      (Set.Ioi x) :=
    nicolasThetaTail_integrableOn_Ioi_two.mono_set (fun _ ht => lt_of_le_of_lt hx ht)
  have hD := (greedyDeletedPrimeClass_nicolas_tail x hx1).1
  unfold greedyPrimeNicolasIntegral
  calc
    _ = integral (volume.restrict (Set.Ioi x))
        (fun t => nicolasThetaError t * nicolasTailKernel t -
          primeClassThetaReal greedyDeletedPrimeClass t * nicolasTailKernel t) :=
      integral_congr_ae (Filter.Eventually.of_forall greedyPrimeNicolas_integrand_eq)
    _ = nicolasK x - integral (volume.restrict (Set.Ioi x))
        (fun t => primeClassThetaReal greedyDeletedPrimeClass t * nicolasTailKernel t) :=
      integral_sub hF hD
    _ = _ := by rw [(greedyDeletedPrimeClass_nicolas_tail x hx1).2]

theorem greedyPrimeNicolasIntegral_nonpos (x : Real) (hx : 2 <= x) :
    greedyPrimeNicolasIntegral x <= 0 := by
  unfold greedyPrimeNicolasIntegral
  apply integral_nonpos_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change x < t at ht
  have ht0 : 0 <= t := by linarith only [hx, ht]
  exact mul_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr (greedyPrimeClass_thetaReal_le t ht0))
    (nicolasTailKernel_nonneg (by linarith only [hx, ht]))

theorem greedyPrimeNicolasIntegral_transfer (x : Real) (hx : 2 <= x) :
    nicolasK x = greedyPrimeNicolasIntegral x +
      integral (volume.restrict (Set.Ioi x))
        (fun t => primeClassThetaReal greedyDeletedPrimeClass t * nicolasTailKernel t) := by
  have hx1 : 1 < x := by linarith only [hx]
  rw [(greedyDeletedPrimeClass_nicolas_tail x hx1).2]
  have h := greedyPrimeNicolasIntegral_eq_K_sub_tail x hx
  linarith only [h]

private theorem mertensSummand_mask_summable (Q : Nat -> Prop) :
    Summable (fun p : Nat => @ite Real (Q p) (Classical.propDecidable _)
      (Mertens.M_eq_summand p) 0) := by
  classical
  apply Summable.of_norm_bounded_eventually_nat Mertens.M_eq_summable.norm
  filter_upwards with p
  split_ifs
  case pos => exact le_refl _
  case neg =>
    simp only [norm_zero]
    exact norm_nonneg _

private theorem mertensSummand_tsum_eq :
    tsum Mertens.M_eq_summand = Mertens.M - Real.eulerMascheroniConstant := by
  have hM := Mertens.tsum_M_eq_summand_eq
  run_tac
    let gamma := String.singleton (Char.ofNat 947)
    let declaration := Lean.Name.str
      (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "Mertens") gamma)
      "eq_eulerMascheroni"
    let source := Lean.mkIdent (Lean.Name.mkSimple "hM")
    let proofSyntax <- `(tactic| simpa only [($(Lean.mkIdent declaration))] using $source)
    Lean.Elab.Tactic.evalTactic proofSyntax

theorem mertensSummand_nonpos (p : Nat) : Mertens.M_eq_summand p <= 0 := by
  classical
  by_cases hp : Nat.Prime p
  case neg => simp only [Mertens.M_eq_summand, ite_eq_right hp, le_refl]
  case pos =>
    have hp0 : (0 : Real) < p := Nat.cast_pos.mpr hp.pos
    have hp1 : (1 : Real) < p := by exact_mod_cast hp.one_lt
    have hsmall : (1 : Real) / p < 1 := (div_lt_one hp0).mpr hp1
    have hlog := Real.log_le_sub_one_of_pos (sub_pos.mpr hsmall)
    simp only [Mertens.M_eq_summand, ite_eq_left hp]
    linarith only [hlog]

noncomputable def primeClassMertensTail (P : Set Nat) (x : Real) : Nat -> Real := by
  classical
  exact fun p => if And (Membership.mem P p) (x < (p : Real))
    then Mertens.M_eq_summand p else 0

theorem primeClassMertensTail_summable (P : Set Nat) (x : Real) :
    Summable (primeClassMertensTail P x) := by
  classical
  convert mertensSummand_mask_summable
    (fun p => And (Membership.mem P p) (x < (p : Real))) using 1
  funext p
  by_cases h : And (Membership.mem P p) (x < (p : Real))
  case pos => simp only [primeClassMertensTail, ite_eq_left h]
  case neg => simp only [primeClassMertensTail, ite_eq_right h]

theorem primeClassMertensTail_nonpos (P : Set Nat) (x : Real) :
    tsum (primeClassMertensTail P x) <= 0 := by
  classical
  apply tsum_nonpos
  intro p
  dsimp only [primeClassMertensTail]
  split_ifs
  case pos => exact mertensSummand_nonpos p
  case neg => exact le_refl 0

theorem nicolasMertensPrefixRemainder_eq_neg_tail (x : Real) (hx : 0 <= x) :
    (Finset.Ioc 0 (Nat.floor x)).sum Mertens.M_eq_summand -
        (Mertens.M - Real.eulerMascheroniConstant) =
      -tsum (primeClassMertensTail Set.univ x) := by
  classical
  let S : Finset Nat := Finset.Ioc 0 (Nat.floor x)
  let low : Nat -> Real := fun p => if Membership.mem S p then Mertens.M_eq_summand p else 0
  have hsLow : Summable low := by
    convert mertensSummand_mask_summable (fun p => Membership.mem S p) using 1
    funext p
    by_cases h : Membership.mem S p
    case pos => simp only [low, ite_eq_left h]
    case neg => simp only [low, ite_eq_right h]
  have hLowTotal : tsum low = S.sum Mertens.M_eq_summand := by
    calc
      _ = S.sum low := tsum_eq_sum (fun p hp => by simp only [ite_eq_right hp])
      _ = _ := by
        apply Finset.sum_congr rfl
        intro p hp
        simp only [low, ite_eq_left hp]
  have hEach (p : Nat) :
      Mertens.M_eq_summand p = low p + primeClassMertensTail Set.univ x p := by
    by_cases hp0 : p = 0
    case pos =>
      subst p
      norm_num [low, S, primeClassMertensTail, Mertens.M_eq_summand]
    case neg =>
      by_cases hpx : (p : Real) <= x
      case pos =>
        have hIn : Membership.mem S p :=
          Finset.mem_Ioc.mpr (And.intro (Nat.pos_of_ne_zero hp0) (Nat.le_floor hpx))
        have hNot : Not (x < (p : Real)) := not_lt.mpr hpx
        simp only [low, ite_eq_left hIn, primeClassMertensTail, hNot, and_false,
          ite_false, add_zero]
      case neg =>
        have hxp : x < (p : Real) := lt_of_not_ge hpx
        have hnotS : Not (Membership.mem S p) := by
          intro hIn
          exact hpx ((Nat.cast_le.mpr (Finset.mem_Ioc.mp hIn).2).trans (Nat.floor_le hx))
        simp only [low, ite_eq_right hnotS, primeClassMertensTail, Set.mem_univ,
          true_and, ite_eq_left hxp, zero_add]
  have hTotal :
      tsum Mertens.M_eq_summand =
        S.sum Mertens.M_eq_summand + tsum (primeClassMertensTail Set.univ x) := by
    calc
      _ = tsum (fun p => low p + primeClassMertensTail Set.univ x p) := tsum_congr hEach
      _ = tsum low + tsum (primeClassMertensTail Set.univ x) :=
        hsLow.tsum_add (primeClassMertensTail_summable Set.univ x)
      _ = _ := by rw [hLowTotal]
  rw [mertensSummand_tsum_eq] at hTotal
  dsimp only [S] at hTotal
  linarith only [hTotal]

noncomputable def greedyPrimeNicolasEulerTail (x : Real) : Real :=
  -tsum (primeClassMertensTail greedyPrimeClass x)

theorem greedyPrimeNicolasEulerTail_nonneg (x : Real) :
    0 <= greedyPrimeNicolasEulerTail x :=
  neg_nonneg.mpr (primeClassMertensTail_nonpos greedyPrimeClass x)

theorem primeClassMertensTail_greedy_partition (x : Real) :
    tsum (primeClassMertensTail Set.univ x) =
      tsum (primeClassMertensTail greedyPrimeClass x) +
        tsum (primeClassMertensTail greedyDeletedPrimeClass x) := by
  classical
  have hPoint (p : Nat) : primeClassMertensTail Set.univ x p =
      primeClassMertensTail greedyPrimeClass x p +
        primeClassMertensTail greedyDeletedPrimeClass x p := by
    by_cases hxp : x < (p : Real)
    case neg => simp [primeClassMertensTail, hxp]
    case pos =>
      by_cases hS : Membership.mem greedyPrimeClass p
      case pos =>
        have hNotD : Not (Membership.mem greedyDeletedPrimeClass p) := by
          intro hD
          change And (Nat.Prime p) (Not (greedyPrimeIndices (Nat.count Nat.Prime p))) at hD
          have hS' := hS
          change And (Nat.Prime p) (greedyPrimeIndices (Nat.count Nat.Prime p)) at hS'
          exact hD.2 hS'.2
        simp [primeClassMertensTail, hxp, hS, hNotD]
      case neg =>
        by_cases hp : Nat.Prime p
        case neg => simp [primeClassMertensTail, Mertens.M_eq_summand, hp]
        case pos =>
          have hD : Membership.mem greedyDeletedPrimeClass p := by
            refine And.intro hp ?_
            intro hi
            exact hS (And.intro hp hi)
          simp [primeClassMertensTail, hxp, hS, hD]
  have hFun : primeClassMertensTail Set.univ x =
      (fun p => primeClassMertensTail greedyPrimeClass x p +
        primeClassMertensTail greedyDeletedPrimeClass x p) := funext hPoint
  rw [hFun]
  exact (primeClassMertensTail_summable greedyPrimeClass x).tsum_add
    (primeClassMertensTail_summable greedyDeletedPrimeClass x)

private theorem greedyMissingEulerTail_pointwise (x : Real) (p : Nat) :
    primeClassMissingWeightTail greedyPrimeClass primeEulerLogWeight x p =
      primeClassReciprocalTail greedyDeletedPrimeClass x p -
        primeClassMertensTail greedyDeletedPrimeClass x p := by
  classical
  by_cases hxp : x < (p : Real)
  case neg =>
    simp [primeClassMissingWeightTail, primeClassReciprocalTail,
      primeClassMertensTail, hxp]
  case pos =>
    by_cases hp : Nat.Prime p
    case neg =>
      have hNotD : Not (Membership.mem greedyDeletedPrimeClass p) := by
        intro hD
        change And (Nat.Prime p) (Not (greedyPrimeIndices (Nat.count Nat.Prime p))) at hD
        exact hp hD.1
      simp [primeClassMissingWeightTail, primeClassReciprocalTail,
        primeClassMissingWeight, classPowerWeight, primeClassMertensTail, hp, hNotD]
    case pos =>
      by_cases hS : Membership.mem greedyPrimeClass p
      case pos =>
        have hNotD : Not (Membership.mem greedyDeletedPrimeClass p) := by
          intro hD
          change And (Nat.Prime p) (Not (greedyPrimeIndices (Nat.count Nat.Prime p))) at hD
          have hS' := hS
          change And (Nat.Prime p) (greedyPrimeIndices (Nat.count Nat.Prime p)) at hS'
          exact hD.2 hS'.2
        simp [primeClassMissingWeightTail, primeClassReciprocalTail,
          primeClassMissingWeight, classPowerWeight, primeClassMertensTail, hS, hNotD]
      case neg =>
        have hD : Membership.mem greedyDeletedPrimeClass p := by
          refine And.intro hp ?_
          intro hi
          exact hS (And.intro hp hi)
        simp only [primeClassMissingWeightTail, primeClassReciprocalTail, ite_eq_left hxp,
          primeClassMissingWeight, ite_eq_left (And.intro hp hS), classPowerWeight,
          ite_eq_left (And.intro hp hD), Real.rpow_neg_one, primeClassMertensTail,
          ite_eq_left (And.intro hD hxp), Mertens.M_eq_summand, ite_eq_left hp,
          primeEulerLogWeight, one_div]
        ring

theorem greedyPrimeMissingEulerTail_eq_reciprocal_sub_mertens (x : Real) :
    tsum (primeClassMissingWeightTail greedyPrimeClass primeEulerLogWeight x) =
      tsum (primeClassReciprocalTail greedyDeletedPrimeClass x) -
        tsum (primeClassMertensTail greedyDeletedPrimeClass x) := by
  classical
  have hsR : Summable (primeClassReciprocalTail greedyDeletedPrimeClass x) := by
    apply Summable.of_norm_bounded_eventually_nat
      greedyDeletedPrimeClass_reciprocal_summable.norm
    filter_upwards with p
    dsimp only [primeClassReciprocalTail]
    split_ifs
    case pos => exact le_refl _
    case neg =>
      simp only [norm_zero]
      exact norm_nonneg _
  have hFun : primeClassMissingWeightTail greedyPrimeClass primeEulerLogWeight x =
      (fun p => primeClassReciprocalTail greedyDeletedPrimeClass x p -
        primeClassMertensTail greedyDeletedPrimeClass x p) :=
    funext (greedyMissingEulerTail_pointwise x)
  rw [hFun]
  exact hsR.tsum_sub (primeClassMertensTail_summable greedyDeletedPrimeClass x)

noncomputable def greedyPrimeNicolasHeightRemainder (x : Real) : Real :=
  (primeClassThetaReal greedyPrimeClass x - x) / (x * Real.log x) -
    (Real.log (Real.log (primeClassThetaReal greedyPrimeClass x)) -
      Real.log (Real.log x))

theorem greedyPrimeCalibratedError_eq_integral_sub_height_add_tail
    (x : Real) (hx : 3 <= x) :
    greedyPrimeCalibratedError x = greedyPrimeNicolasIntegral x -
      greedyPrimeNicolasHeightRemainder x + greedyPrimeNicolasEulerTail x := by
  have hx0 : 0 <= x := by linarith only [hx]
  have hx2 : 2 <= x := by linarith only [hx]
  have hFull := nicolasLogMertensOscillation_eq_components hx
  rw [nicolasMertensPrefixRemainder_eq_neg_tail x hx0,
    primeClassMertensTail_greedy_partition x] at hFull
  have hDiff := greedyPrimeCalibratedError_difference x hx
  rw [greedyPrimeMissingEulerTail_eq_reciprocal_sub_mertens x] at hDiff
  have hK := greedyPrimeNicolasIntegral_eq_K_sub_tail x hx2
  have hEndpoint : nicolasThetaError x / (x * Real.log x) =
      (primeClassThetaReal greedyPrimeClass x - x) / (x * Real.log x) +
        primeClassThetaReal greedyDeletedPrimeClass x / (x * Real.log x) := by
    unfold nicolasThetaError
    rw [<- greedyPrimeClass_thetaReal_add_deleted x]
    ring
  rw [hEndpoint] at hFull
  dsimp only [greedyPrimeNicolasHeightRemainder, greedyPrimeNicolasEulerTail]
  linarith only [hFull, hDiff, hK]

theorem greedyPrimeNicolasHeightRemainder_nonneg (x : Real) (hx : 1 < x)
    (hS : 1 < primeClassThetaReal greedyPrimeClass x) :
    0 <= greedyPrimeNicolasHeightRemainder x := by
  let y : Real := primeClassThetaReal greedyPrimeClass x
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hy0 : 0 < y := lt_trans zero_lt_one hS
  have hLx : 0 < Real.log x := Real.log_pos hx
  have hLy : 0 < Real.log y := Real.log_pos hS
  have hFirst := Real.log_le_sub_one_of_pos (div_pos hLy hLx)
  rw [Real.log_div hLy.ne' hLx.ne'] at hFirst
  have hSecond := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
  rw [Real.log_div hy0.ne' hx0.ne'] at hSecond
  have hScaled := div_le_div_of_nonneg_right hSecond hLx.le
  have hFirstEq : Real.log y / Real.log x - 1 =
      (Real.log y - Real.log x) / Real.log x := by
    field_simp [hLx.ne']
  have hSecondEq : (y / x - 1) / Real.log x = (y - x) / (x * Real.log x) := by
    field_simp [hx0.ne', hLx.ne']
  rw [hFirstEq] at hFirst
  rw [hSecondEq] at hScaled
  have h := hFirst.trans hScaled
  change 0 <= (y - x) / (x * Real.log x) -
    (Real.log (Real.log y) - Real.log (Real.log x))
  exact sub_nonneg.mpr h

theorem greedyPrimeCalibratedError_le_integral_add_tail (x : Real) (hx : 3 <= x)
    (hS : 1 < primeClassThetaReal greedyPrimeClass x) :
    greedyPrimeCalibratedError x <=
      greedyPrimeNicolasIntegral x + greedyPrimeNicolasEulerTail x := by
  rw [greedyPrimeCalibratedError_eq_integral_sub_height_add_tail x hx]
  have h := greedyPrimeNicolasHeightRemainder_nonneg x (by linarith only [hx]) hS
  linarith only [h]

end PrimeFactorOscillations.PrimeClassDeletion
