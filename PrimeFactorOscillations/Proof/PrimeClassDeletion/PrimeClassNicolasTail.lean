/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.NicolasOscillation
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.RobinWeightedIntegral
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyPrimeEulerSummability
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeClassAbel

/-!
# Full Nicolas-kernel tails for actual prime classes

The complete theta mass is retained. The reciprocal-prime summability
proved for the actual greedy deletion supplies the infinite-tail consumer.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter MeasureTheory Set
open PrimeFactorOscillations.PrimeClassSampling

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem nicolasTailKernel_eq_robinRealWeight_one (t : Real) (ht : 1 < t) :
    Robin1984.nicolasTailKernel t = Robin1984.robinRealWeight 1 t := by
  have ht0 : 0 <= t := (lt_trans zero_lt_one ht).le
  have hlog : 0 < Real.log t := Real.log_pos ht
  unfold Robin1984.nicolasTailKernel Robin1984.robinRealWeight
  norm_num only [Nat.cast_one]
  rw [Real.rpow_neg ht0]
  norm_num only [Real.rpow_ofNat]
  field_simp [hlog.ne', (lt_trans zero_lt_one ht).ne']

theorem integrableOn_nicolasTailKernel (x : Real) (hx : 1 < x) :
    IntegrableOn Robin1984.nicolasTailKernel (Ioi x) := by
  have h := Robin1984.integrableOn_robinRealWeight (n := 1) (by norm_num) hx
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (nicolasTailKernel_eq_robinRealWeight_one t (lt_trans hx ht)).symm

theorem integral_nicolasTailKernel (x : Real) (hx : 1 < x) :
    integral (volume.restrict (Ioi x)) Robin1984.nicolasTailKernel =
      1 / (x * Real.log x) := by
  calc
    _ = integral (volume.restrict (Ioi x)) (Robin1984.robinRealWeight 1) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact nicolasTailKernel_eq_robinRealWeight_one t (lt_trans hx ht)
    _ = x ^ (-(1 : Real)) * Inv.inv (Real.log x) := by
      simpa only [Nat.cast_one] using
        Robin1984.integral_robinRealWeight (n := 1) (by norm_num) hx
    _ = 1 / (x * Real.log x) := by
      rw [Real.rpow_neg (lt_trans zero_lt_one hx).le, Real.rpow_one]
      ring

noncomputable def primeClassNicolasStep (P : Set Nat) (p : Nat) : Real -> Real := by
  classical
  exact if And (Nat.Prime p) (Membership.mem P p) then
    (Ici (p : Real)).indicator
      (fun u => Real.log (p : Real) * Robin1984.nicolasTailKernel u) else fun _ => 0

theorem primeClassNicolasStep_integrable (P : Set Nat) (p : Nat)
    (x : Real) (hx : 1 < x) :
    Integrable (primeClassNicolasStep P p) (volume.restrict (Ioi x)) := by
  classical
  by_cases hp : And (Nat.Prime p) (Membership.mem P p)
  case pos =>
    simp only [primeClassNicolasStep, ite_eq_left hp]
    exact ((integrableOn_nicolasTailKernel x hx).const_mul
      (Real.log (p : Real))).indicator measurableSet_Ici
  case neg =>
    simp only [primeClassNicolasStep, ite_eq_right hp]
    exact integrable_zero Real Real (volume.restrict (Ioi x))

theorem primeClassNicolasStep_integral (P : Set Nat) (p : Nat)
    (x : Real) (hx : 1 < x) :
    integral (volume.restrict (Ioi x)) (primeClassNicolasStep P p) =
      @ite Real (And (Nat.Prime p) (Membership.mem P p)) (Classical.propDecidable _)
        (Real.log (p : Real) /
          (max x (p : Real) * Real.log (max x (p : Real)))) 0 := by
  classical
  by_cases hp : And (Nat.Prime p) (Membership.mem P p)
  case neg => simp only [primeClassNicolasStep, ite_eq_right hp, integral_zero]
  case pos =>
    simp only [primeClassNicolasStep, ite_eq_left hp]
    rw [integral_indicator measurableSet_Ici,
      Measure.restrict_restrict measurableSet_Ici]
    change integral (volume.restrict {t : Real | And ((p : Real) <= t) (x < t)})
      (fun t => Real.log (p : Real) * Robin1984.nicolasTailKernel t) = _
    by_cases hpx : (p : Real) <= x
    case pos =>
      have hset : {t : Real | And ((p : Real) <= t) (x < t)} = Ioi x := by
        ext t
        constructor
        case mp => intro ht; exact ht.2
        case mpr => intro ht; exact And.intro (hpx.trans ht.le) ht
      rw [hset, integral_const_mul, integral_nicolasTailKernel x hx, max_eq_left hpx]
      ring
    case neg =>
      have hxp : x < (p : Real) := lt_of_not_ge hpx
      have hset : {t : Real | And ((p : Real) <= t) (x < t)} = Ici (p : Real) := by
        ext t
        constructor
        case mp => intro ht; exact ht.1
        case mpr => intro ht; exact And.intro ht (lt_of_lt_of_le hxp ht)
      rw [hset, integral_Ici_eq_integral_Ioi, integral_const_mul,
        integral_nicolasTailKernel (p : Real) (lt_trans hx hxp), max_eq_right hxp.le]
      ring

theorem primeClassNicolasStep_nonneg (P : Set Nat) (p : Nat)
    (t : Real) (ht : 1 < t) : 0 <= primeClassNicolasStep P p t := by
  classical
  by_cases hp : And (Nat.Prime p) (Membership.mem P p)
  case neg => simp only [primeClassNicolasStep, ite_eq_right hp, le_refl]
  case pos =>
    by_cases hpt : (p : Real) <= t
    case neg =>
      simp only [primeClassNicolasStep, ite_eq_left hp, Set.indicator,
        Set.mem_Ici, ite_eq_right hpt, le_refl]
    case pos =>
      simp only [primeClassNicolasStep, ite_eq_left hp, Set.indicator,
        Set.mem_Ici, ite_eq_left hpt]
      exact mul_nonneg
        (Real.log_nonneg (by exact_mod_cast hp.1.one_le))
        (Robin1984.nicolasTailKernel_nonneg ht.le)

theorem primeClassNicolasStep_integral_norm_le (P : Set Nat) (p : Nat)
    (x : Real) (hx : 1 < x) :
    integral (volume.restrict (Ioi x)) (fun t => norm (primeClassNicolasStep P p t)) <=
      classPowerWeight P 1 p := by
  classical
  have hnorm : integral (volume.restrict (Ioi x))
      (fun t => norm (primeClassNicolasStep P p t)) =
        integral (volume.restrict (Ioi x)) (primeClassNicolasStep P p) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact abs_of_nonneg (primeClassNicolasStep_nonneg P p t (lt_trans hx ht))
  rw [hnorm, primeClassNicolasStep_integral P p x hx]
  by_cases hp : And (Nat.Prime p) (Membership.mem P p)
  case neg =>
    simp only [classPowerWeight, ite_eq_right hp, le_refl]
  case pos =>
    simp only [classPowerWeight, ite_eq_left hp, Real.rpow_neg_one]
    let q : Real := max x (p : Real)
    have hp0 : (0 : Real) < p := Nat.cast_pos.mpr hp.1.pos
    have hlog : 0 < Real.log (p : Real) :=
      Real.log_pos (by exact_mod_cast hp.1.one_lt)
    have hpq : (p : Real) <= q := le_max_right x (p : Real)
    have hden : (p : Real) * Real.log (p : Real) <= q * Real.log q :=
      mul_le_mul hpq (Real.log_le_log hp0 hpq) hlog.le (hp0.le.trans hpq)
    calc
      Real.log (p : Real) / (q * Real.log q) =
          Real.log (p : Real) * (1 / (q * Real.log q)) := by ring
      _ <= Real.log (p : Real) * (1 / ((p : Real) * Real.log (p : Real))) :=
        mul_le_mul_of_nonneg_left
          (one_div_le_one_div_of_le (mul_pos hp0 hlog) hden) hlog.le
      _ = Inv.inv (p : Real) := by
        field_simp [hp0.ne', hlog.ne']

theorem primeClassNicolasStep_tsum (P : Set Nat) (t : Real) (ht : 0 <= t) :
    tsum (fun p : Nat => primeClassNicolasStep P p t) =
      primeClassThetaReal P t * Robin1984.nicolasTailKernel t := by
  classical
  let S := primeClassPrefix P (Nat.floor t)
  have hout (p : Nat) (hp : Not (Membership.mem S p)) :
      primeClassNicolasStep P p t = 0 := by
    by_cases hclass : And (Nat.Prime p) (Membership.mem P p)
    case neg => simp only [primeClassNicolasStep, ite_eq_right hclass]
    case pos =>
      have hnpt : Not ((p : Real) <= t) := by
        intro hpt
        apply hp
        exact (primeClassPrefix_mem_iff P (Nat.floor t) p).mpr
          (And.intro hclass.1.two_le (And.intro (Nat.le_floor hpt) hclass))
      simp only [primeClassNicolasStep, ite_eq_left hclass, Set.indicator,
        Set.mem_Ici, ite_eq_right hnpt]
  calc
    _ = S.sum (fun p => primeClassNicolasStep P p t) := tsum_eq_sum hout
    _ = S.sum (fun p => Real.log (p : Real) * Robin1984.nicolasTailKernel t) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hm := (primeClassPrefix_mem_iff P (Nat.floor t) p).mp hp
      have hpt : (p : Real) <= t :=
        (Nat.cast_le.mpr hm.2.1).trans (Nat.floor_le ht)
      simp only [primeClassNicolasStep, ite_eq_left hm.2.2, Set.indicator,
        Set.mem_Ici, ite_eq_left hpt]
    _ = _ := by simp only [S, primeClassThetaReal, primeClassTheta, Finset.sum_mul]

theorem primeClassNicolasTail_eq_tsum (P : Set Nat) (x : Real) (hx : 1 < x)
    (hs : Summable (classPowerWeight P 1)) :
    integral (volume.restrict (Ioi x))
        (fun t => primeClassThetaReal P t * Robin1984.nicolasTailKernel t) =
      tsum (fun p : Nat => integral (volume.restrict (Ioi x))
        (primeClassNicolasStep P p)) := by
  have hsNorm : Summable (fun p : Nat =>
      integral (volume.restrict (Ioi x)) (fun t => norm (primeClassNicolasStep P p t))) :=
    Summable.of_nonneg_of_le
      (fun p => integral_nonneg (fun t => norm_nonneg (primeClassNicolasStep P p t)))
      (fun p => primeClassNicolasStep_integral_norm_le P p x hx) hs
  have hswap := integral_tsum_of_summable_integral_norm
    (fun p => primeClassNicolasStep_integrable P p x hx) hsNorm
  calc
    _ = integral (volume.restrict (Ioi x))
        (fun t => tsum (fun p : Nat => primeClassNicolasStep P p t)) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (primeClassNicolasStep_tsum P t (lt_trans zero_lt_one (lt_trans hx ht)).le).symm
    _ = _ := hswap.symm

noncomputable def primeClassReciprocalTail (P : Set Nat) (x : Real) : Nat -> Real := by
  classical
  exact fun p => if x < (p : Real) then classPowerWeight P 1 p else 0

theorem primeClassNicolasTail_abel (P : Set Nat) (x : Real) (hx : 1 < x)
    (hs : Summable (classPowerWeight P 1)) :
    integral (volume.restrict (Ioi x))
        (fun t => primeClassThetaReal P t * Robin1984.nicolasTailKernel t) =
      primeClassThetaReal P x / (x * Real.log x) +
        tsum (primeClassReciprocalTail P x) := by
  classical
  let S := primeClassPrefix P (Nat.floor x)
  let low : Nat -> Real := fun p =>
    if Membership.mem S p then Real.log (p : Real) / (x * Real.log x) else 0
  have hHigh0 (p : Nat) : 0 <= primeClassReciprocalTail P x p := by
    dsimp only [primeClassReciprocalTail]
    split_ifs
    case pos => exact classPowerWeight_nonneg P 1 p
    case neg => exact le_refl 0
  have hHighLe (p : Nat) : primeClassReciprocalTail P x p <= classPowerWeight P 1 p := by
    dsimp only [primeClassReciprocalTail]
    split_ifs
    case pos => exact le_refl _
    case neg => exact classPowerWeight_nonneg P 1 p
  have hsHigh : Summable (primeClassReciprocalTail P x) :=
    Summable.of_nonneg_of_le hHigh0 hHighLe hs
  have hLow0 (p : Nat) : 0 <= low p := by
    dsimp only [low]
    split_ifs with hp
    case neg => exact le_refl 0
    case pos =>
      have hm := (primeClassPrefix_mem_iff P (Nat.floor x) p).mp hp
      exact div_nonneg
        (Real.log_nonneg (by exact_mod_cast hm.2.2.1.one_le))
        (mul_nonneg (lt_trans zero_lt_one hx).le (Real.log_pos hx).le)
  have hEach (p : Nat) :
      integral (volume.restrict (Ioi x)) (primeClassNicolasStep P p) =
        low p + primeClassReciprocalTail P x p := by
    rw [primeClassNicolasStep_integral P p x hx]
    by_cases hp : And (Nat.Prime p) (Membership.mem P p)
    case neg =>
      have hnotS : Not (Membership.mem S p) := by
        intro hIn
        exact hp ((primeClassPrefix_mem_iff P (Nat.floor x) p).mp hIn).2.2
      simp only [low, ite_eq_right hnotS,
        primeClassReciprocalTail, classPowerWeight, ite_eq_right hp]
      split_ifs <;> norm_num
    case pos =>
      by_cases hpx : (p : Real) <= x
      case pos =>
        have hIn : Membership.mem S p :=
          (primeClassPrefix_mem_iff P (Nat.floor x) p).mpr
            (And.intro hp.1.two_le (And.intro (Nat.le_floor hpx) hp))
        have hNot : Not (x < (p : Real)) := not_lt.mpr hpx
        simp only [ite_eq_left hp, max_eq_left hpx, low, ite_eq_left hIn,
          primeClassReciprocalTail, ite_eq_right hNot, add_zero]
      case neg =>
        have hxp : x < (p : Real) := lt_of_not_ge hpx
        have hnotS : Not (Membership.mem S p) := by
          intro hIn
          have hm := (primeClassPrefix_mem_iff P (Nat.floor x) p).mp hIn
          exact hpx ((Nat.cast_le.mpr hm.2.1).trans
            (Nat.floor_le (lt_trans zero_lt_one hx).le))
        have hp0 : (0 : Real) < p := Nat.cast_pos.mpr hp.1.pos
        have hlog : 0 < Real.log (p : Real) :=
          Real.log_pos (by exact_mod_cast hp.1.one_lt)
        simp only [max_eq_right hxp.le, low, ite_eq_right hnotS,
          primeClassReciprocalTail, ite_eq_left hxp, classPowerWeight,
          ite_eq_left hp, Real.rpow_neg_one, zero_add]
        field_simp [hp0.ne', hlog.ne']
  have hInt0 (p : Nat) :
      0 <= integral (volume.restrict (Ioi x)) (primeClassNicolasStep P p) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact primeClassNicolasStep_nonneg P p t (lt_trans hx ht)
  have hsInt : Summable (fun p : Nat =>
      integral (volume.restrict (Ioi x)) (primeClassNicolasStep P p)) := by
    apply Summable.of_nonneg_of_le hInt0 _ hs
    intro p
    have h := primeClassNicolasStep_integrable P p x hx
    exact (integral_mono h h.norm (fun t => le_abs_self (primeClassNicolasStep P p t))).trans
      (primeClassNicolasStep_integral_norm_le P p x hx)
  have hsLow : Summable low := by
    apply Summable.of_nonneg_of_le hLow0 _ hsInt
    intro p
    rw [hEach]
    exact le_add_of_nonneg_right (hHigh0 p)
  have hLowTotal : tsum low = primeClassThetaReal P x / (x * Real.log x) := by
    calc
      _ = S.sum low := tsum_eq_sum (fun p hp => by simp only [ite_eq_right hp])
      _ = S.sum (fun p => Real.log (p : Real) / (x * Real.log x)) := by
        apply Finset.sum_congr rfl
        intro p hp
        simp only [low, ite_eq_left hp]
      _ = _ := by simp only [S, primeClassThetaReal, primeClassTheta, Finset.sum_div]
  calc
    _ = tsum (fun p : Nat => integral (volume.restrict (Ioi x))
        (primeClassNicolasStep P p)) := primeClassNicolasTail_eq_tsum P x hx hs
    _ = tsum (fun p : Nat => low p + primeClassReciprocalTail P x p) :=
      tsum_congr hEach
    _ = tsum low + tsum (primeClassReciprocalTail P x) := hsLow.tsum_add hsHigh
    _ = _ := by rw [hLowTotal]

theorem primeClassNicolasTail_integrable (P : Set Nat) (x : Real) (hx : 1 < x)
    (hs : Summable (classPowerWeight P 1)) :
    IntegrableOn (fun t => primeClassThetaReal P t * Robin1984.nicolasTailKernel t)
      (Ioi x) := by
  classical
  by_cases hP : Exists fun p : Nat => And (Nat.Prime p) (Membership.mem P p)
  case neg =>
    have hTheta (t : Real) : primeClassThetaReal P t = 0 := by
      unfold primeClassThetaReal primeClassTheta
      apply Finset.sum_eq_zero
      intro p hp
      exact False.elim (hP (Exists.intro p
        ((primeClassPrefix_mem_iff P (Nat.floor t) p).mp hp).2.2))
    have heq : (fun t => primeClassThetaReal P t * Robin1984.nicolasTailKernel t) =
        (fun _ : Real => 0) := by
      funext t
      rw [hTheta t, zero_mul]
    rw [heq]
    exact integrable_zero Real Real (volume.restrict (Ioi x))
  case pos =>
    choose p hp using hP
    have hInt0 (q : Nat) :
        0 <= integral (volume.restrict (Ioi x)) (primeClassNicolasStep P q) := by
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact primeClassNicolasStep_nonneg P q t (lt_trans hx ht)
    have hsInt : Summable (fun q : Nat =>
        integral (volume.restrict (Ioi x)) (primeClassNicolasStep P q)) := by
      apply Summable.of_nonneg_of_le hInt0 _ hs
      intro q
      have h := primeClassNicolasStep_integrable P q x hx
      exact (integral_mono h h.norm (fun t => le_abs_self (primeClassNicolasStep P q t))).trans
        (primeClassNicolasStep_integral_norm_le P q x hx)
    have hAtomPos : 0 < integral (volume.restrict (Ioi x)) (primeClassNicolasStep P p) := by
      rw [primeClassNicolasStep_integral P p x hx, ite_eq_left hp]
      have hq : 1 < max x (p : Real) := lt_of_lt_of_le hx (le_max_left _ _)
      exact div_pos (Real.log_pos (by exact_mod_cast hp.1.one_lt))
        (mul_pos (lt_trans zero_lt_one hq) (Real.log_pos hq))
    have hBound := hsInt.sum_le_tsum ({p} : Finset Nat) (fun q _ => hInt0 q)
    simp only [Finset.sum_singleton] at hBound
    have hPos : 0 < integral (volume.restrict (Ioi x))
        (fun t => primeClassThetaReal P t * Robin1984.nicolasTailKernel t) := by
      rw [primeClassNicolasTail_eq_tsum P x hx hs]
      exact lt_of_lt_of_le hAtomPos hBound
    by_contra hNot
    have hZero := integral_undef hNot
    linarith only [hPos, hZero]

theorem greedyDeletedPrimeClass_nicolas_tail (x : Real) (hx : 1 < x) :
    And
      (IntegrableOn (fun t => primeClassThetaReal greedyDeletedPrimeClass t *
        Robin1984.nicolasTailKernel t) (Ioi x))
      (integral (volume.restrict (Ioi x))
          (fun t => primeClassThetaReal greedyDeletedPrimeClass t *
            Robin1984.nicolasTailKernel t) =
        primeClassThetaReal greedyDeletedPrimeClass x / (x * Real.log x) +
          tsum (primeClassReciprocalTail greedyDeletedPrimeClass x)) := by
  exact And.intro
    (primeClassNicolasTail_integrable greedyDeletedPrimeClass x hx
      greedyDeletedPrimeClass_reciprocal_summable)
    (primeClassNicolasTail_abel greedyDeletedPrimeClass x hx
      greedyDeletedPrimeClass_reciprocal_summable)

end PrimeFactorOscillations.PrimeClassDeletion
