/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Analysis.Normed.Module.Connected
import PrimeFactorOscillations.Assembly.DetectorPackets.DirichletCompanionIntegral

/-!
# DirichletCompanionIdentity

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described by LICENSE.
Authors: Prime Factor Oscillations contributors
-/


noncomputable section
open scoped BigOperators Classical
open MeasureTheory Filter Asymptotics

namespace PrimeFactorOscillations.PeriodicCompanion

theorem character_sum_Icc_eq_blockPrefix {q : Nat}
    (chi : DirichletCharacter Complex q) (N : Nat) :
    (Finset.Icc 1 N).sum (fun n => chi (n : ZMod q)) =
      blockPrefix (characterSequence chi) N := by
  have hset : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hset, Finset.sum_Ico_eq_sum_range]
  have hlen : N + 1 - 1 = N := by omega
  rw [hlen]
  unfold blockPrefix
  apply Finset.sum_congr rfl
  intro n _
  simp only [characterSequence, Nat.add_comm]

theorem character_partial_sum_bigO {q : Nat} (chi : DirichletCharacter Complex q) :
    IsBigO atTop (fun N : Nat => (Finset.Icc 1 N).sum (fun n => chi (n : ZMod q)))
      (fun N : Nat => (N : Real) ^ (1 : Real)) := by
  apply IsBigO.of_bound 1
  apply Filter.Eventually.of_forall
  intro N
  rw [character_sum_Icc_eq_blockPrefix]
  have hN : 0 <= (N : Real) := Nat.cast_nonneg N
  simpa only [Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg hN, one_mul]
    using character_prefix_norm_le chi N

theorem errorMellin_integrable (f : Nat -> Complex) (q : Nat) (hq : 0 < q)
    (hf : forall n : Nat, f (n + q) = f n)
    (hbound : forall n : Nat, norm (f n) <= 1) (s : Complex) (hs : 0 < s.re) :
    IntegrableOn (fun t : Real => (t : Complex) ^ (-s - 1) * floorError f q t)
      (Set.Ioi 1) := by
  have hc := mellinConvergent_of_isBigO_rpow
    ((cutError_locallyIntegrable f q hq hf hbound).locallyIntegrableOn (Set.Ioi 0))
    (cutError_top_bound f q hq hf hbound)
    (show (-s).re < (0 : Real) by simpa using neg_lt_zero.mpr hs)
    (cutError_bottom_bound f q ((-s).re - 1)) (by linarith)
  have hi : IntegrableOn
      (fun t : Real => (t : Complex) ^ (-s - 1) * cutError f q t) (Set.Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul] using hc
  have hsub : Set.Ioi (1 : Real) <= Set.Ioi (0 : Real) := by
    intro t ht
    exact lt_trans (show (0 : Real) < 1 by norm_num) (Set.mem_Ioi.mp ht)
  apply (hi.mono_set hsub).congr_fun _ measurableSet_Ioi
  intro t ht
  change (t : Complex) ^ (-s - 1) * cutError f q t =
    (t : Complex) ^ (-s - 1) * floorError f q t
  rw [cutError, Set.indicator_of_mem (s := Set.Ioi (1 : Real)) ht]

theorem companionContinuation_eq_LFunction_right {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : 0 < q)
    (s : Complex) (hs : 1 < s.re) :
    letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
    companionContinuation chi s = DirichletCharacter.LFunction chi s := by
  letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
  symm
  rw [chi.LFunction_eq_LSeries hs,
    LSeries_eq_mul_integral (fun n => chi (n : ZMod q)) (r := 1)
      (by norm_num) hs (chi.LSeriesSummable_of_one_lt_re hs)
      (character_partial_sum_bigO chi)]
  let m : Complex := mean (characterSequence chi) q
  have hspos : 0 < s.re := zero_lt_one.trans hs
  have he := errorMellin_integrable (characterSequence chi) q hq
    (characterSequence_periodic chi) (characterSequence_norm_le chi) s hspos
  have hp := integrableOn_Ioi_cpow_of_lt
    (show (-s).re < -1 by simpa using neg_lt_neg hs) (show (0 : Real) < 1 by norm_num)
  have hmInt := hp.const_mul m
  have hm : integral (volume.restrict (Set.Ioi (1 : Real)))
      (fun t : Real => m * (t : Complex) ^ (-s)) = m / (s - 1) := by
    rw [integral_const_mul, integral_Ioi_cpow_of_lt
      (show (-s).re < -1 by simpa using neg_lt_neg hs)
      (show (0 : Real) < 1 by norm_num)]
    simp only [Complex.ofReal_one, Complex.one_cpow]
    rw [show -s + 1 = -(s - 1) by ring, neg_div_neg_eq]
    ring
  have hsplit : integral (volume.restrict (Set.Ioi (1 : Real)))
      (fun t : Real => (Finset.Icc 1 (Nat.floor t)).sum (fun n => chi (n : ZMod q)) *
        (t : Complex) ^ (-(s + 1))) =
      integral (volume.restrict (Set.Ioi (1 : Real))) (fun t : Real =>
        m * (t : Complex) ^ (-s) +
          (t : Complex) ^ (-s - 1) * floorError (characterSequence chi) q t) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [character_sum_Icc_eq_blockPrefix]
    have ht0 : Not ((t : Complex) = 0) :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans zero_lt_one ht))
    have hpow : (t : Complex) * (t : Complex) ^ (-s - 1) = (t : Complex) ^ (-s) := by
      calc
        _ = (t : Complex) ^ (1 : Complex) * (t : Complex) ^ (-s - 1) := by
          rw [Complex.cpow_one]
        _ = (t : Complex) ^ (1 + (-s - 1)) := (Complex.cpow_add _ _ ht0).symm
        _ = _ := by congr 1; ring
    rw [show -(s + 1) = -s - 1 by ring]
    calc
      _ = (m * (t : Complex) + floorError (characterSequence chi) q t) *
          (t : Complex) ^ (-s - 1) := by
        dsimp [m, floorError]
        ring
      _ = m * ((t : Complex) * (t : Complex) ^ (-s - 1)) +
          (t : Complex) ^ (-s - 1) * floorError (characterSequence chi) q t := by ring
      _ = _ := by rw [hpow]
  rw [hsplit, integral_add hmInt he, hm, <- errorMellin_eq_integral]
  unfold companionContinuation
  dsimp [m]
  ring

def positivePuncture : Set Complex :=
  fun s => 0 < s.re /\ Not (s = 1)

theorem positivePuncture_isOpen : IsOpen positivePuncture := by
  change IsOpen (Inter.inter (fun s : Complex => 0 < s.re)
    (Compl.compl (Set.singleton (1 : Complex))))
  exact (Complex.isOpen_re_gt 0).inter isClosed_singleton.isOpen_compl

theorem positivePuncture_isPreconnected : IsPreconnected positivePuncture := by
  let H : Complex -> Complex :=
    fun z => (Real.exp z.re : Complex) + (z.im : Complex) * Complex.I
  have hH : Continuous H := by fun_prop
  have hHre (z : Complex) : (H z).re = Real.exp z.re := by
    simp only [H, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hHim (z : Complex) : (H z).im = z.im := by
    simp only [H, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_one, zero_mul, zero_add, add_zero]
  have hc : IsConnected (fun z : Complex => Not (z = 0)) := by
    have heq : (fun z : Complex => Not (z = 0)) =
        (Compl.compl (Singleton.singleton (0 : Complex)) : Set Complex) := by
      ext z
      rfl
    rw [heq]
    exact isConnected_compl_singleton_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; exact Nat.one_lt_ofNat) (0 : Complex)
  have himage : Set.image H (fun z : Complex => Not (z = 0)) = positivePuncture := by
    ext s
    constructor
    . intro hs
      cases hs with
      | intro z hz =>
        change 0 < s.re /\ Not (s = 1)
        rw [<- hz.2]
        refine And.intro ?_ ?_
        . rw [hHre]
          exact Real.exp_pos z.re
        . intro he
          have hre : Real.exp z.re = 1 := by
            have hr := congrArg Complex.re he
            rw [hHre] at hr
            simpa only [Complex.one_re] using hr
          have him : z.im = 0 := by
            have hi := congrArg Complex.im he
            rw [hHim] at hi
            simpa only [Complex.one_im] using hi
          apply hz.1
          apply Complex.ext
          . simpa only [Complex.zero_re] using (Real.exp_eq_one_iff z.re).mp hre
          . simpa only [Complex.zero_im] using him
    . intro hs
      change 0 < s.re /\ Not (s = 1) at hs
      let z : Complex := (Real.log s.re : Complex) + (s.im : Complex) * Complex.I
      have hzs : H z = s := by
        apply Complex.ext
        . rw [hHre]
          simp only [z, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
            sub_zero, add_zero]
          exact Real.exp_log hs.1
        . rw [hHim]
          simp only [z, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
            Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_one, zero_mul,
            zero_add, add_zero]
      have hz0 : Not (z = 0) := by
        intro hz
        apply hs.2
        calc
          s = H z := hzs.symm
          _ = 1 := by
            rw [hz]
            apply Complex.ext
            . rw [hHre]
              simp
            . rw [hHim]
              simp
      exact Exists.intro z (And.intro hz0 hzs)
  rw [<- himage]
  exact (hc.image H hH.continuousOn).isPreconnected

theorem companionContinuation_eq_LFunction {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : 0 < q)
    (s : Complex) (hs : 0 < s.re) (hs1 : Not (s = 1)) :
    letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
    companionContinuation chi s = DirichletCharacter.LFunction chi s := by
  letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
  have hF : AnalyticOnNhd Complex (companionContinuation chi) positivePuncture := by
    apply DifferentiableOn.analyticOnNhd _ positivePuncture_isOpen
    intro z hz
    exact (companionContinuation_differentiableAt chi hq z hz.1 hz.2).differentiableWithinAt
  have hL : AnalyticOnNhd Complex (DirichletCharacter.LFunction chi) positivePuncture := by
    apply DifferentiableOn.analyticOnNhd _ positivePuncture_isOpen
    intro z hz
    exact (chi.differentiableAt_LFunction z (Or.inl hz.2)).differentiableWithinAt
  have htwo : Membership.mem positivePuncture (2 : Complex) := by
    change 0 < (2 : Complex).re /\ Not ((2 : Complex) = 1)
    norm_num
  have heq : Filter.EventuallyEq (nhds (2 : Complex))
      (companionContinuation chi) (DirichletCharacter.LFunction chi) := by
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds
      (by norm_num : (1 : Real) < (2 : Complex).re)] with z hz
    exact companionContinuation_eq_LFunction_right chi hq z hz
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hF hL
    positivePuncture_isPreconnected htwo heq (And.intro hs hs1)

theorem dirichlet_LFunction_norm_bound {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : 0 < q)
    (s : Complex) (hs : 0 < s.re) (hs1 : Not (s = 1)) :
    letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
    norm (DirichletCharacter.LFunction chi s) <=
      norm s * (1 / norm (s - 1) + (2 * (q : Real) + 1) / s.re) := by
  letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
  rw [<- companionContinuation_eq_LFunction chi hq s hs hs1]
  exact companionContinuation_norm_bound chi hq s hs

end PrimeFactorOscillations.PeriodicCompanion
