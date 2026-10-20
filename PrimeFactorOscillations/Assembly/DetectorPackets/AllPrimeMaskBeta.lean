/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.AllPrimeMaskFactorization

/-!
# AllPrimeMaskBeta

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

namespace PrimeFactorOscillations.AllPrimeMask

open QuadraticCoprimeMean QuadraticCarrierPacket QuadraticDivisorMean
open QuadraticMainTermCancellation QuadraticPrincipalBoundary
open QuadraticBoundaryMean IntegerQuadraticPrefix

def pairMask (u n m : Nat) : Complex :=
  if And (Nat.Coprime u n) (Nat.Coprime u m) then 1 / (u : Complex) else 0

theorem pairMask_mul (p u n m : Nat) :
    pairMask (p * u) n m = pairMask p n m * pairMask u n m := by
  unfold pairMask
  simp only [Nat.coprime_mul_iff_left, Nat.cast_mul, one_div, mul_inv_rev]
  by_cases hp : And (Nat.Coprime p n) (Nat.Coprime p m)
  . by_cases hu : And (Nat.Coprime u n) (Nat.Coprime u m)
    . have hpu := And.intro (And.intro hp.1 hu.1) (And.intro hp.2 hu.2)
      rw [if_pos hpu, if_pos hp, if_pos hu]
      ring
    . have hpu : Not (And (And (Nat.Coprime p n) (Nat.Coprime u n))
          (And (Nat.Coprime p m) (Nat.Coprime u m))) :=
        fun h => hu (And.intro h.1.2 h.2.2)
      rw [if_neg hpu, if_pos hp, if_neg hu, mul_zero]
  . have hpu : Not (And (And (Nat.Coprime p n) (Nat.Coprime u n))
        (And (Nat.Coprime p m) (Nat.Coprime u m))) :=
      fun h => hp (And.intro h.1.1 h.2.1)
    rw [if_neg hpu, if_neg hp, zero_mul]

theorem pairMask_signedSum (G : Finset Nat) (n m : Nat)
    (hG : forall p, Membership.mem G p -> Nat.Prime p) :
    signedSum G (fun u => pairMask u n m) = (weight G n m : Complex) := by
  induction G using Finset.induction_on with
  | empty => simp [signedSum, subsetProduct, pairMask, weight]
  | @insert p G hp ih =>
    have hprime := hG p (Finset.mem_insert_self _ _)
    have hsmall := fun q hq => hG q (Finset.mem_insert_of_mem hq)
    have hscale : signedSum G (fun u => pairMask (p * u) n m) =
        pairMask p n m * signedSum G (fun u => pairMask u n m) := by
      simp only [pairMask_mul, signedSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro U hU
      ring
    have hlocal : (1 : Complex) - pairMask p n m =
        ((if Or (Dvd.dvd p n) (Dvd.dvd p m) then (1 : Real)
          else 1 - 1 / (p : Real)) : Complex) := by
      unfold pairMask
      simp only [hprime.coprime_iff_not_dvd]
      by_cases hn : Dvd.dvd p n <;> by_cases hm : Dvd.dvd p m <;>
        simp only [hn, hm, not_true_eq_false, not_false_eq_true, true_or,
          false_or, and_true, true_and, and_false, false_and, ite_true,
          ite_false, sub_zero, Complex.ofReal_one, Complex.ofReal_sub,
          Complex.ofReal_div, Complex.ofReal_natCast] <;> ring
    rw [signedSum_insert G p hp, hscale, ih hsmall]
    calc
      _ = (1 - pairMask p n m) * (weight G n m : Complex) := by ring
      _ = _ := by
        rw [hlocal]
        simp only [weight, Finset.prod_insert hp, Complex.ofReal_mul]
        split_ifs <;> push_cast <;> ring

theorem weightedForm_square (S T : Finset Nat) (a b : Nat -> Complex)
    (u v : Nat)
    (hS : forall n, Membership.mem S n -> 0 < n)
    (hT : forall m, Membership.mem T m -> 0 < m) :
    QuadraticPrincipalBoundary.weightedForm S T a b (u ^ 2 * v) =
      (1 / (u : Complex)) *
        QuadraticPrincipalBoundary.weightedForm S T
          (coprimeColumn u a) (coprimeColumn u b) v := by
  have hsqrt : Real.sqrt ((u ^ 2 * v : Nat) : Real) =
      (u : Real) * Real.sqrt (v : Real) := by
    push_cast
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]
  unfold QuadraticPrincipalBoundary.weightedForm rowForm
  rw [square_row_form S T a b u v hS hT, hsqrt]
  simp only [Complex.ofReal_mul, Complex.ofReal_natCast,
    div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

theorem weightedForm_square_expansion (S T : Finset Nat)
    (a b : Nat -> Complex) (u v : Nat)
    (hS : forall n, Membership.mem S n -> 0 < n)
    (hT : forall m, Membership.mem T m -> 0 < m) :
    QuadraticPrincipalBoundary.weightedForm S T a b (u ^ 2 * v) =
      S.sum (fun n => T.sum (fun m => pairMask u n m *
        ((if Nat.Coprime n m then
          (a n * kernel v n) * (b m * kernel v m) else 0) /
            (Real.sqrt (v : Real) : Complex)))) := by
  rw [weightedForm_square S T a b u v hS hT]
  unfold QuadraticPrincipalBoundary.weightedForm rowForm coprimeForm
  simp only [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  unfold coprimeColumn pairMask
  by_cases hnm : Nat.Coprime n m
  . rw [if_pos hnm, if_pos hnm]
    by_cases hun : Nat.Coprime u n
    . by_cases hum : Nat.Coprime u m
      . rw [if_pos hun, if_pos hum, if_pos (And.intro hun hum)]
      . have hboth : Not (And (Nat.Coprime u n) (Nat.Coprime u m)) :=
          fun h => hum h.2
        rw [if_neg hum, if_neg hboth]
        ring
    . have hboth : Not (And (Nat.Coprime u n) (Nat.Coprime u m)) :=
        fun h => hun h.1
      rw [if_neg hun, if_neg hboth]
      ring
  . rw [if_neg hnm, if_neg hnm]
    ring

theorem signed_square_factorization (G S T : Finset Nat)
    (a b : Nat -> Complex) (v : Nat)
    (hG : forall p, Membership.mem G p -> Nat.Prime p)
    (hS : forall n, Membership.mem S n -> 0 < n)
    (hT : forall m, Membership.mem T m -> 0 < m) :
    signedSum G (fun u =>
        QuadraticPrincipalBoundary.weightedForm S T a b (u ^ 2 * v)) =
      (density G : Complex) *
        QuadraticPrincipalBoundary.weightedForm S T
          (fun n => (amplifier G n : Complex) * a n)
          (fun m => (amplifier G m : Complex) * b m) v := by
  let f := fun n m => (if Nat.Coprime n m then
    (a n * kernel v n) * (b m * kernel v m) else 0) /
      (Real.sqrt (v : Real) : Complex)
  have heq : signedSum G (fun u =>
      QuadraticPrincipalBoundary.weightedForm S T a b (u ^ 2 * v)) =
      S.sum (fun n => T.sum (fun m => (weight G n m : Complex) * f n m)) := by
    unfold signedSum
    simp_rw [weightedForm_square_expansion S T a b _ v hS hT, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m hm
    change G.powerset.sum (fun U =>
      (-1 : Complex) ^ U.card * (pairMask (subsetProduct U) n m * f n m)) = _
    simp_rw [<- mul_assoc]
    rw [<- Finset.sum_mul]
    change signedSum G (fun u => pairMask u n m) * f n m = _
    rw [pairMask_signedSum G n m hG]
  have hform : S.sum (fun n => T.sum (fun m =>
      (weight G n m : Complex) * f n m)) =
      weightedForm G S T (fun n => a n * kernel v n)
        (fun m => b m * kernel v m) / (Real.sqrt (v : Real) : Complex) := by
    unfold weightedForm f
    simp only [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro m hm
    by_cases hc : Nat.Coprime n m
    . rw [if_pos hc, if_pos hc]
      ring
    . rw [if_neg hc, if_neg hc]
      ring
  rw [heq, hform, weightedForm_factorization G S T _ _
    (fun p hp => (hG p hp).two_le)]
  unfold QuadraticPrincipalBoundary.weightedForm rowForm
  simp only [mul_assoc]
  ring

theorem beta_factorization (G V S T : Finset Nat)
    (K : Nat) (a b : Nat -> Complex)
    (hG : forall p, Membership.mem G p -> Nat.Prime p)
    (hS : forall n, Membership.mem S n -> 0 < n)
    (hT : forall m, Membership.mem T m -> 0 < m) :
    beta G V K (QuadraticPrincipalBoundary.weightedForm S T a b) =
      (density G : Complex) *
        (V.filter (fun v => v <= K)).sum (fun v =>
          QuadraticPrincipalBoundary.weightedForm S T
            (fun n => (amplifier G n : Complex) * a n)
            (fun m => (amplifier G m : Complex) * b m) v) := by
  unfold beta
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases h : v <= K
  . simp only [h, ite_true]
    exact signed_square_factorization G S T a b v hG hS hT
  . simp only [h, ite_false, Finset.sum_const_zero]

theorem meanCap_mass_transfer (M N1 N2 : Nat) (S T : Finset Nat)
    (a b a' b' : Nat -> Complex) (c : Real) (hc : 0 <= c)
    (ha : maskedMass 1 S a' <= c * maskedMass 1 S a)
    (hb : maskedMass 1 T b' <= c * maskedMass 1 T b) :
    meanCap M N1 N2 S T a' b' <= c * meanCap M N1 N2 S T a b := by
  have hp : 0 <= prefixNorm M N1 := by unfold prefixNorm; exact sq_nonneg _
  have hq : 0 <= prefixNorm M N2 := by unfold prefixNorm; exact sq_nonneg _
  have hA := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left ha hp)
  have hB := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hb hq)
  have hA' : Real.sqrt (prefixNorm M N1 * maskedMass 1 S a') <=
      Real.sqrt c * Real.sqrt (prefixNorm M N1 * maskedMass 1 S a) := by
    simpa only [mul_left_comm (prefixNorm M N1) c, Real.sqrt_mul hc] using hA
  have hB' : Real.sqrt (prefixNorm M N2 * maskedMass 1 T b') <=
      Real.sqrt c * Real.sqrt (prefixNorm M N2 * maskedMass 1 T b) := by
    simpa only [mul_left_comm (prefixNorm M N2) c, Real.sqrt_mul hc] using hB
  unfold meanCap
  calc
    _ <= (Real.sqrt c * Real.sqrt (prefixNorm M N1 * maskedMass 1 S a)) *
        (Real.sqrt c * Real.sqrt (prefixNorm M N2 * maskedMass 1 T b)) :=
      mul_le_mul hA' hB' (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by
      rw [show (Real.sqrt c * Real.sqrt (prefixNorm M N1 * maskedMass 1 S a)) *
          (Real.sqrt c * Real.sqrt (prefixNorm M N2 * maskedMass 1 T b)) =
          (Real.sqrt c * Real.sqrt c) *
            (Real.sqrt (prefixNorm M N1 * maskedMass 1 S a) *
              Real.sqrt (prefixNorm M N2 * maskedMass 1 T b)) by ring,
        Real.mul_self_sqrt hc]

theorem beta_all_masks_mean_bound (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall (G V : Finset Nat) (K N1 N2 : Nat)
        (S T : Finset Nat) (a b : Nat -> Complex),
      0 < K -> 0 < N1 ->
      (forall p, Membership.mem G p -> Nat.Prime p) ->
      (forall v, Membership.mem V v -> v <= K ->
        Membership.mem (columns K) v) ->
      (forall n, Membership.mem S n -> Membership.mem (columns N1) n) ->
      (forall m, Membership.mem T m -> Membership.mem (columns N2) m) ->
      norm (beta G V K (QuadraticPrincipalBoundary.weightedForm S T a b)) <=
        density G * C * ((max N1 N2 : Nat) : Real) ^ eps *
          meanCap K N1 N2 S T a b := by
  choose C hC hc using weighted_tag_mean (eps / 2) (by linarith)
  choose A hA ha using amplifier_mass_subpower (eps / 2) (by linarith)
  refine Exists.intro (C * A) (And.intro (mul_pos hC hA) ?_)
  intro G V K N1 N2 S T a b hK hN1 hG hV hS hT
  let R := V.filter (fun v => v <= K)
  let a' := fun n => (amplifier G n : Complex) * a n
  let b' := fun n => (amplifier G n : Complex) * b n
  let J := max N1 N2
  let scale := A * (J : Real) ^ (eps / 2)
  have hscale : 0 <= scale := by dsimp only [scale]; positivity
  have hJ : 0 < (J : Real) := by
    exact_mod_cast hN1.trans_le (le_max_left N1 N2)
  have hrows : forall v, Membership.mem R v ->
      Membership.mem (columns K) (1 * v) := by
    intro v hv
    have hvF := Finset.mem_filter.mp hv
    simpa only [one_mul] using hV v hvF.1 hvF.2
  have hfreq : forall v, Membership.mem R v -> 1 <= 1 ^ 2 * (1 * v) := by
    intro v hv
    have hb := columns_bounds K v (by simpa only [one_mul] using hrows v hv)
    simpa only [one_pow, one_mul] using Nat.succ_le_of_lt hb.1
  have hmean := hc K N1 N2 1 1 1 (by decide) (by decide)
    R S T a' b' hrows hfreq hS hT
  simp only [one_pow, one_mul, Nat.cast_one, Real.sqrt_one, one_div_one] at hmean
  have hmassA : maskedMass 1 S a' <= scale * maskedMass 1 S a := by
    apply (ha G S N1 1 a hG hS).trans
    apply mul_le_mul_of_nonneg_right _ (by unfold maskedMass; positivity)
    apply mul_le_mul_of_nonneg_left _ hA.le
    exact Real.rpow_le_rpow (Nat.cast_nonneg N1)
      (Nat.cast_le.mpr (le_max_left N1 N2)) (by linarith)
  have hmassB : maskedMass 1 T b' <= scale * maskedMass 1 T b := by
    apply (ha G T N2 1 b hG hT).trans
    apply mul_le_mul_of_nonneg_right _ (by unfold maskedMass; positivity)
    apply mul_le_mul_of_nonneg_left _ hA.le
    exact Real.rpow_le_rpow (Nat.cast_nonneg N2)
      (Nat.cast_le.mpr (le_max_right N1 N2)) (by linarith)
  have hcap := meanCap_mass_transfer K N1 N2 S T a b a' b'
    scale hscale hmassA hmassB
  have hsum : norm (R.sum (fun v =>
      QuadraticPrincipalBoundary.weightedForm S T a' b' v)) <=
      C * A * (J : Real) ^ eps * meanCap K N1 N2 S T a b := by
    calc
      _ <= R.sum (fun v =>
          norm (QuadraticPrincipalBoundary.weightedForm S T a' b' v)) :=
        norm_sum_le _ _
      _ <= C * (J : Real) ^ (eps / 2) * meanCap K N1 N2 S T a' b' := hmean
      _ <= C * (J : Real) ^ (eps / 2) *
          (scale * meanCap K N1 N2 S T a b) :=
        mul_le_mul_of_nonneg_left hcap (by positivity)
      _ = _ := by
        have hp : (J : Real) ^ (eps / 2) * (J : Real) ^ (eps / 2) =
            (J : Real) ^ eps := by
          rw [<- Real.rpow_add hJ]
          congr 1
          ring
        dsimp only [scale]
        calc
          _ = C * A * ((J : Real) ^ (eps / 2) * (J : Real) ^ (eps / 2)) *
              meanCap K N1 N2 S T a b := by ring
          _ = _ := by rw [hp]
  rw [beta_factorization G V S T K a b hG
    (fun n hn => (columns_bounds N1 n (hS n hn)).1)
    (fun m hm => (columns_bounds N2 m (hT m hm)).1), norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (density_pos G (fun p hp => (hG p hp).two_le))]
  change density G * norm (R.sum (fun v =>
    QuadraticPrincipalBoundary.weightedForm S T a' b' v)) <= _
  calc
    _ <= density G *
        (C * A * (J : Real) ^ eps * meanCap K N1 N2 S T a b) :=
      mul_le_mul_of_nonneg_left hsum
        (density_pos G (fun p hp => (hG p hp).two_le)).le
    _ = _ := by ring

end PrimeFactorOscillations.AllPrimeMask

