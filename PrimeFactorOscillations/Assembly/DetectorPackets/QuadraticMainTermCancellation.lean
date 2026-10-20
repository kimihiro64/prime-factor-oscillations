/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.IntegerQuadraticEffectiveFrequency

/-!
# QuadraticMainTermCancellation

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

namespace PrimeFactorOscillations.QuadraticMainTermCancellation

def subsetProduct (s : Finset Nat) : Nat := s.prod id

def plainSum (s : Finset Nat) (f : Nat -> Complex) : Complex :=
  s.powerset.sum (fun t => f (subsetProduct t))

def signedSum (s : Finset Nat) (f : Nat -> Complex) : Complex :=
  s.powerset.sum (fun t => (-1 : Complex) ^ t.card * f (subsetProduct t))

def paired (s : Finset Nat) (f : Nat -> Complex) : Complex :=
  signedSum s (fun e => plainSum s (fun b => f (e * b)))

theorem plainSum_congr (s : Finset Nat) {f g : Nat -> Complex}
    (h : forall n, f n = g n) : plainSum s f = plainSum s g := by
  unfold plainSum
  apply Finset.sum_congr rfl
  intro t ht
  exact h (subsetProduct t)

theorem signedSum_congr (s : Finset Nat) {f g : Nat -> Complex}
    (h : forall n, f n = g n) : signedSum s f = signedSum s g := by
  unfold signedSum
  apply Finset.sum_congr rfl
  intro t ht
  rw [h]

theorem plainSum_insert (s : Finset Nat) (p : Nat)
    (hp : Not (Membership.mem s p)) (f : Nat -> Complex) :
    plainSum (insert p s) f =
      plainSum s f + plainSum s (fun n => f (p * n)) := by
  unfold plainSum
  rw [Finset.sum_powerset_insert hp]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  have hpt : Not (Membership.mem t p) :=
    fun h => hp ((Finset.mem_powerset.mp ht) h)
  simp only [subsetProduct, Finset.prod_insert hpt, id_eq]

theorem signedSum_insert (s : Finset Nat) (p : Nat)
    (hp : Not (Membership.mem s p)) (f : Nat -> Complex) :
    signedSum (insert p s) f =
      signedSum s f - signedSum s (fun n => f (p * n)) := by
  unfold signedSum
  rw [Finset.sum_powerset_insert hp, sub_eq_add_neg, <- Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  have hpt : Not (Membership.mem t p) :=
    fun h => hp ((Finset.mem_powerset.mp ht) h)
  simp only [Finset.card_insert_of_notMem hpt, pow_succ,
    subsetProduct, Finset.prod_insert hpt, id_eq]
  ring

theorem signedSum_add (s : Finset Nat) (f g : Nat -> Complex) :
    signedSum s (fun n => f n + g n) = signedSum s f + signedSum s g := by
  simp only [signedSum, mul_add, Finset.sum_add_distrib]

theorem paired_insert (s : Finset Nat) (p : Nat)
    (hp : Not (Membership.mem s p)) (f : Nat -> Complex) :
    paired (insert p s) f =
      paired s f - paired s (fun n => f (p ^ 2 * n)) := by
  unfold paired
  rw [signedSum_insert s p hp]
  have hfirst (e : Nat) :
      plainSum (insert p s) (fun b => f (e * b)) =
        plainSum s (fun b => f (e * b)) +
          plainSum s (fun b => f (p * (e * b))) := by
    rw [plainSum_insert s p hp]
    congr 1
    apply plainSum_congr
    intro b
    congr 1
    ring
  have hsecond (e : Nat) :
      plainSum (insert p s) (fun b => f ((p * e) * b)) =
        plainSum s (fun b => f (p * (e * b))) +
          plainSum s (fun b => f (p ^ 2 * (e * b))) := by
    rw [plainSum_insert s p hp]
    congr 1
    . apply plainSum_congr
      intro b
      congr 1
      ring
    . apply plainSum_congr
      intro b
      congr 1
      ring
  rw [signedSum_congr s hfirst, signedSum_congr s hsecond,
    signedSum_add, signedSum_add]
  ring

theorem paired_eq_square (s : Finset Nat) (f : Nat -> Complex) :
    paired s f = signedSum s (fun n => f (n ^ 2)) := by
  induction s using Finset.induction_on generalizing f with
  | empty => simp [paired, signedSum, plainSum, subsetProduct]
  | @insert p s hp ih =>
    rw [paired_insert s p hp, ih, ih, signedSum_insert s p hp]
    congr 1
    apply signedSum_congr
    intro n
    congr 1
    ring

theorem paired_with_external_factor (s : Finset Nat) (v : Nat)
    (f : Nat -> Complex) :
    s.powerset.sum (fun e => s.powerset.sum (fun b =>
      (-1 : Complex) ^ e.card * f (subsetProduct e * subsetProduct b * v))) =
        s.powerset.sum (fun u =>
          (-1 : Complex) ^ u.card * f ((subsetProduct u) ^ 2 * v)) := by
  have h := paired_eq_square s (fun n => f (n * v))
  simpa only [paired, signedSum, plainSum, Finset.mul_sum] using h


theorem subsetProduct_one_le (s t : Finset Nat)
    (hs : forall p, Membership.mem s p -> 1 <= p)
    (ht : Membership.mem s.powerset t) :
    1 <= subsetProduct t := by
  have hp : 0 < subsetProduct t := Finset.prod_pos
    (fun p hpt => Nat.lt_of_lt_of_le Nat.zero_lt_one
      (hs p ((Finset.mem_powerset.mp ht) hpt)))
  exact hp

theorem subsetProduct_le (s t : Finset Nat)
    (hs : forall p, Membership.mem s p -> 1 <= p)
    (ht : Membership.mem s.powerset t) :
    subsetProduct t <= subsetProduct s := by
  apply Finset.prod_le_prod_of_subset_of_one_le (Finset.mem_powerset.mp ht)
  intro p hps hpt
  exact hs p hps

def alpha (s : Finset Nat) (V : Finset Nat) (K : Nat)
    (f : Nat -> Complex) : Complex :=
  V.sum (fun v => s.powerset.sum (fun e => s.powerset.sum (fun b =>
    if subsetProduct b * v <= K then
      (-1 : Complex) ^ e.card * f (subsetProduct e * subsetProduct b * v)
    else 0)))

def beta (s : Finset Nat) (V : Finset Nat) (K : Nat)
    (f : Nat -> Complex) : Complex :=
  V.sum (fun v => s.powerset.sum (fun u =>
    if v <= K then
      (-1 : Complex) ^ u.card * f ((subsetProduct u) ^ 2 * v)
    else 0))

theorem truncated_low_equal (s : Finset Nat) (V : Finset Nat) (K : Nat)
    (hs : forall p, Membership.mem s p -> 1 <= p) (f : Nat -> Complex)
    (hf : forall n, K < n -> f n = 0) :
    alpha s V K f = beta s V K f := by
  have ha : alpha s V K f =
      V.sum (fun v => s.powerset.sum (fun e => s.powerset.sum (fun b =>
        (-1 : Complex) ^ e.card * f (subsetProduct e * subsetProduct b * v)))) := by
    unfold alpha
    apply Finset.sum_congr rfl
    intro v hv
    apply Finset.sum_congr rfl
    intro e he
    apply Finset.sum_congr rfl
    intro b hb
    split_ifs with h
    . rfl
    . have hepos := subsetProduct_one_le s e hs he
      have hle : subsetProduct b * v <= subsetProduct e * subsetProduct b * v := by
        nlinarith
      rw [hf _ (lt_of_lt_of_le (Nat.lt_of_not_ge h) hle), mul_zero]
  have hb : beta s V K f =
      V.sum (fun v => s.powerset.sum (fun u =>
        (-1 : Complex) ^ u.card * f ((subsetProduct u) ^ 2 * v))) := by
    unfold beta
    apply Finset.sum_congr rfl
    intro v hv
    apply Finset.sum_congr rfl
    intro u hu
    split_ifs with h
    . rfl
    . have hupos := subsetProduct_one_le s u hs hu
      have hu2 : 1 <= (subsetProduct u) ^ 2 := by
        simpa only [one_pow] using (Nat.pow_le_pow_left hupos 2)
      have hle : v <= (subsetProduct u) ^ 2 * v := by
        simpa only [one_mul] using (Nat.mul_le_mul_right v hu2)
      rw [hf _ (lt_of_lt_of_le (Nat.lt_of_not_ge h) hle), mul_zero]
  rw [ha, hb]
  apply Finset.sum_congr rfl
  intro v hv
  exact paired_with_external_factor s v f

def alphaCoeff (s : Finset Nat) (V : Finset Nat) (K w : Nat) : Complex :=
  alpha s V K (fun n => if n = w then 1 else 0)

def betaCoeff (s : Finset Nat) (V : Finset Nat) (K w : Nat) : Complex :=
  beta s V K (fun n => if n = w then 1 else 0)

def gammaCoeff (s : Finset Nat) (V : Finset Nat) (K w : Nat) : Complex :=
  alphaCoeff s V K w - betaCoeff s V K w

theorem coefficients_equal_below_cutoff (s : Finset Nat) (V : Finset Nat)
    (K w : Nat) (hs : forall p, Membership.mem s p -> 1 <= p) (hw : w <= K) :
    alphaCoeff s V K w = betaCoeff s V K w := by
  apply truncated_low_equal s V K hs
  intro n hn
  have hne : Not (n = w) := by omega
  simp only [if_neg hne]

theorem alpha_zero_of_prefix_zero (s : Finset Nat) (V : Finset Nat) (K : Nat)
    (hs : forall p, Membership.mem s p -> 1 <= p) (f : Nat -> Complex)
    (hf : forall n, n <= K * subsetProduct s -> f n = 0) :
    alpha s V K f = 0 := by
  unfold alpha
  apply Finset.sum_eq_zero
  intro v hv
  apply Finset.sum_eq_zero
  intro e he
  apply Finset.sum_eq_zero
  intro b hb
  split_ifs with h
  . have hemax := subsetProduct_le s e hs he
    have hle : subsetProduct e * subsetProduct b * v <= K * subsetProduct s := by
      calc
        _ = subsetProduct e * (subsetProduct b * v) := by ring
        _ <= subsetProduct s * K := Nat.mul_le_mul hemax h
        _ = _ := by ring
    rw [hf _ hle, mul_zero]
  . rfl

theorem beta_zero_of_prefix_zero (s : Finset Nat) (V : Finset Nat) (K : Nat)
    (hs : forall p, Membership.mem s p -> 1 <= p) (f : Nat -> Complex)
    (hf : forall n, n <= K * (subsetProduct s) ^ 2 -> f n = 0) :
    beta s V K f = 0 := by
  unfold beta
  apply Finset.sum_eq_zero
  intro v hv
  apply Finset.sum_eq_zero
  intro u hu
  split_ifs with h
  . have humax := subsetProduct_le s u hs hu
    have hle : (subsetProduct u) ^ 2 * v <= K * (subsetProduct s) ^ 2 := by
      calc
        _ <= (subsetProduct s) ^ 2 * K :=
          Nat.mul_le_mul (Nat.pow_le_pow_left humax 2) h
        _ = _ := by ring
    rw [hf _ hle, mul_zero]
  . rfl

theorem gamma_zero_below_cutoff (s : Finset Nat) (V : Finset Nat)
    (K w : Nat) (hs : forall p, Membership.mem s p -> 1 <= p) (hw : w <= K) :
    gammaCoeff s V K w = 0 := by
  unfold gammaCoeff
  rw [coefficients_equal_below_cutoff s V K w hs hw, sub_self]

theorem gamma_zero_above_support (s : Finset Nat) (V : Finset Nat)
    (K w : Nat) (hs : forall p, Membership.mem s p -> 1 <= p)
    (hw : K * (subsetProduct s) ^ 2 < w) :
    gammaCoeff s V K w = 0 := by
  have hspos : 1 <= subsetProduct s :=
    subsetProduct_one_le s s hs (Finset.mem_powerset.mpr (fun x hx => hx))
  have hs2 : subsetProduct s <= (subsetProduct s) ^ 2 := by nlinarith
  have hK : K * subsetProduct s <= K * (subsetProduct s) ^ 2 :=
    Nat.mul_le_mul_left K hs2
  have ha : alphaCoeff s V K w = 0 := by
    apply alpha_zero_of_prefix_zero s V K hs
    intro n hn
    have hne : Not (n = w) := by omega
    simp only [if_neg hne]
  have hb : betaCoeff s V K w = 0 := by
    apply beta_zero_of_prefix_zero s V K hs
    intro n hn
    have hne : Not (n = w) := by omega
    simp only [if_neg hne]
  simp only [gammaCoeff, ha, hb, sub_self]

theorem gamma_support (s : Finset Nat) (V : Finset Nat) (K w : Nat)
    (hs : forall p, Membership.mem s p -> 1 <= p)
    (hw : Not (gammaCoeff s V K w = 0)) :
    K < w /\ w <= K * (subsetProduct s) ^ 2 := by
  constructor
  . by_contra h
    exact hw (gamma_zero_below_cutoff s V K w hs (Nat.le_of_not_gt h))
  . by_contra h
    exact hw (gamma_zero_above_support s V K w hs (Nat.lt_of_not_ge h))


theorem alpha_sub (s : Finset Nat) (V : Finset Nat) (K : Nat)
    (f g : Nat -> Complex) :
    alpha s V K (fun n => f n - g n) = alpha s V K f - alpha s V K g := by
  unfold alpha
  have h (v : Nat) (e b : Finset Nat) :
      (if subsetProduct b * v <= K then
        (-1 : Complex) ^ e.card *
          (f (subsetProduct e * subsetProduct b * v) -
            g (subsetProduct e * subsetProduct b * v)) else 0) =
      (if subsetProduct b * v <= K then
        (-1 : Complex) ^ e.card * f (subsetProduct e * subsetProduct b * v)
        else 0) -
      (if subsetProduct b * v <= K then
        (-1 : Complex) ^ e.card * g (subsetProduct e * subsetProduct b * v)
        else 0) := by
    split_ifs <;> ring
  simp_rw [h, Finset.sum_sub_distrib]

theorem beta_sub (s : Finset Nat) (V : Finset Nat) (K : Nat)
    (f g : Nat -> Complex) :
    beta s V K (fun n => f n - g n) = beta s V K f - beta s V K g := by
  unfold beta
  have h (v : Nat) (u : Finset Nat) :
      (if v <= K then
        (-1 : Complex) ^ u.card *
          (f ((subsetProduct u) ^ 2 * v) - g ((subsetProduct u) ^ 2 * v))
        else 0) =
      (if v <= K then
        (-1 : Complex) ^ u.card * f ((subsetProduct u) ^ 2 * v) else 0) -
      (if v <= K then
        (-1 : Complex) ^ u.card * g ((subsetProduct u) ^ 2 * v) else 0) := by
    split_ifs <;> ring
  simp_rw [h, Finset.sum_sub_distrib]

def boundaryWeight (s : Finset Nat) (K : Nat)
    (f : Nat -> Complex) (n : Nat) : Complex :=
  if K < n /\ n <= K * (subsetProduct s) ^ 2 then f n else 0

theorem compensated_boundary_identity (s : Finset Nat) (V : Finset Nat) (K : Nat)
    (hs : forall p, Membership.mem s p -> 1 <= p) (f : Nat -> Complex) :
    alpha s V K f - beta s V K f =
      alpha s V K (boundaryWeight s K f) -
        beta s V K (boundaryWeight s K f) := by
  let low : Nat -> Complex := fun n => if n <= K then f n else 0
  let tail : Nat -> Complex := boundaryWeight s K f
  have hlow : alpha s V K low = beta s V K low := by
    apply truncated_low_equal s V K hs low
    intro n hn
    dsimp only [low]
    rw [if_neg (Nat.not_le.mpr hn)]
  have hspos : 1 <= subsetProduct s :=
    subsetProduct_one_le s s hs (Finset.mem_powerset.mpr (fun x hx => hx))
  have hs2 : subsetProduct s <= (subsetProduct s) ^ 2 := by nlinarith
  have hK : K * subsetProduct s <= K * (subsetProduct s) ^ 2 :=
    Nat.mul_le_mul_left K hs2
  have hsplit (n : Nat) (hn : n <= K * (subsetProduct s) ^ 2) :
      f n - low n - tail n = 0 := by
    dsimp only [low, tail, boundaryWeight]
    by_cases h : n <= K
    . rw [if_pos h, if_neg (fun ht => (Nat.not_lt.mpr h) ht.1)]
      ring
    . rw [if_neg h, if_pos (And.intro (Nat.lt_of_not_ge h) hn)]
      ring
  have ha0 : alpha s V K (fun n => f n - low n - tail n) = 0 :=
    alpha_zero_of_prefix_zero s V K hs _ (fun n hn => hsplit n (le_trans hn hK))
  have hb0 : beta s V K (fun n => f n - low n - tail n) = 0 :=
    beta_zero_of_prefix_zero s V K hs _ hsplit
  rw [alpha_sub, alpha_sub] at ha0
  rw [beta_sub, beta_sub] at hb0
  have ha : alpha s V K f = alpha s V K low + alpha s V K tail := by
    apply sub_eq_zero.mp
    calc
      _ = alpha s V K f - alpha s V K low - alpha s V K tail := by ring
      _ = 0 := ha0
  have hb : beta s V K f = beta s V K low + beta s V K tail := by
    apply sub_eq_zero.mp
    calc
      _ = beta s V K f - beta s V K low - beta s V K tail := by ring
      _ = 0 := hb0
  change alpha s V K f - beta s V K f = alpha s V K tail - beta s V K tail
  rw [ha, hb, hlow]
  ring


theorem mobius_subset_product (s t : Finset Nat)
    (hs : forall p, Membership.mem s p -> Nat.Prime p)
    (ht : Membership.mem s.powerset t) :
    (ArithmeticFunction.moebius (subsetProduct t) : Complex) =
      (-1 : Complex) ^ t.card := by
  have hprime (p : Nat) (hp : Membership.mem t p) : Nat.Prime p :=
    hs p ((Finset.mem_powerset.mp ht) hp)
  have hm : ArithmeticFunction.moebius (subsetProduct t) = (-1 : Int) ^ t.card := by
    change ArithmeticFunction.moebius (t.prod (fun p : Nat => p)) = (-1 : Int) ^ t.card
    rw [ArithmeticFunction.isMultiplicative_moebius.map_prod_of_prime t hprime]
    calc
      _ = t.prod (fun _ => (-1 : Int)) := by
        apply Finset.prod_congr rfl
        intro p hp
        exact ArithmeticFunction.moebius_apply_prime (hprime p hp)
      _ = _ := by simp
  exact_mod_cast hm

def arithmeticAlpha (s : Finset Nat) (V : Finset Nat) (K : Nat)
    (f : Nat -> Complex) : Complex :=
  V.sum (fun v => s.powerset.sum (fun e => s.powerset.sum (fun b =>
    if subsetProduct b * v <= K then
      (ArithmeticFunction.moebius (subsetProduct e) : Complex) *
        f (subsetProduct e * subsetProduct b * v)
    else 0)))

def arithmeticBeta (s : Finset Nat) (V : Finset Nat) (K : Nat)
    (f : Nat -> Complex) : Complex :=
  V.sum (fun v => s.powerset.sum (fun u =>
    if v <= K then
      (ArithmeticFunction.moebius (subsetProduct u) : Complex) *
        f ((subsetProduct u) ^ 2 * v)
    else 0))

theorem arithmeticAlpha_eq (s : Finset Nat) (V : Finset Nat) (K : Nat)
    (hs : forall p, Membership.mem s p -> Nat.Prime p) (f : Nat -> Complex) :
    arithmeticAlpha s V K f = alpha s V K f := by
  unfold arithmeticAlpha alpha
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro b hb
  rw [mobius_subset_product s e hs he]

theorem arithmeticBeta_eq (s : Finset Nat) (V : Finset Nat) (K : Nat)
    (hs : forall p, Membership.mem s p -> Nat.Prime p) (f : Nat -> Complex) :
    arithmeticBeta s V K f = beta s V K f := by
  unfold arithmeticBeta beta
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro u hu
  rw [mobius_subset_product s u hs hu]

theorem arithmetic_compensated_boundary_identity
    (s : Finset Nat) (V : Finset Nat) (K : Nat)
    (hs : forall p, Membership.mem s p -> Nat.Prime p) (f : Nat -> Complex) :
    arithmeticAlpha s V K f - arithmeticBeta s V K f =
      arithmeticAlpha s V K (boundaryWeight s K f) -
        arithmeticBeta s V K (boundaryWeight s K f) := by
  rw [arithmeticAlpha_eq s V K hs, arithmeticBeta_eq s V K hs,
    arithmeticAlpha_eq s V K hs, arithmeticBeta_eq s V K hs]
  exact compensated_boundary_identity s V K
    (fun p hp => Nat.le_of_lt (hs p hp).one_lt) f

end PrimeFactorOscillations.QuadraticMainTermCancellation
