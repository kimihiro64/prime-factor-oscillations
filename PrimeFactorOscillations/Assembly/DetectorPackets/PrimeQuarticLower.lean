/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.PolarizedCoprimeProbe

/-!
# PrimeQuarticLower

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

namespace PrimeFactorOscillations.PrimeQuarticLower

def coeffSum (S : Finset Nat) (c : Nat -> Complex) : Complex :=
  S.sum c

def energy (S : Finset Nat) (c : Nat -> Complex) : Real :=
  S.sum (fun i => norm (c i) ^ 2)

def secondPower (S : Finset Nat) (c : Nat -> Complex) : Complex :=
  S.sum (fun i => c i ^ 2)

def thirdMixed (S : Finset Nat) (c : Nat -> Complex) : Complex :=
  S.sum (fun i => c i ^ 2 * star (c i))

def fourthEnergy (S : Finset Nat) (c : Nat -> Complex) : Real :=
  S.sum (fun i => norm (c i) ^ 4)

def fourthCarrier (S : Finset Nat) (c : Nat -> Complex) : Real :=
  norm (coeffSum S c) ^ 4 -
    2 * (secondPower S c * star (coeffSum S c) ^ 2).re -
    4 * energy S c * norm (coeffSum S c) ^ 2 +
    norm (secondPower S c) ^ 2 + 2 * energy S c ^ 2 +
    8 * (thirdMixed S c * star (coeffSum S c)).re -
    6 * fourthEnergy S c

def lowerEnvelope (x w : Real) : Real :=
  x ^ 4 - 6 * x ^ 2 * w ^ 2 - 8 * x * w ^ 3 - 4 * w ^ 4

theorem envelope_lower (x w : Real) (hx : 0 <= x) (hw : 0 <= w) :
    -(28 * w ^ 4) <= lowerEnvelope x w := by
  have hq : 0 <= x ^ 2 + 4 * x * w + 6 * w ^ 2 := by
    nlinarith only [sq_nonneg x, sq_nonneg w, mul_nonneg hx hw]
  have hs := mul_nonneg (sq_nonneg (x - 2 * w)) hq
  unfold lowerEnvelope
  nlinarith only [hs]

theorem envelope_coercive (x w : Real) (hx : 0 <= x) (hw : 0 <= w) :
    (1 / 2 : Real) * x ^ 4 - 52 * w ^ 4 <= lowerEnvelope x w := by
  have hq : 0 <= x ^ 2 / 4 + x * w + 3 * w ^ 2 := by
    nlinarith only [sq_nonneg x, sq_nonneg w, mul_nonneg hx hw]
  have hs := mul_nonneg (sq_nonneg (x - 2 * w)) hq
  have ht := sq_nonneg (x ^ 2 / 2 - 6 * w ^ 2)
  unfold lowerEnvelope
  nlinarith only [hs, ht]

theorem energy_nonneg (S : Finset Nat) (c : Nat -> Complex) :
    0 <= energy S c := by
  exact Finset.sum_nonneg (fun i hi => sq_nonneg (norm (c i)))

theorem term_energy_le (S : Finset Nat) (c : Nat -> Complex)
    (i : Nat) (hi : Membership.mem S i) :
    norm (c i) ^ 2 <= energy S c := by
  exact Finset.single_le_sum (fun j hj => sq_nonneg (norm (c j))) hi

theorem secondPower_norm_le (S : Finset Nat) (c : Nat -> Complex) :
    norm (secondPower S c) <= energy S c := by
  unfold secondPower energy
  apply (norm_sum_le S (fun i => c i ^ 2)).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_pow]

theorem thirdMixed_norm_le (S : Finset Nat) (c : Nat -> Complex) :
    norm (thirdMixed S c) <= Real.sqrt (energy S c) * energy S c := by
  have hV := energy_nonneg S c
  have hw := Real.sqrt_nonneg (energy S c)
  have hw2 := Real.sq_sqrt hV
  have hpoint : forall i, Membership.mem S i ->
      norm (c i) <= Real.sqrt (energy S c) := by
    intro i hi
    have ht := term_energy_le S c i hi
    nlinarith only [ht, hw, hw2, norm_nonneg (c i)]
  calc
    norm (thirdMixed S c) <=
        S.sum (fun i => norm (c i ^ 2 * star (c i))) :=
      norm_sum_le S (fun i => c i ^ 2 * star (c i))
    _ = S.sum (fun i => norm (c i) ^ 2 * norm (c i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_mul, norm_pow, norm_star]
    _ <= S.sum (fun i => norm (c i) ^ 2 * Real.sqrt (energy S c)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hpoint i hi) (sq_nonneg (norm (c i)))
    _ = Real.sqrt (energy S c) * energy S c := by
      rw [<- Finset.sum_mul]
      unfold energy
      ring

theorem fourthEnergy_le (S : Finset Nat) (c : Nat -> Complex) :
    fourthEnergy S c <= energy S c ^ 2 := by
  calc
    fourthEnergy S c <=
        S.sum (fun i => norm (c i) ^ 2 * energy S c) := by
      apply Finset.sum_le_sum
      intro i hi
      have h := mul_le_mul_of_nonneg_left (term_energy_le S c i hi)
        (sq_nonneg (norm (c i)))
      nlinarith only [h]
    _ = energy S c ^ 2 := by
      rw [<- Finset.sum_mul]
      unfold energy
      ring

theorem algebra_lower (x V A B C U w : Real)
    (hwV : w ^ 2 = V) (hA : 0 <= A ^ 2)
    (hB : B <= V * x ^ 2) (hC : -(w * V * x) <= C)
    (hU : U <= V ^ 2) :
    lowerEnvelope x w <=
      x ^ 4 - 2 * B - 4 * V * x ^ 2 + A ^ 2 + 2 * V ^ 2 + 8 * C - 6 * U := by
  subst V
  unfold lowerEnvelope
  nlinarith only [hA, hB, hC, hU]

theorem fourthCarrier_ge_envelope (S : Finset Nat) (c : Nat -> Complex) :
    lowerEnvelope (norm (coeffSum S c)) (Real.sqrt (energy S c)) <=
      fourthCarrier S c := by
  have hP := secondPower_norm_le S c
  have hT := thirdMixed_norm_le S c
  have hpair :
      (secondPower S c * star (coeffSum S c) ^ 2).re <=
        energy S c * norm (coeffSum S c) ^ 2 := by
    calc
      _ <= norm (secondPower S c * star (coeffSum S c) ^ 2) :=
        Complex.re_le_norm _
      _ = norm (secondPower S c) * norm (coeffSum S c) ^ 2 := by
        simp only [norm_mul, norm_pow, norm_star]
      _ <= energy S c * norm (coeffSum S c) ^ 2 :=
        mul_le_mul_of_nonneg_right hP (sq_nonneg _)
  have hthird :
      -(Real.sqrt (energy S c) * energy S c * norm (coeffSum S c)) <=
        (thirdMixed S c * star (coeffSum S c)).re := by
    have hn := Complex.re_le_norm (-(thirdMixed S c * star (coeffSum S c)))
    simp only [Complex.neg_re, norm_neg, norm_mul, norm_star] at hn
    have hm := mul_le_mul_of_nonneg_right hT (norm_nonneg (coeffSum S c))
    linarith only [hn, hm]
  exact algebra_lower _ _ _ _ _ _ _
    (Real.sq_sqrt (energy_nonneg S c)) (sq_nonneg _)
    hpair hthird (fourthEnergy_le S c)

theorem fourthCarrier_lower (S : Finset Nat) (c : Nat -> Complex) :
    -(28 * energy S c ^ 2) <= fourthCarrier S c := by
  have h := envelope_lower (norm (coeffSum S c)) (Real.sqrt (energy S c))
    (norm_nonneg _) (Real.sqrt_nonneg _)
  have h4 : Real.sqrt (energy S c) ^ 4 = energy S c ^ 2 := by
    calc
      _ = (Real.sqrt (energy S c) ^ 2) ^ 2 := by ring
      _ = energy S c ^ 2 := by rw [Real.sq_sqrt (energy_nonneg S c)]
  rw [h4] at h
  exact h.trans (fourthCarrier_ge_envelope S c)

theorem fourthCarrier_coercive (S : Finset Nat) (c : Nat -> Complex) :
    (1 / 2 : Real) * norm (coeffSum S c) ^ 4 - 52 * energy S c ^ 2 <=
      fourthCarrier S c := by
  have h := envelope_coercive (norm (coeffSum S c)) (Real.sqrt (energy S c))
    (norm_nonneg _) (Real.sqrt_nonneg _)
  have h4 : Real.sqrt (energy S c) ^ 4 = energy S c ^ 2 := by
    calc
      _ = (Real.sqrt (energy S c) ^ 2) ^ 2 := by ring
      _ = energy S c ^ 2 := by rw [Real.sq_sqrt (energy_nonneg S c)]
  rw [h4] at h
  exact h.trans (fourthCarrier_ge_envelope S c)

theorem energy_mul_le (S : Finset Nat) (c z : Nat -> Complex)
    (hz : forall i, Membership.mem S i -> norm (z i) <= 1) :
    energy S (fun i => z i * c i) <= energy S c := by
  apply Finset.sum_le_sum
  intro i hi
  have h := mul_le_mul_of_nonneg_right (hz i hi) (norm_nonneg (c i))
  simp only [one_mul] at h
  have hsq := mul_le_mul h h
    (mul_nonneg (norm_nonneg (z i)) (norm_nonneg (c i))) (norm_nonneg (c i))
  simpa only [norm_mul, pow_two] using hsq

theorem weighted_carrier_upper (R S : Finset Nat)
    (c : Nat -> Complex) (z : Nat -> Nat -> Complex) (w : Nat -> Real)
    (hz : forall v, Membership.mem R v ->
      forall i, Membership.mem S i -> norm (z v i) <= 1)
    (hw : forall v, Membership.mem R v -> w v <= 0) :
    R.sum (fun v => w v * fourthCarrier S (fun i => z v i * c i)) <=
      28 * energy S c ^ 2 * R.sum (fun v => -w v) := by
  calc
    _ <= R.sum (fun v => 28 * energy S c ^ 2 * (-w v)) := by
      apply Finset.sum_le_sum
      intro v hv
      have he := energy_mul_le S c (z v) (hz v hv)
      have hs := mul_le_mul he he
        (energy_nonneg S (fun i => z v i * c i)) (energy_nonneg S c)
      have hl := fourthCarrier_lower S (fun i => z v i * c i)
      have hlow : -(28 * energy S c ^ 2) <=
          fourthCarrier S (fun i => z v i * c i) := by
        nlinarith only [hs, hl]
      calc
        _ <= w v * (-(28 * energy S c ^ 2)) :=
          mul_le_mul_of_nonpos_left hlow (hw v hv)
        _ = 28 * energy S c ^ 2 * (-w v) := by ring
    _ = _ := by rw [Finset.mul_sum]

end PrimeFactorOscillations.PrimeQuarticLower
