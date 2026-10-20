/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Helpers.DirichletPacketMellin
import PrimeFactorOscillations.Helpers.PowerPolynomialLaw

/-!
# PositiveCharacterEnvelope

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

/-!
Positive character envelopes with a canonical logarithmic compensator.
The comparison is for each fixed law. No one-sided arithmetic estimate or
improved zero-free strip is asserted.
-/


noncomputable section
namespace PrimeFactorOscillations.PositiveCharacterEnvelope

def amplitude (z t : Complex) : Real :=
  (2 + 2 * z.re) * (1 + t.re)

theorem amplitude_bounds (z t : Complex)
    (hz : norm z <= 1) (ht : norm t <= 1) :
    0 <= amplitude z t /\ amplitude z t <= 8 := by
  have hzr := abs_le.mp ((Complex.abs_re_le_norm z).trans hz)
  have htr := abs_le.mp ((Complex.abs_re_le_norm t).trans ht)
  have hb0 : 0 <= 2 + 2 * z.re := by linarith
  have hb4 : 2 + 2 * z.re <= 4 := by linarith
  have hc0 : 0 <= 1 + t.re := by linarith
  have hc2 : 1 + t.re <= 2 := by linarith
  exact And.intro (mul_nonneg hb0 hc0)
    (by
      dsimp only [amplitude]
      calc
        _ <= 4 * 2 := mul_le_mul hb4 hc2 hc0 (by norm_num : (0 : Real) <= 4)
        _ = 8 := by norm_num)

theorem local_bounds (r v : Real)
    (hr0 : 0 <= r) (hr8 : r <= 8)
    (hv0 : 0 <= v) (hv1 : v <= 1 / 10) :
    0 <= r * v /\ r * v < 1 /\
    0 <= r * Real.log (1 + v) /\
    r * Real.log (1 + v) <= 8 * v /\
    abs (r * v / (1 - r * v) - r * Real.log (1 + v)) <=
      324 * v ^ 2 := by
  have hrv0 : 0 <= r * v := mul_nonneg hr0 hv0
  have hrv8 : r * v <= 8 * v := mul_le_mul_of_nonneg_right hr8 hv0
  have hrv : r * v <= 4 / 5 := by nlinarith
  have hden : 0 < 1 - r * v := by linarith
  have hden5 : (1 / 5 : Real) <= 1 - r * v := by linarith
  have hlog := Real.sub_log_one_add_bounds v hv0
  have hlog0 : 0 <= Real.log (1 + v) := Real.log_nonneg (by linarith)
  have hc0 : 0 <= r * Real.log (1 + v) := mul_nonneg hr0 hlog0
  have hc8 : r * Real.log (1 + v) <= 8 * v := by
    have h1 : r * Real.log (1 + v) <= r * v :=
      mul_le_mul_of_nonneg_left (by linarith [hlog.1]) hr0
    exact h1.trans hrv8
  have hsq : (r * v) ^ 2 <= 64 * v ^ 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hrv8) (add_nonneg (by positivity : 0 <= 8 * v) hrv0)
    nlinarith
  have hquot0 : 0 <= (r * v) ^ 2 / (1 - r * v) := div_nonneg (sq_nonneg _) hden.le
  have hquot : (r * v) ^ 2 / (1 - r * v) <= 320 * v ^ 2 := by
    calc
      _ <= (r * v) ^ 2 / (1 / 5 : Real) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) hden5
      _ <= 320 * v ^ 2 := by nlinarith only [hsq]
  have htail0 : 0 <= r * (v - Real.log (1 + v)) := mul_nonneg hr0 hlog.1
  have htail : r * (v - Real.log (1 + v)) <= 4 * v ^ 2 := by
    have hp := mul_le_mul hr8 hlog.2 hlog.1 (by norm_num : (0 : Real) <= 8)
    nlinarith
  have hid : r * v / (1 - r * v) - r * Real.log (1 + v) =
      (r * v) ^ 2 / (1 - r * v) + r * (v - Real.log (1 + v)) := by
    field_simp [hden.ne']
    ring
  refine And.intro hrv0 (And.intro (by linarith) (And.intro hc0 (And.intro hc8 ?_)))
  rw [hid, abs_of_nonneg (add_nonneg hquot0 htail0)]
  linarith

theorem prime_weight_small (p : Nat.Primes) (hp : 11 <= (p : Nat)) :
    primeProfileWeight (p : Nat) <= (1 / 10 : Real) := by
  have hn : 10 <= (p : Nat) - 1 := by omega
  have hnr : (10 : Real) <= (((p : Nat) - 1 : Nat) : Real) := by exact_mod_cast hn
  unfold primeProfileWeight
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnr

def eta (z t : Nat.Primes -> Complex) (p : Nat.Primes) : Real :=
  if 11 <= (p : Nat) then
    amplitude (z p) (t p) * primeProfileWeight (p : Nat) else 0

def odds (z t : Nat.Primes -> Complex) (p : Nat.Primes) : Real :=
  eta z t p / (1 - eta z t p)

def clock (z t : Nat.Primes -> Complex) (p : Nat.Primes) : Real :=
  if 11 <= (p : Nat) then
    amplitude (z p) (t p) * Real.log (1 + primeProfileWeight (p : Nat)) else 0

theorem eta_bounds (z t : Nat.Primes -> Complex)
    (hz : forall p, norm (z p) <= 1) (ht : forall p, norm (t p) <= 1)
    (p : Nat.Primes) : 0 <= eta z t p /\ eta z t p < 1 := by
  unfold eta
  split_ifs with hp
  . have hb := amplitude_bounds (z p) (t p) (hz p) (ht p)
    have h := local_bounds _ _ hb.1 hb.2 (primeProfileWeight_nonneg _)
      (prime_weight_small p hp)
    exact And.intro h.1 h.2.1
  . norm_num

def law (z t : Nat.Primes -> Complex)
    (hz : forall p, norm (z p) <= 1) (ht : forall p, norm (t p) <= 1) :
    PrimeClockLaw where
  weight := odds z t
  compensator := clock z t
  scale := 8
  error := 324
  scale_pos := by norm_num
  error_nonneg := by norm_num
  weight_nonneg := by
    intro p
    have h := eta_bounds z t hz ht p
    exact div_nonneg h.1 (sub_pos.mpr h.2).le
  compensator_nonneg := by
    intro p
    unfold clock
    split_ifs with hp
    . have hb := amplitude_bounds (z p) (t p) (hz p) (ht p)
      exact (local_bounds _ _ hb.1 hb.2 (primeProfileWeight_nonneg _)
        (prime_weight_small p hp)).2.2.1
    . exact le_rfl
  compensator_le := by
    intro p
    unfold clock
    split_ifs with hp
    . have hb := amplitude_bounds (z p) (t p) (hz p) (ht p)
      exact (local_bounds _ _ hb.1 hb.2 (primeProfileWeight_nonneg _)
        (prime_weight_small p hp)).2.2.2.1
    . exact mul_nonneg (by norm_num) (primeProfileWeight_nonneg _)
  quadratic_error := by
    intro p
    unfold odds eta clock
    split_ifs with hp
    . have hb := amplitude_bounds (z p) (t p) (hz p) (ht p)
      exact (local_bounds _ _ hb.1 hb.2 (primeProfileWeight_nonneg _)
        (prime_weight_small p hp)).2.2.2.2
    . simp only [zero_div, sub_zero, abs_zero]
      positivity

def dirichletLaw {q r : Nat} [NeZero q] [NeZero r]
    (chi : DirichletCharacter Complex q) (xi : DirichletCharacter Complex r) :
    PrimeClockLaw :=
  law (fun p => chi ((p : Nat) : ZMod q)) (fun p => xi ((p : Nat) : ZMod r))
    (fun p => chi.norm_le_one (((p : Nat) : ZMod q)))
    (fun p => xi.norm_le_one (((p : Nat) : ZMod r)))

theorem dirichletLaw_parameters {q r : Nat} [NeZero q] [NeZero r]
    (chi : DirichletCharacter Complex q) (xi : DirichletCharacter Complex r) :
    (dirichletLaw chi xi).scale = 8 /\ (dirichletLaw chi xi).error = 324 := by
  exact And.intro rfl rfl

theorem dirichletLaw_comparison {q r : Nat} [NeZero q] [NeZero r]
    (chi : DirichletCharacter Complex q) (xi : DirichletCharacter Complex r)
    (b : Real) (hb : 0 < b) :
    PowerPolynomialLaw.ComparisonClaim (dirichletLaw chi xi) b :=
  (dirichletLaw chi xi).exists_densityRatio_linearization b hb

end PrimeFactorOscillations.PositiveCharacterEnvelope
