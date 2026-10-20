/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# DilationFilterInversion

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
# Inversion estimates for logarithmic dilation filters

These estimates apply in a normed complex vector space, including the
finite row Hilbert space of a packet. Contracting forward inverses retain
a uniform geometric bound when the terminal term tends to zero.
Backward inverses, including unit-modulus factors, cost only the number
of logarithmic scale steps from the actual zero cutoff.
-/


noncomputable section
namespace PrimeFactorOscillations.DilationFilterInversion

variable {E : Type} [NormedAddCommGroup E] [NormedSpace Complex E]

def forwardDefect (c : Complex) (u : Nat -> E) (j : Nat) : E :=
  u j - HSMul.hSMul c (u (j+1))

theorem forward_telescope (c : Complex) (u : Nat -> E) (N : Nat) :
    (Finset.range N).sum (fun j => HSMul.hSMul (c^j) (forwardDefect c u j)) =
      u 0 - HSMul.hSMul (c^N) (u N) := by
  induction N with
  | zero => simp [forwardDefect]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [forwardDefect, smul_sub, smul_smul, pow_succ]
    abel

theorem forward_recover (c : Complex) (u : Nat -> E) (N : Nat) :
    u 0 = (Finset.range N).sum (fun j => HSMul.hSMul (c^j) (forwardDefect c u j)) +
      HSMul.hSMul (c^N) (u N) := by
  rw [forward_telescope]
  exact (sub_add_cancel _ _).symm

theorem geometric_partial_bound (r : Real) (hr0 : 0 <= r) (hr1 : r < 1)
    (N : Nat) :
    (Finset.range N).sum (fun j => r^j) <= 1/(1-r) := by
  have hden : 0 < 1-r := by linarith
  have hgeom := geom_sum_mul_neg r N
  have hpow := pow_nonneg hr0 N
  have hprod : (Finset.range N).sum (fun j => r^j)*(1-r) <= 1 := by linarith
  have hh := div_le_div_of_nonneg_right hprod hden.le
  simpa only [mul_div_assoc, div_self hden.ne', mul_one] using hh

theorem forward_partial_bound (c : Complex) (u : Nat -> E)
    (M q : Real) (hM : 0 <= M) (hq : 0 <= q) (hcq : norm c*q < 1)
    (hg : forall j : Nat, norm (forwardDefect c u j) <= M*q^j)
    (N : Nat) :
    norm ((Finset.range N).sum (fun j => HSMul.hSMul (c^j) (forwardDefect c u j))) <=
      M/(1-norm c*q) := by
  have hr0 : 0 <= norm c*q := mul_nonneg (norm_nonneg c) hq
  calc
    norm ((Finset.range N).sum (fun j => HSMul.hSMul (c^j) (forwardDefect c u j))) <=
        (Finset.range N).sum (fun j => norm (HSMul.hSMul (c^j) (forwardDefect c u j))) :=
      norm_sum_le _ _
    _ = (Finset.range N).sum (fun j => (norm c)^j * norm (forwardDefect c u j)) := by
      simp only [norm_smul, norm_pow]
    _ <= (Finset.range N).sum (fun j => (norm c)^j * (M*q^j)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hg j) (pow_nonneg (norm_nonneg c) j)
    _ = M * (Finset.range N).sum (fun j => (norm c*q)^j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [mul_pow]
      ring
    _ <= M * (1/(1-norm c*q)) :=
      mul_le_mul_of_nonneg_left (geometric_partial_bound _ hr0 hcq N) hM
    _ = M/(1-norm c*q) := by ring

theorem forward_bound (c : Complex) (u : Nat -> E) (M q : Real)
    (hM : 0 <= M) (hq : 0 <= q) (hcq : norm c*q < 1)
    (hg : forall j : Nat, norm (forwardDefect c u j) <= M*q^j)
    (hterminal : Filter.Tendsto (fun N : Nat => HSMul.hSMul (c^N) (u N))
      Filter.atTop (nhds 0)) :
    norm (u 0) <= M/(1-norm c*q) := by
  apply le_of_forall_pos_le_add
  intro epsilon hepsilon
  have hnorm : Filter.Tendsto (fun N : Nat => norm (HSMul.hSMul (c^N) (u N)))
      Filter.atTop (nhds (0 : Real)) := by
    simpa only [norm_zero] using hterminal.norm
  have hev : Filter.Eventually
      (fun N : Nat => norm (HSMul.hSMul (c^N) (u N)) < epsilon) Filter.atTop :=
    (tendsto_order.mp hnorm).2 epsilon hepsilon
  choose N hN using hev.exists
  calc
    norm (u 0) = norm ((Finset.range N).sum
        (fun j => HSMul.hSMul (c^j) (forwardDefect c u j)) + HSMul.hSMul (c^N) (u N)) :=
      congrArg norm (forward_recover c u N)
    _ <= norm ((Finset.range N).sum (fun j => HSMul.hSMul (c^j) (forwardDefect c u j))) +
        norm (HSMul.hSMul (c^N) (u N)) := norm_add_le _ _
    _ <= M/(1-norm c*q) + epsilon :=
      add_le_add (forward_partial_bound c u M q hM hq hcq hg N) hN.le

theorem backward_bound (c : Complex) (u : Nat -> E) (M : Real)
    (hM : 0 <= M) (hc : norm c <= 1) (hu : u 0 = 0) :
    forall N : Nat,
      (forall j : Nat, j < N -> norm (u (j+1) - HSMul.hSMul c (u j)) <= M) ->
      norm (u N) <= (N : Real)*M := by
  intro N
  induction N with
  | zero =>
    intro hg
    simp [hu]
  | succ N ih =>
    intro hg
    have hprev := ih (fun j hj => hg j (Nat.lt.step hj))
    have hlast := hg N (Nat.lt_succ_self N)
    have heq : u (N+1) = (u (N+1)-HSMul.hSMul c (u N)) + HSMul.hSMul c (u N) := by
      abel
    calc
      norm (u (N+1)) = norm ((u (N+1)-HSMul.hSMul c (u N))+HSMul.hSMul c (u N)) :=
        congrArg norm heq
      _ <= norm (u (N+1)-HSMul.hSMul c (u N)) + norm (HSMul.hSMul c (u N)) :=
        norm_add_le _ _
      _ = norm (u (N+1)-HSMul.hSMul c (u N)) + norm c * norm (u N) := by rw [norm_smul]
      _ <= M + 1*((N : Real)*M) :=
        add_le_add hlast (mul_le_mul hc hprev (norm_nonneg _) (by linarith))
      _ = ((N+1 : Nat) : Real)*M := by push_cast; ring

theorem terminal_of_growth (c : Complex) (u : Nat -> E) (C a : Real)
    (ha : 0 <= a) (hca : norm c*a < 1)
    (hu : forall N : Nat, norm (u N) <= C*a^N) :
    Filter.Tendsto (fun N : Nat => HSMul.hSMul (c^N) (u N))
      Filter.atTop (nhds 0) := by
  apply squeeze_zero_norm (a := fun N : Nat => C*(norm c*a)^N)
  . intro N
    rw [norm_smul, norm_pow]
    calc
      (norm c)^N * norm (u N) <= (norm c)^N * (C*a^N) :=
        mul_le_mul_of_nonneg_left (hu N) (pow_nonneg (norm_nonneg c) N)
      _ = C*(norm c*a)^N := by rw [mul_pow]; ring
  . have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one
        (mul_nonneg (norm_nonneg c) ha) hca).const_mul C
    simpa only [mul_zero] using hh

theorem forward_bound_of_growth (c : Complex) (u : Nat -> E)
    (M q C a : Real) (hM : 0 <= M) (hq : 0 <= q)
    (hcq : norm c*q < 1) (ha : 0 <= a) (hca : norm c*a < 1)
    (hg : forall j : Nat, norm (forwardDefect c u j) <= M*q^j)
    (hu : forall N : Nat, norm (u N) <= C*a^N) :
    norm (u 0) <= M/(1-norm c*q) := by
  exact forward_bound c u M q hM hq hcq hg
    (terminal_of_growth c u C a ha hca hu)

end PrimeFactorOscillations.DilationFilterInversion
