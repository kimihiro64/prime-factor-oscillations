/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Sequences
import PrimeFactorOscillations.Proof.DetectorPackets.RHFourierMean

/-!
# RHWaveRecurrence

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter
open scoped Topology

noncomputable section

namespace PrimeFactorOscillations

/-- Countably many phases have simultaneous arbitrarily late return times.
No arithmetic independence of the frequencies is required. -/
theorem exists_simultaneous_phase_returns {J : Type*} [Countable J] (f : J -> Real) :
    Exists (fun d : Nat -> Nat => Tendsto d atTop atTop /\
      forall j : J, Tendsto (fun n : Nat => Circle.exp (f j * (d n : Real)))
        atTop (nhds 1)) := by
  let v : Nat -> (J -> Circle) := fun n j => Circle.exp (f j * (n : Real))
  let a := Classical.choose (CompactSpace.tendsto_subseq v)
  have hA := Classical.choose_spec (CompactSpace.tendsto_subseq v)
  let phi := Classical.choose hA
  have h := Classical.choose_spec hA
  have hphi : StrictMono phi := h.1
  have ht := h.2
  let d : Nat -> Nat := fun n => phi (n + n) - phi n
  have hGrow (m k : Nat) : phi m + k <= phi (m + k) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hs := hphi (Nat.lt_succ_self (m + k))
      simp only [Nat.succ_eq_add_one] at hs
      have hNext : phi m + (k + 1) <= phi ((m + k) + 1) := by omega
      simpa only [Nat.add_assoc] using hNext
  have hd (n : Nat) : n <= d n := by
    have h := hGrow n n
    dsimp only [d]
    omega
  have hdTop : Tendsto d atTop atTop := tendsto_atTop_mono hd tendsto_id
  have hDouble : Tendsto (fun n : Nat => n + n) atTop atTop :=
    tendsto_atTop_mono (fun n : Nat => Nat.le_add_right n n) tendsto_id
  have hDiv : Tendsto (fun n : Nat => v (phi (n + n)) / v (phi n))
      atTop (nhds (1 : J -> Circle)) := by
    simpa only [Function.comp_def, div_self'] using (ht.comp hDouble).div' ht
  refine Exists.intro d (And.intro hdTop ?_)
  intro j
  have hEval := (continuous_apply j).tendsto (1 : J -> Circle) |>.comp hDiv
  have hId : (fun n : Nat => (v (phi (n + n)) / v (phi n)) j) =
      (fun n : Nat => Circle.exp (f j * (d n : Real))) := by
    funext n
    dsimp only [v, Pi.div_apply]
    rw [<- Circle.exp_sub]
    have hLe : phi n <= phi (n + n) := hphi.monotone (Nat.le_add_right n n)
    dsimp only [d]
    rw [Nat.cast_sub hLe]
    congr 1
    ring
  simpa only [Function.comp_def, hId, Pi.one_apply] using hEval

/-- Pointwise phase convergence passes through every absolutely summable spectrum. -/
theorem tendsto_logSpectrum_of_phase_tendsto_one {J : Type*}
    (a : J -> Real) (f : J -> Real) (ha : Summable a) (x : Nat -> Real)
    (hPhase : forall j : J,
      Tendsto (fun n : Nat => logCharacter (f j) (x n)) atTop (nhds 1)) :
    Tendsto (fun n : Nat => (logSpectrum (fun j => (a j : Complex)) f (x n)).re)
      atTop (nhds (tsum a)) := by
  have hNorm : Summable (fun j : J => norm ((a j : Real) : Complex)) := by
    simpa only [Complex.norm_real] using ha.norm
  have hT : Tendsto (fun n : Nat =>
      tsum (fun j : J => (a j : Complex) * logCharacter (f j) (x n)))
      atTop (nhds (tsum (fun j : J => (a j : Complex)))) := by
    apply tendsto_tsum_of_dominated_convergence hNorm
    . intro j
      simpa only [mul_one] using (tendsto_const_nhds.mul (hPhase j))
    . apply Filter.Eventually.of_forall
      intro n j
      rw [norm_mul, norm_logCharacter, mul_one]
  have hLimit : tsum (fun j : J => (a j : Complex)) = Complex.ofReal (tsum a) :=
    (Complex.ofRealCLM.map_tsum ha).symm
  rw [hLimit] at hT
  simpa only [Function.comp_def, logSpectrum, Complex.ofReal_re] using
    (Complex.continuous_re.tendsto (Complex.ofReal (tsum a))).comp hT

/-- Every absolutely summable real spectrum returns to its value at phase zero. -/
theorem exists_logSpectrum_return_sequence {J : Type*} [Countable J]
    (a : J -> Real) (f : J -> Real) (ha : Summable a) :
    Exists (fun d : Nat -> Nat => Tendsto d atTop atTop /\
      Tendsto (fun n : Nat =>
        (logSpectrum (fun j => (a j : Complex)) f (Real.exp (d n : Real))).re)
        atTop (nhds (tsum a))) := by
  have hExists := exists_simultaneous_phase_returns f
  let d := Classical.choose hExists
  have hd := Classical.choose_spec hExists
  have hChar (j : J) : Tendsto
      (fun n : Nat => logCharacter (f j) (Real.exp (d n : Real))) atTop (nhds 1) := by
    have h := (continuous_subtype_val.tendsto (1 : Circle)).comp (hd.2 j)
    have hId : (fun n : Nat => (Circle.exp (f j * (d n : Real)) : Complex)) =
        (fun n : Nat => logCharacter (f j) (Real.exp (d n : Real))) := by
      funext n
      rw [Circle.coe_exp]
      unfold logCharacter
      rw [Real.log_exp]
      congr 1 <;> push_cast <;> ring
    change Tendsto (fun n : Nat => (Circle.exp (f j * (d n : Real)) : Complex))
      atTop (nhds 1) at h
    rwa [hId] at h
  refine Exists.intro d (And.intro hd.1 ?_)
  exact tendsto_logSpectrum_of_phase_tendsto_one a f ha _ hChar

end PrimeFactorOscillations
