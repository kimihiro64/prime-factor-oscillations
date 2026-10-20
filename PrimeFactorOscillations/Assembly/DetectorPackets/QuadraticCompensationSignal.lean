/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticMainTermCancellation

/-!
# QuadraticCompensationSignal

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

namespace PrimeFactorOscillations.QuadraticCompensationSignal

open QuadraticMainTermCancellation

/- The v = 1 component is an exact finite test of the shared square channel.
It is not an estimate for the remaining nonsquare rows of a physical probe. -/

theorem singleton_one_alpha_eq_beta
    (G : Finset Nat) (K : Nat)
    (hG : forall p, Membership.mem G p -> 1 <= p)
    (hK : subsetProduct G <= K) (f : Nat -> Complex) :
    alpha G {1} K f = beta G {1} K f := by
  have hOne : 1 <= K :=
    (subsetProduct_one_le G G hG (Finset.mem_powerset.mpr (fun _ h => h))).trans hK
  have ha : alpha G {1} K f = paired G f := by
    unfold alpha paired signedSum plainSum
    simp only [Finset.sum_singleton, mul_one]
    apply Finset.sum_congr rfl
    intro E hE
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro B hB
    rw [if_pos ((subsetProduct_le G B hG hB).trans hK)]
  have hb : beta G {1} K f = signedSum G (fun u => f (u ^ 2)) := by
    unfold beta signedSum
    simp only [Finset.sum_singleton, mul_one, if_pos hOne]
  rw [ha, hb, paired_eq_square]

theorem singleton_one_compensation_zero
    (G : Finset Nat) (K : Nat)
    (hG : forall p, Membership.mem G p -> 1 <= p)
    (hK : subsetProduct G <= K) (f : Nat -> Complex) :
    alpha G {1} K f - beta G {1} K f = 0 := by
  rw [singleton_one_alpha_eq_beta G K hG hK f, sub_self]

theorem singleton_one_weighted_signal
    (G : Finset Nat) (K : Nat)
    (hG : forall p, Membership.mem G p -> 1 <= p)
    (hK : subsetProduct G <= K) (f : Nat -> Complex) (c : Complex) :
    alpha G {1} K f - c * beta G {1} K f =
      (1 - c) * beta G {1} K f := by
  rw [singleton_one_alpha_eq_beta G K hG hK f]
  ring

theorem singleton_one_observation_compensation_zero
    (G : Finset Nat) (K : Nat)
    (hG : forall p, Membership.mem G p -> 1 <= p)
    (hK : subsetProduct G <= K) (f error : Nat -> Complex) :
    alpha G {1} K (fun n => f n + error n) -
      beta G {1} K (fun n => f n + error n) = 0 := by
  exact singleton_one_compensation_zero G K hG hK _

end PrimeFactorOscillations.QuadraticCompensationSignal

