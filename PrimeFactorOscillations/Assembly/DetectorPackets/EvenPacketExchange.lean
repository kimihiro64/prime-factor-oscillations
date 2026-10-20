/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.EvenFrequencyPacket

/-!
# EvenPacketExchange

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

namespace PrimeFactorOscillations.EvenPacketExchange

open CoprimeSchwartzSplit EvenFrequencyPacket

theorem finite_even_packet_exchange {I : Type} (S : Finset I)
    (z : I -> Complex) (scale : I -> Real) (F : SchwartzMap Real Complex)
    (hF : forall x : Real, F (-x) = F x) (L : Nat) :
    S.sum (fun i => z i * frequencyPacket L F (scale i)) =
      2 * (Finset.Ioc 0 L).sum (fun ell =>
        S.sum (fun i => z i * F ((ell : Real) * scale i))) := by
  calc
    _ = S.sum (fun i => z i *
        (2 * (Finset.Ioc 0 L).sum (fun ell => F ((ell : Real) * scale i)))) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [even_frequencyPacket F hF (scale i) L]
    _ = S.sum (fun i => (Finset.Ioc 0 L).sum (fun ell =>
        2 * (z i * F ((ell : Real) * scale i)))) := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        _ = (z i * 2) * (Finset.Ioc 0 L).sum (fun ell =>
            F ((ell : Real) * scale i)) := by ring
        _ = (Finset.Ioc 0 L).sum (fun ell =>
            (z i * 2) * F ((ell : Real) * scale i)) := Finset.mul_sum _ _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro ell hell
          ring
    _ = (Finset.Ioc 0 L).sum (fun ell => S.sum (fun i =>
        2 * (z i * F ((ell : Real) * scale i)))) := Finset.sum_comm
    _ = (Finset.Ioc 0 L).sum (fun ell => 2 * S.sum (fun i =>
        z i * F ((ell : Real) * scale i))) := by
      apply Finset.sum_congr rfl
      intro ell hell
      exact (Finset.mul_sum _ _ _).symm
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem finite_even_packet_norm {I : Type} (S : Finset I)
    (z : I -> Complex) (scale : I -> Real) (F : SchwartzMap Real Complex)
    (hF : forall x : Real, F (-x) = F x) (L : Nat) :
    norm (S.sum (fun i => z i * frequencyPacket L F (scale i))) <=
      2 * (Finset.Ioc 0 L).sum (fun ell =>
        norm (S.sum (fun i => z i * F ((ell : Real) * scale i)))) := by
  rw [finite_even_packet_exchange S z scale F hF L]
  calc
    _ = 2 * norm ((Finset.Ioc 0 L).sum (fun ell =>
        S.sum (fun i => z i * F ((ell : Real) * scale i)))) := by
      rw [norm_mul]
      norm_num
    _ <= _ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by norm_num)

end PrimeFactorOscillations.EvenPacketExchange

