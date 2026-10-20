/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.EvenPacketExchange

/-!
# EvenPacketRowBound

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

namespace PrimeFactorOscillations.EvenPacketRowBound

open CoprimeSchwartzSplit EvenPacketExchange

theorem weighted_even_packet_rows {I J : Type} (E : Finset I) (S : Finset J)
    (w : I -> Real) (hw : forall i, Membership.mem E i -> 0 <= w i)
    (z : I -> J -> Complex) (scale : I -> J -> Real) (F : SchwartzMap Real Complex)
    (hF : forall x : Real, F (-x) = F x) (L : Nat) :
    E.sum (fun i => w i * norm (S.sum (fun j => z i j * frequencyPacket L F (scale i j)))) <=
      2 * (Finset.Ioc 0 L).sum (fun ell => E.sum (fun i =>
        w i * norm (S.sum (fun j => z i j * F ((ell : Real) * scale i j))))) := by
  let V : I -> Nat -> Real := fun i ell =>
    norm (S.sum (fun j => z i j * F ((ell : Real) * scale i j)))
  calc
    _ <= E.sum (fun i => w i * (2 * (Finset.Ioc 0 L).sum (V i))) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (finite_even_packet_norm S (z i) (scale i) F hF L) (hw i hi)
    _ = E.sum (fun i => (Finset.Ioc 0 L).sum (fun ell => 2 * (w i * V i ell))) := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        _ = (w i * 2) * (Finset.Ioc 0 L).sum (V i) := by ring
        _ = (Finset.Ioc 0 L).sum (fun ell => (w i * 2) * V i ell) :=
          Finset.mul_sum _ _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro ell hell
          ring
    _ = (Finset.Ioc 0 L).sum (fun ell => E.sum (fun i => 2 * (w i * V i ell))) :=
      Finset.sum_comm
    _ = (Finset.Ioc 0 L).sum (fun ell => 2 * E.sum (fun i => w i * V i ell)) := by
      apply Finset.sum_congr rfl
      intro ell hell
      exact (Finset.mul_sum _ _ _).symm
    _ = _ := (Finset.mul_sum _ _ _).symm

end PrimeFactorOscillations.EvenPacketRowBound

