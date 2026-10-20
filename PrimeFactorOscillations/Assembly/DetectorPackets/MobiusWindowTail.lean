/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.MobiusWindowBound

/-!
# MobiusWindowTail

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
open PrimeFactorOscillations.DepletedMobius

namespace PrimeFactorOscillations.MobiusWindow

theorem character_normalized_smooth_size_bound {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : 0 < q)
    (r : Nat) (hr : Not (r = 0))
    (W : Real -> Complex) (lo hi : Real) (hlo : 0 < lo) (hhi : 0 <= hi)
    (hsupp : Function.support W <= Set.Icc lo hi)
    (hW : ContDiff Real ((Top.top : ENat) : WithTop ENat) W)
    (u : Real) (hu : 0 < u) (hfit : (7 / 8 : Real) + u <= 2) :
    Exists (fun K : Real => 0 <= K /\
      forall (h : Nat) (D : Real), Not (h = 0) -> 0 < D ->
        normalizedSmoothSize h r (fun n : Nat => chi (n : ZMod q)) W hi D <=
          K * D ^ (3 / 8 + u) * (h : Real) ^ (-(7 / 8 : Real))) := by
  choose C hC using smoothBase_character_norm_bound
    chi hq W lo hi hlo hsupp hW (7 / 8 + u) (by linarith) hfit
  have hsup : forall t : Real, hi < t -> W t = 0 := by
    intro t ht
    by_contra hn
    have hmem : Membership.mem (Function.support W) t := hn
    exact (not_le_of_gt ht) (hsupp hmem).2
  choose K hK using normalized_smooth_size_uniform r hr
    (fun n : Nat => chi (n : ZMod q)) W
    (fun m n => by simp only [Nat.cast_mul, map_mul])
    (fun n => chi.norm_le_one _) hi (7 / 8 + u) u C hhi (by linarith)
    hu hC.1 hsup hC.2
  refine Exists.intro K (And.intro hK.1 ?_)
  intro h D hh hD
  have hrow := hK.2 h D hh hD
  rwa [show (7 / 8 : Real) + u - 1 / 2 = 3 / 8 + u by ring,
    show u - ((7 / 8 : Real) + u) = -(7 / 8 : Real) by ring] at hrow

theorem character_packet_energy_tail {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : 0 < q)
    (r : Nat) (hr : Not (r = 0))
    (W : Real -> Complex) (lo hi : Real) (hlo : 0 < lo) (hhi : 0 <= hi)
    (hsupp : Function.support W <= Set.Icc lo hi)
    (hW : ContDiff Real ((Top.top : ENat) : WithTop ENat) W)
    (u : Real) (hu : 0 < u) (hfit : (7 / 8 : Real) + u <= 2) :
    Exists (fun K : Real => 0 <= K /\
      forall (D : Real) (H N : Nat), 0 < D -> 0 < H ->
        (Finset.Ioc H N).sum (fun h =>
          (normalizedSmoothSize h r (fun n : Nat => chi (n : ZMod q)) W hi D) ^ 2) <=
          (4 / 3 : Real) * K ^ 2 * D ^ (3 / 4 + 2 * u) *
            (H : Real) ^ (-(3 / 4 : Real))) := by
  choose K hK using character_normalized_smooth_size_bound
    chi hq r hr W lo hi hlo hhi hsupp hW u hu hfit
  refine Exists.intro K (And.intro hK.1 ?_)
  intro D H N hD hH
  apply finite_energy_tail_le
    (fun h => normalizedSmoothSize h r (fun n : Nat => chi (n : ZMod q)) W hi D)
    K D u hK.1 hD H N hH
  intro h hh
  have hhpos : 0 < h :=
    Nat.lt_of_le_of_lt (Nat.zero_le H) (Finset.mem_Ioc.mp hh).1
  exact And.intro
    (normalized_smooth_size_nonneg h r (fun n : Nat => chi (n : ZMod q)) W hi D hD.le)
    (hK.2 h D (Nat.ne_of_gt hhpos) hD)

theorem character_signed_packet_tail {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : 0 < q)
    (r : Nat) (hr : Not (r = 0))
    (W : Real -> Complex) (lo hi : Real) (hlo : 0 < lo) (hhi : 0 <= hi)
    (hsupp : Function.support W <= Set.Icc lo hi)
    (hW : ContDiff Real ((Top.top : ENat) : WithTop ENat) W)
    (u : Real) (hu : 0 < u) (hfit : (7 / 8 : Real) + u <= 2) :
    Exists (fun K : Real => 0 <= K /\
      forall (D : Real) (H N : Nat), 0 < D -> 0 < H ->
        norm ((Finset.Ioc H N).sum (fun h => (ArithmeticFunction.moebius h : Real) *
          (normalizedSmoothSize h r (fun n : Nat => chi (n : ZMod q)) W hi D) ^ 2)) <=
          (4 / 3 : Real) * K ^ 2 * D ^ (3 / 4 + 2 * u) *
            (H : Real) ^ (-(3 / 4 : Real))) := by
  choose K hK using character_packet_energy_tail
    chi hq r hr W lo hi hlo hhi hsupp hW u hu hfit
  refine Exists.intro K (And.intro hK.1 ?_)
  intro D H N hD hH
  exact (signed_energy_tail_abs_le
    (fun h => normalizedSmoothSize h r (fun n : Nat => chi (n : ZMod q)) W hi D) H N).trans
      (hK.2 D H N hD hH)

theorem character_signed_packet_endpoint {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : 0 < q)
    (r : Nat) (hr : Not (r = 0))
    (W : Real -> Complex) (lo hi : Real) (hlo : 0 < lo) (hhi : 0 <= hi)
    (hsupp : Function.support W <= Set.Icc lo hi)
    (hW : ContDiff Real ((Top.top : ENat) : WithTop ENat) W)
    (u tau : Real) (hu : 0 < u) (htau : 0 < tau) (htau2 : tau < 2 / 3)
    (hsmall : u < 3 * tau / 8) :
    Exists (fun K : Real => 0 <= K /\
      forall (D : Real) (H N : Nat), 0 < D -> 0 < H ->
        D ^ (1 / 3 + tau) <= (H : Real) ->
        norm ((Finset.Ioc H N).sum (fun h => (ArithmeticFunction.moebius h : Real) *
          (normalizedSmoothSize h r (fun n : Nat => chi (n : ZMod q)) W hi D) ^ 2)) <=
          (4 / 3 : Real) * K ^ 2 * D ^ (1 / 2 - (3 * tau / 4 - 2 * u))) := by
  have hfit : (7 / 8 : Real) + u <= 2 := by linarith
  choose K hK using character_signed_packet_tail
    chi hq r hr W lo hi hlo hhi hsupp hW u hu hfit
  refine Exists.intro K (And.intro hK.1 ?_)
  intro D H N hD hH hscale
  exact energy_tail_endpoint_scale _ K D u tau H hK.1 hD hscale
    (hK.2 D H N hD hH)

end PrimeFactorOscillations.MobiusWindow
