/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.SchwartzIntegerPowerTail

/-!
# CoprimeSchwartzHigh

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

namespace PrimeFactorOscillations.CoprimeSchwartzHigh

open CoprimeSchwartzCenter CoprimeSchwartzMixed CoprimeSchwartzDecay
open SchwartzIntegerPowerTail

theorem highPrimal_norm_bound (f : SchwartzMap Real Complex) (k : Nat) (hk : 2 <= k) :
    exists C : Real, 0 < C /\
      forall (q : Nat) (X Z : Real), 0 < X -> 0 < Z ->
      norm (highPrimal q X Z f) <= C * X * (X / Z) ^ (k - 1) := by
  choose A hA ha using finite_power_tail k hk
  choose C hC hc using offZero_norm_bound f k hk
  refine Exists.intro (C * A) (And.intro (mul_pos hC hA) ?_)
  intro q X Z hX hZ
  have hrow (d : Nat) (hd : Membership.mem (largeDivisors q Z) d) :
      norm ((ArithmeticFunction.moebius d : Complex) *
        offZeroSum f ((d : Real) / X)) <=
      (C * X ^ k) * (1 / (d : Real) ^ k) := by
    have hZd := (Finset.mem_filter.mp hd).2
    have hdR : (0 : Real) < (d : Real) := lt_trans hZ hZd
    have hmu : norm (ArithmeticFunction.moebius d : Complex) <= 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
    calc
      _ = norm (ArithmeticFunction.moebius d : Complex) *
          norm (offZeroSum f ((d : Real) / X)) := norm_mul _ _
      _ <= 1 * (C / ((d : Real) / X) ^ k) :=
        mul_le_mul hmu (hc _ (div_pos hdR hX)) (norm_nonneg _) (by norm_num)
      _ = _ := by
        rw [one_mul, div_pow]
        field_simp
  have htail := ha Z (largeDivisors q Z) hZ
    (fun d hd => (Finset.mem_filter.mp hd).2)
  have hkEq : k = (k - 1) + 1 := by omega
  have hpow : X ^ k = X ^ (k - 1) * X := by
    calc
      _ = X ^ ((k - 1) + 1) := congrArg (fun j : Nat => X ^ j) hkEq
      _ = _ := pow_succ _ _
  calc
    _ <= (largeDivisors q Z).sum (fun d =>
        norm ((ArithmeticFunction.moebius d : Complex) *
          offZeroSum f ((d : Real) / X))) := norm_sum_le _ _
    _ <= (largeDivisors q Z).sum (fun d =>
        (C * X ^ k) * (1 / (d : Real) ^ k)) := by
      apply Finset.sum_le_sum
      exact hrow
    _ = (C * X ^ k) * (largeDivisors q Z).sum (fun d =>
        1 / (d : Real) ^ k) := (Finset.mul_sum _ _ _).symm
    _ <= (C * X ^ k) * (A / Z ^ (k - 1)) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ = _ := by rw [hpow, div_pow]; ring

end PrimeFactorOscillations.CoprimeSchwartzHigh

