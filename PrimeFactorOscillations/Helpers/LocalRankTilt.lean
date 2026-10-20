/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Tactic.FieldSimp
import PrimeFactorOscillations.Helpers.LocalMassGenerating

/-!
# Exact rank tilts of a local probability step

The full supported rank mixture retains the local gap term exactly.
This identity does not supply an independent positivity estimate.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

theorem localStep_rank_generating (eta : Nat -> Rat) (ps : List Nat)
    (p q : Nat) (z : Rat) :
    (Finset.range (ps.length + 2)).sum (fun r =>
      (eta q * finiteLocalMass eta (p :: ps) r -
        eta p * finiteLocalMass eta ps r) * z ^ r) =
      (eta q * (1 - eta p + eta p * z) - eta p) *
        (ps.map (fun l => 1 - eta l + eta l * z)).prod := by
  simp_rw [sub_mul, mul_assoc]
  rw [Finset.sum_sub_distrib, <- Finset.mul_sum, <- Finset.mul_sum]
  have hnew := finiteLocalMass_generating eta (p :: ps) z
  simp only [List.length_cons, List.map_cons, List.prod_cons] at hnew
  have hold : (Finset.range (ps.length + 2)).sum
      (fun r => finiteLocalMass eta ps r * z ^ r) =
      (ps.map (fun l => 1 - eta l + eta l * z)).prod := by
    rw [Finset.sum_range_succ]
    rw [finiteLocalMass_eq_zero_of_length_lt eta ps (ps.length + 1) (by omega)]
    simp only [zero_mul, add_zero]
    exact finiteLocalMass_generating eta ps z
  rw [hnew, hold]

theorem reciprocal_localStep_rank_generating (ps : List Nat) (p q : Nat)
    (hp : 0 < p) (hq : 0 < q) (z : Rat) :
    (Finset.range (ps.length + 2)).sum (fun r =>
      ((1 / (q : Rat)) * finiteLocalMass (fun l => 1 / (l : Rat)) (p :: ps) r -
        (1 / (p : Rat)) * finiteLocalMass (fun l => 1 / (l : Rat)) ps r) * z ^ r) =
      ((z - 1 - ((q : Rat) - p)) / ((p : Rat) * q)) *
        (ps.map (fun l : Nat => 1 - 1 / (l : Rat) + (1 / (l : Rat)) * z)).prod := by
  rw [localStep_rank_generating (fun l : Nat => 1 / (l : Rat)) ps p q z]
  have hp0 : Not ((p : Rat) = 0) := by exact_mod_cast (Nat.ne_of_gt hp)
  have hq0 : Not ((q : Rat) = 0) := by exact_mod_cast (Nat.ne_of_gt hq)
  congr 1
  field_simp
  ring

end PrimeFactorOscillations
