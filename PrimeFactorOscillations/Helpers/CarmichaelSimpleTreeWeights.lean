/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.CarmichaelDyadicWeights

/-!
# Exact inverse-height weights of the simple dyadic spectrum

Keeping every multiplicity equal to one squares the previous word weight.
The two child contributions are 4 and 16, and the complete finite support
has total weight (20^(N+1)-1)/19.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness

def simpleWordWeight (w : List Bool) : Real :=
  (4 : Real) ^ wordScore w

def simpleTreeWeight (N : Nat) : Real :=
  (wordSupport N).sum simpleWordWeight

theorem simpleWordWeight_nil : simpleWordWeight [] = 1 := by
  norm_num [simpleWordWeight, wordScore]

theorem simpleWordWeight_false (w : List Bool) :
    simpleWordWeight (false :: w) = 4 * simpleWordWeight w := by
  simp only [simpleWordWeight, wordScore, pow_succ]
  ring

theorem simpleWordWeight_true (w : List Bool) :
    simpleWordWeight (true :: w) = 16 * simpleWordWeight w := by
  simp only [simpleWordWeight, wordScore, pow_add]
  norm_num
  ring

theorem simpleTreeWeight_zero : simpleTreeWeight 0 = 1 := by
  norm_num [simpleTreeWeight, wordSupport, simpleWordWeight, wordScore]

theorem simpleTreeWeight_succ (N : Nat) :
    simpleTreeWeight (N + 1) = 1 + 20 * simpleTreeWeight N := by
  classical
  have hDisjoint : Disjoint ((wordSupport N).image (List.cons false))
      ((wordSupport N).image (List.cons true)) := by
    apply Finset.disjoint_left.mpr
    intro w hf ht
    choose u hu heu using Finset.mem_image.mp hf
    choose v hv hev using Finset.mem_image.mp ht
    have he : false :: u = true :: v := heu.trans hev.symm
    simp at he
  have hRoot : Not (Membership.mem
      (Union.union ((wordSupport N).image (List.cons false))
        ((wordSupport N).image (List.cons true))) []) := by simp
  have hf : Set.InjOn (List.cons false) (wordSupport N) := by
    intro u hu v hv he
    simpa using congrArg List.tail he
  have ht : Set.InjOn (List.cons true) (wordSupport N) := by
    intro u hu v hv he
    simpa using congrArg List.tail he
  unfold simpleTreeWeight
  rw [wordSupport, Finset.sum_insert hRoot, Finset.sum_union hDisjoint,
    Finset.sum_image hf, Finset.sum_image ht, simpleWordWeight_nil]
  simp_rw [simpleWordWeight_false, simpleWordWeight_true]
  rw [<- Finset.mul_sum, <- Finset.mul_sum]
  ring

theorem simpleTreeWeight_lower (N : Nat) :
    (N : Real) + 1 <= simpleTreeWeight N := by
  induction N with
  | zero => norm_num [simpleTreeWeight_zero]
  | succ N ih =>
    rw [simpleTreeWeight_succ]
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith

theorem simpleTreeWeight_pos (N : Nat) : 0 < simpleTreeWeight N := by
  have h := simpleTreeWeight_lower N
  have hn : (0 : Real) <= (N : Real) := Nat.cast_nonneg N
  linarith

theorem nineteen_simpleTreeWeight_add_one (N : Nat) :
    19 * simpleTreeWeight N + 1 = (20 : Real) ^ (N + 1) := by
  induction N with
  | zero => norm_num [simpleTreeWeight_zero]
  | succ N ih =>
    rw [simpleTreeWeight_succ, pow_succ (20 : Real) (N + 1)]
    nlinarith

end PrimeFactorOscillations.CarmichaelDyadicSharpness
