/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import PrimeFactorOscillations.Helpers.CarmichaelDyadicWords

/-!
# Natural multiplicities and exact dyadic tree mass

The finite-depth multiplicities are positive natural numbers. Their inverse
square-height masses are a common positive scale times the word weight.
All words through depth N have total word weight (6^(N+1)-1)/5.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness

def wordHeight (H : Real) (w : List Bool) : Real :=
  H / (2 : Real) ^ wordScore w

def wordMultiplicity (N : Nat) (w : List Bool) : Nat :=
  2 ^ (2 * N - wordScore w)

def wordWeight (w : List Bool) : Real :=
  (2 : Real) ^ wordScore w

def rootMass (N : Nat) (H : Real) : Real :=
  (2 : Real) ^ (2 * N) / H ^ 2

def wordMass (N : Nat) (H : Real) (w : List Bool) : Real :=
  (wordMultiplicity N w : Real) / (wordHeight H w) ^ 2

def treeWeight (N : Nat) : Real :=
  (wordSupport N).sum wordWeight

theorem wordHeight_pos (H : Real) (hH : 0 < H) (w : List Bool) :
    0 < wordHeight H w :=
  div_pos hH (pow_pos (by norm_num) _)

theorem wordMultiplicity_pos (N : Nat) (w : List Bool) :
    0 < wordMultiplicity N w := by
  unfold wordMultiplicity
  exact Nat.pow_pos (by decide)

theorem rootMass_pos (N : Nat) (H : Real) (hH : 0 < H) :
    0 < rootMass N H :=
  div_pos (pow_pos (by norm_num) _) (pow_pos hH _)

theorem wordMultiplicity_scale (N : Nat) (w : List Bool)
    (hw : Membership.mem (wordSupport N) w) :
    (wordMultiplicity N w : Real) * (2 : Real) ^ wordScore w =
      (2 : Real) ^ (2 * N) := by
  have hs := wordScore_le_of_mem N w hw
  simp only [wordMultiplicity, Nat.cast_pow, Nat.cast_ofNat]
  rw [<- pow_add, Nat.sub_add_cancel hs]

theorem wordMass_eq (N : Nat) (H : Real) (w : List Bool)
    (hw : Membership.mem (wordSupport N) w) :
    wordMass N H w = rootMass N H * wordWeight w := by
  have hm := wordMultiplicity_scale N w hw
  have hm2 :
      (wordMultiplicity N w : Real) * ((2 : Real) ^ wordScore w) ^ 2 =
        (2 : Real) ^ (2 * N) * (2 : Real) ^ wordScore w := by
    calc
      _ = ((wordMultiplicity N w : Real) * (2 : Real) ^ wordScore w) *
          (2 : Real) ^ wordScore w := by ring
      _ = _ := by rw [hm]
  unfold wordMass wordHeight rootMass wordWeight
  rw [div_pow, div_div_eq_mul_div, hm2]
  ring

theorem wordHeight_false (H : Real) (w : List Bool) :
    wordHeight H (false :: w) = wordHeight H w / 2 := by
  simp only [wordHeight, wordScore, pow_succ]
  ring

theorem wordHeight_true (H : Real) (w : List Bool) :
    wordHeight H (true :: w) = wordHeight H w / 4 := by
  simp only [wordHeight, wordScore, pow_add]
  norm_num
  ring

theorem wordMultiplicity_false (N : Nat) (w : List Bool)
    (hw : w.length < N) :
    wordMultiplicity N w = 2 * wordMultiplicity N (false :: w) := by
  have hs := wordScore_le_twice_length w
  have he : 2 * N - wordScore w = (2 * N - (wordScore w + 1)) + 1 := by omega
  unfold wordMultiplicity
  simp only [wordScore]
  rw [he, pow_succ]
  ring

theorem wordMultiplicity_true (N : Nat) (w : List Bool)
    (hw : w.length < N) :
    wordMultiplicity N w = 4 * wordMultiplicity N (true :: w) := by
  have hs := wordScore_le_twice_length w
  have he : 2 * N - wordScore w = (2 * N - (wordScore w + 2)) + 2 := by omega
  unfold wordMultiplicity
  simp only [wordScore]
  rw [he, pow_add]
  norm_num
  ring

theorem wordWeight_nil : wordWeight [] = 1 := by
  norm_num [wordWeight, wordScore]

theorem wordWeight_false (w : List Bool) :
    wordWeight (false :: w) = 2 * wordWeight w := by
  simp only [wordWeight, wordScore, pow_succ]
  ring

theorem wordWeight_true (w : List Bool) :
    wordWeight (true :: w) = 4 * wordWeight w := by
  simp only [wordWeight, wordScore, pow_add]
  norm_num
  ring

theorem treeWeight_zero : treeWeight 0 = 1 := by
  simp [treeWeight, wordSupport, wordWeight_nil]

theorem treeWeight_succ (N : Nat) : treeWeight (N + 1) = 1 + 6 * treeWeight N := by
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
  unfold treeWeight
  rw [wordSupport, Finset.sum_insert hRoot, Finset.sum_union hDisjoint,
    Finset.sum_image hf, Finset.sum_image ht, wordWeight_nil]
  simp_rw [wordWeight_false, wordWeight_true]
  rw [<- Finset.mul_sum, <- Finset.mul_sum]
  ring

theorem treeWeight_lower (N : Nat) : (N : Real) + 1 <= treeWeight N := by
  induction N with
  | zero => norm_num [treeWeight_zero]
  | succ N ih =>
    rw [treeWeight_succ]
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith

theorem treeWeight_pos (N : Nat) : 0 < treeWeight N := by
  have h := treeWeight_lower N
  have hn : (0 : Real) <= (N : Real) := Nat.cast_nonneg N
  linarith

theorem five_treeWeight_add_one (N : Nat) :
    5 * treeWeight N + 1 = (6 : Real) ^ (N + 1) := by
  induction N with
  | zero => norm_num [treeWeight_zero]
  | succ N ih =>
    rw [treeWeight_succ, pow_succ (6 : Real) (N + 1)]
    nlinarith

end PrimeFactorOscillations.CarmichaelDyadicSharpness
