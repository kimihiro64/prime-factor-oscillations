/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Finset.Card
import PrimeFactorOscillations.Definitions.ReciprocalSmoothLaw

/-!
# Tilting local laws and detecting strict ascent thresholds on a finite grid

The local probabilities t / (p - 1 + t) have odds t / (p - 1).
Their exact reciprocal gap threshold becomes g + t after multiplying
by t. A mesh finer than a positive comparison residual detects an
additional strict ascent in a finite tilt count.

These are algebraic sampling ingredients. No short-interval prime theorem,
RH equivalence, or bound for a maximal reversal count is asserted here.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

noncomputable def oddsTiltLaw (t : Real) (ht : 0 < t) : ReciprocalSmoothLaw where
  eta p := t / ((p : Real) - 1 + t)
  nu := t
  offset := (t - 1) / t
  nu_pos := ht
  probability := by
    intro p hp
    have hpTwo : (2 : Real) <= p := by exact_mod_cast hp.two_le
    have hden : 0 < (p : Real) - 1 + t := by linarith
    refine And.intro (div_nonneg ht.le hden.le) ?_
    have hid : (t / ((p : Real) - 1 + t)) * ((p : Real) - 1 + t) = t := by
      field_simp [hden.ne']
    by_contra hn
    have hmul := mul_lt_mul_of_pos_right (lt_of_not_ge hn) hden
    rw [one_mul, hid] at hmul
    linarith
  reciprocal_control := by
    intro epsilon he
    refine Exists.intro 2 ?_
    intro p hp hprime
    have hpTwo : (2 : Real) <= p := by exact_mod_cast hp
    have hden : 0 < (p : Real) - 1 + t := by linarith
    have hid : 1 / (t / ((p : Real) - 1 + t)) - (p : Real) / t -
        (t - 1) / t = 0 := by
      field_simp [ht.ne', hden.ne']
      ring
    rw [hid, abs_zero]
    exact he.le

theorem oddsTiltLaw_odds (t : Real) (ht : 0 < t) (p : Nat)
    (hp : 1 < p) :
    (oddsTiltLaw t ht).eta p / (1 - (oddsTiltLaw t ht).eta p) =
      t / ((p : Real) - 1) := by
  have hpReal : (1 : Real) < p := by exact_mod_cast hp
  have hden : 0 < (p : Real) - 1 + t := by linarith
  have hpSub : Not ((p : Real) - 1 = 0) := by linarith
  change (t / ((p : Real) - 1 + t)) /
    (1 - t / ((p : Real) - 1 + t)) = t / ((p : Real) - 1)
  have hc : 1 - t / ((p : Real) - 1 + t) =
      ((p : Real) - 1) / ((p : Real) - 1 + t) := by
    field_simp [hden.ne']
    ring
  rw [hc]
  field_simp [hden.ne', hpSub]

theorem tilted_gap_threshold_iff (R g t : Real) (ht : 0 < t) :
    g / t + 1 < R / t <-> g + t < R := by
  have hid : g / t + 1 = (g + t) / t := by
    field_simp [ht.ne']
  rw [hid]
  have hR : (R / t) * t = R := by field_simp [ht.ne']
  have hG : ((g + t) / t) * t = g + t := by field_simp [ht.ne']
  constructor
  next =>
    intro h
    have hm := mul_lt_mul_of_pos_right h ht
    rwa [hR, hG] at hm
  next =>
    intro h
    by_contra hn
    have hm := _root_.mul_le_mul_of_nonneg_right (le_of_not_gt hn) ht.le
    rw [hR, hG] at hm
    linarith

theorem exists_tilt_grid_detection (H M : Nat) (hM : 0 < M)
    (R U g : Real) (hLow : 1 <= U - g)
    (hHigh : R - g <= (H : Real) + 1)
    (hGain : 1 / (M : Real) < R - U) :
    exists j : Nat, j <= H * M /\
      U < g + 1 + (j : Real) / M /\
      g + 1 + (j : Real) / M < R := by
  have hMr : (0 : Real) < M := by exact_mod_cast hM
  let y : Real := (M : Real) * (U - g - 1)
  have hy : 0 <= y := by dsimp [y]; exact mul_nonneg hMr.le (by linarith)
  let j : Nat := Nat.floor y + 1
  have hyj : y < (j : Real) := by
    simpa only [j, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one y
  have hjy : (j : Real) <= y + 1 := by
    have hf := Nat.floor_le hy
    dsimp only [j]
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  have hLower : U < g + 1 + (j : Real) / M := by
    have hm : (U - g - 1) * (M : Real) < j := by
      simpa only [y, mul_comm] using hyj
    have hd := div_lt_div_of_pos_right hm hMr
    have hc : ((U - g - 1) * (M : Real)) / M = U - g - 1 := by
      field_simp [hMr.ne']
    rw [hc] at hd
    linarith
  have hUpper : g + 1 + (j : Real) / M < R := by
    have hd : (j : Real) / M <= U - g - 1 + 1 / M := by
      calc
        (j : Real) / M <= (y + 1) / M :=
          _root_.div_le_div_of_nonneg_right hjy hMr.le
        _ = U - g - 1 + 1 / M := by
          dsimp [y]
          field_simp [hMr.ne']
    linarith
  have hjBound : (j : Real) < (H : Real) * M := by
    have hd : (j : Real) / M < H := by linarith
    have hm := mul_lt_mul_of_pos_right hd hMr
    have hc : ((j : Real) / M) * M = j := by field_simp [hMr.ne']
    rwa [hc] at hm
  have hjNat : j < H * M := by exact_mod_cast hjBound
  exact Exists.intro j (And.intro hjNat.le (And.intro hLower hUpper))

noncomputable def tiltAscentSet (H M : Nat) (R g : Real) : Finset Nat := by
  classical
  exact (Finset.range (H * M + 1)).filter
    (fun j => g + 1 + (j : Real) / M < R)

theorem tiltAscentSet_subset (H M : Nat) (R U g : Real) (h : U <= R) :
    tiltAscentSet H M U g <= tiltAscentSet H M R g := by
  classical
  intro j hj
  simp only [tiltAscentSet, Finset.mem_filter] at hj
  simp only [tiltAscentSet, Finset.mem_filter]
  exact And.intro hj.1 (hj.2.trans_le h)

theorem tiltAscentSet_card_le (H M : Nat) (R U g : Real) (h : U <= R) :
    (tiltAscentSet H M U g).card <= (tiltAscentSet H M R g).card :=
  Finset.card_le_card (tiltAscentSet_subset H M R U g h)

theorem tiltAscentSet_card_lt_of_mesh_lt (H M : Nat) (hM : 0 < M)
    (R U g : Real) (hLow : 1 <= U - g)
    (hHigh : R - g <= (H : Real) + 1)
    (hGain : 1 / (M : Real) < R - U) :
    (tiltAscentSet H M U g).card < (tiltAscentSet H M R g).card := by
  classical
  choose j hjBound hjLow hjHigh using
    exists_tilt_grid_detection H M hM R U g hLow hHigh hGain
  have hMr : (0 : Real) < M := by exact_mod_cast hM
  have hInv : (0 : Real) < 1 / M := one_div_pos.mpr hMr
  have hsub := tiltAscentSet_subset H M R U g (by linarith)
  apply Finset.card_lt_card
  apply ssubset_iff_subset_ne.mpr
  refine And.intro hsub ?_
  intro heq
  have hjActual : Membership.mem (tiltAscentSet H M R g) j := by
    simp only [tiltAscentSet, Finset.mem_filter, Finset.mem_range]
    exact And.intro (Nat.lt_succ_of_le hjBound) hjHigh
  rw [<- heq] at hjActual
  simp only [tiltAscentSet, Finset.mem_filter] at hjActual
  linarith only [hjActual.2, hjLow]

end PrimeFactorOscillations
