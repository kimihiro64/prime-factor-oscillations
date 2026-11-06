/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Fintype.BigOperators
import PrimeFactorOscillations.Assembly.CarmichaelDyadicRows
import PrimeFactorOscillations.Assembly.CarmichaelFiniteCarrier

/-!
# Exact dyadic carrier masses

The complete finite natural-multiplicity spectrum has two reflected rails.
Only the nonterminal left rail is common weak. Summing the actual atomic
masses gives a carrier ratio 11/12 + 1/(12*treeWeight(N+1)).
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness

theorem tree_word_sum (N : Nat) (f : List Bool -> Real) :
    (Finset.univ : Finset {w : List Bool // Membership.mem (wordSupport N) w}).sum
      (fun w => f w.val) = (wordSupport N).sum f := by
  change (wordSupport N).attach.sum (fun w => f w.val) = _
  exact Finset.sum_attach _ _

theorem treeSpectrum_totalMass (N : Nat) (H : Real) (hH : 0 < H) :
    (treeSpectrum N H hH).totalMass = 2 * rootMass N H * treeWeight N := by
  classical
  unfold ReflectedSpectrum.totalMass
  rw [Fintype.sum_prod_type]
  simp_rw [treeSpectrum_mass]
  rw [Fintype.sum_bool]
  simp only [<- Finset.mul_sum, tree_word_sum]
  unfold treeWeight
  ring

theorem treeSpectrum_weakMass_succ (N : Nat) (H : Real) (hH : 0 < H) :
    (treeSpectrum (N + 1) H hH).weakMass = rootMass (N + 1) H * treeWeight N := by
  classical
  let S := treeSpectrum (N + 1) H hH
  have hWeak : S.weakIndices = Finset.univ.filter
      (fun i : TreeIndex (N + 1) => i.1 = false /\ i.2.val.length < N + 1) := by
    apply Finset.ext
    intro i
    simp only [tree_weak_iff, Finset.mem_filter, Finset.mem_univ, true_and, S]
  change S.weakIndices.sum S.mass = _
  rw [hWeak, Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Bool.true_eq_false, false_and, ite_false, Finset.sum_const_zero, zero_add,
    true_and]
  change (Finset.univ :
      Finset {w : List Bool // Membership.mem (wordSupport (N + 1)) w}).sum
      (fun w => if w.val.length < N + 1 then
        (treeSpectrum (N + 1) H hH).mass (Prod.mk false w) else 0) = _
  simp_rw [treeSpectrum_mass]
  rw [tree_word_sum (N + 1) (fun w : List Bool =>
    if w.length < N + 1 then rootMass (N + 1) H * wordWeight w else 0)]
  have hFilter : (wordSupport (N + 1)).filter (fun w => w.length < N + 1) = wordSupport N := by
    apply Finset.ext
    intro w
    simp only [Finset.mem_filter, mem_wordSupport]
    omega
  rw [<- Finset.sum_filter, hFilter, <- Finset.mul_sum]
  rfl

theorem treeSpectrum_carrierMass_succ (N : Nat) (H : Real) (hH : 0 < H) :
    (treeSpectrum (N + 1) H hH).carrierMass =
      rootMass (N + 1) H * (2 * treeWeight (N + 1) - treeWeight N) := by
  have h := (treeSpectrum (N + 1) H hH).totalMass_eq_weakMass_add_carrierMass
  rw [treeSpectrum_totalMass, treeSpectrum_weakMass_succ] at h
  nlinarith only [h]

theorem treeSpectrum_totalMass_pos (N : Nat) (H : Real) (hH : 0 < H) :
    0 < (treeSpectrum N H hH).totalMass := by
  rw [treeSpectrum_totalMass]
  exact mul_pos (mul_pos (by norm_num) (rootMass_pos N H hH)) (treeWeight_pos N)

theorem treeSpectrum_carrier_ratio (N : Nat) (H : Real) (hH : 0 < H) :
    (treeSpectrum (N + 1) H hH).carrierMass /
        (treeSpectrum (N + 1) H hH).totalMass =
      11 / 12 + 1 / (12 * treeWeight (N + 1)) := by
  have hc : Not (rootMass (N + 1) H = 0) := ne_of_gt (rootMass_pos (N + 1) H hH)
  have ht : Not (1 + 6 * treeWeight N = 0) := by
    rw [<- treeWeight_succ]
    exact ne_of_gt (treeWeight_pos (N + 1))
  rw [treeSpectrum_carrierMass_succ, treeSpectrum_totalMass]
  simp only [treeWeight_succ]
  field_simp [hc, ht]
  ring

theorem treeSpectrum_carrier_ratio_closed (N : Nat) (H : Real) (hH : 0 < H) :
    (treeSpectrum (N + 1) H hH).carrierMass /
        (treeSpectrum (N + 1) H hH).totalMass =
      11 / 12 + 5 / (12 * ((6 : Real) ^ (N + 2) - 1)) := by
  have h : (6 : Real) ^ (N + 2) - 1 = 5 * treeWeight (N + 1) := by
    have hh := five_treeWeight_add_one (N + 1)
    nlinarith only [hh]
  rw [treeSpectrum_carrier_ratio, h]
  field_simp [(treeWeight_pos (N + 1)).ne']

end PrimeFactorOscillations.CarmichaelDyadicSharpness
