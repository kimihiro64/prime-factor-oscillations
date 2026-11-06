/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelDyadicMass
import PrimeFactorOscillations.Assembly.CarmichaelSimpleTreeRows

/-!
# Complete carrier mass of the simple dyadic spectrum

The exact common-weak support and every retained carrier atom are summed.
For depth N+1 the carrier ratio is 39/40 + 1/(40*T(N+1)), with
19*T(N+1)+1 = 20^(N+2). No asymptotic remainder is estimated.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness

theorem simpleTreeSpectrum_totalMass (N : Nat) (H : Real) (hH : 0 < H) :
    (simpleTreeSpectrum N H hH).totalMass =
      2 * rootMass 0 H * simpleTreeWeight N := by
  classical
  unfold ReflectedSpectrum.totalMass
  rw [Fintype.sum_prod_type]
  simp_rw [simpleTreeSpectrum_mass]
  rw [Fintype.sum_bool]
  simp only [<- Finset.mul_sum, tree_word_sum]
  unfold simpleTreeWeight
  ring

theorem simpleTreeSpectrum_weakMass_succ (N : Nat) (H : Real) (hH : 0 < H) :
    (simpleTreeSpectrum (N + 1) H hH).weakMass =
      rootMass 0 H * simpleTreeWeight N := by
  classical
  let S := simpleTreeSpectrum (N + 1) H hH
  have hWeak : S.weakIndices = Finset.univ.filter
      (fun i : TreeIndex (N + 1) => i.1 = false /\ i.2.val.length < N + 1) := by
    apply Finset.ext
    intro i
    simp only [simpleTree_weak_iff, Finset.mem_filter, Finset.mem_univ, true_and, S]
  change S.weakIndices.sum S.mass = _
  rw [hWeak, Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Bool.true_eq_false, false_and, ite_false, Finset.sum_const_zero, zero_add,
    true_and]
  change (Finset.univ :
      Finset {w : List Bool // Membership.mem (wordSupport (N + 1)) w}).sum
      (fun w => if w.val.length < N + 1 then
        (simpleTreeSpectrum (N + 1) H hH).mass (Prod.mk false w) else 0) = _
  simp_rw [simpleTreeSpectrum_mass]
  rw [tree_word_sum (N + 1) (fun w : List Bool =>
    if w.length < N + 1 then rootMass 0 H * simpleWordWeight w else 0)]
  have hFilter : (wordSupport (N + 1)).filter (fun w => w.length < N + 1) = wordSupport N := by
    apply Finset.ext
    intro w
    simp only [Finset.mem_filter, mem_wordSupport]
    omega
  rw [<- Finset.sum_filter, hFilter, <- Finset.mul_sum]
  rfl

theorem simpleTreeSpectrum_carrierMass_succ (N : Nat) (H : Real) (hH : 0 < H) :
    (simpleTreeSpectrum (N + 1) H hH).carrierMass =
      rootMass 0 H * (2 * simpleTreeWeight (N + 1) - simpleTreeWeight N) := by
  have h := (simpleTreeSpectrum (N + 1) H hH).totalMass_eq_weakMass_add_carrierMass
  rw [simpleTreeSpectrum_totalMass, simpleTreeSpectrum_weakMass_succ] at h
  nlinarith only [h]

theorem simpleTreeSpectrum_totalMass_pos (N : Nat) (H : Real) (hH : 0 < H) :
    0 < (simpleTreeSpectrum N H hH).totalMass := by
  rw [simpleTreeSpectrum_totalMass]
  exact mul_pos (mul_pos (by norm_num) (rootMass_pos 0 H hH)) (simpleTreeWeight_pos N)

theorem simpleTreeSpectrum_carrier_ratio (N : Nat) (H : Real) (hH : 0 < H) :
    (simpleTreeSpectrum (N + 1) H hH).carrierMass /
        (simpleTreeSpectrum (N + 1) H hH).totalMass =
      39 / 40 + 1 / (40 * simpleTreeWeight (N + 1)) := by
  have hc : Not (rootMass 0 H = 0) := ne_of_gt (rootMass_pos 0 H hH)
  have ht : Not (1 + 20 * simpleTreeWeight N = 0) := by
    rw [<- simpleTreeWeight_succ]
    exact ne_of_gt (simpleTreeWeight_pos (N + 1))
  rw [simpleTreeSpectrum_carrierMass_succ, simpleTreeSpectrum_totalMass]
  simp only [simpleTreeWeight_succ]
  field_simp [hc, ht]
  ring

theorem simpleTreeSpectrum_carrier_ratio_closed (N : Nat) (H : Real) (hH : 0 < H) :
    (simpleTreeSpectrum (N + 1) H hH).carrierMass /
        (simpleTreeSpectrum (N + 1) H hH).totalMass =
      39 / 40 + 19 / (40 * ((20 : Real) ^ (N + 2) - 1)) := by
  have h : (20 : Real) ^ (N + 2) - 1 = 19 * simpleTreeWeight (N + 1) := by
    have hh := nineteen_simpleTreeWeight_add_one (N + 1)
    nlinarith only [hh]
  rw [simpleTreeSpectrum_carrier_ratio, h]
  field_simp [(simpleTreeWeight_pos (N + 1)).ne']

end PrimeFactorOscillations.CarmichaelDyadicSharpness
