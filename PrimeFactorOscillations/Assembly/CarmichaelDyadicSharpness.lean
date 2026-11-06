/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelDyadicMass
import PrimeFactorOscillations.Assembly.CarmichaelStripReadout

/-!
# Optimality of the quadratic-quartic finite-spectrum carrier coefficient

Every coefficient greater than 11/12 fails in a finite reflected spectrum
already contained in [1/7, 6/7], with positive natural multiplicities.
The witnessing depth is uniform in every positive root height. All points
are realized by the complete atomic readout, whose full nonreal residues
remain nonzero for every real compensation power greater than one.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness

theorem exists_depth_carrier_ratio_lt (eps : Real) (hEps : 0 < eps) :
    exists N : Nat, forall (H : Real) (hH : 0 < H),
      0 < (treeSpectrum (N + 1) H hH).totalMass /\
        (treeSpectrum (N + 1) H hH).carrierMass /
            (treeSpectrum (N + 1) H hH).totalMass < 11 / 12 + eps := by
  choose N hN using exists_nat_gt (1 / (12 * eps))
  refine Exists.intro N ?_
  intro H hH
  apply And.intro (treeSpectrum_totalMass_pos (N + 1) H hH)
  rw [treeSpectrum_carrier_ratio]
  have hScale : 0 < 12 * eps := mul_pos (by norm_num) hEps
  have hMul := mul_lt_mul_of_pos_right hN hScale
  have hCancel : (1 / (12 * eps)) * (12 * eps) = 1 := by
    field_simp [hEps.ne']
  rw [hCancel] at hMul
  have hWeight := treeWeight_lower (N + 1)
  have hDepth : (N : Real) < treeWeight (N + 1) := by
    norm_num only [Nat.cast_add, Nat.cast_one] at hWeight
    linarith
  have hGrow := mul_lt_mul_of_pos_right hDepth hScale
  have hOne : 1 < eps * (12 * treeWeight (N + 1)) := by
    nlinarith only [hMul, hGrow]
  have hDen : 0 < 12 * treeWeight (N + 1) :=
    mul_pos (by norm_num) (treeWeight_pos (N + 1))
  have hDiv := mul_lt_mul_of_pos_right hOne (div_pos (by norm_num : (0 : Real) < 1) hDen)
  have hCancel2 : (eps * (12 * treeWeight (N + 1))) *
      (1 / (12 * treeWeight (N + 1))) = eps := by
    field_simp [hDen.ne', (treeWeight_pos (N + 1)).ne']
  rw [one_mul, hCancel2] at hDiv
  linarith

theorem universal_carrier_coefficient_iff (c : Real) :
    (forall (I : Type) [Fintype I] (S : ReflectedSpectrum I (7 / 8)),
      c * S.totalMass <= S.carrierMass) <-> c <= 11 / 12 := by
  constructor
  . intro h
    by_contra hn
    have hc : 11 / 12 < c := lt_of_not_ge hn
    let eps : Real := (c - 11 / 12) / 2
    have hEps : 0 < eps := by dsimp only [eps]; linarith
    choose N hN using exists_depth_carrier_ratio_lt eps hEps
    have hp := hN 1 (by norm_num)
    let S := treeSpectrum (N + 1) 1 (by norm_num : (0 : Real) < 1)
    have hBound := h (TreeIndex (N + 1)) S
    have hPos : 0 < S.totalMass := hp.1
    have hDiv := div_le_div_of_nonneg_right hBound hPos.le
    have hCancel : c * S.totalMass / S.totalMass = c := by field_simp [hPos.ne']
    rw [hCancel] at hDiv
    have hRatio : S.carrierMass / S.totalMass < 11 / 12 + eps := hp.2
    dsimp only [eps] at hRatio
    linarith
  . intro hc I inst S
    have hNonneg : 0 <= S.totalMass := Finset.sum_nonneg (fun i _ => S.mass_nonneg i)
    exact (mul_le_mul_of_nonneg_right hc hNonneg).trans S.eleven_twelfths_carrier_bound

theorem treeSpectrum_projection_negative_iff (N : Nat) (H : Real) (hH : 0 < H)
    (d : Real) (i : TreeIndex N) :
    (CarmichaelTraceSharpness.atomicPowerResidue (treeSpectrum N H hH).point
        (treeSpectrum N H hH).mult d ((treeSpectrum N H hH).point i) *
      ((treeSpectrum N H hH).point i + (d : Complex) - 1)).im < 0 <->
      d * ((treeSpectrum N H hH).rowOrder d i : Real) <
        ((treeSpectrum N H hH).mult i : Real) := by
  let S := treeSpectrum N H hH
  have h := CarmichaelTraceSharpness.atomicPower_projection S.point S.mult d
    (S.point i) (treeSpectrum_den_ne N H hH d i)
  rw [CarmichaelTraceSharpness.atomicOrder_at _ _ S.point_injective i] at h
  change (CarmichaelTraceSharpness.atomicPowerResidue S.point S.mult d (S.point i) *
      (S.point i + (d : Complex) - 1)).im =
    (d * (S.rowOrder d i : Real) - (S.mult i : Real)) * (S.point i).im at h
  rw [h]
  constructor
  . intro hNeg
    by_contra hn
    have hNonneg := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hn)) (S.im_pos i).le
    exact (not_lt_of_ge hNonneg) hNeg
  . intro hNeg
    exact mul_neg_of_neg_of_pos (sub_neg.mpr hNeg) (S.im_pos i)

theorem treeSpectrum_joint_readout_carrier (N : Nat) (H : Real) (hH : 0 < H) :
    (treeSpectrum N H hH).carrierIndices = Finset.univ.filter (fun i : TreeIndex N =>
      (CarmichaelTraceSharpness.atomicPowerResidue (treeSpectrum N H hH).point
          (treeSpectrum N H hH).mult 2 ((treeSpectrum N H hH).point i) *
        ((treeSpectrum N H hH).point i + ((2 : Real) : Complex) - 1)).im < 0 \/
      (CarmichaelTraceSharpness.atomicPowerResidue (treeSpectrum N H hH).point
          (treeSpectrum N H hH).mult 4 ((treeSpectrum N H hH).point i) *
        ((treeSpectrum N H hH).point i + ((4 : Real) : Complex) - 1)).im < 0) := by
  classical
  apply Finset.ext
  intro i
  simp only [ReflectedSpectrum.carrierIndices, Finset.mem_filter, Finset.mem_univ,
    true_and, treeSpectrum_projection_negative_iff]

end PrimeFactorOscillations.CarmichaelDyadicSharpness
