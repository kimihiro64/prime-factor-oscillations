/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Energy.OriginalHighReflectionGeometry
import PrimeFactorOscillations.Proof.DetectorPackets.KappaHalfReflection

/-!
# KappaHalfUnbalancedGeometry

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors

Original-input deletion gates at every fixed kappa0>1/2.
These gates concern the original short input X1, with no substitution
of the balanced comparison pair. Every finite divisor deletion is retained.
-/

set_option maxHeartbeats 800000

namespace OAI

noncomputable section

open scoped Classical BigOperators

namespace SevenEighths.KappaHalfUnbalancedGeometry

open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceDivisors
open CenteredMomentEnergyReferenceLowBranchGeometry

local notation "O" => HeckeFamily.O

theorem unbalanced_deleted_gates {Z Bmask bPhi : Real}
    (s : NaturalState Z Bmask bPhi)
    (hZ : 1 < Z) (hM : 0 < s.width) (hB : 0 <= Bmask)
    (Mcap L X1 X2 ell z k k0 xi : Real)
    (hwidth : s.width <= Mcap) (hL : Mcap + Bmask + xi <= L)
    (hX1 : 0 < X1) (hX2 : 0 < X2) (hell : 0 <= ell)
    (hz : 0 <= z) (hze : z <= ell)
    (hk0 : 1 / 2 < k0) (hk : k0 <= k) (hxi : 0 <= xi)
    (hreserve : (6 * k0 - 1) * xi <= (6 * k0 - 3) * s.width / 6)
    (hshort : length Z X1 <= s.width / 4)
    (hlarge : 5 * s.width / 6 <= length Z X1 + length Z X2 + ell)
    (hcap : length Z X1 + length Z X2 + 6 * k * ell <= s.width)
    (D1 D2 : Finset (Ideal O))
    (hD1 : Membership.mem (CompletedGauss.primeSupport s.puncture).powerset D1)
    (hD2 : Membership.mem (CompletedGauss.primeSupport s.puncture).powerset D2) :
    let short := Real.logb Z (X1 / ((D1.prod (fun I => I)).absNorm : Real));
    let along := Real.logb Z (X2 / ((D2.prod (fun I => I)).absNorm : Real));
    Z ^ short = X1 / ((D1.prod (fun I => I)).absNorm : Real) /\
    Z ^ along = X2 / ((D2.prod (fun I => I)).absNorm : Real) /\
    short <= s.width / 4 /\ short <= L /\ along <= L /\
    s.width <= (Mcap + Bmask) + along /\
    max 0 (s.width - along + xi) <= L /\
    ((length Z (Z ^ short) + length Z (Z ^ along) + z <= 5 * s.width / 6 /\
        length Z (Z ^ short) + length Z (Z ^ along) + 6 * k * z <= s.width) \/
      (max 0 (s.width - along + xi) + length Z (Z ^ short) + z <= 5 * s.width / 6 /\
        max 0 (s.width - along + xi) + length Z (Z ^ short) + 6 * k * z <= s.width)) := by
  classical
  dsimp only
  have hbase : 0 < Z := zero_lt_one.trans hZ
  have hn1 := (divisor_norm s D1 hD1).1
  have hn2 := (divisor_norm s D2 hD2).1
  have hp1 := div_pos hX1 (zero_lt_one.trans_le hn1)
  have hp2 := div_pos hX2 (zero_lt_one.trans_le hn2)
  have he1 := Real.rpow_logb hbase hZ.ne' hp1
  have he2 := Real.rpow_logb hbase hZ.ne' hp2
  have hd1 := CenteredMomentEnergyOriginalHighReflectionGeometry.deleted_length_le
    Z X1 _ hZ hX1 hn1
  have hd2 := CenteredMomentEnergyOriginalHighReflectionGeometry.deleted_length_le
    Z X2 _ hZ hX2 hn2
  have hraw1 : Real.logb Z (X1 / ((D1.prod (fun I => I)).absNorm : Real)) <=
      length Z (X1 / ((D1.prod (fun I => I)).absNorm : Real)) := by
    rw [length_eq_max_log Z _ hZ hp1]
    exact le_max_right _ _
  have hraw2 : Real.logb Z (X2 / ((D2.prod (fun I => I)).absNorm : Real)) <=
      length Z (X2 / ((D2.prod (fun I => I)).absNorm : Real)) := by
    rw [length_eq_max_log Z _ hZ hp2]
    exact le_max_right _ _
  have hlen1 := length_nonneg Z X1 hZ
  have hlen2 := length_nonneg Z X2 hZ
  have hslot : 0 <= 6 * k * ell := mul_nonneg (by linarith) hell
  have hj := KappaHalfReflection.joint_slot_budget s.width
    (length Z X1 + length Z X2) ell k k0 xi 0 hk0 hk hell
    (by simpa only [sub_zero] using hlarge) hcap
    (by simpa only [mul_zero, add_zero] using hreserve)
  have hjoint : 2 * ell + xi <= s.width / 6 := by simpa only [add_zero] using hj
  have hellCap : ell <= s.width / 12 := by linarith
  have hlongLength : 0 < length Z X2 := by linarith
  have hlongLog : 0 < Real.logb Z X2 := by
    by_contra hn
    have he := length_eq_max_log Z X2 hZ hX2
    rw [he, max_eq_left (le_of_not_gt hn)] at hlongLength
    exact (lt_irrefl 0) hlongLength
  have hX2one : 1 <= X2 := by
    by_contra hn
    have hh := Real.logb_le_logb_of_le hZ hX2 (le_of_not_ge hn)
    rw [Real.logb_one] at hh
    linarith
  have hrange := divisor_reflection_range s hZ Mcap X2 hwidth hX2one D2 hD2
  dsimp only at hrange
  have hlogdiv := Real.logb_div (b := Z) hX2.ne' (zero_lt_one.trans_le hn2).ne'
  rw [<- hlogdiv] at hrange
  have hL0 : 0 <= L := by linarith
  refine And.intro he1 (And.intro he2 (And.intro (by linarith)
    (And.intro (by linarith) (And.intro (by linarith)
      (And.intro hrange.2.1 (And.intro (max_le hL0 (by linarith [hrange.1])) ?_))))))
  rw [he1, he2]
  by_cases hd : length Z (X1 / ((D1.prod (fun I => I)).absNorm : Real)) +
      length Z (X2 / ((D2.prod (fun I => I)).absNorm : Real)) + z <= 5 * s.width / 6
  . apply Or.inl
    have hkz := mul_le_mul_of_nonneg_left hze (by linarith : 0 <= 6 * k)
    exact And.intro hd (by linarith)
  . apply Or.inr
    have hbudget : (6 * k - 1) * ell <= s.width / 6 := by nlinarith
    have hzbudget : (6 * k - 1) * z <= s.width / 6 :=
      (mul_le_mul_of_nonneg_left hze (by linarith)).trans hbudget
    have hhigh := lt_of_not_ge hd
    have hapos : 0 < Real.logb Z (X2 / ((D2.prod (fun I => I)).absNorm : Real)) := by
      by_contra hn
      rw [length_eq_max_log Z _ hZ hp2, max_eq_left (le_of_not_gt hn)] at hhigh
      linarith
    rw [length_eq_max_log Z _ hZ hp2, max_eq_right hapos.le] at hhigh
    by_cases hr : 0 <= s.width -
        Real.logb Z (X2 / ((D2.prod (fun I => I)).absNorm : Real)) + xi
    . rw [max_eq_right hr]
      constructor <;> nlinarith
    . rw [max_eq_left (le_of_not_ge hr)]
      constructor <;> nlinarith

end SevenEighths.KappaHalfUnbalancedGeometry

end

end OAI
