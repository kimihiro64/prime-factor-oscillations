/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelJointTransport

/-!
# Strip-dependent joint multiplicity carriers

A finite escape depth for the coupled reference map improves the fraction
of inverse-square-height multiplicity mass retained by two power rows.
The seven-eighths specialization is unconditional and concerns carrier mass,
not an improved zero-free boundary or an upper bound on multiplicities.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelStripCarrier

open DirichletCompensatedProbe CarmichaelWeightedSignal

def jointCarrierSupport (d e T : Real) : Finset Complex :=
  (upperZeroValues T).filter (fun z =>
    d * (analyticOrderNatAt riemannZeta (powerMap d z) : Real) <
      (analyticOrderNatAt riemannZeta z : Real) \/
    e * (analyticOrderNatAt riemannZeta (powerMap e z) : Real) <
      (analyticOrderNatAt riemannZeta z : Real))

theorem zeta_joint_weak_mass_strip_bound (d e T sigma : Real)
    (hd : 2 <= d) (he : 2 <= e) (L : Nat) (hL : 0 < L)
    (hStrip : forall z, Membership.mem (rightZeroSupport T) z -> z.re <= sigma)
    (hDepth : (1 / 2 : Real) <= (e / d) ^ L * (1 - sigma)) :
    2 * e * (jointWeakSupport d e T).sum zetaSquareMass <=
      (1 - 1 / (Finset.range L).sum (fun j => (e / d) ^ j)) *
        (upperZeroValues T).sum zetaSquareMass := by
  classical
  let r := e / d
  let H := (Finset.range L).sum (fun j => r ^ j)
  have hd0 : 0 < d := by linarith
  have he0 : 0 < e := by linarith
  have hr : 0 < r := div_pos he0 hd0
  have hH1 : 1 <= H := by
    have h := Finset.single_le_sum
      (fun j (_ : Membership.mem (Finset.range L) j) => pow_nonneg hr.le j)
      (Finset.mem_range.mpr hL)
    simpa only [pow_zero] using h
  have hH0 : 0 < H := by linarith
  have hEscape := rightZeroMass_escape T sigma r hr.le hStrip L hDepth
  have hC := finite_nilpotent_transport_covered_mass (rightZeroSupport T)
    (stripTransport r) (stripTransport_injective r hr)
    (rightZeroMass T) (jointWeakLift d e T) r hr.le
    (jointWeakLift_le_rightMass d e T he) (rightZeroMass_support T)
    (jointWeakLift_support d e T he) (jointWeakLift_transport d e T hd he)
    L hEscape hH0
  rw [jointWeakLift_sum d e T he, rightZeroMass_sum T] at hC
  change e * (jointWeakSupport d e T).sum zetaSquareMass <=
    (1 - 1 / H) * (rightZeroSupport T).sum zetaSquareMass at hC
  have hHalf := zeta_weighted_right_half_le T (fun t => 1 / t ^ 2)
    (fun t _ => one_div_nonneg.mpr (sq_nonneg t))
  change 2 * (rightZeroSupport T).sum zetaSquareMass <=
    (upperZeroValues T).sum zetaSquareMass at hHalf
  have hInvProduct : H * (1 / H) = 1 := by
    field_simp [ne_of_gt hH0]
  have hExtra := mul_nonneg (sub_nonneg.mpr hH1) (one_div_nonneg.mpr hH0.le)
  have hAlpha : 0 <= 1 - 1 / H := by
    nlinarith only [hInvProduct, hExtra]
  have hHalfScaled := mul_le_mul_of_nonneg_left hHalf hAlpha
  change 2 * e * (jointWeakSupport d e T).sum zetaSquareMass <=
    (1 - 1 / H) * (upperZeroValues T).sum zetaSquareMass
  nlinarith only [hC, hHalfScaled]

theorem joint_carrier_mass_split (d e T : Real) :
    (upperZeroValues T).sum zetaSquareMass =
      (jointWeakSupport d e T).sum zetaSquareMass +
        (jointCarrierSupport d e T).sum zetaSquareMass := by
  classical
  dsimp only [jointWeakSupport, jointCarrierSupport]
  rw [Finset.sum_filter, Finset.sum_filter, <- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hD : (analyticOrderNatAt riemannZeta z : Real) <=
      d * (analyticOrderNatAt riemannZeta (powerMap d z) : Real)
  . by_cases hE : (analyticOrderNatAt riemannZeta z : Real) <=
        e * (analyticOrderNatAt riemannZeta (powerMap e z) : Real)
    . simp [hD, hE, not_lt_of_ge hD, not_lt_of_ge hE]
    . have hEt := lt_of_not_ge hE
      simp [hD, hE, hEt]
  . have hDt := lt_of_not_ge hD
    simp [hD, hDt]

theorem zeta_joint_carrier_strip_bound (d e T sigma : Real)
    (hd : 2 <= d) (he : 2 <= e) (L : Nat) (hL : 0 < L)
    (hStrip : forall z, Membership.mem (rightZeroSupport T) z -> z.re <= sigma)
    (hDepth : (1 / 2 : Real) <= (e / d) ^ L * (1 - sigma)) :
    (1 - (1 - 1 / (Finset.range L).sum (fun j => (e / d) ^ j)) / (2 * e)) *
        (upperZeroValues T).sum zetaSquareMass <=
      (jointCarrierSupport d e T).sum zetaSquareMass := by
  let H := (Finset.range L).sum (fun j => (e / d) ^ j)
  let A := (upperZeroValues T).sum zetaSquareMass
  let C := (jointCarrierSupport d e T).sum zetaSquareMass
  let U := (jointWeakSupport d e T).sum zetaSquareMass
  have he0 : 0 < e := by linarith
  have hWeak := zeta_joint_weak_mass_strip_bound d e T sigma hd he L hL hStrip hDepth
  change 2 * e * U <= (1 - 1 / H) * A at hWeak
  have hSplit : A = U + C := joint_carrier_mass_split d e T
  have hSplitScaled : 2 * e * A = 2 * e * U + 2 * e * C := by
    rw [hSplit]
    ring
  change (1 - (1 - 1 / H) / (2 * e)) * A <= C
  have hFactor : (2 * e) * ((1 - (1 - 1 / H) / (2 * e)) * A) =
      (2 * e - (1 - 1 / H)) * A := by
    field_simp
    <;> ring
  by_contra hNot
  have hlt := mul_lt_mul_of_pos_left (lt_of_not_ge hNot)
    (show 0 < 2 * e by positivity)
  rw [hFactor] at hlt
  nlinarith only [hWeak, hSplitScaled, hlt]

theorem zeta_two_three_carrier_seven_eighths (T : Real) :
    (111 / 130 : Real) * (upperZeroValues T).sum zetaSquareMass <=
      (jointCarrierSupport 2 3 T).sum zetaSquareMass := by
  have h := zeta_joint_carrier_strip_bound 2 3 T (7 / 8)
    (by norm_num) (by norm_num) 4 (by norm_num)
    (rightZeroSupport_seven_eighths T) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  exact h

end PrimeFactorOscillations.CarmichaelStripCarrier
