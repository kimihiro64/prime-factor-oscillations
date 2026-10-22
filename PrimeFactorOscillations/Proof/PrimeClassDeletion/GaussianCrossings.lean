/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GaussianFiniteEnvelope

/-!
# Exact Gaussian crossings and finite exceptional shifts

At equal height the score is injective in the zero's real part.
At different heights a tie forces one explicit shift. The crossing
denominator is used only for positive c and unequal heights.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

noncomputable def gaussianCrossingTime
    (c : Real) (z w : ZetaDistinctZero) : Real :=
  (c / 2 * (z.val.im ^ 2 - w.val.im ^ 2) -
    (z.val.re - w.val.re) * (1 + c / 2 * (z.val.re + w.val.re))) /
      (c * (z.val.im - w.val.im))

theorem gaussianZeroExponent_eq_crossingTime_of_eq
    (c tau : Real) (z w : ZetaDistinctZero) (hc : 0 < c)
    (hHeight : Not (z.val.im = w.val.im))
    (hEq : gaussianZeroExponent c z.val.re z.val.im tau =
      gaussianZeroExponent c w.val.re w.val.im tau) :
    tau = gaussianCrossingTime c z w := by
  unfold gaussianCrossingTime
  apply (eq_div_iff (mul_ne_zero hc.ne' (sub_ne_zero.mpr hHeight))).mpr
  unfold gaussianZeroExponent at hEq
  nlinarith only [hEq]

theorem gaussianZeroExponent_eq_of_equal_height
    (c tau : Real) (z w : ZetaDistinctZero) (hc : 0 <= c)
    (hHeight : z.val.im = w.val.im)
    (hEq : gaussianZeroExponent c z.val.re z.val.im tau =
      gaussianZeroExponent c w.val.re w.val.im tau) : z = w := by
  have hNonneg : 0 <= c / 2 * (z.val.re + w.val.re) :=
    mul_nonneg (div_nonneg hc (by norm_num))
      (add_nonneg z.property.2.1.le w.property.2.1.le)
  have hFactor : Not (1 + c / 2 * (z.val.re + w.val.re) = 0) := by
    linarith only [hNonneg]
  have hDiff := gaussianZeroExponent_beta_difference c z.val.re w.val.re w.val.im tau
  rw [hHeight] at hEq
  have hMul : (w.val.re - z.val.re) * (1 + c / 2 * (z.val.re + w.val.re)) = 0 := by
    rw [<- hDiff, hEq, sub_self]
  have hRe : w.val.re = z.val.re :=
    sub_eq_zero.mp ((mul_eq_zero.mp hMul).resolve_right hFactor)
  exact Subtype.ext (Complex.ext hRe.symm hHeight)

noncomputable def gaussianCrossingSet (c : Real) (S : Set ZetaDistinctZero) : Set Real :=
  Set.image (fun p : Prod ZetaDistinctZero ZetaDistinctZero => gaussianCrossingTime c p.1 p.2)
    {p | And (Membership.mem S p.1)
      (And (Membership.mem S p.2) (Not (p.1.val.im = p.2.val.im)))}

theorem gaussianCrossingSet_finite (c : Real) (S : Set ZetaDistinctZero) (hS : S.Finite) :
    (gaussianCrossingSet c S).Finite := by
  unfold gaussianCrossingSet
  apply Set.Finite.image
  apply (hS.prod hS).subset
  intro p hp
  exact And.intro hp.1 hp.2.1

theorem gaussianZeroExponent_injOn_outside_crossings
    (c tau : Real) (hc : 0 < c) (S : Set ZetaDistinctZero)
    (hNot : Not (Membership.mem (gaussianCrossingSet c S) tau)) :
    Set.InjOn (fun z : ZetaDistinctZero =>
      gaussianZeroExponent c z.val.re z.val.im tau) S := by
  intro z hz w hw hEq
  by_cases hHeight : z.val.im = w.val.im
  . exact gaussianZeroExponent_eq_of_equal_height c tau z w hc.le hHeight hEq
  . have hTau := gaussianZeroExponent_eq_crossingTime_of_eq c tau z w hc hHeight hEq
    apply False.elim
    apply hNot
    exact Exists.intro (Prod.mk z w)
      (And.intro (And.intro hz (And.intro hw hHeight)) hTau.symm)

end PrimeFactorOscillations.PrimeClassDeletion
