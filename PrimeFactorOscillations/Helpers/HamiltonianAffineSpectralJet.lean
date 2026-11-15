/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianSpectralFactorDerivatives

/-! # Actual second derivative of an affine spectral determinant factor

Eigenvalues may have either sign. Every denominator is retained.
The consumer identifies the determinant-derivative part of the first
permanent correction with full covariance traces.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

def affineSpectralCoordinate0 (lam t : Real) : Real :=
  -(1 / 2 : Real) * Real.log (1 + t * lam)

def affineSpectralCoordinate1 (lam t : Real) : Real :=
  (-(1 / 2 : Real) * lam) / (1 + t * lam)

def affineSpectralCoordinate2 (lam t : Real) : Real :=
  ((1 / 2 : Real) * lam ^ 2) / (1 + t * lam) ^ 2

variable {Iota : Type*}

def affineSpectralFactors (S : Finset Iota) (lam : Iota -> Real) (t : Real) : Real :=
  Real.exp (Finset.sum S (fun i => affineSpectralCoordinate0 (lam i) t))

private theorem affineDenominator_hasDerivAt (lam t : Real) :
    HasDerivAt (fun x : Real => 1 + x * lam) lam t := by
  convert (hasDerivAt_const t (1 : Real)).add ((hasDerivAt_id t).mul_const lam) using 1
  case e'_8 =>
    funext x
    rfl
  case e'_9 =>
    simp only [id_eq, zero_add, one_mul]

theorem affineSpectralCoordinate0_hasDerivAt (lam t : Real)
    (hDen : Not (1 + t * lam = 0)) :
    HasDerivAt (affineSpectralCoordinate0 lam) (affineSpectralCoordinate1 lam t) t := by
  have h := ((affineDenominator_hasDerivAt lam t).log hDen).const_mul (-(1 / 2 : Real))
  unfold affineSpectralCoordinate0 affineSpectralCoordinate1
  convert h using 1
  ring

theorem affineSpectralCoordinate1_hasDerivAt (lam t : Real)
    (hDen : Not (1 + t * lam = 0)) :
    HasDerivAt (affineSpectralCoordinate1 lam) (affineSpectralCoordinate2 lam t) t := by
  have h := (hasDerivAt_const t (-(1 / 2 : Real) * lam)).div
    (affineDenominator_hasDerivAt lam t) hDen
  unfold affineSpectralCoordinate1 affineSpectralCoordinate2
  convert h using 1
  all_goals first
  | (funext x; rfl)
  | (field_simp [hDen] <;> ring)

theorem affineSpectralFactors_hasDerivAt (S : Finset Iota) (lam : Iota -> Real)
    (t : Real) (hDen : forall i, Membership.mem S i -> Not (1 + t * lam i = 0)) :
    HasDerivAt (affineSpectralFactors S lam)
      (affineSpectralFactors S lam t *
        Finset.sum S (fun i => affineSpectralCoordinate1 (lam i) t)) t := by
  exact (HasDerivAt.fun_sum
    (fun i hi => affineSpectralCoordinate0_hasDerivAt (lam i) t (hDen i hi))).exp

theorem affineSpectralFactors_second_derivative (S : Finset Iota) (lam : Iota -> Real)
    (t : Real) (hDen : forall i, Membership.mem S i -> Not (1 + t * lam i = 0)) :
    deriv (deriv (affineSpectralFactors S lam)) t =
      affineSpectralFactors S lam t *
        ((Finset.sum S (fun i => affineSpectralCoordinate1 (lam i) t)) ^ 2 +
          Finset.sum S (fun i => affineSpectralCoordinate2 (lam i) t)) := by
  have hEvent : Filter.Eventually
      (fun y : Real => forall i, Membership.mem S i -> Not (1 + y * lam i = 0)) (nhds t) := by
    apply (Filter.eventually_all_finset S).mpr
    intro i hi
    exact (continuous_const.add (continuous_id.mul continuous_const)).continuousAt.eventually_ne
      (hDen i hi)
  have hEq : Filter.EventuallyEq (nhds t) (deriv (affineSpectralFactors S lam))
      (fun y => affineSpectralFactors S lam y *
        Finset.sum S (fun i => affineSpectralCoordinate1 (lam i) y)) :=
    hEvent.mono (fun y hy => (affineSpectralFactors_hasDerivAt S lam y hy).deriv)
  have hSum : HasDerivAt
      (fun y : Real => Finset.sum S (fun i => affineSpectralCoordinate1 (lam i) y))
      (Finset.sum S (fun i => affineSpectralCoordinate2 (lam i) t)) t :=
    HasDerivAt.fun_sum (fun i hi => affineSpectralCoordinate1_hasDerivAt (lam i) t (hDen i hi))
  have hJet : HasDerivAt
      (fun y => affineSpectralFactors S lam y *
        Finset.sum S (fun i => affineSpectralCoordinate1 (lam i) y))
      (affineSpectralFactors S lam t *
        ((Finset.sum S (fun i => affineSpectralCoordinate1 (lam i) t)) ^ 2 +
          Finset.sum S (fun i => affineSpectralCoordinate2 (lam i) t))) t := by
    convert (affineSpectralFactors_hasDerivAt S lam t hDen).mul hSum using 1 <;> ring
  exact (Filter.EventuallyEq.deriv_eq hEq).trans hJet.deriv

end PrimeFactorOscillations
