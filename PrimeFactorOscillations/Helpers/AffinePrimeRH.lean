/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.AffineReciprocalSmooth
import PrimeFactorOscillations.Helpers.ReciprocalSmoothRH

/-!
# RH criteria for the actual affine prime-pair local laws

The dimension is the number of distinct affine factors. Coefficient,
determinant, collision, excluded, and forced-prime exceptions remain in the
exact profile constant. The statement assumes no bounded-gap conjecture.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.AffineSumFamily

noncomputable def rhReferenceConstant (F : AffineSumFamily) (z : Real) : Real :=
  F.reciprocalSmoothLaw.quadraticPrimeLaw.referenceConstant z

theorem rhReferenceConstant_pos (F : AffineSumFamily) (z : Real) :
    0 < F.rhReferenceConstant z :=
  F.reciprocalSmoothLaw.quadraticPrimeLaw.referenceConstant_pos z

theorem riemannHypothesis_iff_eventually_local_prime_product
    (F : AffineSumFamily) (z : Real) (hz : 0 < z) :
    RiemannHypothesis <-> Filter.Eventually (fun N : Nat =>
      F.rhReferenceConstant z *
        (Real.log (Chebyshev.theta (N : Real))) ^ ((F.arity : Real) * z) <
      (primeProfilePrefixSet N).prod (fun p =>
        1 + F.localProbability (p : Nat) / (1 - F.localProbability (p : Nat)) * z))
      Filter.atTop := by
  exact F.reciprocalSmoothLaw.riemannHypothesis_iff_eventually_prime_product z hz

end PrimeFactorOscillations.AffineSumFamily
