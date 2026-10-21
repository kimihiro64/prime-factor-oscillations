/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassDecoderFiniteSupply

/-!
# The full signed half-integer supply for the actual Euler profile

Finite products have their exact prime-label parity and a uniform positive
lower bound. The already proved Euler-product limit retains that bound,
the same parity and reality at every half-integer point.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open Filter
open PrimeFactorOscillations.PrimeClassDecoder

theorem finite_halfIntegerProduct_complex_eq
    (P : Set Nat) (Y n : Nat) :
    (((primeClassPrefix P Y).prod
      (fun p => ((p : Real) - (n : Real) - 3 / 2) / (p : Real)) : Real) : Complex) =
        ((finiteReferencePolynomial (primeClassPrefix P Y)).map Complex.ofRealHom).eval
          (((-(n : Real) - 1 / 2 : Real) : Complex)) := by
  classical
  rw [finiteReference_euler_eval]
  change Complex.ofRealHom ((primeClassPrefix P Y).prod
    (fun p => ((p : Real) - (n : Real) - 3 / 2) / (p : Real))) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro p hp
  have hactive := (Finset.mem_filter.mp hp).2
  exact (classEulerFactor_halfInteger P p n hactive.1 hactive.2).symm

theorem classEulerProfile_halfInteger_signed_lower
    (P : Set Nat) (sigma : Real) (hs0 : 0 <= sigma) (hs1 : sigma <= 1)
    (hsum : Summable (classPowerWeight P sigma)) (R n : Nat) (hR : 1 <= R) (hn : n <= R) :
    And ((classEulerProfile P (((-(n : Real) - 1 / 2 : Real) : Complex))).im = 0)
      (Real.exp (-((6 : Real) ^ sigma * tsum (classPowerWeight P sigma) * (R : Real) ^ sigma *
        Real.log (12 * (R : Real))) - 5 * tsum (classPowerWeight P sigma) * (R : Real) ^ sigma) <=
          (-1 : Real) ^ (primeClassPrefix P (n + 1)).card *
            (classEulerProfile P (((-(n : Real) - 1 / 2 : Real) : Complex))).re) := by
  let w : Complex := (((-(n : Real) - 1 / 2 : Real) : Complex))
  let f := fun Y : Nat => (primeClassPrefix P Y).prod
    (fun p => ((p : Real) - (n : Real) - 3 / 2) / (p : Real))
  have hlimit := finiteReference_euler_eval_tendsto P
    (classPowerWeight_one_summable P sigma hs1 hsum) w
  have heq : (fun Y : Nat =>
      ((finiteReferencePolynomial (primeClassPrefix P Y)).map Complex.ofRealHom).eval w) =
      (fun Y : Nat => (f Y : Complex)) := by
    funext Y
    exact (finite_halfIntegerProduct_complex_eq P Y n).symm
  rw [heq] at hlimit
  have hre : Tendsto f atTop (nhds (classEulerProfile P w).re) := by
    have h := (Complex.continuous_re.tendsto (classEulerProfile P w)).comp hlimit
    simpa only [Function.comp_def, Complex.ofReal_re] using h
  have him : (classEulerProfile P w).im = 0 := by
    have h := (Complex.continuous_im.tendsto (classEulerProfile P w)).comp hlimit
    have hzero : Tendsto (fun Y : Nat => ((f Y : Complex)).im) atTop (nhds 0) := by
      simp only [Complex.ofReal_im]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique h hzero
  refine And.intro him ?_
  have hsign := hre.const_mul ((-1 : Real) ^ (primeClassPrefix P (n + 1)).card)
  apply ge_of_tendsto hsign
  filter_upwards [eventually_ge_atTop (4 * R + 2)] with Y hY
  exact finite_primeClass_halfInteger_signed_lower P sigma hs0 hs1 hsum R n Y hR hn hY

end PrimeFactorOscillations.PrimeClassSampling
