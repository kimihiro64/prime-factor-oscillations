/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeProfileRootShift
import PrimeFactorOscillations.Helpers.ThetaEndpointLogCount

/-!
# Sharp double-logarithm normalization of the reference capacity

The actual strict theta endpoint count is evaluated at the same locally
unique reference crossing. The formula is unconditional at every fixed
positive level, with its inverse-rank error and log positivity explicit.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

theorem exists_primeProfile_reference_loglog_capacity (s : Real) (hs : 0 < s) :
    exists (A C : Real) (r0 : Nat), 0 < A /\ 0 <= C /\ 0 < r0 /\
      forall r : Nat, r0 <= r -> exists u : Real,
        Set.Ioo ((r : Real) / s - A) ((r : Real) / s + A) u /\
        Nat.factorialConvolution primeProfileRealCoefficient (r - 1) u /
          Nat.factorialConvolution primeProfileRealCoefficient r u = s /\
        abs (u - (r : Real) / s +
          deriv (fun x : Real => (primeProfile (x : Complex)).re) s /
            (primeProfile (s : Complex)).re) <= C / (r : Real) /\
        1 < (primeThetaEndpointCount
          (Real.exp (Real.exp (u - Real.eulerMascheroniConstant))) : Real) /\
        abs (Real.log (Real.log (primeThetaEndpointCount
          (Real.exp (Real.exp (u - Real.eulerMascheroniConstant))) : Real)) -
            ((r : Real) / s - Real.eulerMascheroniConstant -
              deriv (fun x : Real => (primeProfile (x : Complex)).re) s /
                (primeProfile (s : Complex)).re)) <= (C + 32 * s) / (r : Real) /\
        forall v : Real, Set.Icc ((r : Real) / s - A) ((r : Real) / s + A) v ->
          Nat.factorialConvolution primeProfileRealCoefficient (r - 1) v /
            Nat.factorialConvolution primeProfileRealCoefficient r v = s -> v = u := by
  choose A C rC hA hC hrC hcross using exists_primeProfile_reference_sharp_crossing s hs
  choose rB hrB hcount using exists_primeThetaEndpointCount_near_rank_loglog_error s A hs hA.le
  refine Exists.intro A (Exists.intro C (Exists.intro (max rC rB)
    (And.intro hA (And.intro hC (And.intro (hrC.trans_le (le_max_left _ _)) ?_)))))
  intro r hr
  have hrC' : rC <= r := (le_max_left _ _).trans hr
  have hrB' : rB <= r := (le_max_right _ _).trans hr
  choose u hu hroot hshift hunique using hcross r hrC'
  have hnear : abs (u - (r : Real) / s) <= A := by
    apply abs_le.mpr
    constructor <;> linarith [hu.1, hu.2]
  have hb := hcount r hrB' u hnear
  let center := (r : Real) / s - Real.eulerMascheroniConstant -
    deriv (fun x : Real => (primeProfile (x : Complex)).re) s /
      (primeProfile (s : Complex)).re
  have hcenter : (u - Real.eulerMascheroniConstant) - center =
      u - (r : Real) / s +
        deriv (fun x : Real => (primeProfile (x : Complex)).re) s /
          (primeProfile (s : Complex)).re := by dsimp [center]; ring
  have herror : abs (Real.log (Real.log (primeThetaEndpointCount
      (Real.exp (Real.exp (u - Real.eulerMascheroniConstant))) : Real)) - center) <=
        (C + 32 * s) / (r : Real) := by
    calc
      abs (Real.log (Real.log (primeThetaEndpointCount
          (Real.exp (Real.exp (u - Real.eulerMascheroniConstant))) : Real)) - center) <=
          abs (Real.log (Real.log (primeThetaEndpointCount
            (Real.exp (Real.exp (u - Real.eulerMascheroniConstant))) : Real)) -
              (u - Real.eulerMascheroniConstant)) +
            abs ((u - Real.eulerMascheroniConstant) - center) := abs_sub_le _ _ _
      _ <= 32 * s / (r : Real) + C / (r : Real) := by
        rw [hcenter]
        exact add_le_add hb.2 hshift
      _ = (C + 32 * s) / (r : Real) := by ring
  exact Exists.intro u (And.intro hu (And.intro hroot
    (And.intro hshift (And.intro hb.1 (And.intro herror hunique)))))

end PrimeFactorOscillations
