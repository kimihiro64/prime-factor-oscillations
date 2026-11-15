/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Ring

/-! # The derivative of a fully cleared parity observable

The equality supplied away from the parity root is extended by the
actual continuous limits. The derivative retains the numerator
compensation and the determinant derivative.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_cleared_root_derivative
    (f D V c : Real -> Real) (fPrime DPrime VPrime cPrime : Real)
    (hf : HasDerivAt f fPrime 0) (hD : HasDerivAt D DPrime 0)
    (hV : HasDerivAt V VPrime 0) (hc : HasDerivAt c cPrime 0)
    (hNear : Filter.Eventually (fun t : Real => Not (t = 0) ->
      f t = D t * (t / (1 + t) * V t - c t / (1 + t) ^ 2)) (nhds 0)) :
    fPrime = D 0 * (V 0 + 2 * c 0 - cPrime) - DPrime * c 0 := by
  let g := fun t : Real => D t * (t / (1 + t) * V t - c t / (1 + t) ^ 2)
  have hId : HasDerivAt id (1 : Real) 0 := hasDerivAt_id (0 : Real)
  have hDen : HasDerivAt (fun t : Real => 1 + t) (1 : Real) 0 := by
    simpa using! (hasDerivAt_const (0 : Real) (1 : Real)).add hId
  have hDen0 : Not ((1 : Real) + (0 : Real) = 0) := by norm_num
  have hDenSquare0 : Not (((1 : Real) + (0 : Real)) ^ 2 = 0) := by norm_num
  have hRaw := hD.mul
    (((hId.div hDen hDen0).mul hV).sub (hc.div (hDen.pow 2) hDenSquare0))
  have hg : HasDerivAt g
      (D 0 * (V 0 + 2 * c 0 - cPrime) - DPrime * c 0) 0 := by
    convert (by simpa only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.div_apply,
      Pi.pow_apply, id_eq, add_zero, mul_zero, zero_mul, zero_add, one_pow,
      div_one, one_mul, mul_one, zero_sub] using! hRaw) using 1 <;> (try funext t) <;>
      (try simp only [g, Pi.mul_apply, Pi.sub_apply, Pi.div_apply, Pi.pow_apply, id_eq]) <;> ring
  have hOn : Filter.EventuallyEq (nhdsWithin (0 : Real) (Set.Ioi 0)) f g := by
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hNear,
      self_mem_nhdsWithin] with t ht htPos
    exact ht (ne_of_gt htPos)
  have hfLim := hf.continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : nhdsWithin (0 : Real) (Set.Ioi 0) <= nhds 0)
  have hgLim := hg.continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : nhdsWithin (0 : Real) (Set.Ioi 0) <= nhds 0)
  have hValue : f 0 = g 0 := tendsto_nhds_unique hfLim (hgLim.congr' hOn.symm)
  have hEq : Filter.EventuallyEq (nhds (0 : Real)) f g := by
    filter_upwards [hNear] with t ht
    by_cases h : t = 0
    case pos => simpa only [h] using hValue
    case neg => exact ht h
  calc
    fPrime = deriv f 0 := hf.deriv.symm
    _ = deriv g 0 := hEq.deriv_eq
    _ = _ := hg.deriv

end PrimeFactorOscillations
