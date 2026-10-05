/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.Linarith
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannXiDivisorZeros

/-!
# Fractional inverse moments of the xi divisor

Direct source adaptation of PrimeNumberTheoremAnd/IEANTN/RobinXiZeroSummability
at f6147e7572ab3abe5428101bc0b13627bcb005df, blob
766f702ff1939c68f2eaaf57b4ca8ab5e64995f4. The source proof uses only the
already cached xi-divisor growth theorem. The case a=3/2 is required for the
weighted Mellin interchange; inverse-square summability alone does not suffice.
-/

set_option autoImplicit false
set_option Elab.async false

open Complex

theorem summable_riemannXiDivisorZero_norm_inv_rpow
    {a : Real} (ha : 1 < a) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      (Inv.inv (norm (riemannXiDivisorZeroValue p))) ^ a) := by
  have hMid : (1 : Real) < (1 + a) / 2 := by linarith
  have hMidNonneg : (0 : Real) <= (1 + a) / 2 := by linarith
  have hMidLt : (1 + a) / 2 < a := by linarith
  run_tac
    let declaration := Lean.Name.str
      (Lean.Name.str (Lean.Name.mkSimple "Complex") "Hadamard")
      ("summable_norm_inv_rpow_divisorZeroIndex" ++
        String.singleton (Char.ofNat 8320) ++ "_of_growth")
    let mid := Lean.mkIdent (Lean.Name.mkSimple "hMid")
    let midNonneg := Lean.mkIdent (Lean.Name.mkSimple "hMidNonneg")
    let midLt := Lean.mkIdent (Lean.Name.mkSimple "hMidLt")
    let proofSyntax <- `(tactic|
      exact $(Lean.mkIdent declaration)
        $midNonneg $midLt differentiable_riemannXi riemannXi_nontrivial
        (riemannXi_entireOfOrderAtMost_one.exists_log_growth $mid $midNonneg))
    Lean.Elab.Tactic.evalTactic proofSyntax
