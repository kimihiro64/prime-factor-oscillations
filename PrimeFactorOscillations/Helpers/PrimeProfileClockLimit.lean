/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Helpers.PrimeProfileFactorization
import VendorPrimeNumberTheoremAnd.Mertens

/-!
# The actual finite prime-product clock

Exact logarithmic identities reduce the clock error to the released Mertens
third-theorem error. Its existing cached proof gives convergence to zero.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

theorem primeProfile_logFactor_eq_neg_log (p : Nat) (hp : Nat.Prime p) :
    Real.log (1 + primeProfileWeight p) = -Real.log (1 - 1 / (p : Real)) := by
  have hpR : (1 : Real) < p := by exact_mod_cast hp.one_lt
  have hp0 : Not ((p : Real) = 0) := by linarith
  have hp1 : Not ((p : Real) - 1 = 0) := by linarith
  have hbase : Not (1 - 1 / (p : Real) = 0) := by
    have hlt : (1 : Real) / p < 1 := (div_lt_one (by linarith)).mpr hpR
    linarith
  have hfactor : 1 + primeProfileWeight p = (1 - 1 / (p : Real)) ^ (-1 : Int) := by
    rw [primeProfileWeight, Nat.cast_sub hp.one_lt.le, Nat.cast_one, zpow_neg_one]
    field_simp
    ring
  rw [hfactor, zpow_neg_one, Real.log_inv]

theorem primePrefixProfile_logSum_eq_neg_logProduct (N : Nat) :
    (primeProfilePrefixSet N).sum
        (fun p => Real.log (1 + primeProfileWeight (p : Nat))) =
      -((Finset.Ioc 0 N).filter Nat.Prime).sum
        (fun p => Real.log (1 - 1 / (p : Real))) := by
  have hsets : (Finset.range (N + 1)).filter Nat.Prime =
      (Finset.Ioc 0 N).filter Nat.Prime := by
    apply Finset.ext
    intro p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    constructor
    . intro hp
      exact And.intro (And.intro hp.2.pos (Nat.lt_succ_iff.mp hp.1)) hp.2
    . intro hp
      exact And.intro (Nat.lt_succ_iff.mpr hp.1.2) hp.2
  change ((Finset.range (N + 1)).subtype Nat.Prime).sum
      (fun p : Subtype Nat.Prime => Real.log (1 + primeProfileWeight p.val)) = _
  rw [Finset.sum_subtype_eq_sum_filter
    (fun p : Nat => Real.log (1 + primeProfileWeight p)), hsets,
    <- Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  exact primeProfile_logFactor_eq_neg_log p (Finset.mem_filter.mp hp).2

/-- ASCII statement of the already released Mertens third-theorem error.
The explicit name construction accesses the imported subscript-three identifier;
no dependency is rebuilt or new analytic assumption added. -/
private theorem mertens_logProduct_error_isLittleO :
    Asymptotics.IsLittleO Filter.atTop
      (fun x : Real =>
        ((Finset.Ioc 0 (Nat.floor x)).filter Nat.Prime).sum
            (fun p => Real.log (1 - 1 / (p : Real))) +
          Real.log (Real.log x) + Real.eulerMascheroniConstant)
      (fun _ : Real => (1 : Real)) := by
  run_tac
    let subscriptThree := String.singleton (Char.ofNat 8323)
    let declaration := Lean.Name.str
      (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "Mertens")
        ("E" ++ subscriptThree)) "bound'"
    let proofSyntax <- `(tactic| exact $(Lean.mkIdent declaration))
    Lean.Elab.Tactic.evalTactic proofSyntax

theorem tendsto_primePrefixProfile_logSum_error :
    Filter.Tendsto
      (fun N : Nat => (primeProfilePrefixSet N).sum
          (fun p => Real.log (1 + primeProfileWeight (p : Nat))) -
        Real.eulerMascheroniConstant - Real.log (Real.log (N : Real)))
      Filter.atTop (nhds (0 : Real)) := by
  have hreal : Filter.Tendsto
      (fun x : Real =>
        ((Finset.Ioc 0 (Nat.floor x)).filter Nat.Prime).sum
            (fun p => Real.log (1 - 1 / (p : Real))) +
          Real.log (Real.log x) + Real.eulerMascheroniConstant)
      Filter.atTop (nhds (0 : Real)) :=
    (Asymptotics.isLittleO_one_iff Real).mp mertens_logProduct_error_isLittleO
  have hnat := (hreal.comp tendsto_natCast_atTop_atTop).neg
  have heq :
      (fun N : Nat => (primeProfilePrefixSet N).sum
          (fun p => Real.log (1 + primeProfileWeight (p : Nat))) -
        Real.eulerMascheroniConstant - Real.log (Real.log (N : Real))) =
      (fun N : Nat =>
        -(((Finset.Ioc 0 (Nat.floor (N : Real))).filter Nat.Prime).sum
            (fun p => Real.log (1 - 1 / (p : Real))) +
          Real.log (Real.log (N : Real)) + Real.eulerMascheroniConstant)) := by
    funext N
    rw [primePrefixProfile_logSum_eq_neg_logProduct, Nat.floor_natCast]
    ring
  rw [heq]
  simpa only [Function.comp_def, neg_zero] using hnat

end PrimeFactorOscillations

