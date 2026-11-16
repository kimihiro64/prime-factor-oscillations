/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import VendorPrimeNumberTheoremAnd.Mertens

/-! # The cached classical Mertens product input for coprime density

This records an ASCII interface to the existing asymptotic and derives
a positive lower product and reciprocal upper bound. Its consumer is
the uniform totient-density hypothesis in the coprime-circle count.
No dependency is rebuilt and no RH hypothesis is added.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianMertensProduct (x : Real) : Real :=
  ((Finset.Ioc 0 (Nat.floor x)).filter Nat.Prime).prod (fun p => 1 - 1 / (p : Real))

-- Fixed ASCII spelling of the cached provider's E-subscript-three identifier.
-- This expands to one known theorem identifier, without proof search.
local macro "hamiltonianCachedMertensProductLimit" : term => do
  let errName := Lean.Name.str (Lean.Name.str Lean.Name.anonymous "Mertens")
    ("E" ++ String.singleton (Char.ofNat 8323))
  pure (Lean.TSyntax.mk (Lean.mkIdent (Lean.Name.str errName "bound''")))

theorem hamiltonian_mertens_product_equivalent :
    Asymptotics.IsEquivalent Filter.atTop hamiltonianMertensProduct
      (fun x : Real => Real.exp (-Real.eulerMascheroniConstant) / Real.log x) := by
  unfold hamiltonianMertensProduct
  exact hamiltonianCachedMertensProductLimit

theorem hamiltonian_mertens_product_reciprocal_bound :
    exists C : Real, 0 < C /\ exists X : Real, 2 <= X /\
      forall x : Real, X <= x ->
        0 < hamiltonianMertensProduct x /\
          1 / hamiltonianMertensProduct x <= C * Real.log x := by
  let a := Real.exp (-Real.eulerMascheroniConstant)
  have ha : 0 < a := Real.exp_pos _
  have hDiff : Asymptotics.IsLittleO Filter.atTop
      (fun x : Real => hamiltonianMertensProduct x - a / Real.log x)
      (fun x : Real => a / Real.log x) :=
    hamiltonian_mertens_product_equivalent
  have hBound := hDiff.bound (by norm_num : (0 : Real) < 1 / 2)
  choose Y hY using Filter.eventually_atTop.mp hBound
  refine Exists.intro (2 / a) (And.intro (div_pos (by norm_num) ha)
    (Exists.intro (max 2 Y) (And.intro (le_max_left _ _) ?_)))
  intro x hx
  have hx2 : (2 : Real) <= x := (le_max_left _ _).trans hx
  have hxY : Y <= x := (le_max_right _ _).trans hx
  have hLog : 0 < Real.log x := Real.log_pos (by linarith only [hx2])
  have hMain : 0 < a / Real.log x := div_pos ha hLog
  have hError := hY x hxY
  simp only [Real.norm_eq_abs, abs_of_pos hMain] at hError
  have hProduct : (a / Real.log x) / 2 <= hamiltonianMertensProduct x := by
    have h := (abs_le.mp hError).1
    linarith only [h]
  have hPositive : 0 < hamiltonianMertensProduct x :=
    (div_pos hMain (by norm_num)).trans_le hProduct
  refine And.intro hPositive ?_
  have hANe : Not (a = 0) := ne_of_gt ha
  have hLogNe : Not (Real.log x = 0) := ne_of_gt hLog
  have hCancel : (a / Real.log x) * Real.log x = a := by field_simp
  have hScaled := mul_le_mul_of_nonneg_right hProduct hLog.le
  have hSupply : a / 2 <= Real.log x * hamiltonianMertensProduct x := by
    nlinarith only [hScaled, hCancel]
  apply (mul_le_mul_iff_of_pos_right hPositive).mp
  have hPNe : Not (hamiltonianMertensProduct x = 0) := ne_of_gt hPositive
  have hOne : (1 / hamiltonianMertensProduct x) * hamiltonianMertensProduct x = 1 := by
    field_simp
  rw [hOne]
  have h := mul_le_mul_of_nonneg_left hSupply (div_nonneg (by norm_num : (0 : Real) <= 2) ha.le)
  have hTwo : (2 / a) * (a / 2) = (1 : Real) := by field_simp
  rw [hTwo] at h
  nlinarith only [h]

end PrimeFactorOscillations
