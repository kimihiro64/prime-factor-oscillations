/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Helpers.XiZetaMultiplicity

/-! # Actual analytic multiplicities under same-height zeta reflection -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations

open scoped ComplexConjugate

theorem deriv_conj_equivariant (f : Complex -> Complex)
    (hf : forall z : Complex, f (conj z) = conj (f z)) (z : Complex) :
    deriv f (conj z) = conj (deriv f z) := by
  have hFunction : (Function.comp conj (Function.comp f conj)) = f := by
    funext w
    simp [Function.comp_def, hf]
  have h := congrArg (fun g : Complex -> Complex => g (conj z)) (deriv_conj_conj (f := f))
  rw [hFunction] at h
  simpa [Function.comp_def] using h

theorem iteratedDeriv_conj_equivariant (f : Complex -> Complex)
    (hf : forall z : Complex, f (conj z) = conj (f z)) (n : Nat) (z : Complex) :
    iteratedDeriv n f (conj z) = conj (iteratedDeriv n f z) := by
  induction n generalizing f z with
  | zero => simpa only [iteratedDeriv_zero] using hf z
  | succ n ih =>
      simpa only [iteratedDeriv_succ'] using
        ih (deriv f) (deriv_conj_equivariant f hf) z

theorem analyticOrderNatAt_conj_equivariant (f : Complex -> Complex) (z : Complex)
    (hf : forall w : Complex, f (conj w) = conj (f w))
    (ha : AnalyticAt Complex f z) (hc : AnalyticAt Complex f (conj z))
    (hFinite : Not (analyticOrderAt f z = Top.top)) :
    analyticOrderNatAt f (conj z) = analyticOrderNatAt f z := by
  let n := analyticOrderNatAt f z
  have hn : analyticOrderAt f z = (n : ENat) := (Nat.cast_analyticOrderNatAt hFinite).symm
  have hDerivs := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero ha).mp hn
  have hConjDerivs : And (forall k : Nat, k < n -> iteratedDeriv k f (conj z) = 0)
      (Not (iteratedDeriv n f (conj z) = 0)) := by
    constructor
    case left =>
      intro k hk
      rw [iteratedDeriv_conj_equivariant f hf k z, hDerivs.1 k hk]
      simp
    case right =>
      intro hZero
      apply hDerivs.2
      rw [iteratedDeriv_conj_equivariant f hf n z] at hZero
      have h := congrArg (fun q : Complex => conj q) hZero
      simpa using h
  have hnConj := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hc).mpr hConjDerivs
  change (analyticOrderAt f (conj z)).toNat = (analyticOrderAt f z).toNat
  rw [hnConj, hn]

theorem zetaOrder_conj (z : Complex) (hz : And (0 < z.re) (z.re < 1)) :
    analyticOrderNatAt riemannZeta (conj z) = analyticOrderNatAt riemannZeta z := by
  have h1 : Not (z = 1) := by
    intro h
    have hh := hz.2
    rw [h] at hh
    norm_num at hh
  have hc1 : Not (conj z = 1) := by
    intro h
    have hr := congrArg Complex.re h
    have hh : z.re = 1 := by simpa using hr
    linarith [hz.2]
  have hFinite : Not (analyticOrderAt riemannZeta z = Top.top) := by
    rw [<- analyticOrderAt_xi_eq_zeta hz.1 h1]
    exact analyticOrderAt_xi_ne_top z
  exact analyticOrderNatAt_conj_equivariant riemannZeta z riemannZeta_conj
    (analyticOn_riemannZeta z h1) (analyticOn_riemannZeta (conj z) hc1) hFinite

def zetaHorizontalReflection (z : Complex) : Complex := 1 - conj z

theorem zetaHorizontalReflection_re (z : Complex) :
    (zetaHorizontalReflection z).re = 1 - z.re := by
  simp [zetaHorizontalReflection]

theorem zetaHorizontalReflection_im (z : Complex) :
    (zetaHorizontalReflection z).im = z.im := by
  simp [zetaHorizontalReflection]

theorem zetaHorizontalReflection_involutive : Function.Involutive zetaHorizontalReflection := by
  intro z
  apply Complex.ext <;> simp [zetaHorizontalReflection]

theorem zetaHorizontalReflection_injective : Function.Injective zetaHorizontalReflection := by
  intro a b h
  have hh := congrArg zetaHorizontalReflection h
  rw [zetaHorizontalReflection_involutive a, zetaHorizontalReflection_involutive b] at hh
  exact hh

theorem zetaHorizontalReflection_critical (z : Complex)
    (hz : And (0 < z.re) (z.re < 1)) :
    And (0 < (zetaHorizontalReflection z).re) ((zetaHorizontalReflection z).re < 1) := by
  constructor
  case left => rw [zetaHorizontalReflection_re]; linarith [hz.2]
  case right => rw [zetaHorizontalReflection_re]; linarith [hz.1]

theorem zetaOrder_reflection (z : Complex) (hz : And (0 < z.re) (z.re < 1)) :
    analyticOrderNatAt riemannZeta (zetaHorizontalReflection z) = analyticOrderNatAt riemannZeta z := by
  have hr := zetaHorizontalReflection_critical z hz
  have hr1 : Not (zetaHorizontalReflection z = 1) := by
    intro h
    have hh := hr.2
    rw [h] at hh
    norm_num at hh
  have hc : 0 < (conj z).re := by simpa using hz.1
  have hc1 : Not (conj z = 1) := by
    intro h
    have hh := congrArg Complex.re h
    have hh1 : z.re = 1 := by simpa using hh
    linarith [hz.2]
  calc
    _ = xiZeroMultiplicity (zetaHorizontalReflection z) :=
      (xiZeroMultiplicity_eq_zetaOrder hr.1 hr1).symm
    _ = xiZeroMultiplicity (conj z) := by
      unfold zetaHorizontalReflection
      exact xiZeroMultiplicity_one_sub (conj z)
    _ = analyticOrderNatAt riemannZeta (conj z) := xiZeroMultiplicity_eq_zetaOrder hc hc1
    _ = _ := zetaOrder_conj z hz

theorem zetaHorizontalCoord_reflection (z : Complex) :
    (zetaHorizontalReflection z).re - 1 / 2 = -(z.re - 1 / 2) := by
  rw [zetaHorizontalReflection_re]
  ring

end PrimeFactorOscillations
