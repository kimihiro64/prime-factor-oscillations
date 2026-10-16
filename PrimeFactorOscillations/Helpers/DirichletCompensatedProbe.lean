/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.FunProp
import PrimeFactorOscillations.Helpers.DirichletZeroReadout
import PrimeFactorOscillations.Helpers.QRHSevenEighths

/-!
# Quartic compensated Dirichlet probe

The seven-eighths reference is analytic throughout the RH half-plane after
quartic rescaling. Subtracting it preserves every zero pole away from one.
This proves pole detection, not a stronger zero-free region.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.DirichletCompensatedProbe

def quarticMap (s : Complex) : Complex := (s + 3) / 4

def quarticProbe {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    (G : Complex -> Complex) (s : Complex) : Complex :=
  DirichletZeroReadout.readout chi G s -
    s / (s + 3) * DirichletZeroReadout.readout chi G (quarticMap s)

theorem quarticMap_re (s : Complex) :
    (quarticMap s).re = (s.re + 3) / 4 := by
  simp [quarticMap]

theorem analyticAt_reference {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {s : Complex | 0 < s.re})
    (rho : Complex) (hr : (1 / 2 : Real) < rho.re) (hOne : Not (rho = 1)) :
    AnalyticAt Complex
      (fun s => s / (s + 3) * DirichletZeroReadout.readout chi G (quarticMap s)) rho := by
  have hTr : (7 / 8 : Real) < (quarticMap rho).re := by
    rw [quarticMap_re]
    linarith
  have hTOne : Not (quarticMap rho = 1) := by
    intro he
    apply hOne
    dsimp [quarticMap] at he
    linear_combination 4 * he
  have hL := (DirichletZeroReadout.analyticOnNhd_LFunction_off_one chi)
    (quarticMap rho) (Set.mem_compl_singleton_iff.mpr hTOne)
  have hNZ : Not (DirichletCharacter.LFunction chi (quarticMap rho) = 0) :=
    QRH.dirichletL_ne_zero q chi (quarticMap rho) hTr
      (fun h => hTOne h.2)
  have hRead : AnalyticAt Complex (DirichletZeroReadout.readout chi G) (quarticMap rho) := by
    change AnalyticAt Complex
      (fun s => -logDeriv (DirichletCharacter.LFunction chi) s + G s) (quarticMap rho)
    simp only [logDeriv_apply]
    exact (hL.deriv.div hL hNZ).neg.add
      (hG _ (by change 0 < (quarticMap rho).re; linarith))
  have hMap : AnalyticAt Complex quarticMap rho := by
    change AnalyticAt Complex (fun s : Complex => (s + 3) / 4) rho
    fun_prop
  have hDen : Not (rho + 3 = 0) := by
    intro he
    have := congrArg Complex.re he
    change rho.re + 3 = 0 at this
    linarith
  have hScalar : AnalyticAt Complex (fun s : Complex => s / (s + 3)) rho :=
    analyticAt_id.div (analyticAt_id.add analyticAt_const) hDen
  exact hScalar.mul (hRead.comp hMap)

/-- Quartic compensation preserves every zero pole in the RH half-plane.
The reference is regular there by the installed unconditional seven-eighths theorem. -/
theorem quarticProbe_order_iff_zero {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {s : Complex | 0 < s.re})
    (rho : Complex) (hr : (1 / 2 : Real) < rho.re) (hOne : Not (rho = 1)) :
    meromorphicOrderAt (quarticProbe chi G) rho = -1 <->
      DirichletCharacter.LFunction chi rho = 0 := by
  have hRef := analyticAt_reference chi G hG rho hr hOne
  let H : Complex -> Complex := fun s => G s -
    s / (s + 3) * DirichletZeroReadout.readout chi G (quarticMap s)
  have hH : AnalyticAt Complex H rho :=
    (hG rho (by change 0 < rho.re; linarith)).sub hRef
  have heq : quarticProbe chi G = DirichletZeroReadout.readout chi H := by
    funext s
    dsimp [quarticProbe, H, DirichletZeroReadout.readout]
    ring
  rw [heq]
  exact DirichletZeroReadout.readout_order_iff_zero chi rho hOne H hH

end PrimeFactorOscillations.DirichletCompensatedProbe
