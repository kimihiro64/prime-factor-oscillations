/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.DirichletCompensatedProbe

/-!
# Power compensated Dirichlet probes

Every positive power gives a pole-preserving probe on the positive
half-plane above Re(s)=1-d/8, using the installed seven-eighths reference.
Quadratic, cubic and quartic compensation have distinct data costs.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.DirichletCompensatedProbe

def powerMap (d : Real) (s : Complex) : Complex :=
  (s + (d : Complex) - 1) / (d : Complex)

def powerProbe {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    (G : Complex -> Complex) (d : Real) (s : Complex) : Complex :=
  DirichletZeroReadout.readout chi G s -
    s / (s + (d : Complex) - 1) *
      DirichletZeroReadout.readout chi G (powerMap d s)

theorem powerMap_real_identity (d : Real) (hd : 0 < d) (s : Complex) :
    (powerMap d s).re * d = s.re + d - 1 := by
  have hdC : Not ((d : Complex) = 0) := by exact_mod_cast hd.ne'
  have h : powerMap d s * (d : Complex) = s + (d : Complex) - 1 := by
    dsimp [powerMap]
    field_simp [hdC]
  have hRe := congrArg Complex.re h
  simpa using hRe

theorem powerProbe_order_iff_zero {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {s : Complex | 0 < s.re})
    (d : Real) (hd : 0 < d) (rho : Complex)
    (hr : 0 < rho.re) (hBand : 1 - d / 8 < rho.re)
    (hOne : Not (rho = 1)) :
    meromorphicOrderAt (powerProbe chi G d) rho = -1 <->
      DirichletCharacter.LFunction chi rho = 0 := by
  have hdC : Not ((d : Complex) = 0) := by exact_mod_cast hd.ne'
  have hRel := powerMap_real_identity d hd rho
  have hTr : (7 / 8 : Real) < (powerMap d rho).re := by nlinarith
  have hTOne : Not (powerMap d rho = 1) := by
    intro he
    have heq := (div_eq_iff hdC).mp he
    apply hOne
    change rho + (d : Complex) - 1 = 1 * (d : Complex) at heq
    linear_combination heq
  have hL := (DirichletZeroReadout.analyticOnNhd_LFunction_off_one chi)
    (powerMap d rho) (Set.mem_compl_singleton_iff.mpr hTOne)
  have hNZ := QRH.dirichletL_ne_zero q chi (powerMap d rho) hTr
    (fun h => hTOne h.2)
  have hRead : AnalyticAt Complex (DirichletZeroReadout.readout chi G) (powerMap d rho) := by
    change AnalyticAt Complex
      (fun s => -logDeriv (DirichletCharacter.LFunction chi) s + G s) (powerMap d rho)
    simp only [logDeriv_apply]
    exact (hL.deriv.div hL hNZ).neg.add
      (hG _ (by change 0 < (powerMap d rho).re; linarith))
  have hMap : AnalyticAt Complex (powerMap d) rho := by
    change AnalyticAt Complex
      (fun s : Complex => (s + (d : Complex) - 1) / (d : Complex)) rho
    fun_prop
  have hDen : Not (rho + (d : Complex) - 1 = 0) := by
    intro he
    have hRe := congrArg Complex.re he
    have heq : rho.re + d - 1 = 0 := by simpa using hRe
    nlinarith
  have hScalar : AnalyticAt Complex
      (fun s : Complex => s / (s + (d : Complex) - 1)) rho :=
    analyticAt_id.div ((analyticAt_id.add analyticAt_const).sub analyticAt_const) hDen
  have hRef := hScalar.mul (hRead.comp hMap)
  let H : Complex -> Complex := fun s => G s -
    s / (s + (d : Complex) - 1) *
      DirichletZeroReadout.readout chi G (powerMap d s)
  have hH : AnalyticAt Complex H rho := (hG rho hr).sub hRef
  have heq : powerProbe chi G d = DirichletZeroReadout.readout chi H := by
    funext s
    dsimp [powerProbe, H, DirichletZeroReadout.readout]
    ring
  rw [heq]
  exact DirichletZeroReadout.readout_order_iff_zero chi rho hOne H hH

end PrimeFactorOscillations.DirichletCompensatedProbe
