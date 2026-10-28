/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelNativeWindow

/-!
# Local logarithmic-derivative residues with arbitrary multiplicity

A local analytic factorization gives the exact multiplicity as the scaled
logarithmic-derivative limit. No simple-zero hypothesis is used. Applying
this to the full finite character packet and its retained principal signal
is a separate consumer, not a zero-exclusion estimate.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.CarmichaelWeightedResidue

theorem factor_logDeriv_limit (f g : Complex -> Complex) (rho : Complex) (n : Nat)
    (hg : AnalyticAt Complex g rho) (hg0 : Not (g rho = 0))
    (hfg : Filter.Eventually (fun z : Complex => f z = (z - rho) ^ n * g z) (nhds rho)) :
    Filter.Tendsto (fun z : Complex => (z - rho) * logDeriv f z)
      (nhdsWithin rho (Set.compl {rho})) (nhds (n : Complex)) := by
  have hLog := logDeriv_congr_nhds hfg
  have hDiff : Filter.Eventually (fun z => DifferentiableAt Complex g z) (nhds rho) :=
    hg.eventually_analyticAt.mono (fun _ hz => hz.differentiableAt)
  have hNe := hg.continuousAt.eventually_ne hg0
  have hLinear (z : Complex) :
      logDeriv (fun s : Complex => s - rho) z = 1 / (z - rho) := by
    have hd : HasDerivAt (fun s : Complex => s - rho) 1 z :=
      (hasDerivAt_id z).sub_const rho
    rw [logDeriv_apply, hd.deriv]
  have hRegular : AnalyticAt Complex (fun z => logDeriv g z) rho := by
    have hDer : AnalyticAt Complex (deriv g) rho := hg.deriv
    have hRat : AnalyticAt Complex (fun z => deriv g z / g z) rho := hDer.div hg hg0
    change AnalyticAt Complex (fun z => deriv g z / g z) rho
    exact hRat
  have hRight : Filter.Tendsto
      (fun z : Complex => (n : Complex) + (z - rho) * logDeriv g z)
      (nhdsWithin rho (Set.compl {rho})) (nhds (n : Complex)) := by
    have hc : ContinuousAt
        (fun z : Complex => (n : Complex) + (z - rho) * logDeriv g z) rho :=
      continuousAt_const.add ((continuousAt_id.sub continuousAt_const).mul hRegular.continuousAt)
    simpa only [sub_self, zero_mul, add_zero] using
      hc.tendsto.mono_left nhdsWithin_le_nhds
  have hEq : Filter.EventuallyEq (nhdsWithin rho (Set.compl {rho}))
      (fun z : Complex => (z - rho) * logDeriv f z)
      (fun z : Complex => (n : Complex) + (z - rho) * logDeriv g z) := by
    filter_upwards [hLog.filter_mono nhdsWithin_le_nhds,
      hDiff.filter_mono nhdsWithin_le_nhds,
      hNe.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hL hD hN hZ
    change Not (z = rho) at hZ
    have hz : Not (z = rho) := hZ
    have hz0 : Not (z - rho = 0) := sub_ne_zero.mpr hz
    have hId : DifferentiableAt Complex (fun s : Complex => s - rho) z :=
      differentiableAt_id.sub_const rho
    have hMul := logDeriv_fun_mul (f := fun s : Complex => (s - rho) ^ n) (g := g)
      z (pow_ne_zero n hz0) hN (hId.pow n) hD
    rw [hL, hMul, logDeriv_fun_pow hId n, hLinear]
    field_simp [hz0]
    <;> ring
  exact (Filter.tendsto_congr' hEq).mpr hRight

end PrimeFactorOscillations.CarmichaelWeightedResidue
