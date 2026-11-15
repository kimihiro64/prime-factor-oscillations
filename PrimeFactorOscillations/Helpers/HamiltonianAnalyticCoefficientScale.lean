/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianWickTaylorSeries

/-! # Local analytic coefficient scaling

All arguments use local analytic power series, without assuming a global
smooth extension across the singularities of the actual normalizer.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem wickTaylorSeries_coeff_of_hasFPowerSeriesAt
    (f : Complex -> Complex) (p : FormalMultilinearSeries Complex Complex Complex)
    (hp : HasFPowerSeriesAt f p 0) (k : Nat) :
    PowerSeries.coeff k (wickTaylorSeries f) = p k (fun _ => 1) := by
  let r := Classical.choose hp
  have hBall : HasFPowerSeriesOnBall f p 0 r := Classical.choose_spec hp
  have h := hBall.factorial_smul (1 : Complex) k
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
    Finset.prod_const_one, one_smul] at h
  simp only [nsmul_eq_mul] at h
  change (k.factorial : Complex) * p k (fun _ => 1) = iteratedDeriv k f 0 at h
  have hFac : Not ((k.factorial : Complex) = 0) := by
    exact_mod_cast Nat.factorial_ne_zero k
  rw [wickTaylorSeries_coeff, <- h]
  field_simp

theorem wickTaylorSeries_coeff_comp_mul
    (f : Complex -> Complex) (hf : AnalyticAt Complex f 0) (c : Complex) (k : Nat) :
    PowerSeries.coeff k (wickTaylorSeries (fun z => f (c * z))) =
      c ^ k * PowerSeries.coeff k (wickTaylorSeries f) := by
  let p := Classical.choose hf
  have hp : HasFPowerSeriesAt f p 0 := Classical.choose_spec hf
  let u : ContinuousLinearMap (RingHom.id Complex) Complex Complex :=
    HSMul.hSMul c (ContinuousLinearMap.id Complex Complex)
  have hAt : HasFPowerSeriesAt f p (u 0) := by
    simpa only [map_zero] using hp
  have hComp := hAt.compContinuousLinearMap (u := u) (x := 0)
  have hDiagonal : (p.compContinuousLinearMap u) k (fun _ => 1) =
      c ^ k * p k (fun _ => 1) := by
    change p k (fun _ => c * 1) = _
    have h := (p k).map_smul_univ (fun _ : Fin k => c) (fun _ => (1 : Complex))
    simpa only [smul_eq_mul, mul_one, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] using h
  calc
    _ = (p.compContinuousLinearMap u) k (fun _ => 1) :=
      wickTaylorSeries_coeff_of_hasFPowerSeriesAt (fun z => f (c * z))
        (p.compContinuousLinearMap u) hComp k
    _ = c ^ k * p k (fun _ => 1) := hDiagonal
    _ = _ := by rw [wickTaylorSeries_coeff_of_hasFPowerSeriesAt f p hp k]

theorem wickTaylorSeries_hasSum
    (f : Complex -> Complex) (p : FormalMultilinearSeries Complex Complex Complex)
    (R : NNReal) (hSeries : HasFPowerSeriesOnBall f p 0 R) (z : Complex)
    (hz : Membership.mem (Metric.eball (0 : Complex) (R : ENNReal)) z) :
    HasSum (fun k => z ^ k * PowerSeries.coeff k (wickTaylorSeries f)) (f z) := by
  have hp : HasFPowerSeriesAt f p 0 := Exists.intro (R : ENNReal) hSeries
  have hDiagonal : forall k, p k (fun _ => z) =
      z ^ k * PowerSeries.coeff k (wickTaylorSeries f) := by
    intro k
    rw [wickTaylorSeries_coeff_of_hasFPowerSeriesAt f p hp k]
    have h := (p k).map_smul_univ (fun _ : Fin k => z) (fun _ => (1 : Complex))
    simpa only [smul_eq_mul, mul_one, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] using h
  have h := hSeries.hasSum hz
  simp only [zero_add, hDiagonal] at h
  exact h

end PrimeFactorOscillations
