/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelPowerTrace

/-!
# Finite atomic logarithmic readouts for affine trace models

Every atom and its natural weight is retained in the actual readout.
The scaled limits at both target and reference points give the complete
compensated residue. Positive target order preserves its full complex signal.
These are finite-spectrum models, not Euler products or arithmetic L-functions.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelTraceSharpness

open DirichletCompensatedProbe
open PrimeFactorOscillations.CarmichaelWeightedSignal

def atomicOrder {I : Type*} [Fintype I]
    (point : I -> Complex) (mu : I -> Nat) (rho : Complex) : Nat := by
  classical
  exact Finset.univ.sum (fun i => if point i = rho then mu i else 0)

def atomicReadout {I : Type*} [Fintype I]
    (point : I -> Complex) (mu : I -> Nat) (s : Complex) : Complex :=
  readout (fun i z => z - point i) (fun i => (mu i : Complex)) (fun _ => 0) s

theorem atomicOrder_at {I : Type*} [Fintype I]
    (point : I -> Complex) (mu : I -> Nat) (hPoint : Function.Injective point) (i : I) :
    atomicOrder point mu (point i) = mu i := by
  classical
  simp [atomicOrder, hPoint.eq_iff]

theorem atomicOrder_zero {I : Type*} [Fintype I]
    (point : I -> Complex) (mu : I -> Nat) (rho : Complex)
    (h : forall i, Not (point i = rho)) : atomicOrder point mu rho = 0 := by
  classical
  unfold atomicOrder
  apply Finset.sum_eq_zero
  intro i hi
  rw [if_neg (h i)]

theorem atomicReadout_scaled_limit {I : Type*} [Fintype I]
    (point : I -> Complex) (mu : I -> Nat) (rho : Complex) :
    Filter.Tendsto (fun s => (s - rho) * atomicReadout point mu s)
      (nhdsWithin rho (Set.compl {rho})) (nhds (-(atomicOrder point mu rho : Complex))) := by
  classical
  let n : I -> Nat := fun i => if point i = rho then 1 else 0
  let g : I -> Complex -> Complex :=
    fun i s => if point i = rho then 1 else s - point i
  have hg (i : I) : AnalyticAt Complex (g i) rho := by
    by_cases h : point i = rho
    . simp only [g, if_pos h]
      fun_prop
    . simp only [g, if_neg h]
      fun_prop
  have hgn (i : I) : Not (g i rho = 0) := by
    by_cases h : point i = rho
    . simp [g, h]
    . simpa [g, h, sub_eq_zero] using Ne.symm h
  have hEq (i : I) : Filter.Eventually
      (fun s => s - point i = (s - rho) ^ n i * g i s) (nhds rho) := by
    apply Filter.Eventually.of_forall
    intro s
    by_cases h : point i = rho <;> simp [n, g, h]
  have hs : Finset.univ.sum (fun i => (mu i : Complex) * (n i : Complex)) =
      (atomicOrder point mu rho : Complex) := by
    simp only [atomicOrder, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : point i = rho <;> simp [n, h]
  have ht := weighted_limit (fun i s => s - point i) g
    (fun i => (mu i : Complex)) n rho hg hgn hEq (fun _ => 0) (by fun_prop)
  simpa only [atomicReadout, hs] using ht

def atomicPowerResidue {I : Type*} [Fintype I]
    (point : I -> Complex) (mu : I -> Nat) (d : Real) (rho : Complex) : Complex :=
  -(atomicOrder point mu rho : Complex) +
    (d : Complex) * rho / (rho + (d : Complex) - 1) *
      (atomicOrder point mu (powerMap d rho) : Complex)

theorem atomicPower_scaled_limit {I : Type*} [Fintype I]
    (point : I -> Complex) (mu : I -> Nat) (d : Real) (hd : 0 < d)
    (rho : Complex) (hden : Not (rho + (d : Complex) - 1 = 0)) :
    Filter.Tendsto
      (fun s => (s - rho) * affinePowerReadout (atomicReadout point mu) d s)
      (nhdsWithin rho (Set.compl {rho})) (nhds (atomicPowerResidue point mu d rho)) := by
  have hA := atomicReadout_scaled_limit point mu rho
  have hB := atomicReadout_scaled_limit point mu (powerMap d rho)
  simpa [atomicPowerResidue] using
    affinePowerReadout_scaled_limit (atomicReadout point mu) d hd rho hden
      (atomicOrder point mu rho : Real) (atomicOrder point mu (powerMap d rho) : Real)
      (by simpa using hA) (by simpa using hB)

theorem realPowerResidue_projection (d A B : Real) (rho : Complex)
    (hden : Not (rho + (d : Complex) - 1 = 0)) :
    ((-(A : Complex) + (d : Complex) * rho /
      (rho + (d : Complex) - 1) * (B : Complex)) *
        (rho + (d : Complex) - 1)).im = (d * B - A) * rho.im := by
  have he :
      (-(A : Complex) + (d : Complex) * rho /
        (rho + (d : Complex) - 1) * (B : Complex)) *
        (rho + (d : Complex) - 1) =
      rho * ((d : Complex) * (B : Complex) - (A : Complex)) -
        (A : Complex) * ((d : Complex) - 1) := by
    field_simp [hden]
    ring
  rw [he]
  simp only [Complex.mul_im, Complex.mul_re, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re, Complex.one_im]
  ring

theorem atomicPower_projection {I : Type*} [Fintype I]
    (point : I -> Complex) (mu : I -> Nat) (d : Real) (rho : Complex)
    (hden : Not (rho + (d : Complex) - 1 = 0)) :
    (atomicPowerResidue point mu d rho * (rho + (d : Complex) - 1)).im =
      (d * (atomicOrder point mu (powerMap d rho) : Real) -
        (atomicOrder point mu rho : Real)) * rho.im := by
  simpa [atomicPowerResidue] using
    realPowerResidue_projection d (atomicOrder point mu rho : Real)
      (atomicOrder point mu (powerMap d rho) : Real) rho hden

theorem atomicPowerResidue_ne_zero {I : Type*} [Fintype I]
    (point : I -> Complex) (mu : I -> Nat) (d : Real) (hd : 1 < d)
    (rho : Complex) (hIm : Not (rho.im = 0))
    (hden : Not (rho + (d : Complex) - 1 = 0))
    (hm : 0 < atomicOrder point mu rho) :
    Not (atomicPowerResidue point mu d rho = 0) := by
  have hRec := power_residue_target_multiplicity d
    (atomicOrder point mu rho : Real) (atomicOrder point mu (powerMap d rho) : Real)
    rho hd hIm hden
  have hmR : (0 : Real) < (atomicOrder point mu rho : Real) := by exact_mod_cast hm
  intro hr
  change powerTargetMultiplicity d rho (atomicPowerResidue point mu d rho) =
    (atomicOrder point mu rho : Real) at hRec
  rw [hr] at hRec
  have hz : (atomicOrder point mu rho : Real) = 0 := by
    simpa [powerTargetMultiplicity] using hRec.symm
  exact (ne_of_gt hmR) hz

end PrimeFactorOscillations.CarmichaelTraceSharpness
