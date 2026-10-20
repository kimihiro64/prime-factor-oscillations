/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Tactic.IntervalCases
import PrimeFactorOscillations.Assembly.DetectorPackets.GaussianMobiusDivisors

/-!
# GaussianIdealNorm

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

/-!
# Exact Gaussian principal ideal norm

This identifies the ideal norm used by the arithmetic packet with the
coordinate norm used by Gaussian Poisson summation. No zero-free estimate
or moment hypothesis is used.
-/


noncomputable section
namespace PrimeFactorOscillations.GaussianIdealNorm

open GaussianMobiusDivisors

def coordinateBasis : Module.Basis (Fin 2) Int G :=
  (Module.Basis.finTwoProd Int).map integerLinearCoordinates.symm

theorem algebra_norm (z : G) : Algebra.norm Int z = z.norm := by
  rw [Algebra.norm_eq_matrix_det coordinateBasis, Matrix.det_fin_two]
  simp [Algebra.leftMulMatrix, LinearMap.toMatrix, coordinateBasis,
    integerLinearCoordinates, integerCoordinates, Zsqrtd.norm]

theorem principal_absNorm (z : G) :
    Ideal.absNorm (Ideal.span ({z} : Set G)) = z.norm.natAbs := by
  rw [Ideal.absNorm_span_singleton, algebra_norm]

theorem principal_absNorm_real (z : G) :
    (Ideal.absNorm (Ideal.span ({z} : Set G)) : Real) =
      Complex.normSq (GaussianArithmetic.GaussianInt.toComplex z) := by
  rw [principal_absNorm, GaussianArithmetic.GaussianInt.natCast_natAbs_norm]
  exact GaussianArithmetic.GaussianInt.intCast_real_norm z

def imaginaryUnit : G := GaussianResidueField.imaginaryUnit

def unitI : Units G where
  val := imaginaryUnit
  inv := -imaginaryUnit
  val_inv := by
    apply Zsqrtd.ext <;> norm_num [imaginaryUnit, GaussianResidueField.imaginaryUnit]
  inv_val := by
    apply Zsqrtd.ext <;> norm_num [imaginaryUnit, GaussianResidueField.imaginaryUnit]

theorem norm_of_isUnit (z : G) (hz : IsUnit z) : z.norm = 1 := by
  choose u hu using hz
  rw [<- hu]
  have hprod : (u : G).norm * ((Inv.inv u : Units G) : G).norm = 1 := by
    rw [<- Zsqrtd.norm_mul]
    simp
  have hu1 : 1 <= (u : G).norm :=
    Int.add_one_le_of_lt (GaussianArithmetic.GaussianInt.norm_pos.mpr (Units.ne_zero u))
  have hv1 : 1 <= ((Inv.inv u : Units G) : G).norm :=
    Int.add_one_le_of_lt
      (GaussianArithmetic.GaussianInt.norm_pos.mpr (Units.ne_zero (Inv.inv u)))
  have hle : (u : G).norm <= 1 := by
    calc
      _ = (u : G).norm * 1 := (mul_one _).symm
      _ <= (u : G).norm * ((Inv.inv u : Units G) : G).norm :=
        mul_le_mul_of_nonneg_left hv1 (GaussianArithmetic.GaussianInt.norm_nonneg _)
      _ = 1 := hprod
  exact le_antisymm hle hu1

theorem norm_one_classification (z : G) (hz : z.norm = 1) :
    z = 1 \/ z = -1 \/ z = imaginaryUnit \/ z = -imaginaryUnit := by
  cases z with
  | mk x y =>
    norm_num [Zsqrtd.norm] at hz
    have hxlo : -1 <= x := by nlinarith [sq_nonneg y]
    have hxhi : x <= 1 := by nlinarith [sq_nonneg y]
    have hylo : -1 <= y := by nlinarith [sq_nonneg x]
    have hyhi : y <= 1 := by nlinarith [sq_nonneg x]
    interval_cases x <;> interval_cases y <;> norm_num at hz
    all_goals decide

theorem isUnit_iff_norm_one (z : G) : IsUnit z <-> z.norm = 1 := by
  constructor
  . exact norm_of_isUnit z
  . intro hz
    rcases norm_one_classification z hz with h | h | h | h
    . rw [h]
      exact isUnit_one
    . rw [h]
      exact isUnit_neg_one
    . rw [h]
      exact unitI.isUnit
    . rw [h]
      exact unitI.isUnit.neg

def unitValues : Finset G := {1, -1, imaginaryUnit, -imaginaryUnit}

theorem mem_unitValues (z : G) :
    Membership.mem unitValues z <-> IsUnit z := by
  constructor
  . intro hz
    apply (isUnit_iff_norm_one z).mpr
    simp only [unitValues, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with h | h | h | h <;> rw [h] <;>
      norm_num [imaginaryUnit, GaussianResidueField.imaginaryUnit, Zsqrtd.norm]
  . intro hz
    simpa only [unitValues, Finset.mem_insert, Finset.mem_singleton] using
      norm_one_classification z (norm_of_isUnit z hz)

def unitValuesEquiv : Equiv (Units G) {z : G // Membership.mem unitValues z} where
  toFun u := Subtype.mk (u : G) ((mem_unitValues _).mpr u.isUnit)
  invFun z := Classical.choose ((mem_unitValues z.val).mp z.property)
  left_inv u := by
    apply Units.ext
    exact Classical.choose_spec ((mem_unitValues (u : G)).mp
      ((mem_unitValues _).mpr u.isUnit))
  right_inv z := by
    apply Subtype.ext
    exact Classical.choose_spec ((mem_unitValues z.val).mp z.property)

instance unitsFintype : Fintype (Units G) :=
  Fintype.ofEquiv {z : G // Membership.mem unitValues z} unitValuesEquiv.symm

theorem units_card : Fintype.card (Units G) = 4 := by
  calc
    _ = Fintype.card {z : G // Membership.mem unitValues z} :=
      Fintype.card_congr unitValuesEquiv
    _ = unitValues.card := Fintype.card_coe unitValues
    _ = 4 := by decide

end PrimeFactorOscillations.GaussianIdealNorm
