/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.CarmichaelQuadraticScalarChain
import PrimeFactorOscillations.Mathlib.Analysis.Complex.ScalarResidueErasure

/-!
# Unconditional multiplicity cost of losing one real Dirichlet residue

Erasure with positive zero mass forces a positive reference order, a degree
at most seven, and a precise quadratic height cost. The quadratic unit-order
case lies on the unit circle. Sharpness is an integer-code model, not an
assertion of realized Dirichlet zero patterns. QRH remains seven-eighths.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelWeightedSignal

open DirichletCompensatedProbe

def scalarErasureReferenceOrder {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (d : Nat) (rho : Complex) : Nat :=
  analyticOrderNatAt (DirichletCharacter.LFunction chi) (powerMap (d : Real) rho)

private theorem scalar_erasure_code {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (d : Nat) (rho : Complex) :
    dirichletCanonicalPowerResidue chi (d : Real) rho =
      Complex.integerResidueCode d rho
        (analyticOrderNatAt (DirichletCharacter.LFunction chi) rho : Int)
        (scalarErasureReferenceOrder chi d rho : Int) := by
  simp [dirichletCanonicalPowerResidue, scalarErasureReferenceOrder,
    Complex.integerResidueCode]

private theorem scalar_erasure_reference_strip (d : Nat) (hd : 2 <= d)
    (rho : Complex) (hRe : And (0 < rho.re) (rho.re < 1)) :
    And (0 < (powerMap (d : Real) rho).re) ((powerMap (d : Real) rho).re < 1) := by
  have hdR : (2 : Real) <= d := by exact_mod_cast hd
  have h := powerMap_real_identity (d : Real) (by linarith) rho
  constructor <;> nlinarith [hRe.1, hRe.2]

private theorem scalar_erasure_ne_one (s : Complex) (hs : s.re < 1) : Not (s = 1) := by
  intro he
  have hh := congrArg Complex.re he
  change s.re = 1 at hh
  linarith

private theorem scalar_erasure_mass {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (d : Nat) (hd : 2 <= d)
    (rho : Complex) (hRe : And (0 < rho.re) (rho.re < 1))
    (hSignal : Or (DirichletCharacter.LFunction chi rho = 0)
      (DirichletCharacter.LFunction chi (powerMap (d : Real) rho) = 0)) :
    0 < analyticOrderNatAt (DirichletCharacter.LFunction chi) rho +
      scalarErasureReferenceOrder chi d rho := by
  have hA := LFunction_order_pos_iff_zero chi rho (scalar_erasure_ne_one rho hRe.2)
  have hB := LFunction_order_pos_iff_zero chi (powerMap (d : Real) rho)
    (scalar_erasure_ne_one _ (scalar_erasure_reference_strip d hd rho hRe).2)
  change 0 < analyticOrderNatAt (DirichletCharacter.LFunction chi) rho +
    analyticOrderNatAt (DirichletCharacter.LFunction chi) (powerMap (d : Real) rho)
  cases hSignal with
  | inl ha => have hp := hA.mpr ha; omega
  | inr hb => have hp := hB.mpr hb; omega

private theorem scalar_erasure_regular_mono (d b : Nat) (hd : 2 <= d) (hb : 0 < b)
    (hReg : Or (3 <= d) (2 <= b)) :
    2 * (1 - (d : Real) / 8 + (d : Real) - 1) <=
      (d : Real) * ((d : Real) - 1) * (b : Real) := by
  have hdR : (2 : Real) <= d := by exact_mod_cast hd
  have hk : 0 <= (d : Real) * ((d : Real) - 1) :=
    mul_nonneg (by linarith) (by linarith)
  cases hReg with
  | inl hd3 =>
    have hd3R : (3 : Real) <= d := by exact_mod_cast hd3
    have hbR : (1 : Real) <= b := by exact_mod_cast (Nat.succ_le_of_lt hb)
    have hm := mul_le_mul_of_nonneg_left hbR hk
    have hf := mul_nonneg (show (0 : Real) <= d by linarith)
      (show 0 <= (d : Real) - 3 by linarith)
    nlinarith [hm, hf]
  | inr hb2 =>
    have hb2R : (2 : Real) <= b := by exact_mod_cast hb2
    have hm := mul_le_mul_of_nonneg_left hb2R hk
    have hf := mul_nonneg (show (0 : Real) <= d by linarith)
      (show 0 <= (d : Real) - 2 by linarith)
    nlinarith [hm, hf]

theorem dirichlet_scalar_erasure_constraints {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (d : Nat) (hd : 2 <= d)
    (rho : Complex) (hRe : And (0 < rho.re) (rho.re < 1))
    (hSignal : Or (DirichletCharacter.LFunction chi rho = 0)
      (DirichletCharacter.LFunction chi (powerMap (d : Real) rho) = 0))
    (hErase : (dirichletCanonicalPowerResidue chi (d : Real) rho).re = 0) :
    And (d <= 7) (And (0 < scalarErasureReferenceOrder chi d rho)
      (rho.re <= 1 - (d : Real) / 8)) := by
  have hdR : (2 : Real) <= d := by exact_mod_cast hd
  have hCode : (Complex.integerResidueCode d rho
      (analyticOrderNatAt (DirichletCharacter.LFunction chi) rho : Int)
      (scalarErasureReferenceOrder chi d rho : Int)).re = 0 := by
    rw [<- scalar_erasure_code chi d rho]
    exact hErase
  have hCost := Complex.scalar_erasure_cost d hd rho hRe.1.le
    (analyticOrderNatAt (DirichletCharacter.LFunction chi) rho)
    (scalarErasureReferenceOrder chi d rho) (scalar_erasure_mass chi d hd rho hRe hSignal) hCode
  have hStrip := scalar_erasure_reference_strip d hd rho hRe
  have hOne := scalar_erasure_ne_one _ hStrip.2
  have hBZero := (LFunction_order_pos_iff_zero chi (powerMap (d : Real) rho) hOne).mp hCost.1
  have hQBound : (powerMap (d : Real) rho).re <= (7 / 8 : Real) := by
    by_contra hn
    exact (QRH.dirichletL_ne_zero q chi (powerMap (d : Real) rho) (lt_of_not_ge hn)
      (by intro hPole; exact hOne hPole.2)) hBZero
  have hId := powerMap_real_identity (d : Real) (by linarith) rho
  have hMul := mul_le_mul_of_nonneg_right hQBound (show (0 : Real) <= d by linarith)
  rw [hId] at hMul
  have hUpper : rho.re <= 1 - (d : Real) / 8 := by nlinarith [hMul]
  have hd7 : d <= 7 := by
    by_contra hn
    have hd8 : 8 <= d := by omega
    have hd8R : (8 : Real) <= d := by exact_mod_cast hd8
    linarith [hRe.1, hUpper]
  exact And.intro hd7 (And.intro hCost.1 hUpper)

theorem dirichlet_scalar_erasure_height {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (d : Nat) (hd : 2 <= d)
    (rho : Complex) (hRe : And (0 < rho.re) (rho.re < 1))
    (hSignal : Or (DirichletCharacter.LFunction chi rho = 0)
      (DirichletCharacter.LFunction chi (powerMap (d : Real) rho) = 0))
    (hErase : (dirichletCanonicalPowerResidue chi (d : Real) rho).re = 0)
    (hReg : Or (3 <= d) (2 <= scalarErasureReferenceOrder chi d rho)) :
    64 * rho.im ^ 2 + 49 * (d : Real) ^ 2 <=
      56 * (d : Real) ^ 2 * ((d : Real) - 1) *
        (scalarErasureReferenceOrder chi d rho : Real) := by
  have hC := dirichlet_scalar_erasure_constraints chi d hd rho hRe hSignal hErase
  have hCode : (Complex.integerResidueCode d rho
      (analyticOrderNatAt (DirichletCharacter.LFunction chi) rho : Int)
      (scalarErasureReferenceOrder chi d rho : Int)).re = 0 := by
    rw [<- scalar_erasure_code chi d rho]
    exact hErase
  have hH := Complex.scalar_erasure_height d hd rho hRe.1.le (1 - (d : Real) / 8) hC.2.2
    (analyticOrderNatAt (DirichletCharacter.LFunction chi) rho)
    (scalarErasureReferenceOrder chi d rho) (scalar_erasure_mass chi d hd rho hRe hSignal)
    hCode (scalar_erasure_regular_mono d _ hd hC.2.1 hReg)
  nlinarith [hH]

theorem dirichlet_quadratic_scalar_unit_erasure {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (rho : Complex)
    (hRe : And (0 < rho.re) (rho.re < 1))
    (hB : scalarErasureReferenceOrder chi 2 rho = 1)
    (hErase : (dirichletCanonicalPowerResidue chi 2 rho).re = 0) :
    And (analyticOrderNatAt (DirichletCharacter.LFunction chi) rho = 1)
      (rho.re ^ 2 + rho.im ^ 2 = 1) := by
  have hCode : (Complex.integerResidueCode 2 rho
      (analyticOrderNatAt (DirichletCharacter.LFunction chi) rho : Int) 1).re = 0 := by
    have hh := hErase
    have hCode := scalar_erasure_code chi (2 : Nat) rho
    norm_num only [Nat.cast_ofNat] at hCode
    rw [hCode, hB] at hh
    simpa only [Nat.cast_one] using hh
  exact Complex.quadratic_scalar_unit_erasure rho hRe.1 _ hCode

theorem dirichlet_scalar_erasure_classification {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (d : Nat) (hd : 2 <= d)
    (rho : Complex) (hRe : And (0 < rho.re) (rho.re < 1))
    (hSignal : Or (DirichletCharacter.LFunction chi rho = 0)
      (DirichletCharacter.LFunction chi (powerMap (d : Real) rho) = 0))
    (hErase : (dirichletCanonicalPowerResidue chi (d : Real) rho).re = 0) :
    And (d <= 7) (And (0 < scalarErasureReferenceOrder chi d rho)
      (And (rho.re <= 1 - (d : Real) / 8)
        (Or (And (d = 2) (And (scalarErasureReferenceOrder chi d rho = 1)
          (And (analyticOrderNatAt (DirichletCharacter.LFunction chi) rho = 1)
            (rho.re ^ 2 + rho.im ^ 2 = 1))))
          (64 * rho.im ^ 2 + 49 * (d : Real) ^ 2 <=
            56 * (d : Real) ^ 2 * ((d : Real) - 1) *
              (scalarErasureReferenceOrder chi d rho : Real))))) := by
  have hC := dirichlet_scalar_erasure_constraints chi d hd rho hRe hSignal hErase
  refine And.intro hC.1 (And.intro hC.2.1 (And.intro hC.2.2 ?_))
  by_cases hReg : Or (3 <= d) (2 <= scalarErasureReferenceOrder chi d rho)
  . exact Or.inr (dirichlet_scalar_erasure_height chi d hd rho hRe hSignal hErase hReg)
  . have hd2 : d = 2 := by omega
    have hB : scalarErasureReferenceOrder chi d rho = 1 := by omega
    have he := dirichlet_quadratic_scalar_unit_erasure chi rho hRe (by simpa [hd2] using hB)
      (by simpa [hd2] using hErase)
    exact Or.inl (And.intro hd2 (And.intro hB he))

theorem dirichlet_cubic_scalar_nonzero_of_order_bound {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (rho : Complex)
    (hRe : And (0 < rho.re) (rho.re < 1)) (M : Nat)
    (hCap : scalarErasureReferenceOrder chi 3 rho <= M)
    (hSignal : Or (DirichletCharacter.LFunction chi rho = 0)
      (DirichletCharacter.LFunction chi (powerMap 3 rho) = 0))
    (hHeight : 1008 * (M : Real) < 64 * rho.im ^ 2 + 441) :
    Not ((dirichletCanonicalPowerResidue chi 3 rho).re = 0) := by
  intro hErase
  have h := dirichlet_scalar_erasure_height chi 3 (by norm_num) rho hRe hSignal hErase
    (Or.inl (by norm_num))
  norm_num at h
  have hCapR : (scalarErasureReferenceOrder chi 3 rho : Real) <= M := by exact_mod_cast hCap
  nlinarith

theorem scalar_erasure_qrh_model_attains (d : Nat) (hd : 2 <= d) (hd7 : d <= 7)
    (M : Nat) (hM : 1 <= M) (hReg : Or (3 <= d) (2 <= M)) :
    And (0 < (d : Int) * (M : Int) - 1)
      (Exists (fun z : Complex => And (z.re = 1 - (d : Real) / 8)
        (And (And (0 < z.re) (z.re < 1))
          (And ((powerMap (d : Real) z).re = 7 / 8)
            (And ((Complex.integerResidueCode d z ((d : Int) * (M : Int) - 1)
              (M : Int)).re = 0)
              (64 * z.im ^ 2 + 49 * (d : Real) ^ 2 =
                56 * (d : Real) ^ 2 * ((d : Real) - 1) * (M : Real))))))) := by
  have hdR : (2 : Real) <= d := by exact_mod_cast hd
  have hd7R : (d : Real) <= 7 := by exact_mod_cast hd7
  have hB : 0 < M := by omega
  have hAtt := Complex.scalar_erasure_height_attains d hd M hM (1 - (d : Real) / 8)
    (by linarith) (scalar_erasure_regular_mono d M hd hB hReg)
  choose z hz hErase hHeight using hAtt.2
  refine And.intro hAtt.1 (Exists.intro z (And.intro hz (And.intro ?_ (And.intro ?_
    (And.intro hErase ?_)))))
  . exact And.intro (by linarith [hz]) (by linarith [hz])
  . have hId := powerMap_real_identity (d : Real) (by linarith) z
    have hh : ((powerMap (d : Real) z).re - 7 / 8) * (d : Real) = 0 := by
      nlinarith [hz, hId]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right (by linarith))
  . nlinarith [hHeight]

end PrimeFactorOscillations.CarmichaelWeightedSignal
