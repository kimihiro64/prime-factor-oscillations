/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeRecordEnergy
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimeRecordLeftLimits

/-! # Quantitative consumers of the full signed record identity

The independent signed-energy estimate remains an explicit hypothesis.
The reverse square envelope and the forward square-root implication have
different inputs. Neither one establishes an improved unconditional bound.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem recordEnergy_root_comparison (R C L S : Real)
    (hL : 0 <= L) (hS : 0 <= S)
    (henergy : R ^ 2 <= 2 * C + R * L) (hC : 2 * C <= S ^ 2) :
    R <= L + S := by
  by_contra h
  have hgt : L + S < R := lt_of_not_ge h
  have hd : S < R - L := by linarith only [hgt]
  have hR : S < R := by linarith only [hgt, hL]
  have hd0 : 0 < R - L := hS.trans_lt hd
  have hlo : S * S <= S * (R - L) :=
    mul_le_mul_of_nonneg_left hd.le hS
  have hhi : S * (R - L) < R * (R - L) :=
    mul_lt_mul_of_pos_right hR hd0
  nlinarith only [hlo, hhi, henergy, hC]

theorem primeRecordEnergy_signed_bounds (x : Real) (hx : 2 <= x)
    (hrecord : greedyPrimeRegulatorReal x = primeClassThetaReal Set.univ x - x) :
    And (((greedyPrimeRegulatorReal x) ^ 2 -
        greedyPrimeRegulatorReal x * Real.log x) / 2 <= primeRecordSignedEnergy x)
      (primeRecordSignedEnergy x <= (greedyPrimeRegulatorReal x) ^ 2 / 2) := by
  have h := primeRecordEnergy_at_record x hx hrecord
  constructor <;> nlinarith only [h.1, h.2.1, h.2.2]

theorem primeRecordEnergy_root_bound (x A : Real) (hx : 2 <= x)
    (hA : 0 <= A)
    (hrecord : greedyPrimeRegulatorReal x = primeClassThetaReal Set.univ x - x)
    (hC : primeRecordSignedEnergy x <= A) :
    greedyPrimeRegulatorReal x <= Real.log x + Real.sqrt (2 * A) := by
  have h := primeRecordEnergy_at_record x hx hrecord
  have hlog : 0 <= Real.log x := Real.log_nonneg (by linarith only [hx])
  have hs := Real.sq_sqrt (show 0 <= 2 * A by linarith only [hA])
  apply recordEnergy_root_comparison
    (greedyPrimeRegulatorReal x) (primeRecordSignedEnergy x) (Real.log x)
    (Real.sqrt (2 * A)) hlog (Real.sqrt_nonneg _)
  case henergy => nlinarith only [h.1, h.2.2]
  case hC => nlinarith only [hC, hs]

theorem primeRecordEnergy_power_bound (x a K B : Real) (hx : 2 <= x)
    (hK : 0 <= K)
    (hrecord : greedyPrimeRegulatorReal x = primeClassThetaReal Set.univ x - x)
    (hC : primeRecordSignedEnergy x <= K * x ^ (2 * a))
    (hlog : Real.log x <= B * x ^ a) :
    greedyPrimeRegulatorReal x <= (B + Real.sqrt (2 * K)) * x ^ a := by
  have hx0 : 0 <= x := by linarith only [hx]
  have hy : 0 <= x ^ a := Real.rpow_nonneg hx0 a
  have hpow : x ^ (2 * a) = (x ^ a) ^ 2 := by
    rw [mul_comm 2 a, Real.rpow_mul hx0, Real.rpow_two]
  have hs : (Real.sqrt (2 * K)) ^ 2 = 2 * K :=
    Real.sq_sqrt (show 0 <= 2 * K by linarith only [hK])
  have h := primeRecordEnergy_at_record x hx hrecord
  have hroot : greedyPrimeRegulatorReal x <= Real.log x + Real.sqrt (2 * K) * x ^ a := by
    apply recordEnergy_root_comparison
      (greedyPrimeRegulatorReal x) (primeRecordSignedEnergy x) (Real.log x)
      (Real.sqrt (2 * K) * x ^ a)
    case hL => exact Real.log_nonneg (by linarith only [hx])
    case hS => exact mul_nonneg (Real.sqrt_nonneg _) hy
    case henergy => nlinarith only [h.1, h.2.2]
    case hC =>
      rw [hpow] at hC
      nlinarith only [hC, hs, sq_nonneg (x ^ a)]
  nlinarith only [hroot, hlog]

theorem primeRecordEnergy_source_square_bound (x a K : Real) (hx : 2 <= x)
    (hK : 0 <= K)
    (hrecord : greedyPrimeRegulatorReal x = primeClassThetaReal Set.univ x - x)
    (hR : greedyPrimeRegulatorReal x <= K * x ^ a) :
    primeRecordSignedEnergy x <= (K ^ 2 / 2) * x ^ (2 * a) := by
  have hx0 : 0 <= x := by linarith only [hx]
  have hy : 0 <= x ^ a := Real.rpow_nonneg hx0 a
  have hnonneg : 0 <= greedyPrimeRegulatorReal x :=
    clockRecord_nonneg primeClockError (primeCutoffLength (Nat.floor x))
  have hsq : greedyPrimeRegulatorReal x * greedyPrimeRegulatorReal x <=
      (K * x ^ a) * (K * x ^ a) :=
    mul_le_mul hR hR hnonneg (mul_nonneg hK hy)
  have hC := (primeRecordEnergy_signed_bounds x hx hrecord).2
  have hpow : x ^ (2 * a) = (x ^ a) ^ 2 := by
    rw [mul_comm 2 a, Real.rpow_mul hx0, Real.rpow_two]
  rw [hpow]
  nlinarith only [hsq, hC]

theorem record_log_le_power (x a : Real) (hx : 0 < x) (ha : 0 < a) :
    Real.log x <= (1 / a) * x ^ a := by
  calc
    Real.log x <= x ^ a / a := Real.log_le_rpow_div hx.le ha
    _ = (1 / a) * x ^ a := by ring

theorem primeRecordEnergy_power_bound_explicit (x a K : Real) (hx : 2 <= x)
    (ha : 0 < a) (hK : 0 <= K)
    (hrecord : greedyPrimeRegulatorReal x = primeClassThetaReal Set.univ x - x)
    (hC : primeRecordSignedEnergy x <= K * x ^ (2 * a)) :
    greedyPrimeRegulatorReal x <= (1 / a + Real.sqrt (2 * K)) * x ^ a :=
  primeRecordEnergy_power_bound x a K (1 / a) hx hK hrecord hC
    (record_log_le_power x a (by linarith only [hx]) ha)

end PrimeFactorOscillations.PrimeClassDeletion
