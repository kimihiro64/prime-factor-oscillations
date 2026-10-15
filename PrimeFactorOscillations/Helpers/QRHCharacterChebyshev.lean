/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import BombieriVinogradov.Assembly.SiegelWalfisz.ExplicitFormula.Main
import BombieriVinogradov.Helpers.DirichletCharacter.ConductorFacts
import BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Imprimitive.ChebyshevCorrection
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Helpers.QRHCharacterExceptional
import PrimeFactorOscillations.Helpers.QRHCharacterZeroSum

/-!
# Uniform character Chebyshev power bounds

Both the retained-zero sum and the selected exceptional-zero contribution are
included. The primitive estimate transfers to every nonprincipal character
with the exact finite Euler correction. Constants are chosen before the modulus,
character and argument. The inputs are the audited seven-eighths source theorem
and the existing BV explicit formula.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QRH

open BombieriVinogradov.SiegelWalfisz

theorem explicitFormulaRemainderMajorant_le_seven_eighths
    {N x : Nat} (hN : 1 <= N) (hx : 1 <= x) :
    explicitFormulaRemainderMajorant N x (x : Real) <=
      2 * (x : Real) ^ (7 / 8 : Real) *
        (1 + Real.log N + Real.log ((x : Real) + 2)) ^ 2 := by
  have hNR : (1 : Real) <= (N : Real) := by exact_mod_cast hN
  have hxR : (1 : Real) <= (x : Real) := by exact_mod_cast hx
  have hNpos : 0 < (N : Real) := zero_lt_one.trans_le hNR
  have hxpos : 0 < (x : Real) := zero_lt_one.trans_le hxR
  let B : Real := 1 + Real.log N + Real.log ((x : Real) + 2)
  have hLN := Real.log_nonneg hNR
  have hLx := Real.log_nonneg hxR
  have hLx2 : 0 <= Real.log ((x : Real) + 2) :=
    Real.log_nonneg (by linarith)
  have hLogs : Real.log x <= Real.log ((x : Real) + 2) :=
    Real.log_le_log hxpos (by linarith)
  have hB : 1 <= B := by dsimp [B]; linarith
  have hBsq : B <= B ^ 2 := by nlinarith
  have hLsum : (Real.log N + Real.log x) ^ 2 <= B ^ 2 := by
    have hlower : 0 <= Real.log N + Real.log x := add_nonneg hLN hLx
    have hupper : Real.log N + Real.log x <= B := by dsimp [B]; linarith
    nlinarith
  have hxpow : 1 <= (x : Real) ^ (7 / 8 : Real) :=
    Real.one_le_rpow hxR (by norm_num)
  have hsmallpow : (x : Real) ^ (1 / 4 : Real) <= (x : Real) ^ (7 / 8 : Real) :=
    Real.rpow_le_rpow_of_exponent_le hxR (by norm_num)
  have hlog : Real.log x <= B ^ 2 := by
    have h : Real.log x <= B := by dsimp [B]; linarith
    exact h.trans hBsq
  have hFirst : (Real.log N + Real.log x) ^ 2 <=
      (x : Real) ^ (7 / 8 : Real) * B ^ 2 :=
    hLsum.trans (by
      calc
        B ^ 2 = 1 * B ^ 2 := by ring
        _ <= _ := mul_le_mul_of_nonneg_right hxpow (sq_nonneg B))
  have hSecond : (x : Real) ^ (1 / 4 : Real) * Real.log x <=
      (x : Real) ^ (7 / 8 : Real) * B ^ 2 :=
    mul_le_mul hsmallpow hlog hLx (Real.rpow_nonneg hxpos.le _)
  unfold explicitFormulaRemainderMajorant
  rw [div_self hxpos.ne', one_mul, Nat.cast_mul,
    Real.log_mul hNpos.ne' hxpos.ne']
  change (Real.log N + Real.log x) ^ 2 + (x : Real) ^ (1 / 4 : Real) * Real.log x <=
    2 * (x : Real) ^ (7 / 8 : Real) * B ^ 2
  nlinarith

theorem exists_primitive_characterChebyshevSum_le_seven_eighths :
    exists A : Real, And (0 < A)
      (forall {N : Nat} [NeZero N], 3 <= N ->
        forall (chi : DirichletCharacter Complex N), Not (chi = 1) ->
          DirichletCharacter.IsPrimitive chi ->
          forall {x : Nat}, 2 <= x ->
            norm (characterChebyshevSum x chi) <=
              A * (x : Real) ^ (7 / 8 : Real) *
                (1 + Real.log N + Real.log ((x : Real) + 2)) ^ 2) := by
  classical
  let c : Real := Classical.choose dirichletExplicitFormula
  have hcAll := Classical.choose_spec dirichletExplicitFormula
  have hc : 0 < c := hcAll.1
  let C : Real := Classical.choose hcAll.2.2
  have hCAll := Classical.choose_spec hcAll.2.2
  have hC : 0 < C := hCAll.1
  let K : Real := Classical.choose
    (exists_norm_truncatedCriticalZeroSum_le_seven_eighths_log_sq hc)
  have hKAll := Classical.choose_spec
    (exists_norm_truncatedCriticalZeroSum_le_seven_eighths_log_sq hc)
  have hK : 0 < K := hKAll.1
  refine Exists.intro (2 * C + K + 2) (And.intro (by positivity) ?_)
  intro N inst hN chi hchi hPrimitive x hx
  have hx1 : 1 <= x := (by decide : 1 <= 2).trans hx
  have hN1 : 1 <= N := (by decide : 1 <= 3).trans hN
  have hxR : (2 : Real) <= (x : Real) := by exact_mod_cast hx
  have hxPos : 0 < (x : Real) := by linarith
  have hChoiceExists : exists e, IsExceptionalZeroChoice c chi e := by
    by_cases he : exists beta, IsExceptionalZero c chi beta
    next =>
      exact Exists.intro (some (Classical.choose he)) (Classical.choose_spec he)
    next =>
      exact Exists.intro none he
  let e : Option Complex := Classical.choose hChoiceExists
  have he := Classical.choose_spec hChoiceExists
  have hE := norm_exceptionalZeroContribution_le_seven_eighths hchi (hcAll.2.1 chi hchi) e he hx1
  have hZ := hKAll.2 hN hchi hPrimitive (hcAll.2.1 chi hchi) e he hx1 (T := (x : Real)) hxPos
  simp only [Nat.ceil_natCast] at hZ
  have hF := hCAll.2 hchi hx (T := (x : Real)) hxR le_rfl e he
  have hR := explicitFormulaRemainderMajorant_le_seven_eighths hN1 hx1
  let B : Real := 1 + Real.log N + Real.log ((x : Real) + 2)
  have hLogN : 0 <= Real.log (N : Real) :=
    Real.log_nonneg (by exact_mod_cast hN1)
  have hLogX : 0 <= Real.log ((x : Real) + 2) :=
    Real.log_nonneg (by linarith)
  have hB : 1 <= B := by dsimp [B]; linarith
  have hBsq : 1 <= B ^ 2 := by nlinarith
  have hLogs : (Real.log N + Real.log ((x : Real) + 2)) ^ 2 <= B ^ 2 := by
    dsimp [B]
    nlinarith
  have hPow := Real.rpow_nonneg hxPos.le (7 / 8 : Real)
  have hZ' : norm (truncatedCriticalZeroSum chi x (x : Real) e) <=
      K * (x : Real) ^ (7 / 8 : Real) * B ^ 2 :=
    hZ.trans (mul_le_mul_of_nonneg_left hLogs (mul_nonneg hK.le hPow))
  have hE' : norm (exceptionalZeroContribution x e) <=
      2 * (x : Real) ^ (7 / 8 : Real) * B ^ 2 := by
    calc
      _ <= 2 * (x : Real) ^ (7 / 8 : Real) := hE
      _ = (2 * (x : Real) ^ (7 / 8 : Real)) * 1 := by ring
      _ <= _ := mul_le_mul_of_nonneg_left hBsq (mul_nonneg (by norm_num) hPow)
  have hF' : norm (characterChebyshevSum x chi +
      truncatedCriticalZeroSum chi x (x : Real) e + exceptionalZeroContribution x e) <=
      (2 * C) * (x : Real) ^ (7 / 8 : Real) * B ^ 2 := by
    calc
      _ <= C * explicitFormulaRemainderMajorant N x (x : Real) := hF
      _ <= C * (2 * (x : Real) ^ (7 / 8 : Real) * B ^ 2) :=
        mul_le_mul_of_nonneg_left hR hC.le
      _ = _ := by ring
  have hTriangle : norm (characterChebyshevSum x chi) <=
      norm (characterChebyshevSum x chi +
        truncatedCriticalZeroSum chi x (x : Real) e + exceptionalZeroContribution x e) +
      (norm (truncatedCriticalZeroSum chi x (x : Real) e) +
        norm (exceptionalZeroContribution x e)) := by
    calc
      _ = norm ((characterChebyshevSum x chi +
          truncatedCriticalZeroSum chi x (x : Real) e + exceptionalZeroContribution x e) -
          (truncatedCriticalZeroSum chi x (x : Real) e + exceptionalZeroContribution x e)) := by
        congr 1
        ring
      _ <= _ := (norm_sub_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
  change norm (characterChebyshevSum x chi) <=
    (2 * C + K + 2) * (x : Real) ^ (7 / 8 : Real) * B ^ 2
  nlinarith


/-- The same exponent is uniform for all nonprincipal characters, including imprimitive ones. -/
theorem exists_characterChebyshevSum_le_seven_eighths :
    exists A : Real, And (0 < A)
      (forall {N : Nat} [NeZero N] (chi : DirichletCharacter Complex N),
        Not (chi = 1) -> forall {x : Nat}, 2 <= x ->
          norm (characterChebyshevSum x chi) <=
            A * (x : Real) ^ (7 / 8 : Real) *
              (1 + Real.log N + Real.log ((x : Real) + 2)) ^ 2) := by
  classical
  let A0 : Real := Classical.choose exists_primitive_characterChebyshevSum_le_seven_eighths
  have hA0All := Classical.choose_spec exists_primitive_characterChebyshevSum_le_seven_eighths
  have hA0 : 0 < A0 := hA0All.1
  have hLogTwo : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  refine Exists.intro (A0 + 1 / Real.log (2 : Real)) (And.intro (by positivity) ?_)
  intro N inst chi hchi x hx
  let _ : NeZero chi.conductor := NeZero.mk chi.conductor_ne_zero
  have hPrimitiveNe : Not (chi.primitiveCharacter = 1) :=
    BombieriVinogradov.DirichletCharacter.primitiveCharacter_ne_one_of_ne_one chi hchi
  have hConductor3 :=
    BombieriVinogradov.DirichletCharacter.three_le_level_of_ne_one
      chi.primitiveCharacter hPrimitiveNe
  have hConductorLe := BombieriVinogradov.DirichletCharacter.conductor_le_level chi
  have hConductorR : (1 : Real) <= (chi.conductor : Real) := by
    exact_mod_cast (by omega : 1 <= chi.conductor)
  have hNR : (1 : Real) <= (N : Real) :=
    hConductorR.trans (Nat.cast_le.mpr hConductorLe)
  have hxR : (1 : Real) <= (x : Real) := by exact_mod_cast (by omega : 1 <= x)
  have hxPos : 0 < (x : Real) := zero_lt_one.trans_le hxR
  have hLogConductor : Real.log chi.conductor <= Real.log N :=
    Real.log_le_log (zero_lt_one.trans_le hConductorR) (Nat.cast_le.mpr hConductorLe)
  have hLogC0 := Real.log_nonneg hConductorR
  have hLogN0 := Real.log_nonneg hNR
  have hLogx0 := Real.log_nonneg hxR
  have hLogx2 : 0 <= Real.log ((x : Real) + 2) := Real.log_nonneg (by linarith)
  have hLogs : Real.log x <= Real.log ((x : Real) + 2) :=
    Real.log_le_log hxPos (by linarith)
  let B : Real := 1 + Real.log N + Real.log ((x : Real) + 2)
  have hB : 1 <= B := by dsimp [B]; linarith
  have hSquares : (1 + Real.log chi.conductor + Real.log ((x : Real) + 2)) ^ 2 <=
      B ^ 2 := by
    dsimp [B]
    nlinarith
  have hPow := Real.rpow_nonneg hxPos.le (7 / 8 : Real)
  have hOnePow : 1 <= (x : Real) ^ (7 / 8 : Real) :=
    Real.one_le_rpow hxR (by norm_num)
  have hPrimitive := hA0All.2 hConductor3 chi.primitiveCharacter
    hPrimitiveNe chi.primitiveCharacter_isPrimitive hx
  have hPrimitive' : norm (characterChebyshevSum x chi.primitiveCharacter) <=
      A0 * (x : Real) ^ (7 / 8 : Real) * B ^ 2 :=
    hPrimitive.trans (mul_le_mul_of_nonneg_left hSquares (mul_nonneg hA0.le hPow))
  have hProduct : Real.log N * Real.log x <= B ^ 2 := by
    have hn : Real.log N <= B := by dsimp [B]; linarith
    have ht : Real.log x <= B := by dsimp [B]; linarith
    simpa only [pow_two] using mul_le_mul hn ht hLogx0 (zero_le_one.trans hB)
  have hProduct' : Real.log N * Real.log x <=
      (x : Real) ^ (7 / 8 : Real) * B ^ 2 :=
    hProduct.trans (by
      calc
        B ^ 2 = 1 * B ^ 2 := by ring
        _ <= _ := mul_le_mul_of_nonneg_right hOnePow (sq_nonneg B))
  have hCorrection := norm_characterChebyshevSum_sub_primitive_le
    (NeZero.ne N) chi (by omega : 0 < x)
  have hCorrection' : norm (characterChebyshevSum x chi -
      characterChebyshevSum x chi.primitiveCharacter) <=
      (1 / Real.log (2 : Real)) * (x : Real) ^ (7 / 8 : Real) * B ^ 2 := by
    calc
      _ <= Real.log N * Real.log x / Real.log (2 : Real) := hCorrection
      _ <= ((x : Real) ^ (7 / 8 : Real) * B ^ 2) / Real.log (2 : Real) :=
        div_le_div_of_nonneg_right hProduct' hLogTwo.le
      _ = _ := by ring
  have hTriangle : norm (characterChebyshevSum x chi) <=
      norm (characterChebyshevSum x chi.primitiveCharacter) +
        norm (characterChebyshevSum x chi - characterChebyshevSum x chi.primitiveCharacter) := by
    calc
      _ = norm (characterChebyshevSum x chi.primitiveCharacter +
          (characterChebyshevSum x chi - characterChebyshevSum x chi.primitiveCharacter)) := by
        congr 1
        ring
      _ <= _ := norm_add_le _ _
  change norm (characterChebyshevSum x chi) <=
    (A0 + 1 / Real.log (2 : Real)) * (x : Real) ^ (7 / 8 : Real) * B ^ 2
  nlinarith

end PrimeFactorOscillations.QRH
