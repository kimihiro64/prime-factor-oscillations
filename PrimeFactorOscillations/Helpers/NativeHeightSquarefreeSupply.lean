/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeBlockPackingSupply
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Pow.PowerLogCount

/-!
# Asymptotic squarefree supply for the native height codebook

The complete finite squarefree-gap bound is combined with both actual
PNT prime blocks. All cutoff rounding and both error allowances are retained.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QRH

open Filter

private theorem eventually_height_squarefree_cutoff (C : Real) (hC : 0 <= C) :
    Filter.Eventually (fun Y : Nat =>
      let R := Nat.ceil ((Y : Real) ^ (1 / 8 : Real))
      24 <= Y /\ 1 <= Real.log (Y : Real) /\ 2 <= R /\
        R ^ 2 <= 2 * (Y / 4) /\
        C * (R : Real) * (Y : Real) ^ (7 / 4 : Real) *
            (1 + 2 * Real.log ((Y : Real) + 2)) ^ 4 +
          (Y : Real) * ((Y / R : Nat) : Real) <=
            (Y : Real) ^ 2 / (2000 * Real.log (Y : Real) ^ 2)) Filter.atTop := by
  have hLog := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R := Real))).eventually
      (Filter.eventually_ge_atTop (1 : Real))
  have hPoly := Real.eventually_const_mul_log_natpow_le_rpow
    (2000 * (1250 * C + 1)) 6 (s := (1 / 8 : Real)) (by norm_num)
  have hRadius := Real.eventually_const_mul_log_natpow_le_rpow
    3 0 (s := (1 / 8 : Real)) (by norm_num)
  have hGeometry := Real.eventually_const_mul_log_natpow_le_rpow
    12 0 (s := (3 / 4 : Real)) (by norm_num)
  filter_upwards [Filter.eventually_ge_atTop (24 : Nat), hLog, hPoly,
      hRadius, hGeometry] with Y hY hl hp hr hg
  let x : Real := Y
  let R := Nat.ceil (x ^ (1 / 8 : Real))
  let L := 1 + 2 * Real.log (x + 2)
  change 1 <= Real.log x at hl
  change (2000 * (1250 * C + 1)) * Real.log x ^ 6 <= x ^ (1 / 8 : Real) at hp
  simp only [pow_zero, mul_one] at hr hg
  have hx24 : (24 : Real) <= x := by
    dsimp [x]
    exact_mod_cast hY
  have hx : 0 < x := by linarith
  have hz : 0 < x ^ (1 / 8 : Real) := Real.rpow_pos_of_pos hx _
  have hz0 : Not (x ^ (1 / 8 : Real) = 0) := ne_of_gt hz
  have hLower : x ^ (1 / 8 : Real) <= (R : Real) := Nat.le_ceil _
  have hUpper : (R : Real) <= 2 * x ^ (1 / 8 : Real) := by
    have hc : (R : Real) < x ^ (1 / 8 : Real) + 1 := Nat.ceil_lt_add_one hz.le
    linarith
  have hR : 2 <= R := by
    have h : (2 : Real) <= R := by linarith
    exact_mod_cast h
  have hSquare : x ^ (1 / 8 : Real) * x ^ (1 / 8 : Real) =
      x ^ (1 / 4 : Real) := by
    rw [<- Real.rpow_add hx]
    norm_num
  have hRSquare : (R : Real) ^ 2 <= 4 * x ^ (1 / 4 : Real) := by
    have hs := mul_self_le_mul_self (Nat.cast_nonneg R) hUpper
    nlinarith only [hs, hSquare]
  have hGeometryProduct : 12 * x ^ (1 / 4 : Real) <= x := by
    calc
      12 * x ^ (1 / 4 : Real) <=
          x ^ (3 / 4 : Real) * x ^ (1 / 4 : Real) :=
        mul_le_mul_of_nonneg_right hg (Real.rpow_nonneg hx.le _)
      _ = x := by
        rw [<- Real.rpow_add hx]
        norm_num
  have hNatGeometry : Y <= 6 * (Y / 4) := by omega
  have hCastGeometry : x <= 6 * ((Y / 4 : Nat) : Real) := by
    dsimp [x]
    exact_mod_cast hNatGeometry
  have hRGeometry : R ^ 2 <= 2 * (Y / 4) := by
    have h : (R : Real) ^ 2 <= 2 * ((Y / 4 : Nat) : Real) := by
      nlinarith only [hRSquare, hGeometryProduct, hCastGeometry]
    exact_mod_cast h
  have hLogAdd : Real.log (x + 2) <= 2 * Real.log x := by
    calc
      Real.log (x + 2) <= Real.log (x ^ 2) :=
        Real.log_le_log (by linarith) (by nlinarith)
      _ = 2 * Real.log x := by rw [Real.log_pow]; norm_num
  have hL0 : 0 <= L := by
    have h := Real.log_nonneg (by linarith : 1 <= x + 2)
    dsimp [L]
    linarith
  have hL : L <= 5 * Real.log x := by
    dsimp [L]
    linarith
  have hL4 : L ^ 4 <= 625 * Real.log x ^ 4 := by
    have h2 := mul_self_le_mul_self hL0 hL
    have h4 := mul_self_le_mul_self (mul_nonneg hL0 hL0) h2
    nlinarith only [h4]
  have hProduct : x ^ (1 / 8 : Real) * x ^ (7 / 4 : Real) =
      x ^ (15 / 8 : Real) := by
    rw [<- Real.rpow_add hx]
    norm_num
  have hPower7 : 0 <= x ^ (7 / 4 : Real) := Real.rpow_nonneg hx.le _
  have hPower15 : 0 <= x ^ (15 / 8 : Real) := Real.rpow_nonneg hx.le _
  have hLow : C * (R : Real) * x ^ (7 / 4 : Real) * L ^ 4 <=
      1250 * C * x ^ (15 / 8 : Real) * Real.log x ^ 4 := by
    calc
      C * (R : Real) * x ^ (7 / 4 : Real) * L ^ 4 <=
          C * (2 * x ^ (1 / 8 : Real)) * x ^ (7 / 4 : Real) * L ^ 4 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hUpper hC) hPower7) (pow_nonneg hL0 4)
      _ <= C * (2 * x ^ (1 / 8 : Real)) * x ^ (7 / 4 : Real) *
          (625 * Real.log x ^ 4) :=
        mul_le_mul_of_nonneg_left hL4
          (mul_nonneg (mul_nonneg hC (mul_nonneg (by norm_num) hz.le)) hPower7)
      _ = 1250 * C * x ^ (15 / 8 : Real) * Real.log x ^ 4 := by
        calc
          _ = 1250 * C * (x ^ (1 / 8 : Real) * x ^ (7 / 4 : Real)) *
              Real.log x ^ 4 := by ring
          _ = _ := by rw [hProduct]
  have hQuotient : x ^ 2 / x ^ (1 / 8 : Real) = x ^ (15 / 8 : Real) := by
    have he : x ^ (15 / 8 : Real) * x ^ (1 / 8 : Real) = x ^ 2 := by
      rw [<- Real.rpow_add hx]
      norm_num [Real.rpow_natCast]
    calc
      x ^ 2 / x ^ (1 / 8 : Real) =
          (x ^ (15 / 8 : Real) * x ^ (1 / 8 : Real)) /
            x ^ (1 / 8 : Real) := by rw [he]
      _ = x ^ (15 / 8 : Real) := by field_simp
  have hHigh : x * ((Y / R : Nat) : Real) <= x ^ (15 / 8 : Real) := by
    calc
      x * ((Y / R : Nat) : Real) <= x * (x / (R : Real)) :=
        mul_le_mul_of_nonneg_left Nat.cast_div_le hx.le
      _ = x ^ 2 / (R : Real) := by ring
      _ <= x ^ 2 / x ^ (1 / 8 : Real) :=
        div_le_div_of_nonneg_left (sq_nonneg x) hz hLower
      _ = x ^ (15 / 8 : Real) := hQuotient
  have hLog2 : 1 <= Real.log x ^ 2 := by nlinarith only [hl]
  have hLog4 : 1 <= Real.log x ^ 4 := by
    nlinarith only [hLog2, sq_nonneg (Real.log x ^ 2 - 1)]
  have hHighLog : x ^ (15 / 8 : Real) <=
      x ^ (15 / 8 : Real) * Real.log x ^ 4 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hLog4 hPower15
  let E := C * (R : Real) * x ^ (7 / 4 : Real) * L ^ 4 +
    x * ((Y / R : Nat) : Real)
  have hCombined : E <= (1250 * C + 1) * x ^ (15 / 8 : Real) *
      Real.log x ^ 4 := by
    dsimp [E]
    nlinarith only [hLow, hHigh, hHighLog]
  have hlPos : 0 < Real.log x := by linarith
  have hl0 : Not (Real.log x = 0) := ne_of_gt hlPos
  have hDen : 0 < 2000 * Real.log x ^ 2 := by positivity
  have hFinal : E * (2000 * Real.log x ^ 2) <= x ^ 2 := by
    calc
      E * (2000 * Real.log x ^ 2) <=
          ((1250 * C + 1) * x ^ (15 / 8 : Real) * Real.log x ^ 4) *
            (2000 * Real.log x ^ 2) :=
        mul_le_mul_of_nonneg_right hCombined hDen.le
      _ = (2000 * (1250 * C + 1) * Real.log x ^ 6) *
          x ^ (15 / 8 : Real) := by ring
      _ <= x ^ (1 / 8 : Real) * x ^ (15 / 8 : Real) :=
        mul_le_mul_of_nonneg_right hp hPower15
      _ = x ^ 2 := by
        rw [<- Real.rpow_add hx]
        norm_num [Real.rpow_natCast]
  have hCancel : (x ^ 2 / (2000 * Real.log x ^ 2)) *
      (2000 * Real.log x ^ 2) = x ^ 2 := by field_simp
  refine And.intro hY (And.intro hl (And.intro hR (And.intro hRGeometry ?_)))
  change E <= x ^ 2 / (2000 * Real.log x ^ 2)
  exact le_of_mul_le_mul_right (hFinal.trans_eq hCancel.symm) hDen

/-- Actual squarefree short prime pairs supply the full log-squared height order. -/
theorem eventually_squarefree_quarter_prime_pair_supply :
    Filter.Eventually (fun Y : Nat => 24 <= Y /\ 1 <= Real.log (Y : Real) /\
      (Y : Real) ^ 2 / (2000 * Real.log (Y : Real) ^ 2) <=
        ((squarefreePrimeBlockGapSet (2 * (Y / 4)) (3 * (Y / 4))
          (4 * (Y / 4))).card : Real)) Filter.atTop := by
  classical
  choose C hC using exists_squarefreePrimeBlockGapSet_lower
  have hError := eventually_height_squarefree_cutoff C hC.1.le
  choose N0 hN0 using eventually_primeQuarterBlock_supply.exists_forall_of_atTop
  filter_upwards [hError, Filter.eventually_ge_atTop (4 * N0 + 24)]
    with Y hErr hY
  let N := Y / 4
  let R := Nat.ceil ((Y : Real) ^ (1 / 8 : Real))
  let A := primeBlockSet (2 * N) (3 * N)
  let B := primeBlockSet (3 * N) (4 * N)
  let S := squarefreePrimeBlockGapSet (2 * N) (3 * N) (4 * N)
  let l := Real.log (Y : Real)
  let t := (Y : Real) ^ 2 / (2000 * l ^ 2)
  have hNbase : N0 <= N := by dsimp [N]; omega
  have hNY : 4 * N <= Y := by dsimp [N]; omega
  have hNrel : 2 * Y <= 9 * N := by dsimp [N]; omega
  have hSupply := (hN0 N hNbase).2 Y hNY
  have hLog : 1 <= l := hErr.2.1
  have hlPos : 0 < l := by linarith
  have hl0 : Not (l = 0) := ne_of_gt hlPos
  have hR : 2 <= R := hErr.2.2.1
  have hRGeometry : R ^ 2 <= 2 * N := hErr.2.2.2.1
  have hErrorBound :
      C * (R : Real) * (Y : Real) ^ (7 / 4 : Real) *
          (1 + 2 * Real.log ((Y : Real) + 2)) ^ 4 +
        (Y : Real) * ((Y / R : Nat) : Real) <= t := hErr.2.2.2.2
  have hFinite := hC.2 (2 * N) (3 * N) (4 * N) Y R
    hR hRGeometry (by omega) (by omega) hNY
  have hCardA : A.card <= Y := by
    have hSub : forall p : Nat, Membership.mem A p ->
        Membership.mem (Finset.Icc 1 Y) p := by
      intro p hp
      have h := (mem_primeBlockSet_iff (2 * N) (3 * N) p).mp hp
      exact Finset.mem_Icc.mpr (And.intro h.1.one_le (by omega))
    have h := Finset.card_le_card hSub
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using h
  have hCardAR : (A.card : Real) <= Y := by exact_mod_cast hCardA
  have hTail := mul_le_mul_of_nonneg_right hCardAR
    (Nat.cast_nonneg (Y / R) : (0 : Real) <= ((Y / R : Nat) : Real))
  have hN0R : (0 : Real) <= N := Nat.cast_nonneg N
  have hA0 : (0 : Real) <= A.card := Nat.cast_nonneg A.card
  have hB0 : (0 : Real) <= B.card := Nat.cast_nonneg B.card
  have hA : (N : Real) <= 2 * (A.card : Real) * l := hSupply.1
  have hB : (N : Real) <= 2 * (B.card : Real) * l := hSupply.2
  have hAB := mul_le_mul hA hB hN0R (by positivity : 0 <= 2 * (A.card : Real) * l)
  have hNSquare : (N : Real) ^ 2 <= 4 * (A.card : Real) * B.card * l ^ 2 := by
    nlinarith only [hAB]
  have hNrelR : (2 : Real) * Y <= 9 * (N : Real) := by exact_mod_cast hNrel
  have hYSquare := mul_self_le_mul_self
    (by positivity : (0 : Real) <= 2 * Y) hNrelR
  have hProductSupply : (Y : Real) ^ 2 <= 81 * (A.card : Real) * B.card * l ^ 2 := by
    nlinarith only [hYSquare, hNSquare]
  have hABl : 0 <= (A.card : Real) * B.card * l ^ 2 :=
    mul_nonneg (mul_nonneg hA0 hB0) (sq_nonneg l)
  have ht : 2000 * t * l ^ 2 = (Y : Real) ^ 2 := by
    dsimp [t]
    field_simp
  have h24 : (24 * t) * l ^ 2 <= ((A.card : Real) * B.card) * l ^ 2 := by
    nlinarith only [hProductSupply, ht, hABl]
  have h24' : 24 * t <= (A.card : Real) * B.card :=
    le_of_mul_le_mul_right h24 (pow_pos hlPos 2)
  have hPositive : 2 * t <= (A.card : Real) * B.card / 12 := by
    nlinarith only [h24']
  have hFull : (A.card : Real) * B.card / 12 <= (S.card : Real) +
      (C * (R : Real) * (Y : Real) ^ (7 / 4 : Real) *
          (1 + 2 * Real.log ((Y : Real) + 2)) ^ 4 +
        (Y : Real) * ((Y / R : Nat) : Real)) := by
    nlinarith only [hFinite, hTail]
  refine And.intro hErr.1 (And.intro hLog ?_)
  change t <= (S.card : Real)
  linarith only [hPositive, hFull, hErrorBound]

end PrimeFactorOscillations.QRH
