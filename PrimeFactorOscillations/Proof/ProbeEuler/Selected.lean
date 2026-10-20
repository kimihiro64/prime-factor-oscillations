/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import OAI.NumberTheory.DirichletL.Detector.HighEulerRational
import OAI.NumberTheory.DirichletL.Detector.HighRowsSelectedUnramified

/-!
# Quotient-free selected Euler replacements

Bounds the canonical selected replacement while retaining its phase identities.
The local continuation divides only by the explicit moving denominator and
does not require a nonvanishing unramified correction factor.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.SelectedEulerContinuation

theorem compensatedReplacement_analyticAt
    (V W D P B q : Complex -> Complex) (x : Complex)
    (hV : AnalyticAt Complex V x) (hW : AnalyticAt Complex W x)
    (hD : AnalyticAt Complex D x) (hP : AnalyticAt Complex P x)
    (hB : AnalyticAt Complex B x) (hq : AnalyticAt Complex q x)
    (hden : Not (1 - D x = 0)) :
    AnalyticAt Complex (fun y =>
      OAI.SevenEighths.ProbeLocal.compensatedReplacement
        (V y) (W y) (D y) (P y) (B y) (q y)) x := by
  have hnum : AnalyticAt Complex
      (fun y => (B y - q y) * (1 - V y) * (1 - W y) * P y -
        q y * (1 - V y * W y)) x := by fun_prop
  have hd : AnalyticAt Complex (fun y => 1 - D y) x := by fun_prop
  apply AnalyticAt.div
  . exact hnum
  . exact hd
  . exact hden

theorem weighted_marked_error_bound (R V t K W D B : Complex) (T : Real)
    (hR : norm R <= 1 / 2) (hV : norm V <= 1 / 2)
    (ht : norm t <= 1) (hD : norm D <= 1 / 2) (hW : norm W <= 1 / 2)
    (hBR : norm (B * R) <= T) (hBKV : norm (B * (K * V)) <= T) :
    norm (B * (OAI.SevenEighths.ProbeEuler.markedFactor
      R V t K (-D + W * R) 1 + D)) <= 22 * T := by
  have hmain := OAI.SevenEighths.ProbeLocal.unramified_marked_error_bound
    R V t K W D hR hV ht hD
  have hweighted : norm (B * R) * (1 + norm W) <= (3 / 2) * T := by
    rw [mul_comm]
    exact mul_le_mul (by linarith : 1 + norm W <= 3 / 2) hBR
      (norm_nonneg _) (by norm_num)
  calc
    _ = norm B * norm (OAI.SevenEighths.ProbeEuler.markedFactor
        R V t K (-D + W * R) 1 + D) := norm_mul _ _
    _ <= norm B * (12 * norm R * (1 + norm W) + 4 * norm K * norm V) :=
      mul_le_mul_of_nonneg_left hmain (norm_nonneg _)
    _ = 12 * (norm (B * R) * (1 + norm W)) +
        4 * norm (B * (K * V)) := by simp only [norm_mul]; ring
    _ <= 22 * T := by linarith

theorem normalized_selected_bound (V W D P B q vInv : Complex) (T : Real)
    (hT : 0 <= T) (hV : norm V <= 1 / 2) (hW : norm W <= 1 / 2)
    (hD : norm D <= 1 / 2) (hv : norm vInv <= 1) (hq : norm q <= 1)
    (hVT : norm V <= T) (hDT : norm D <= T)
    (hE : norm (P + D) <= 22 * T) (hBE : norm (B * (P + D)) <= 22 * T)
    (hBD : B * D = vInv) (hvW : vInv * W = q) :
    norm (OAI.SevenEighths.ProbeLocal.compensatedReplacement V W D P B q +
      OAI.SevenEighths.ProbeLocal.continuedCorrection V W D P * vInv) <= 600 * T := by
  have hnV := OAI.SevenEighths.ProbeLocal.one_sub_ne_zero_of_norm_le_half V hV
  have hnD := OAI.SevenEighths.ProbeLocal.one_sub_ne_zero_of_norm_le_half D hD
  have hiV := OAI.SevenEighths.ProbeLocal.inv_one_sub_norm_le_two V hV
  have hiD := OAI.SevenEighths.ProbeLocal.inv_one_sub_norm_le_two D hD
  have huV : norm (1 - V) <= 2 := by
    have h := norm_sub_le (1 : Complex) V
    simp only [norm_one] at h
    linarith
  have huW : norm (1 - W) <= 2 := by
    have h := norm_sub_le (1 : Complex) W
    simp only [norm_one] at h
    linarith
  have hfac : norm ((1 - V) * (1 - W) / (1 - D)) <= 8 := by
    rw [div_eq_mul_inv, norm_mul, norm_mul]
    have hprod : norm (1 - V) * norm (1 - W) <= 4 := by
      calc
        _ <= (2 : Real) * 2 := mul_le_mul huV huW (norm_nonneg _) (by norm_num)
        _ = 4 := by norm_num
    calc
      _ <= (4 : Real) * 2 := mul_le_mul hprod hiD (norm_nonneg _) (by norm_num)
      _ = 8 := by norm_num
  have hVquot : norm (V / (1 - V)) <= 2 * T := by
    rw [div_eq_mul_inv, norm_mul, mul_comm]
    exact mul_le_mul hiV hVT (norm_nonneg _) (by norm_num)
  have hsmall : norm (V / (1 - V) - D) <= 3 * T :=
    (norm_sub_le _ _).trans (by linarith)
  have hdiff : norm (vInv - q) <= 2 :=
    (norm_sub_le _ _).trans (by linarith)
  have hfirst : norm ((vInv - q) * (V / (1 - V) - D)) <= 6 * T := by
    rw [norm_mul]
    calc
      _ <= 2 * (3 * T) := mul_le_mul hdiff hsmall (norm_nonneg _) (by norm_num)
      _ = 6 * T := by ring
  have hvE : norm (vInv * (P + D)) <= 22 * T := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hv).trans hE
  have hqE : norm (q * (P + D)) <= 22 * T := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hq).trans hE
  have hsecond : norm ((B + vInv - q) * (P + D)) <= 66 * T := by
    rw [show (B + vInv - q) * (P + D) =
      B * (P + D) + vInv * (P + D) - q * (P + D) by ring]
    have h1 := norm_add_le (B * (P + D)) (vInv * (P + D))
    have h2 := norm_sub_le (B * (P + D) + vInv * (P + D)) (q * (P + D))
    linarith
  rw [OAI.SevenEighths.ProbeLocal.continued_normalized_cancellation
    V W D P B q vInv hnV hnD hBD hvW, norm_mul]
  have hinner : norm ((vInv - q) * (V / (1 - V) - D) +
      (B + vInv - q) * (P + D)) <= 72 * T :=
    (norm_add_le _ _).trans (by linarith)
  calc
    _ <= 8 * (72 * T) := mul_le_mul hfac hinner (norm_nonneg _) (by norm_num)
    _ <= 600 * T := by linarith

private theorem exp_neg_le_half (u : Real) (hu : 1 <= u) :
    Real.exp (-u) <= 1 / 2 := by
  have he : 2 <= Real.exp u := by linarith [Real.add_one_le_exp u]
  have hc : Real.exp u * Real.exp (-u) = 1 := by rw [<- Real.exp_add]; simp
  nlinarith [mul_nonneg (Real.exp_nonneg (-u)) (show 0 <= Real.exp u - 2 by linarith)]

private theorem rpow_half_bound (Q : Real) (hQ : Real.exp 2 <= Q) :
    Q ^ (-(1 / 2) : Real) <= 1 / 2 := by
  have hQpos : 0 < Q := lt_of_lt_of_le (Real.exp_pos 2) hQ
  have hlog : 2 <= Real.log Q := by
    have h := Real.log_le_log (Real.exp_pos 2) hQ
    simpa using h
  rw [Real.rpow_def_of_pos hQpos]
  convert exp_neg_le_half ((1 / 2) * Real.log Q) (by linarith) using 1
  congr 1
  ring

private theorem norm_mul_rpow (Q : Real) (hQ : 1 <= Q) (x y : Complex)
    (a b c : Real) (hx : norm x <= Q ^ a) (hy : norm y <= Q ^ b)
    (hab : a + b <= c) : norm (x * y) <= Q ^ c := by
  have hQpos : 0 < Q := by linarith
  rw [norm_mul]
  calc
    _ <= Q ^ a * Q ^ b :=
      mul_le_mul hx hy (norm_nonneg _) (Real.rpow_nonneg hQpos.le _)
    _ = Q ^ (a + b) := (Real.rpow_add hQpos _ _).symm
    _ <= Q ^ c := Real.rpow_le_rpow_of_exponent_le hQ hab

theorem unramified_selected_uniform_bound (Q : Real) (A eta v s w z : Complex)
    (hQ : Real.exp 2 <= Q) (hA : norm A <= 1)
    (heta : norm eta <= 1) (hv : norm v <= 1)
    (hs : 3 / 4 <= s.re) (hw : 19 / 20 <= w.re) (hz : 33 / 200 <= z.re)
    (hBD : (star eta * (Q : Complex) ^ s) *
      OAI.SevenEighths.ProbeEuler.coordD Q eta v s = star v)
    (hvW : star v * OAI.SevenEighths.ProbeEuler.coordW Q v w =
      (Q : Complex) ^ (-w)) :
    let V := OAI.SevenEighths.ProbeEuler.coordV Q z
    let W := OAI.SevenEighths.ProbeEuler.coordW Q v w
    let D := OAI.SevenEighths.ProbeEuler.coordD Q eta v s
    let R := OAI.SevenEighths.ProbeEuler.coordR Q A s z
    let K := OAI.SevenEighths.ProbeEuler.coordK Q eta s w
    let P := OAI.SevenEighths.ProbeEuler.markedFactor R V
      (Inv.inv (Q : Complex)) K (-D + W * R) 1
    norm (OAI.SevenEighths.ProbeLocal.compensatedReplacement V W D P
      (star eta * (Q : Complex) ^ s) ((Q : Complex) ^ (-w)) +
        OAI.SevenEighths.ProbeEuler.unramifiedClosed Q A eta v s w z * star v) <=
      600 * Q ^ (-(37 / 50) : Real) := by
  have hQpos : 0 < Q := lt_of_lt_of_le (Real.exp_pos 2) hQ
  have hQ1 : 1 <= Q := by linarith [hQ, Real.add_one_le_exp (2 : Real)]
  let V := OAI.SevenEighths.ProbeEuler.coordV Q z
  let W := OAI.SevenEighths.ProbeEuler.coordW Q v w
  let D := OAI.SevenEighths.ProbeEuler.coordD Q eta v s
  let R := OAI.SevenEighths.ProbeEuler.coordR Q A s z
  let K := OAI.SevenEighths.ProbeEuler.coordK Q eta s w
  let B := star eta * (Q : Complex) ^ s
  let q := (Q : Complex) ^ (-w)
  let P := OAI.SevenEighths.ProbeEuler.markedFactor R V
    (Inv.inv (Q : Complex)) K (-D + W * R) 1
  let T : Real := Q ^ (-(37 / 50) : Real)
  have hVN : norm V <= Q ^ (-6 * z.re) :=
    (OAI.SevenEighths.ProbeEuler.coordV_norm Q hQpos z).le
  have hWN : norm W <= Q ^ (-w.re) :=
    OAI.SevenEighths.ProbeEuler.coordW_norm_le Q hQpos v w hv
  have hDN : norm D <= Q ^ (-s.re) :=
    OAI.SevenEighths.ProbeEuler.coordD_norm_le Q hQpos eta v s heta hv
  have hRN : norm R <= Q ^ (4 - 6 * s.re - 6 * z.re) :=
    OAI.SevenEighths.ProbeEuler.coordR_norm_le Q hQpos A s z hA
  have hKN : norm K <= Q ^ (1 - s.re - w.re) :=
    OAI.SevenEighths.ProbeEuler.coordK_norm_le Q hQ1 eta s w heta
  have hBN : norm B <= Q ^ s.re := by
    change norm (star eta * (Q : Complex) ^ s) <= Q ^ s.re
    rw [norm_mul, norm_star, Complex.norm_cpow_eq_rpow_re_of_pos hQpos]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hQpos.le _) heta
  have hqN : norm q <= Q ^ (-w.re) := by
    dsimp [q]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQpos, Complex.neg_re]
  have hbase := rpow_half_bound Q hQ
  have hVhalf : norm V <= 1 / 2 :=
    hVN.trans ((Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)).trans hbase)
  have hWhalf : norm W <= 1 / 2 :=
    hWN.trans ((Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)).trans hbase)
  have hDhalf : norm D <= 1 / 2 :=
    hDN.trans ((Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)).trans hbase)
  have hRhalf : norm R <= 1 / 2 :=
    hRN.trans ((Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)).trans hbase)
  have hqhalf : norm q <= 1 / 2 :=
    hqN.trans ((Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)).trans hbase)
  have hVT : norm V <= T :=
    hVN.trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hDT : norm D <= T :=
    hDN.trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hRT : norm R <= T :=
    hRN.trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hKVT : norm (K * V) <= T :=
    norm_mul_rpow Q hQ1 K V _ _ _ hKN hVN (by linarith)
  have hBRT : norm (B * R) <= T :=
    norm_mul_rpow Q hQ1 B R _ _ _ hBN hRN (by linarith)
  have hKVN : norm (K * V) <= Q ^ (1 - s.re - w.re - 6 * z.re) :=
    norm_mul_rpow Q hQ1 K V _ _ _ hKN hVN (by linarith)
  have hBKVT : norm (B * (K * V)) <= T :=
    norm_mul_rpow Q hQ1 B (K * V) _ _ _ hBN hKVN (by linarith)
  have ht : norm (Inv.inv (Q : Complex)) <= 1 := by
    simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQpos]
    have hc : Inv.inv Q * Q = 1 := by field_simp
    have hn : 0 <= Inv.inv Q := inv_nonneg.mpr hQpos.le
    nlinarith [mul_nonneg hn (sub_nonneg.mpr hQ1)]
  have hE : norm (P + D) <= 22 * T := by
    have h := weighted_marked_error_bound R V (Inv.inv (Q : Complex)) K W D 1 T
      hRhalf hVhalf ht hDhalf hWhalf (by simpa using hRT) (by simpa using hKVT)
    simpa only [one_mul] using h
  have hBE : norm (B * (P + D)) <= 22 * T :=
    weighted_marked_error_bound R V (Inv.inv (Q : Complex)) K W D B T
      hRhalf hVhalf ht hDhalf hWhalf hBRT hBKVT
  exact normalized_selected_bound V W D P B q (star v) T
    (Real.rpow_nonneg hQpos.le _) hVhalf hWhalf hDhalf
    (by simpa only [norm_star] using hv) (by linarith)
    hVT hDT hE hBE hBD hvW


theorem local_phase_identities (Q : Real) (eta v s w : Complex)
    (hQ : 0 < Q) (heta : norm eta = 1) (hv : norm v = 1) :
    ((star eta * (Q : Complex) ^ s) *
      OAI.SevenEighths.ProbeEuler.coordD Q eta v s = star v) /\
      (star v * OAI.SevenEighths.ProbeEuler.coordW Q v w =
        (Q : Complex) ^ (-w)) :=
  OAI.SevenEighths.ProbeEuler.selected_phase_identities Q eta v s w hQ heta hv

theorem unramified_selected_unit_bound (Q : Real) (A eta v s w z : Complex)
    (hQ : Real.exp 2 <= Q) (hA : norm A <= 1)
    (heta : norm eta = 1) (hv : norm v = 1)
    (hs : 3 / 4 <= s.re) (hw : 19 / 20 <= w.re) (hz : 33 / 200 <= z.re) :
    norm (OAI.SevenEighths.ProbeEuler.unramifiedSelected Q A eta v s w z +
      OAI.SevenEighths.ProbeEuler.unramifiedClosed Q A eta v s w z * star v) <=
      600 * Q ^ (-(37 / 50) : Real) := by
  have hphase := local_phase_identities Q eta v s w
    (lt_of_lt_of_le (Real.exp_pos 2) hQ) heta hv
  simpa only [OAI.SevenEighths.ProbeEuler.unramifiedSelected,
    OAI.SevenEighths.ProbeEuler.unramifiedMarked] using
    unramified_selected_uniform_bound Q A eta v s w z hQ hA heta.le hv.le
      hs hw hz hphase.1 hphase.2
end PrimeFactorOscillations.SelectedEulerContinuation
