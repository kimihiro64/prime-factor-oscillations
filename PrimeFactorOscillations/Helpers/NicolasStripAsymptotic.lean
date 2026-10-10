/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import PrimeFactorOscillations.Helpers.NicolasZetaStrip

/-!
# The scaled Nicolas bound in a zero-free strip

The complete arithmetic error has an explicit upper envelope whose remainder
vanishes after multiplication by x^(1-b) log x. The zeta nonvanishing premise
remains explicit. The retained leading constant is the one used by the
modified-LCM consequence; this module proves no new zero-free region.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations
open Filter Robin1984 Set

def nicolasStripNormalizedError (b x : Real) : Real :=
  ((Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) / (1 - b)) *
    (Inv.inv (Real.log x) + 2 / (1 - b) * (Inv.inv (Real.log x)) ^ 2) +
  Real.log (2 * Real.pi) * x ^ (-b) + 4 * (x ^ (-b) * Real.log x)

theorem tendsto_nicolasStripNormalizedError {b : Real} (hb : 0 < b) :
    Tendsto (nicolasStripNormalizedError b) atTop (nhds 0) := by
  have hInv : Tendsto (fun x : Real => Inv.inv (Real.log x)) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hPow : Tendsto (fun x : Real => x ^ (-b)) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop hb
  have hLogSmall : Tendsto (fun x : Real => x ^ (-b) * Real.log x)
      atTop (nhds 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (1 : Real) hb).tendsto_div_nhds_zero
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : Real)] with x hx
    simp only [Real.rpow_one, Real.rpow_neg hx.le, div_eq_mul_inv]
    ring
  have h := (((hInv.add ((hInv.pow 2).const_mul (2 / (1 - b)))).const_mul
    ((Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) / (1 - b))).add
      (hPow.const_mul (Real.log (2 * Real.pi)))).add (hLogSmall.const_mul 4)
  change Tendsto (fun x : Real => nicolasStripNormalizedError b x) atTop (nhds 0)
  simpa only [nicolasStripNormalizedError, zero_pow (by decide : Not (2 = 0)),
    mul_zero, add_zero] using h

theorem nicolasLog_scaled_strip_bound {b : Real} (hb : 0 < b) (hbOne : b < 1)
    (hZeroFree : forall s : Complex, b < s.re -> Not (s = 1) ->
      Not (riemannZeta s = 0)) {x : Real} (hx : 3 <= x) :
    (x ^ (1 - b) * Real.log x) * nicolasLogMertensOscillation x <=
      (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) /
        (2 * Real.sqrt (b * (1 - b))) + nicolasStripNormalizedError b x := by
  have hxPos : 0 < x := by linarith
  have hLog : Not (Real.log x = 0) := ne_of_gt (Real.log_pos (by linarith))
  have hB : Not (1 - b = 0) := ne_of_gt (sub_pos.mpr hbOne)
  have hB' : Not (b - 1 = 0) := sub_ne_zero.mpr hbOne.ne
  have hPow : x ^ (1 - b) * x ^ (b - 1) = 1 := by
    rw [<- Real.rpow_add hxPos]
    convert Real.rpow_zero x using 1 <;> congr 1 <;> ring
  have hPowNeg : x ^ (1 - b) * x ^ (-(1 : Real)) = x ^ (-b) := by
    rw [<- Real.rpow_add hxPos]
    congr 1
    ring
  have hK := nicolasThetaTail_integrableOn_Ioi_two.mono_set
    (Ioi_subset_Ioi (le_trans (by norm_num) hx))
  have hJ := nicolasPsiTail_integrableOn_Ioi_three.mono_set (Ioi_subset_Ioi hx)
  have hUpper := (nicolasLogMertensOscillation_le_J_add_four_div hx hK hJ).trans
    (_root_.add_le_add ((le_abs_self _).trans
      (nicolasJ_envelope_of_zeta_nonvanishing hb hbOne hZeroFree hx)) (le_refl (4 / x)))
  have hScale : 0 <= x ^ (1 - b) * Real.log x :=
    mul_nonneg (Real.rpow_nonneg hxPos.le _) (Real.log_nonneg (by linarith))
  have hScaled := mul_le_mul_of_nonneg_left hUpper hScale
  calc
    _ <= _ := hScaled
    _ = (x ^ (1 - b) * x ^ (b - 1)) *
          ((Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) /
            (2 * Real.sqrt (b * (1 - b))) +
           ((Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) / (1 - b)) *
             (Inv.inv (Real.log x) + 2 / (1 - b) * (Inv.inv (Real.log x)) ^ 2)) +
        (x ^ (1 - b) * x ^ (-(1 : Real))) *
          (Real.log (2 * Real.pi) + 4 * Real.log x) := by
      dsimp only [nicolasStripRemainderScale]
      rw [Real.rpow_neg_one]
      field_simp
      ring
    _ = _ := by
      rw [hPow, hPowNeg]
      unfold nicolasStripNormalizedError
      ring

theorem eventually_nicolasLog_scaled_strip_lt {b : Real} (hb : 0 < b)
    (hbOne : b < 1)
    (hZeroFree : forall s : Complex, b < s.re -> Not (s = 1) ->
      Not (riemannZeta s = 0)) {epsilon : Real} (he : 0 < epsilon) :
    Filter.Eventually (fun x : Real =>
      (x ^ (1 - b) * Real.log x) * nicolasLogMertensOscillation x <
        (Real.eulerMascheroniConstant + 2 - Real.log (4 * Real.pi)) /
          (2 * Real.sqrt (b * (1 - b))) + epsilon) atTop := by
  filter_upwards [(tendsto_nicolasStripNormalizedError hb).eventually_lt_const he,
    eventually_ge_atTop (3 : Real)] with x hError hx
  have hBound := nicolasLog_scaled_strip_bound hb hbOne hZeroFree hx
  linarith only [hBound, hError]

end PrimeFactorOscillations
