/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import PrimeFactorOscillations.Helpers.LPFPrimeTargetAsymptotic

/-!
# Complete overlap error cutoffs with independent constants

The external coefficient C is separate from the base W raised to the growing
moment order. A checked initial logarithmic deficit and slope imply the
complete error bound uniformly at every larger argument.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem lpf_log_tangent_upper (u v : Real) (hu : 0 < u) (hv : 0 < v) :
    Real.log u <= Real.log v + (u - v) / v := by
  have h := Real.log_le_sub_one_of_pos (div_pos hu hv)
  rw [Real.log_div hu.ne' hv.ne'] at h
  have he : u / v - 1 = (u - v) / v := by field_simp <;> ring
  rw [he] at h
  linarith only [h]

noncomputable def lpfOverlapLogDeficit (C W r L : Real) : Real :=
  Real.log C + 5 * Real.log L +
    10 * Real.log L * (Real.log W + Real.log (Real.log L)) - r * L

theorem lpf_overlap_log_slope_bound (W L0 L : Real)
    (hB : 1 <= W) (hL0 : 0 < L0) (hLog0 : 1 <= Real.log L0) (hL : L0 <= L) :
    (15 + 10 * Real.log W + 10 * Real.log (Real.log L)) / L <=
      (15 + 10 * Real.log W + 10 * Real.log (Real.log L0)) / L0 := by
  have hLp : 0 < L := hL0.trans_le hL
  have hLogLe := Real.log_le_log hL0 hL
  have hLogPos : 0 < Real.log L0 := by linarith only [hLog0]
  have hLogLPos : 0 < Real.log L := hLogPos.trans_le hLogLe
  have hFirst := lpf_log_tangent_upper L L0 hLp hL0
  have hSecond := lpf_log_tangent_upper (Real.log L) (Real.log L0) hLogLPos hLogPos
  have hDiff : 0 <= Real.log L - Real.log L0 := by linarith only [hLogLe]
  have hDiv := div_le_self hDiff hLog0
  have hLL : Real.log (Real.log L) <=
      Real.log (Real.log L0) + (L - L0) / L0 := by
    linarith only [hFirst, hSecond, hDiv]
  have hLogB : 0 <= Real.log W := Real.log_nonneg hB
  have hLL0 : 0 <= Real.log (Real.log L0) := Real.log_nonneg hLog0
  have hNum : 10 <= 15 + 10 * Real.log W + 10 * Real.log (Real.log L0) := by
    linarith only [hLogB, hLL0]
  have hGap : 0 <= (L - L0) / L0 := div_nonneg (sub_nonneg.mpr hL) hL0.le
  have hScaled := mul_le_mul_of_nonneg_right hNum hGap
  have hTotal :
      15 + 10 * Real.log W + 10 * Real.log (Real.log L) <=
        (15 + 10 * Real.log W + 10 * Real.log (Real.log L0)) * L / L0 := by
    have he : (15 + 10 * Real.log W + 10 * Real.log (Real.log L0)) * L / L0 =
        (15 + 10 * Real.log W + 10 * Real.log (Real.log L0)) +
          (15 + 10 * Real.log W + 10 * Real.log (Real.log L0)) * ((L - L0) / L0) := by
      field_simp
      ring
    rw [he]
    linarith only [hLL, hScaled]
  apply (mul_le_mul_iff_of_pos_right hLp).mp
  have hCancel : ((15 + 10 * Real.log W + 10 * Real.log (Real.log L)) / L) * L =
      15 + 10 * Real.log W + 10 * Real.log (Real.log L) := by field_simp
  rw [hCancel]
  have he : ((15 + 10 * Real.log W + 10 * Real.log (Real.log L0)) / L0) * L =
      (15 + 10 * Real.log W + 10 * Real.log (Real.log L0)) * L / L0 := by ring
  rw [he]
  exact hTotal

theorem lpf_overlap_log_deficit_derivative (C W r L : Real)
    (hL : 0 < L) (hLogL : 0 < Real.log L) :
    HasDerivAt (lpfOverlapLogDeficit C W r)
      ((15 + 10 * Real.log W + 10 * Real.log (Real.log L)) / L - r) L := by
  have hLog := Real.hasDerivAt_log hL.ne'
  have hLL := hLog.log hLogL.ne'
  have hd := (((hasDerivAt_const L (Real.log C)).add (hLog.const_mul 5)).add
    ((hLog.mul ((hasDerivAt_const L (Real.log W)).add hLL)).const_mul 10)).sub
      ((hasDerivAt_id L).const_mul r)
  convert hd using 1
  next => funext x; dsimp [lpfOverlapLogDeficit]; ring
  next => simp only [Pi.add_apply, Pi.mul_apply]; field_simp <;> ring

theorem lpf_overlap_log_deficit_eventual_nonpos (C W r L0 : Real)
    (hB : 1 <= W) (hL0 : 0 < L0) (hLog0 : 1 <= Real.log L0)
    (hStart : lpfOverlapLogDeficit C W r L0 <= 0)
    (hSlope : (15 + 10 * Real.log W + 10 * Real.log (Real.log L0)) / L0 <= r) :
    forall L : Real, L0 <= L -> lpfOverlapLogDeficit C W r L <= 0 := by
  have hD (L : Real) (hL : Membership.mem (Set.Ici L0) L) :=
    lpf_overlap_log_deficit_derivative C W r L (hL0.trans_le hL)
      (by have h := Real.log_le_log hL0 hL; linarith only [h, hLog0])
  have hAnti : AntitoneOn (lpfOverlapLogDeficit C W r) (Set.Ici L0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici L0)
    next => intro L hL; exact (hD L hL).continuousAt.continuousWithinAt
    next => intro L hL; exact (hD L (interior_subset hL)).differentiableAt.differentiableWithinAt
    next =>
      intro L hL
      have hMem : Membership.mem (Set.Ici L0) L := interior_subset hL
      rw [(hD L hMem).deriv]
      exact sub_nonpos.mpr
        ((lpf_overlap_log_slope_bound W L0 L hB hL0 hLog0 hMem).trans hSlope)
  intro L hL
  exact (hAnti (show Membership.mem (Set.Ici L0) L0 from Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hL) hL).trans hStart

theorem lpf_overlap_full_moment_error_cutoff (C W r L0 M : Real) (q : Nat)
    (hC : 0 < C) (hB : 1 <= W) (hL0 : 0 < L0) (hLog0 : 1 <= Real.log L0)
    (hStart : lpfOverlapLogDeficit C W r L0 <= 0)
    (hSlope : (15 + 10 * Real.log W + 10 * Real.log (Real.log L0)) / L0 <= r)
    (hM : 0 < M) (hML : L0 <= Real.log M)
    (hq : (q : Real) <= 10 * Real.log (Real.log M)) :
    C * M ^ (1 - r) * Real.log M ^ 4 *
      (W * Real.log (Real.log M)) ^ q <= M / Real.log M := by
  have hLogM : 0 < Real.log M := hL0.trans_le hML
  have hLogLe := Real.log_le_log hL0 hML
  have hLL : 1 <= Real.log (Real.log M) := hLog0.trans hLogLe
  have hLLPos : 0 < Real.log (Real.log M) := zero_lt_one.trans_le hLL
  have hBPos : 0 < W := zero_lt_one.trans_le hB
  have hBase : 1 <= W * Real.log (Real.log M) := by nlinarith only [hB, hLL]
  have hLogBase : 0 <= Real.log W + Real.log (Real.log (Real.log M)) := by
    have h1 := Real.log_nonneg hB
    have h2 := Real.log_nonneg hLL
    linarith only [h1, h2]
  have hQ := mul_le_mul_of_nonneg_right hq hLogBase
  have hDef := lpf_overlap_log_deficit_eventual_nonpos
    C W r L0 hB hL0 hLog0 hStart hSlope (Real.log M) hML
  dsimp [lpfOverlapLogDeficit] at hDef
  have hPowerPos : 0 < M ^ (1 - r) := Real.rpow_pos_of_pos hM _
  have hProdPos : 0 < C * M ^ (1 - r) * Real.log M ^ 4 *
      (W * Real.log (Real.log M)) ^ q := by positivity
  have hTargetPos : 0 < M / Real.log M := div_pos hM hLogM
  apply (Real.log_le_log_iff hProdPos hTargetPos).mp
  rw [Real.log_mul, Real.log_mul, Real.log_mul, Real.log_pow, Real.log_pow,
    Real.log_mul, Real.log_rpow hM, Real.log_div hM.ne' hLogM.ne'] <;> try positivity
  push_cast
  nlinarith only [hQ, hDef]

end PrimeFactorOscillations.LPF
