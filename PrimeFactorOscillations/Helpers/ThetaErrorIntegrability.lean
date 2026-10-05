/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PrimeNumberTheoremAnd.MediumPNT

/-!
# Absolute integrability of the Nicolas theta-error tail

The quantitative theta bound adapts RS_prime.pntBigO and RS_prime.pnt from
PrimeNumberTheoremAnd at f6147e7572ab3abe5428101bc0b13627bcb005df. Only the
proved cached MediumPNT theorem is imported, not the Rosser source containing
tables and unrelated unfinished statements. The final integrability proof
uses Mathlib's existing inverse-log-square integral directly.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

open Filter MeasureTheory Real Asymptotics
open scoped Topology

namespace PrimeFactorOscillations

private theorem le_div_iff_pos {a b d : Real} (hd : 0 < d) :
    a <= b / d <-> a * d <= b := by
  run_tac
    let declaration := Lean.Name.mkSimple
      ("le_div_iff" ++ String.singleton (Char.ofNat 8320))
    let positive := Lean.mkIdent (Lean.Name.mkSimple "hd")
    let proofSyntax <- `(tactic| exact $(Lean.mkIdent declaration) $positive)
    Lean.Elab.Tactic.evalTactic proofSyntax

theorem thetaError_isBigO_div_log_sq :
    IsBigO atTop (fun x : Real => Chebyshev.theta x - x)
      (fun x : Real => x / Real.log x ^ 2) := by
  let c : Real := Classical.choose MediumPNT
  have hc := Classical.choose_spec MediumPNT
  change And (0 < c)
    (IsBigO atTop (Chebyshev.psi - id)
      (fun x : Real => x * exp (-c * log x ^ (1 / 10 : Real)))) at hc
  have hpsi : IsBigO atTop (Chebyshev.psi - id)
      (fun x : Real => x / log x ^ 2) := by
    have hexp : IsBigO atTop
        (fun x : Real => exp (-c * log x ^ (1 / 10 : Real)))
        (fun x : Real => log x ^ (-2 : Real)) := by
      have hdecay : Tendsto
          (fun x : Real => exp (-c * log x ^ (1 / 10 : Real)) * log x ^ 2)
          atTop (nhds 0) := by
        have hy : Tendsto (fun y : Real => exp (-c * y) * y ^ 20)
            atTop (nhds 0) := by
          have hz : Tendsto (fun z : Real => exp (-z) * (z / c) ^ 20)
              atTop (nhds 0) := by
            convert (tendsto_pow_mul_exp_neg_atTop_nhds_zero 20).div_const (c ^ 20)
              using 2 <;> ring
          convert hz.comp (tendsto_id.const_mul_atTop hc.1) using 2
          norm_num [hc.1.ne']
        have hsubst := hy.comp
          ((tendsto_rpow_atTop (by norm_num : (0 : Real) < 1 / 10)).comp
            tendsto_log_atTop)
        apply hsubst.congr'
        filter_upwards [eventually_gt_atTop (1 : Real)] with x hx
        dsimp only [Function.comp_def]
        rw [<- rpow_natCast, <- rpow_mul (log_nonneg hx.le)]
        norm_num
      rw [isBigO_iff]
      have hev := hdecay.eventually (Metric.ball_mem_nhds (0 : Real) zero_lt_one)
      let M : Real := Classical.choose (eventually_atTop.mp hev)
      have hM := Classical.choose_spec (eventually_atTop.mp hev)
      change forall x : Real, M <= x -> _ at hM
      norm_cast
      norm_num
      refine Exists.intro 1 (Exists.intro (max M 2) ?_)
      intro x hx
      have hxOne : 1 < x := by linarith [le_max_right M (2 : Real)]
      rw [<- div_eq_mul_inv, le_div_iff_pos (sq_pos_of_pos (log_pos hxOne))]
      have hbound := abs_lt.mp (hM x (le_trans (le_max_left M 2) hx))
      norm_num at hbound
      nlinarith
    refine hc.2.trans ?_
    convert (isBigO_refl (fun x : Real => x) atTop).mul hexp using 2
    simp [field]
  have hdiff : IsBigO atTop (fun x : Real => Chebyshev.theta x - Chebyshev.psi x)
      (fun x : Real => x / log x ^ 2) := by
    apply isBigO_iff.mpr
    refine Exists.intro 432 ?_
    filter_upwards [eventually_gt_atTop (1 : Real)] with x hx
    simp only [Real.norm_eq_abs, norm_div, norm_pow, sq_abs, mul_div]
    have hx0 : 0 <= x := (lt_trans zero_lt_one hx).le
    calc
      abs (Chebyshev.theta x - Chebyshev.psi x)
          <= 2 * sqrt x * log x := by
        rw [<- neg_sub, abs_neg]
        exact Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx.le
      _ <= 432 * abs x / log x ^ 2 := by
        rw [le_div_iff_pos (sq_pos_of_pos (log_pos hx)), mul_assoc,
          <- pow_succ' (log x) 2]
        have hlog : log x ^ 3 <= 216 * x ^ (1 / 2 : Real) := by
          have hpow := rpow_le_rpow (log_nonneg hx.le)
            (log_le_rpow_div hx0 (by norm_num : (0 : Real) < 1 / 6))
            (by norm_num : (0 : Real) <= 3)
          simp only [rpow_ofNat, one_div, div_inv_eq_mul, mul_comm,
            mul_rpow (by norm_num : (0 : Real) <= 6) (rpow_nonneg hx0 _),
            <- rpow_mul hx0] at hpow
          norm_num at hpow
          exact hpow
        have hmul := mul_le_mul_of_nonneg_left hlog
          (mul_nonneg (by norm_num : (0 : Real) <= 2) (sqrt_nonneg x))
        rw [<- sqrt_eq_rpow, mul_comm 216 (sqrt x), <- mul_assoc,
          mul_assoc 2 (sqrt x) (sqrt x), mul_self_sqrt hx0,
          <- mul_comm 216, <- mul_assoc] at hmul
        norm_num at hmul
        simpa [abs_of_nonneg hx0] using hmul
  have hsum := hpsi.add hdiff
  convert hsum using 1
  funext x
  simp only [Pi.sub_apply, id_eq]
  ring

theorem exists_thetaError_bound_div_log_sq :
    exists C : Real, And (0 <= C)
      (forall x : Real, 2 <= x ->
        abs (Chebyshev.theta x - x) <= C * x / Real.log x ^ 2) := by
  refine Exists.elim (isBigO_iff'.mp thetaError_isBigO_div_log_sq) ?_
  intro c hc
  have hcPos : 0 < c := hc.1
  let N0 : Real := Classical.choose (eventually_atTop.mp hc.2)
  have hN0 := Classical.choose_spec (eventually_atTop.mp hc.2)
  let N : Real := max N0 2
  have hN : 2 <= N := le_max_right N0 2
  let A : Real := max c (4 * (Chebyshev.theta N + N))
  have hcA : c <= A := le_max_left _ _
  refine Exists.intro A (And.intro (hcPos.le.trans hcA) ?_)
  intro x hx
  have hx0 : 0 <= x := by linarith
  have hxOne : 1 < x := by linarith
  by_cases hsmall : x <= N
  . have herr : abs (Chebyshev.theta x - x) <= Chebyshev.theta N + N := by
      calc
        _ <= abs (Chebyshev.theta x) + abs x := abs_sub _ _
        _ = Chebyshev.theta x + x := by
          rw [abs_of_nonneg (Chebyshev.theta_nonneg x), abs_of_nonneg hx0]
        _ <= _ := add_le_add (Chebyshev.theta_mono hsmall) hsmall
    have hlog0 : 0 <= log x := log_nonneg hxOne.le
    have hlog := log_le_rpow_div hx0 (by norm_num : (0 : Real) < 1 / 2)
    have hlogSq : log x ^ 2 <= (x ^ (1 / 2 : Real) / (1 / 2)) ^ 2 := by
      gcongr
    rw [<- sqrt_eq_rpow, div_pow, sq_sqrt hx0] at hlogSq
    have hsq : log x ^ 2 <= 4 * x := by norm_num at hlogSq; nlinarith
    apply (le_div_iff_pos (sq_pos_of_pos (log_pos hxOne))).mpr
    calc
      abs (Chebyshev.theta x - x) * log x ^ 2
          <= (Chebyshev.theta N + N) * log x ^ 2 :=
        mul_le_mul_of_nonneg_right herr (sq_nonneg _)
      _ <= (Chebyshev.theta N + N) * (4 * x) :=
        mul_le_mul_of_nonneg_left hsq
          (add_nonneg (Chebyshev.theta_nonneg N) (by linarith))
      _ = (4 * (Chebyshev.theta N + N)) * x := by ring
      _ <= A * x := mul_le_mul_of_nonneg_right (le_max_right _ _) hx0
  . have hlarge : N0 <= x := (le_max_left N0 2).trans (by linarith)
    have hb := hN0 x hlarge
    have hb' : abs (Chebyshev.theta x - x) <= c * x / log x ^ 2 := by
      convert hb using 1
      simp only [Real.norm_eq_abs, norm_div, norm_pow, sq_abs,
        abs_of_nonneg hx0, mul_div]
    exact hb'.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcA hx0) (sq_nonneg _))

theorem integrableOn_thetaError_nicolasKernel :
    IntegrableOn (fun t : Real =>
      (Chebyshev.theta t - t) * (1 + Real.log t) /
        (t ^ 2 * Real.log t ^ 2)) (Set.Ioi 2) := by
  let C : Real := Classical.choose exists_thetaError_bound_div_log_sq
  have hC := Classical.choose_spec exists_thetaError_bound_div_log_sq
  have hC0 : 0 <= C := hC.1
  let A : Real := C * (1 / log 2 + 1 / log 2 ^ 2)
  have hlogTwo : 0 < log (2 : Real) := log_pos (by norm_num)
  have hdom : IntegrableOn (fun t : Real => A * (t ^ (-1 : Int) / log t ^ 2))
      (Set.Ioi 2) := by
    convert (integrableOn_inv_div_log_sq_Ioi
      (by norm_num : (1 : Real) < 2)).const_mul A using 1
    simp only [zpow_neg_one]
    rfl
  have hthetaMeas : Measurable Chebyshev.theta := Chebyshev.theta_mono.measurable
  have hmeas : Measurable (fun t : Real =>
      (Chebyshev.theta t - t) * (1 + log t) / (t ^ 2 * log t ^ 2)) := by
    fun_prop
  apply Integrable.mono' hdom hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htTwo : 2 < t := ht
  have ht0 : 0 < t := by linarith
  have htOne : 1 < t := by linarith
  have hlog : 0 < log t := log_pos htOne
  have hlogLe : log (2 : Real) <= log t :=
    log_le_log (by norm_num : (0 : Real) < 2) htTwo.le
  have hinv : 1 / log t <= 1 / log 2 :=
    one_div_le_one_div_of_le hlogTwo hlogLe
  have hinvSq : 1 / log t ^ 2 <= 1 / log 2 ^ 2 := by
    apply one_div_le_one_div_of_le (sq_pos_of_pos hlogTwo)
    nlinarith
  have hmain := hC.2 t htTwo.le
  change _ <= C * (1 / log 2 + 1 / log 2 ^ 2) *
    (t ^ (-1 : Int) / log t ^ 2)
  rw [Real.norm_eq_abs, abs_div, abs_mul,
    abs_of_pos (by positivity : 0 < 1 + log t),
    abs_of_pos (by positivity : 0 < t ^ 2 * log t ^ 2)]
  calc
    abs (Chebyshev.theta t - t) * (1 + log t) / (t ^ 2 * log t ^ 2)
        <= (C * t / log t ^ 2) * (1 + log t) / (t ^ 2 * log t ^ 2) := by
      gcongr
    _ = C * (1 / log t + 1 / log t ^ 2) *
        (t ^ (-1 : Int) / log t ^ 2) := by
      rw [zpow_neg_one]
      field_simp
      ring
    _ <= _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add hinv hinvSq) hC0) (by positivity)

end PrimeFactorOscillations
