/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import OAI.NumberTheory.DirichletL.Detector.HighEulerRational
import OAI.NumberTheory.DirichletL.Hecke.Euler

/-!
# The actual principal Euler factor below the old seven-eighths boundary

At w = 1 and z = 1/6, the source j = 0 local expression simplifies to
the rational factor defined below. Its two moving denominators cannot
vanish for Re(s) > 1/2 and unit-bounded arithmetic phases. This proves
analyticity of each actual rational factor. Normal convergence of the
infinite prime product and the complete compensated probe remain separate.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.PrincipalEulerContinuation

def localD (Q : Real) (eta s : Complex) : Complex :=
  eta * Complex.exp (-s * (Real.log Q : Complex))

def localR (Q : Real) (a s : Complex) : Complex :=
  a ^ 2 * Complex.exp (((3 : Complex) - 6 * s) * (Real.log Q : Complex))

def principalFactor (Q : Real) (eta a s : Complex) : Complex :=
  let t : Complex := 1 / (Q : Complex)
  (1 - t ^ 2) *
    ((1 - localD Q eta s) + t * (localD Q eta s - localR Q a s)) /
    ((1 - localR Q a s) * (1 - localD Q eta s))

def principalPstar (Q : Real) (eta a s : Complex) : Complex :=
  (1 + 1 / (Q : Complex)) * (localR Q a s - localD Q eta s) /
    (1 - localR Q a s)

def originalPrincipalFactor (Q : Real) (eta a s : Complex) : Complex :=
  let t : Complex := 1 / (Q : Complex)
  (1 / (1 - t) + t / (1 - t) + principalPstar Q eta a s) *
    (1 - t) ^ 2 / (1 - localD Q eta s)

theorem localD_norm_le (Q : Real) (eta s : Complex) (heta : norm eta <= 1) :
    norm (localD Q eta s) <= Real.exp (-s.re * Real.log Q) := by
  dsimp [localD]
  rw [norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_le_of_le_one_left (Real.exp_nonneg _) heta

theorem localR_norm_le (Q : Real) (a s : Complex) (ha : norm a <= 1) :
    norm (localR Q a s) <= Real.exp ((3 - 6 * s.re) * Real.log Q) := by
  have ha2 : norm (a ^ 2) <= 1 := by
    rw [norm_pow]
    nlinarith [norm_nonneg a]
  have hre :
      (((3 : Complex) - 6 * s) * (Real.log Q : Complex)).re =
        (3 - 6 * s.re) * Real.log Q := by
    simp [Complex.mul_re]
  dsimp [localR]
  rw [norm_mul, Complex.norm_exp, hre]
  exact mul_le_of_le_one_left (Real.exp_nonneg _) ha2

theorem moving_denominators (Q : Real) (eta a s : Complex)
    (hQ : 2 <= Q) (heta : norm eta <= 1) (ha : norm a <= 1)
    (hs : 1 / 2 < s.re) :
    And (Not (1 - localD Q eta s = 0)) (Not (1 - localR Q a s = 0)) := by
  have hlog : 0 < Real.log Q := Real.log_pos (by linarith)
  have hD : norm (localD Q eta s) < 1 := by
    refine (localD_norm_le Q eta s heta).trans_lt ?_
    calc
      Real.exp (-s.re * Real.log Q) < Real.exp 0 := by
        apply Real.exp_lt_exp.mpr
        nlinarith [mul_pos (show 0 < s.re by linarith) hlog]
      _ = 1 := Real.exp_zero
  have hR : norm (localR Q a s) < 1 := by
    refine (localR_norm_le Q a s ha).trans_lt ?_
    calc
      Real.exp ((3 - 6 * s.re) * Real.log Q) < Real.exp 0 := by
        apply Real.exp_lt_exp.mpr
        have hp := mul_pos (show 0 < 6 * s.re - 3 by linarith) hlog
        nlinarith
      _ = 1 := Real.exp_zero
  constructor
  . intro h
    have heq : (1 : Complex) = localD Q eta s := sub_eq_zero.mp h
    rw [<- heq, norm_one] at hD
    exact (lt_irrefl (1 : Real)) hD
  . intro h
    have heq : (1 : Complex) = localR Q a s := sub_eq_zero.mp h
    rw [<- heq, norm_one] at hR
    exact (lt_irrefl (1 : Real)) hR

theorem principal_factor_identity (Q : Real) (eta a s : Complex)
    (hQ : 2 <= Q) (heta : norm eta <= 1) (ha : norm a <= 1)
    (hs : 1 / 2 < s.re) :
    originalPrincipalFactor Q eta a s = principalFactor Q eta a s := by
  have hn := moving_denominators Q eta a s hQ heta ha hs
  have hQ0 : Not ((Q : Complex) = 0) := by
    exact_mod_cast (show Not (Q = 0) by linarith)
  have hQ1 : Not ((Q : Complex) - 1 = 0) := by
    intro h
    have h : (Q : Complex) = 1 := sub_eq_zero.mp h
    have h' : Q = 1 := by exact_mod_cast h
    linarith
  dsimp [originalPrincipalFactor, principalFactor, principalPstar]
  field_simp [hn.1, hn.2, hQ0, hQ1]
  ring

theorem principal_factor_analyticAt (Q : Real) (eta a s : Complex)
    (hQ : 2 <= Q) (heta : norm eta <= 1) (ha : norm a <= 1)
    (hs : 1 / 2 < s.re) :
    AnalyticAt Complex (principalFactor Q eta a) s := by
  have hn := moving_denominators Q eta a s hQ heta ha hs
  have hD : AnalyticAt Complex (localD Q eta) s := by
    unfold localD
    fun_prop
  have hR : AnalyticAt Complex (localR Q a) s := by
    unfold localR
    fun_prop
  have hnum : AnalyticAt Complex
      (fun v : Complex => (1 - (1 / (Q : Complex)) ^ 2) *
        ((1 - localD Q eta v) + (1 / (Q : Complex)) *
          (localD Q eta v - localR Q a v))) s := by
    fun_prop
  have hden : AnalyticAt Complex
      (fun v : Complex => (1 - localR Q a v) * (1 - localD Q eta v)) s := by
    fun_prop
  exact hnum.div hden (mul_ne_zero hn.2 hn.1)

theorem exp_neg_le_half (u : Real) (hu : 1 <= u) :
    Real.exp (-u) <= 1 / 2 := by
  have hlarge : 2 <= Real.exp u := by
    linarith [Real.add_one_le_exp u]
  have hcancel : Real.exp u * Real.exp (-u) = 1 := by
    rw [<- Real.exp_add]
    simp
  have hprod := mul_nonneg (Real.exp_nonneg (-u))
    (show 0 <= Real.exp u - 2 by linarith)
  nlinarith

theorem rational_defect_identity (t D R : Complex)
    (hD : Not (1 - D = 0)) (hR : Not (1 - R = 0)) :
    (1 - t ^ 2) * ((1 - D) + t * (D - R)) / ((1 - R) * (1 - D)) - 1 =
      (R - t ^ 2) / (1 - R) +
        t * (1 - t ^ 2) * (D - R) / ((1 - R) * (1 - D)) := by
  field_simp [hD, hR]
  ring

private theorem norm_div_from_lower (a b : Complex) (c T : Real)
    (hc : 0 < c) (hb : c <= norm b) (ha : norm a <= c * T) :
    norm (a / b) <= T := by
  rw [norm_div]
  have hb0 : Not (norm b = 0) := ne_of_gt (lt_of_lt_of_le hc hb)
  have hcancel : norm a / norm b * norm b = norm a := by field_simp
  have hn : 0 <= norm a / norm b := div_nonneg (norm_nonneg _) (norm_nonneg _)
  have hprod := mul_nonneg hn (sub_nonneg.mpr hb)
  nlinarith

theorem rational_defect_bound (t D R : Complex) (T : Real)
    (ht : norm t <= 1 / 2) (hD : norm D <= 1 / 2) (hR : norm R <= 1 / 2)
    (hRt : norm R <= T) (htt : norm t ^ 2 <= T)
    (htD : norm t * norm D <= T) (htR : norm t * norm R <= T) :
    norm ((1 - t ^ 2) * ((1 - D) + t * (D - R)) /
      ((1 - R) * (1 - D)) - 1) <= 20 * T := by
  have hbd : 1 / 2 <= norm (1 - D) := by
    have h := norm_sub_norm_le (1 : Complex) D
    simp only [norm_one] at h
    linarith
  have hbr : 1 / 2 <= norm (1 - R) := by
    have h := norm_sub_norm_le (1 : Complex) R
    simp only [norm_one] at h
    linarith
  have hnD : Not (1 - D = 0) := by
    intro h
    rw [h, norm_zero] at hbd
    linarith
  have hnR : Not (1 - R = 0) := by
    intro h
    rw [h, norm_zero] at hbr
    linarith
  have hbdprod : 1 / 4 <= norm ((1 - R) * (1 - D)) := by
    rw [norm_mul]
    nlinarith [mul_nonneg (show 0 <= norm (1 - R) - 1 / 2 by linarith)
      (show 0 <= norm (1 - D) - 1 / 2 by linarith)]
  have hfirst : norm (R - t ^ 2) <= 2 * T := by
    have h := norm_sub_le R (t ^ 2)
    simp only [norm_pow] at h
    linarith
  have ht2 : norm t ^ 2 <= 1 := by
    nlinarith [mul_nonneg (norm_nonneg t) (show 0 <= 1 / 2 - norm t by linarith)]
  have hfac : norm (1 - t ^ 2) <= 2 := by
    have h := norm_sub_le (1 : Complex) (t ^ 2)
    simp only [norm_one, norm_pow] at h
    linarith
  have hcolumn : norm t * norm (D - R) <= 2 * T := by
    have h := mul_le_mul_of_nonneg_left (norm_sub_le D R) (norm_nonneg t)
    nlinarith
  have hsecond : norm (t * (1 - t ^ 2) * (D - R)) <= 4 * T := by
    calc
      norm (t * (1 - t ^ 2) * (D - R)) =
          norm (1 - t ^ 2) * (norm t * norm (D - R)) := by
        simp only [norm_mul]
        ring
      _ <= 2 * (2 * T) := mul_le_mul hfac hcolumn
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
      _ = 4 * T := by ring
  have hb1 : norm ((R - t ^ 2) / (1 - R)) <= 4 * T :=
    norm_div_from_lower _ _ (1 / 2) (4 * T) (by norm_num) hbr (by linarith)
  have hb2 : norm (t * (1 - t ^ 2) * (D - R) / ((1 - R) * (1 - D))) <= 16 * T :=
    norm_div_from_lower _ _ (1 / 4) (16 * T) (by norm_num) hbdprod (by linarith)
  rw [rational_defect_identity t D R hnD hnR]
  exact (norm_add_le _ _).trans (by linarith)

theorem principal_factor_uniform_defect (Q : Real) (eta a s : Complex)
    (hQ : Real.exp 2 <= Q) (heta : norm eta <= 1) (ha : norm a <= 1)
    (hs : 3 / 4 <= s.re) :
    norm (principalFactor Q eta a s - 1) <=
      20 * Real.exp (-(3 / 2) * Real.log Q) := by
  have hQpos : 0 < Q := lt_of_lt_of_le (Real.exp_pos 2) hQ
  have hlog : 2 <= Real.log Q := by
    have h := Real.log_le_log (Real.exp_pos 2) hQ
    simpa using h
  have hlog0 : 0 <= Real.log Q := by linarith
  let t : Complex := 1 / (Q : Complex)
  let D := localD Q eta s
  let R := localR Q a s
  let T := Real.exp (-(3 / 2) * Real.log Q)
  have ht : norm t = Real.exp (-Real.log Q) := by
    dsimp [t]
    rw [norm_div, norm_one]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQpos]
    rw [Real.exp_neg, Real.exp_log hQpos]
    simp only [one_div]
  have hDnorm : norm D <= Real.exp (-s.re * Real.log Q) :=
    localD_norm_le Q eta s heta
  have hRnorm : norm R <= Real.exp ((3 - 6 * s.re) * Real.log Q) :=
    localR_norm_le Q a s ha
  have hthalf : norm t <= 1 / 2 := by
    rw [ht]
    exact exp_neg_le_half _ (by linarith)
  have hDhalf : norm D <= 1 / 2 := by
    apply hDnorm.trans
    have hu : 1 <= s.re * Real.log Q := by
      nlinarith [mul_nonneg (show 0 <= s.re - 3 / 4 by linarith) hlog0]
    simpa only [neg_mul] using exp_neg_le_half _ hu
  have hRhalf : norm R <= 1 / 2 := by
    apply hRnorm.trans
    have hu : 1 <= (6 * s.re - 3) * Real.log Q := by
      nlinarith [mul_nonneg (show 0 <= s.re - 3 / 4 by linarith) hlog0]
    convert exp_neg_le_half _ hu using 1
    congr 1
    ring
  have hRt : norm R <= T := by
    apply hRnorm.trans
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (show 0 <= s.re - 3 / 4 by linarith) hlog0]
  have htt : norm t ^ 2 <= T := by
    rw [ht, pow_two, <- Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have htD : norm t * norm D <= T := by
    rw [ht]
    calc
      Real.exp (-Real.log Q) * norm D <=
          Real.exp (-Real.log Q) * Real.exp (-s.re * Real.log Q) :=
        mul_le_mul_of_nonneg_left hDnorm (Real.exp_nonneg _)
      _ = Real.exp (-Real.log Q + -s.re * Real.log Q) := (Real.exp_add _ _).symm
      _ <= T := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg (show 0 <= s.re - 1 / 2 by linarith) hlog0]
  have htR : norm t * norm R <= T :=
    (mul_le_of_le_one_left (norm_nonneg R) (show norm t <= 1 by linarith)).trans hRt
  change norm ((1 - t ^ 2) * ((1 - D) + t * (D - R)) /
    ((1 - R) * (1 - D)) - 1) <= 20 * T
  exact rational_defect_bound t D R T hthalf hDhalf hRhalf hRt htt htD htR

end PrimeFactorOscillations.PrincipalEulerContinuation
