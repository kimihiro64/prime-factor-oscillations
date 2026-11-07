/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Helpers.EulerRealHalfIntegerBounds
import PrimeFactorOscillations.Helpers.XiZetaMultiplicity

/-! # The coprimality-probability Dirichlet carrier -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations

open scoped Topology

def coprimalityProbability (n : Nat) : Real := (Nat.totient n : Real) / n

def coprimalityDirichletCarrier (s : Complex) : Complex := riemannZeta s / riemannZeta (s + 1)

def coprimalityTotient : ArithmeticFunction Complex where
  toFun n := (Nat.totient n : Complex)
  map_zero' := by simp

@[simp] theorem coprimalityTotient_apply (n : Nat) :
    coprimalityTotient n = (Nat.totient n : Complex) := rfl

theorem coprimalityProbability_nonneg (n : Nat) : 0 <= coprimalityProbability n := by
  unfold coprimalityProbability
  positivity

theorem coprimalityProbability_le_one (n : Nat) : coprimalityProbability n <= 1 := by
  by_cases hn : n = 0
  case pos => subst n; simp [coprimalityProbability]
  case neg =>
    have hnR : 0 < (n : Real) := by exact_mod_cast Nat.pos_of_ne_zero hn
    unfold coprimalityProbability
    calc
      (Nat.totient n : Real) / n <= (n : Real) / n :=
        div_le_div_of_nonneg_right (by exact_mod_cast Nat.totient_le n) hnR.le
      _ = 1 := div_self hnR.ne'

theorem coprimalityProbability_eq_card_ratio (n : Nat) :
    coprimalityProbability n =
      ((Finset.filter (Nat.Coprime n) (Finset.range n)).card : Real) / n := by
  rw [coprimalityProbability, Nat.totient_eq_card_coprime]

theorem coprimalityTotient_convolution_one :
    LSeries.convolution (fun n => coprimalityTotient n) (fun _ => (1 : Complex)) =
      (fun n : Nat => (n : Complex)) := by
  change LSeries.convolution (fun n => coprimalityTotient n) (1 : Nat -> Complex) = _
  rw [LSeries.convolution_one_eq_convolution_zeta]
  change LSeries.convolution coprimalityTotient
    (ArithmeticFunction.zeta : ArithmeticFunction Complex) = _
  rw [ArithmeticFunction.coe_mul]
  funext n
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  change (Finset.sum n.divisors (fun d => (Nat.totient d : Complex))) = (n : Complex)
  exact_mod_cast Nat.sum_totient n

theorem coprimalityTotient_LSeriesSummable (s : Complex) (hs : 1 < s.re) :
    LSeriesSummable (fun n => coprimalityTotient n) (s + 1) := by
  apply LSeriesSummable_of_le_const_mul_rpow (x := 2)
  case hs => simpa only [Complex.add_re, Complex.one_re] using (show 2 < s.re + 1 by linarith)
  refine Exists.intro 1 ?_
  intro n hn
  change norm (Nat.totient n : Complex) <= 1 * (n : Real) ^ ((2 : Real) - 1)
  norm_num only [show (2 : Real) - 1 = 1 by norm_num, Real.rpow_one, one_mul, Complex.norm_natCast]
  exact_mod_cast Nat.totient_le n

theorem coprimality_probability_term (s : Complex) (n : Nat) :
    LSeries.term (fun n => (coprimalityProbability n : Complex)) s n =
      LSeries.term (fun n => coprimalityTotient n) (s + 1) n := by
  by_cases hn : n = 0
  case pos => subst n; simp
  case neg =>
    rw [eulerTerm_successor _ _ _ hn, LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    simp only [coprimalityProbability, Complex.ofReal_div, Complex.ofReal_natCast, coprimalityTotient_apply]
    ring

theorem coprimality_probability_LSeriesSummable (s : Complex) (hs : 1 < s.re) :
    LSeriesSummable (fun n => (coprimalityProbability n : Complex)) s := by
  unfold LSeriesSummable
  exact (coprimalityTotient_LSeriesSummable s hs).congr
    (fun n => (coprimality_probability_term s n).symm)

theorem coprimalityDirichletCarrier_eq_LSeries (s : Complex) (hs : 1 < s.re) :
    coprimalityDirichletCarrier s = LSeries (fun n => (coprimalityProbability n : Complex)) s := by
  have hs1 : 1 < (s + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have ht := coprimalityTotient_LSeriesSummable s hs
  have h1 := LSeriesSummable_one_iff.mpr hs1
  have hconv := LSeries_convolution' ht h1
  have hcone : LSeries.convolution (fun n => coprimalityTotient n) (1 : Nat -> Complex) =
      (fun n : Nat => (n : Complex)) := coprimalityTotient_convolution_one
  rw [hcone, LSeries_one_eq_riemannZeta hs1] at hconv
  have hnat : LSeries (fun n => (n : Complex)) (s + 1) = riemannZeta s := by
    rw [<- LSeries_one_eq_riemannZeta hs]
    apply tsum_congr
    intro n
    by_cases hn : n = 0
    case pos => subst n; simp
    case neg =>
      rw [eulerTerm_successor _ _ _ hn, LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
      have hnC : Not ((n : Complex) = 0) := by exact_mod_cast hn
      field_simp <;> simp
  rw [hnat] at hconv
  have hn : Not (riemannZeta (s + 1) = 0) := riemannZeta_ne_zero_of_one_le_re hs1.le
  have heq : LSeries (fun n => coprimalityTotient n) (s + 1) =
      LSeries (fun n => (coprimalityProbability n : Complex)) s :=
    tsum_congr (fun n => (coprimality_probability_term s n).symm)
  rw [heq] at hconv
  unfold coprimalityDirichletCarrier
  exact (div_eq_iff hn).mpr hconv

theorem coprimalityDirichletCarrier_analyticAt (w : Complex) (hw : 0 < w.re)
    (hw1 : Not (w = 1)) : AnalyticAt Complex coprimalityDirichletCarrier w := by
  have hs : 1 < (w + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have hn : Not (riemannZeta (w + 1) = 0) := riemannZeta_ne_zero_of_one_le_re hs.le
  have hne : Not (w + 1 = 1) := by intro h; have hh := congrArg Complex.re h; simp at hh; linarith
  exact (analyticOn_riemannZeta w hw1).div
    ((analyticOn_riemannZeta (w + 1) hne).comp (f := fun z : Complex => z + 1)
      (analyticAt_id.add analyticAt_const)) hn

theorem analyticOrderAt_coprimalityDirichletCarrier (w : Complex) (hw : 0 < w.re)
    (hw1 : Not (w = 1)) :
    analyticOrderAt coprimalityDirichletCarrier w = analyticOrderAt riemannZeta w := by
  have hs : 1 < (w + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have hn : Not (riemannZeta (w + 1) = 0) := riemannZeta_ne_zero_of_one_le_re hs.le
  have hne : Not (w + 1 = 1) := by intro h; have hh := congrArg Complex.re h; simp at hh; linarith
  have hden : AnalyticAt Complex (fun z => riemannZeta (z + 1)) w :=
    (analyticOn_riemannZeta (w + 1) hne).comp (f := fun z : Complex => z + 1)
      (analyticAt_id.add analyticAt_const)
  have hinv := hden.inv hn
  have hz := analyticOn_riemannZeta w hw1
  change analyticOrderAt (fun z => riemannZeta z / riemannZeta (z + 1)) w = _
  simp only [div_eq_mul_inv]
  have hmul := analyticOrderAt_mul hz hinv
  change analyticOrderAt (fun z => riemannZeta z * Inv.inv (riemannZeta (z + 1))) w =
    analyticOrderAt riemannZeta w + analyticOrderAt (fun z => Inv.inv (riemannZeta (z + 1))) w at hmul
  rw [hmul]
  have hunit : analyticOrderAt (fun z => Inv.inv (riemannZeta (z + 1))) w = 0 :=
    hinv.analyticOrderAt_eq_zero.mpr (inv_ne_zero hn)
  rw [hunit, add_zero]

theorem analyticOrderNatAt_coprimalityDirichletCarrier (w : Complex) (hw : 0 < w.re)
    (hw1 : Not (w = 1)) :
    analyticOrderNatAt coprimalityDirichletCarrier w = analyticOrderNatAt riemannZeta w := by
  unfold analyticOrderNatAt
  rw [analyticOrderAt_coprimalityDirichletCarrier w hw hw1]

theorem analyticOrderAt_coprimalityDirichletCarrier_ne_top (w : Complex) (hw : 0 < w.re)
    (hw1 : Not (w = 1)) : Not (analyticOrderAt coprimalityDirichletCarrier w = Top.top) := by
  rw [analyticOrderAt_coprimalityDirichletCarrier w hw hw1, <- analyticOrderAt_xi_eq_zeta hw hw1]
  exact analyticOrderAt_xi_ne_top w

end PrimeFactorOscillations
