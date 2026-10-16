/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.NumberTheory.LSeries.SumCoeff
import PrimeFactorOscillations.Helpers.DirichletZeroReadout

/-!
# Dirichlet Packet Mellin

Mellin representations and analytic error continuation for von Mangoldt character coefficients.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.DirichletPacketMellin

open Filter Asymptotics MeasureTheory

def coefficient {q : Nat} (chi : DirichletCharacter Complex q) (n : Nat) : Complex :=
  chi n * (ArithmeticFunction.vonMangoldt n : Complex)

def correction {q : Nat} (chi : DirichletCharacter Complex q)
    (a : Nat -> Complex) (s : Complex) : Complex :=
  LSeries (fun n => a n - coefficient chi n) s

def continuation {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    (a : Nat -> Complex) (s : Complex) : Complex :=
  DirichletZeroReadout.readout chi (correction chi a) s

theorem correction_abscissa_le_zero {q : Nat}
    (chi : DirichletCharacter Complex q) (a : Nat -> Complex) (C : Real)
    (herror : forall n : Nat, Not (n = 0) ->
      norm (a n - coefficient chi n) <= C / (n : Real)) :
    LSeries.abscissaOfAbsConv (fun n => a n - coefficient chi n) <= 0 := by
  have h := LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow (x := (-1 : Real))
    (Exists.intro C (by
      intro n hn
      simpa only [Real.rpow_neg_one, div_eq_mul_inv] using herror n hn))
  rw [<- EReal.coe_one, <- EReal.coe_add] at h
  norm_num at h
  exact h

theorem analyticOnNhd_correction {q : Nat}
    (chi : DirichletCharacter Complex q) (a : Nat -> Complex) (C : Real)
    (herror : forall n : Nat, Not (n = 0) ->
      norm (a n - coefficient chi n) <= C / (n : Real)) :
    AnalyticOnNhd Complex (correction chi a) {s : Complex | 0 < s.re} := by
  have hab := correction_abscissa_le_zero chi a C herror
  intro s hs
  apply LSeries_analyticOnNhd (fun n => a n - coefficient chi n) s
  exact hab.trans_lt (by exact_mod_cast hs)

theorem continuation_eq_LSeries {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (a : Nat -> Complex) (C : Real)
    (herror : forall n : Nat, Not (n = 0) ->
      norm (a n - coefficient chi n) <= C / (n : Real))
    (s : Complex) (hs : 1 < s.re) :
    continuation chi a s = LSeries a s := by
  let e : Nat -> Complex := fun n => a n - coefficient chi n
  have he : LSeriesSummable e s := by
    apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
    exact (correction_abscissa_le_zero chi a C herror).trans_lt
      (by exact_mod_cast (zero_lt_one.trans hs))
  have hf : LSeriesSummable (coefficient chi) s :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt chi hs
  have ha : a = coefficient chi + e := by
    funext n
    simp only [Pi.add_apply, e]
    ring
  rw [ha, LSeries_add hf he]
  have hId : LSeries (coefficient chi) s =
      -logDeriv (DirichletCharacter.LFunction chi) s := by
    rw [logDeriv_apply, <- neg_div,
      DirichletCharacter.deriv_LFunction_eq_deriv_LSeries chi hs,
      DirichletCharacter.LFunction_eq_LSeries chi hs]
    exact DirichletCharacter.LSeries_twist_vonMangoldt_eq chi hs
  unfold continuation DirichletZeroReadout.readout correction
  rw [<- hId]
  congr 1
  apply LSeries_congr
  intro n hn
  simp only [Pi.add_apply, e]
  ring

theorem coefficient_norm_le_nat {q : Nat}
    (chi : DirichletCharacter Complex q) (n : Nat) :
    norm (coefficient chi n) <= n := by
  by_cases hn : n = 0
  . subst n
    simp [coefficient]
  . have hnpos : (0 : Real) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hnorm : norm (coefficient chi n) <= ArithmeticFunction.vonMangoldt n := by
      unfold coefficient
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (chi.norm_le_one _)
    have hlog : Real.log (n : Real) <= n := by
      have h := Real.log_le_sub_one_of_pos hnpos
      linarith
    exact hnorm.trans (ArithmeticFunction.vonMangoldt_le_log.trans hlog)

theorem sum_norm_bigO {q : Nat} (chi : DirichletCharacter Complex q)
    (a : Nat -> Complex) (C : Real) (hC : 0 <= C)
    (herror : forall n : Nat, Not (n = 0) ->
      norm (a n - coefficient chi n) <= C / (n : Real)) :
    (fun n : Nat => (Finset.Icc 1 n).sum (fun k => norm (a k))) =O[atTop]
      (fun n : Nat => (n : Real) ^ (2 : Real)) := by
  apply IsBigO.of_bound (C + 1)
  filter_upwards [eventually_ge_atTop (1 : Nat)] with n hn
  have hnR : (1 : Real) <= n := by exact_mod_cast hn
  have hm (k : Nat) (hk : Membership.mem (Finset.Icc 1 n) k) :
      norm (a k) <= (C + 1) * (n : Real) := by
    have hks := Finset.mem_Icc.mp hk
    have hkR : (1 : Real) <= k := by exact_mod_cast hks.1
    have hkn : (k : Real) <= n := by exact_mod_cast hks.2
    have he := herror k (by omega)
    have hdiv : C / (k : Real) <= C := by
      calc
        _ <= C / 1 := div_le_div_of_nonneg_left hC zero_lt_one hkR
        _ = C := div_one _
    have htri := norm_le_norm_sub_add (a k) (coefficient chi k)
    have hc := coefficient_norm_le_nat chi k
    nlinarith
  have hs := Finset.sum_le_sum (fun k hk => hm k hk)
  have hcard : (Finset.Icc 1 n).card = n := by simp
  have hsum : (Finset.Icc 1 n).sum (fun k => norm (a k)) <= (C + 1) * (n : Real) ^ 2 := by
    calc
      _ <= (Finset.Icc 1 n).sum (fun _ => (C + 1) * (n : Real)) := hs
      _ = _ := by rw [Finset.sum_const, hcard, nsmul_eq_mul]; ring
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun k _ => norm_nonneg _)),
    Real.rpow_two, abs_of_nonneg (sq_nonneg (n : Real))] using hsum

theorem mellin_identity {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (a : Nat -> Complex) (C : Real) (hC : 0 <= C)
    (herror : forall n : Nat, Not (n = 0) ->
      norm (a n - coefficient chi n) <= C / (n : Real))
    (s : Complex) (hs : 2 < s.re) :
    continuation chi a s = s * integral (volume.restrict (Set.Ioi (1 : Real)))
      (fun t : Real => (Finset.Icc 1 (Nat.floor t)).sum a * (t : Complex) ^ (-(s + 1))) := by
  rw [continuation_eq_LSeries chi a C herror s (by linarith)]
  exact LSeries_eq_mul_integral' a (by norm_num : (0 : Real) <= 2) hs
    (sum_norm_bigO chi a C hC herror)

theorem zero_readout {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (a : Nat -> Complex) (C : Real)
    (herror : forall n : Nat, Not (n = 0) ->
      norm (a n - coefficient chi n) <= C / (n : Real))
    (rho : Complex) (hr : 0 < rho.re) (hOne : Not (rho = 1)) :
    meromorphicOrderAt (continuation chi a) rho = -1 <->
      DirichletCharacter.LFunction chi rho = 0 :=
  DirichletZeroReadout.readout_order_iff_zero chi rho hOne (correction chi a)
    (analyticOnNhd_correction chi a C herror rho hr)

end PrimeFactorOscillations.DirichletPacketMellin
