/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import PrimeFactorOscillations.Helpers.LPFPrimeTargetMoment
import PrimeFactorOscillations.Helpers.LPFSievePrimeCutoff

/-!
# Numerical Euler-product bounds for LPF overlap

The constants are uniform in the prime cutoff and growing moment order.
The shifted product uses the proved prime-log sum and a convergent p-series,
with no unspecified Mertens error constant.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem lpf_overlap_inverse_square_Ioc_tail (a N : Nat) (ha : 1 <= a) (hAN : a <= N) :
    Finset.sum (Finset.Ioc a N) (fun p => 1 / (p : Real) ^ 2) <=
      1 / (a : Real) - 1 / (N : Real) := by
  induction N, hAN using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ioc_succ_top hn]
    have hnPos : (0 : Real) < (n : Real) := by exact_mod_cast (ha.trans hn)
    have hId : 1 / (n : Real) - 1 / ((n : Real) + 1) =
        1 / ((n : Real) * ((n : Real) + 1)) := by field_simp <;> ring
    have hStep : 1 / ((n : Real) + 1) ^ 2 <=
        1 / (n : Real) - 1 / ((n : Real) + 1) := by
      rw [hId]
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith only [hnPos]
    push_cast
    linarith only [ih, hStep]

theorem lpf_overlap_inverse_square_subset_tail (P : Finset Nat) (a N : Nat)
    (ha : 1 <= a) (hP : forall p, Membership.mem P p -> And (a < p) (p < N)) :
    Finset.sum P (fun p => 1 / (p : Real) ^ 2) <= 1 / (a : Real) := by
  by_cases hAN : a <= N
  next =>
    have hSub : P <= Finset.Ioc a N := by
      intro p hp
      exact Finset.mem_Ioc.mpr (And.intro (hP p hp).1 (hP p hp).2.le)
    have hSum := Finset.sum_le_sum_of_subset_of_nonneg hSub
      (fun p _ _ => by positivity : forall p, Membership.mem (Finset.Ioc a N) p ->
        Not (Membership.mem P p) -> 0 <= 1 / (p : Real) ^ 2)
    have hBound := lpf_overlap_inverse_square_Ioc_tail a N ha hAN
    have hNonneg : 0 <= 1 / (N : Real) := by positivity
    exact hSum.trans (by linarith only [hBound, hNonneg])
  next =>
    have hSum : Finset.sum P (fun p => 1 / (p : Real) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      have h := hP p hp
      omega
    rw [hSum]
    positivity

private theorem lpf_nonneg_product_compare (P : Finset Nat) (f g : Nat -> Real)
    (h0 : forall p, Membership.mem P p -> 0 <= f p)
    (hle : forall p, Membership.mem P p -> f p <= g p) :
    Finset.prod P f <= Finset.prod P g := by
  classical
  revert h0 hle
  induction P using Finset.induction_on with
  | empty => intro _ _; simp
  | @insert p P hp ih =>
    intro h0 hle
    have h0P := fun r hr => h0 r (Finset.mem_insert_of_mem hr)
    have hleP := fun r hr => hle r (Finset.mem_insert_of_mem hr)
    rw [Finset.prod_insert hp, Finset.prod_insert hp]
    exact mul_le_mul (hle p (Finset.mem_insert_self p P)) (ih h0P hleP)
      (Finset.prod_nonneg h0P)
      ((h0 p (Finset.mem_insert_self p P)).trans (hle p (Finset.mem_insert_self p P)))

theorem singular_high_euler_product_uniform_le (P : Finset Nat) (N q : Nat)
    (hq : 1 <= q)
    (hP : forall p, Membership.mem P p -> And (2 * q + 2 < p) (p < N)) :
    Finset.prod P (fun p => 1 + (singularFactor p ^ q - 1) / ((p : Real) - 1)) <=
      Real.exp 3 := by
  have hSum := lpf_overlap_inverse_square_subset_tail P (2 * q + 2) N (by omega) hP
  have hBound : 6 * (q : Real) * Finset.sum P (fun p => 1 / (p : Real) ^ 2) <= 3 := by
    have hScaled := mul_le_mul_of_nonneg_left hSum
      (by positivity : 0 <= 6 * (q : Real))
    have hScale : 6 * (q : Real) * (1 / ((2 * q + 2 : Nat) : Real)) <= 3 := by
      apply (mul_le_mul_iff_of_pos_right
        (by positivity : 0 < ((2 * q + 2 : Nat) : Real))).mp
      have hEq : (6 * (q : Real) * (1 / ((2 * q + 2 : Nat) : Real))) *
          ((2 * q + 2 : Nat) : Real) = 6 * (q : Real) := by field_simp
      rw [hEq]
      push_cast
      linarith
    exact hScaled.trans hScale
  calc
    _ <= Finset.prod P (fun p => Real.exp (6 * (q : Real) / (p : Real) ^ 2)) := by
      apply lpf_nonneg_product_compare
      next =>
        intro p hp
        have hp3 : 3 <= p := by have h := (hP p hp).1; omega
        have hWeight := singular_moment_weight_nonneg p q hp3
        have hDen : (0 : Real) <= (p : Real) - 1 := by
          have h : (3 : Real) <= (p : Real) := by exact_mod_cast hp3
          linarith
        exact add_nonneg zero_le_one (div_nonneg hWeight hDen)
      next =>
        intro p hp
        have hTerm := singular_high_euler_term_le p q hq (hP p hp).1
        have hExp := Real.add_one_le_exp (6 * (q : Real) / (p : Real) ^ 2)
        linarith
    _ = Real.exp (6 * (q : Real) * Finset.sum P (fun p => 1 / (p : Real) ^ 2)) := by
      rw [<- Real.exp_sum, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ <= _ := Real.exp_le_exp.mpr hBound

theorem lpf_singular_rankin_local (p : Nat) (delta : Real)
    (hp : 5 <= p) (hd : 0 <= delta) :
    singularFactor p * (1 - (p : Real) ^ (-(1 + delta))) <=
      Real.exp ((5 / 4 : Real) * delta * Real.log (p : Real) / (p : Real) +
        1 / ((p : Real) * ((p : Real) - 2))) := by
  have hpR : (5 : Real) <= (p : Real) := by exact_mod_cast hp
  have hpPos : (0 : Real) < (p : Real) := by linarith only [hpR]
  have hp1 : 0 < (p : Real) - 1 := by linarith only [hpR]
  have hp2 : 0 < (p : Real) - 2 := by linarith only [hpR]
  have hLog : 0 <= Real.log (p : Real) := Real.log_nonneg (by linarith only [hpR])
  let t : Real := delta * Real.log (p : Real)
  let v : Real := Real.exp (-t)
  let c : Real := 1 / ((p : Real) * ((p : Real) - 2))
  have ht : 0 <= t := mul_nonneg hd hLog
  have hv : 1 - v <= t := by
    have h := Real.add_one_le_exp (-t)
    change -t + 1 <= v at h
    linarith only [h]
  have hvTop : v <= 1 := by
    dsimp [v]
    exact (Real.exp_le_one_iff).mpr (by linarith only [ht])
  have hPower : (p : Real) ^ (-(1 + delta)) = v / (p : Real) := by
    rw [Real.rpow_def_of_pos hpPos]
    have hExp : Real.log (p : Real) * (-(1 + delta)) = -t - Real.log (p : Real) := by dsimp [t]; ring
    rw [hExp, Real.exp_sub, Real.exp_log hpPos]
  have hRatio : t / ((p : Real) - 1) <= (5 / 4 : Real) * t / (p : Real) := by
    have hDen : 1 / ((p : Real) - 1) <= (5 / 4 : Real) / (p : Real) := by
      apply (mul_le_mul_iff_of_pos_right (by linarith : 0 < (p : Real) - 1)).mp
      have hCancel : (1 / ((p : Real) - 1)) * ((p : Real) - 1) = 1 := by field_simp [hp1.ne']
      rw [hCancel]
      apply (mul_le_mul_iff_of_pos_right hpPos).mp
      field_simp
      linarith only [hpR]
    have h := mul_le_mul_of_nonneg_left hDen ht
    convert h using 1 <;> ring
  have hFirst : 1 + (1 - v) / ((p : Real) - 1) <=
      Real.exp ((5 / 4 : Real) * t / (p : Real)) := by
    have hDiv := div_le_div_of_nonneg_right hv (by linarith : 0 <= (p : Real) - 1)
    have hExp := Real.add_one_le_exp ((5 / 4 : Real) * t / (p : Real))
    linarith only [hDiv, hRatio, hExp]
  have hSecond : 1 + c <= Real.exp c := by
    have h := Real.add_one_le_exp c
    linarith only [h]
  have hIdentity : singularFactor p * (1 - (p : Real) ^ (-(1 + delta))) =
      (1 + (1 - v) / ((p : Real) - 1)) * (1 + c) := by
    rw [hPower]
    dsimp [singularFactor, c]
    field_simp [hp1.ne', hp2.ne', hpPos.ne'] <;> ring
  rw [hIdentity]
  have hFirstNonneg : 0 <= 1 + (1 - v) / ((p : Real) - 1) := by
    have hDiv := div_nonneg (sub_nonneg.mpr hvTop) (by linarith : 0 <= (p : Real) - 1)
    linarith only [hDiv]
  have hc : 0 <= c := by dsimp [c]; positivity
  have h := mul_le_mul hFirst hSecond (by positivity) (Real.exp_pos _).le
  calc
    _ <= Real.exp ((5 / 4 : Real) * t / (p : Real)) * Real.exp c := h
    _ = _ := by rw [<- Real.exp_add]; congr 1; dsimp [t, c]; ring


theorem lpf_rankin_pseries_bound (delta : Real) (hd : 0 < delta) :
    tsum (fun n : Nat => (n : Real) ^ (-(1 + delta))) <= 1 + 1 / delta := by
  have hs : Summable (fun n : Nat => (n : Real) ^ (-(1 + delta))) :=
    Real.summable_nat_rpow.mpr (by linarith only [hd])
  have hAnti : AntitoneOn (fun x : Real => x ^ (-(1 + delta))) (Set.Ici (1 : Real)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (by have h := Set.mem_Ici.mp hx; linarith) hxy
      (by linarith only [hd])
  have hTail := AntitoneOn.tsum_comp_add_le_integral
    (f := fun x : Real => x ^ (-(1 + delta))) 1
    (by simpa only [Nat.cast_one] using hAnti)
    (by simpa only [Nat.cast_one] using
      (integrableOn_Ioi_rpow_of_lt (a := -(1 + delta))
        (by linarith only [hd]) (by norm_num : (0 : Real) < 1)))
    (fun x hx => Real.rpow_nonneg (by have h := Set.mem_Ioi.mp hx; linarith) _)
  simp only [Nat.cast_one] at hTail
  rw [integral_Ioi_rpow_of_lt (a := -(1 + delta))
    (by linarith only [hd]) (by norm_num : (0 : Real) < 1)] at hTail
  have hExp : -(1 + delta) + 1 = -delta := by ring
  rw [hExp, Real.one_rpow] at hTail
  have hInv : -(1 : Real) / (-delta) = 1 / delta := by ring
  rw [hInv] at hTail
  have hSplit := hs.sum_add_tsum_nat_add 2
  have hZero : (0 : Real) ^ (-(1 + delta)) = 0 :=
    Real.zero_rpow (by linarith only [hd])
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
    hZero, Real.one_rpow, zero_add] at hSplit
  have hTail' : tsum (fun n : Nat => ((n + 2 : Nat) : Real) ^ (-(1 + delta))) <= 1 / delta := by
    simpa only [show forall n : Nat, n + 1 + 1 = n + 2 by intro n; omega] using hTail
  linarith only [hSplit, hTail']

theorem lpf_rankin_finite_euler_bound (P : Finset Nat) (delta : Real)
    (hd : 0 < delta) (hP : forall p, Membership.mem P p -> Nat.Prime p) :
    Finset.prod P (fun p => (1 - (p : Real) ^ (-(1 + delta))) ^ (-1 : Int)) <=
      1 + 1 / delta := by
  let f : MonoidHom Nat Real :=
    { toFun := fun n => (n : Real) ^ (-(1 + delta))
      map_one' := by simp
      map_mul' := by
        intro m n
        simp only [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)] }
  have hs : Summable (f : Nat -> Real) :=
    Real.summable_nat_rpow.mpr (by linarith only [hd])
  have hFilter : P.filter Nat.Prime = P := Finset.filter_eq_self.mpr hP
  have hEuler := EulerProduct.prod_filter_prime_geometric_eq_tsum_factoredNumbers hs P
  rw [hFilter] at hEuler
  have hSubset := Summable.tsum_subtype_le (f : Nat -> Real) (Nat.factoredNumbers P)
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _) hs
  calc
    _ = tsum (fun m : Nat.factoredNumbers P => f m) := by
      simpa only [zpow_neg_one, f, MonoidHom.coe_mk, OneHom.coe_mk] using hEuler
    _ <= tsum (fun n : Nat => (n : Real) ^ (-(1 + delta))) := hSubset
    _ <= _ := lpf_rankin_pseries_bound delta hd

theorem lpf_singular_prime_product_numeric (P : Finset Nat) (n : Nat)
    (hn : 5 <= n)
    (hP : forall p, Membership.mem P p -> And (Nat.Prime p) (And (5 <= p) (p <= n))) :
    Finset.prod P singularFactor <= 18 * Real.log (n : Real) := by
  have hnR : (5 : Real) <= (n : Real) := by exact_mod_cast hn
  have hnPos : (0 : Real) < (n : Real) := by linarith only [hnR]
  have hLog : 1 <= Real.log (n : Real) :=
    one_le_log_three.trans (Real.log_le_log (by norm_num) (by linarith only [hnR]))
  have hLogPos : 0 < Real.log (n : Real) := zero_lt_one.trans_le hLog
  let delta : Real := 1 / Real.log (n : Real)
  have hd : 0 < delta := by dsimp [delta]; positivity
  have hSub : P <= sharpPrimeCutoff n := by
    intro p hp
    exact mem_sharpPrimeCutoff.mpr (hP p hp)
  have hLogSum : Finset.sum P (fun p => Real.log (p : Real) / (p : Real)) <=
      Real.log (n : Real) := by
    apply le_trans _ (prime_log_sum_sharp n hn)
    apply Finset.sum_le_sum_of_subset_of_nonneg hSub
    intro p hp hNot
    have h := (mem_sharpPrimeCutoff.mp hp).2.1
    have hR : (1 : Real) <= (p : Real) := by exact_mod_cast (show 1 <= p by omega)
    exact div_nonneg (Real.log_nonneg hR) (Nat.cast_nonneg p)
  have hTail := lpf_overlap_inverse_square_subset_tail P 4 (n + 1) (by norm_num)
    (fun p hp => by have h := (hP p hp).2; exact And.intro (by omega) (by omega))
  have hCorrection : Finset.sum P (fun p => 1 / ((p : Real) * ((p : Real) - 2))) <=
      (5 / 12 : Real) := by
    calc
      _ <= Finset.sum P (fun p => (5 / 3 : Real) * (1 / (p : Real) ^ 2)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpR : (5 : Real) <= (p : Real) := by exact_mod_cast (hP p hp).2.1
        have hpPos : (0 : Real) < (p : Real) := by linarith only [hpR]
        have hpTwo : 0 < (p : Real) - 2 := by linarith only [hpR]
        apply (mul_le_mul_iff_of_pos_right (by positivity : 0 < (p : Real) ^ 2)).mp
        apply (mul_le_mul_iff_of_pos_right (by positivity : 0 < (p : Real) * ((p : Real) - 2))).mp
        field_simp
        nlinarith only [hpR, sq_nonneg ((p : Real) - 5)]
      _ = (5 / 3 : Real) * Finset.sum P (fun p => 1 / (p : Real) ^ 2) :=
        (Finset.mul_sum _ _ _).symm
      _ <= (5 / 3 : Real) * (1 / 4) := mul_le_mul_of_nonneg_left hTail (by norm_num)
      _ = _ := by norm_num
  have hExponent : Finset.sum P
      (fun p => (5 / 4 : Real) * delta * Real.log (p : Real) / (p : Real) +
        1 / ((p : Real) * ((p : Real) - 2))) <= (5 / 3 : Real) := by
    have hLogScaled := mul_le_mul_of_nonneg_left hLogSum
      (by positivity : 0 <= (5 / 4 : Real) * delta)
    have hId : (5 / 4 : Real) * delta * Real.log (n : Real) = 5 / 4 := by
      dsimp [delta]
      field_simp
    rw [hId] at hLogScaled
    rw [Finset.sum_add_distrib]
    have hLeft : Finset.sum P (fun p => (5 / 4 : Real) * delta *
        Real.log (p : Real) / (p : Real)) =
        (5 / 4 : Real) * delta * Finset.sum P (fun p => Real.log (p : Real) / (p : Real)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    rw [hLeft]
    linarith only [hLogScaled, hCorrection]
  let w : Nat -> Real := fun p => 1 - (p : Real) ^ (-(1 + delta))
  have hw : forall p, Membership.mem P p -> 0 < w p := by
    intro p hp
    have hpR : (5 : Real) <= (p : Real) := by exact_mod_cast (hP p hp).2.1
    dsimp [w]
    rw [Real.rpow_def_of_pos (by linarith only [hpR])]
    have hPL : 0 < Real.log (p : Real) := Real.log_pos (by linarith only [hpR])
    have hE : Real.log (p : Real) * (-(1 + delta)) < 0 := by
      exact mul_neg_of_pos_of_neg hPL (by linarith only [hd])
    have h := Real.exp_lt_one_iff.mpr hE
    linarith only [h]
  have hS : forall p, Membership.mem P p -> 0 <= singularFactor p := by
    intro p hp
    have hpR : (5 : Real) <= (p : Real) := by exact_mod_cast (hP p hp).2.1
    have hpTwo : 0 <= (p : Real) - 2 := by linarith only [hpR]
    exact add_nonneg zero_le_one (one_div_nonneg.mpr hpTwo)
  have hWeighted : Finset.prod P (fun p => singularFactor p * w p) <= Real.exp (5 / 3) := by
    calc
      _ <= Finset.prod P (fun p => Real.exp ((5 / 4 : Real) * delta *
          Real.log (p : Real) / (p : Real) + 1 / ((p : Real) * ((p : Real) - 2)))) := by
        apply lpf_nonneg_product_compare
        next => exact fun p hp => mul_nonneg (hS p hp) (hw p hp).le
        next => exact fun p hp => lpf_singular_rankin_local p delta (hP p hp).2.1 hd.le
      _ = Real.exp (Finset.sum P (fun p => (5 / 4 : Real) * delta *
          Real.log (p : Real) / (p : Real) + 1 / ((p : Real) * ((p : Real) - 2)))) :=
        (Real.exp_sum _ _).symm
      _ <= _ := Real.exp_le_exp.mpr hExponent
  have hExp : Real.exp (5 / 3 : Real) <= 9 := by
    have hE1 : Real.exp 1 <= 3 := Real.exp_one_lt_three.le
    have hE2 : Real.exp (2 : Real) = Real.exp 1 ^ 2 := by
      rw [show (2 : Real) = 1 + 1 by norm_num, Real.exp_add]
      ring
    have h : Real.exp 2 <= 9 := by rw [hE2]; nlinarith only [hE1, Real.exp_pos 1]
    exact (Real.exp_le_exp.mpr (by norm_num : (5 / 3 : Real) <= 2)).trans h
  have hEuler : Finset.prod P (fun p => (w p) ^ (-1 : Int)) <= 1 + Real.log (n : Real) := by
    have h := lpf_rankin_finite_euler_bound P delta hd (fun p hp => (hP p hp).1)
    have hInv : 1 / delta = Real.log (n : Real) := by dsimp [delta]; field_simp
    simpa only [w, hInv] using h
  have hIdentity : Finset.prod P singularFactor =
      Finset.prod P (fun p => singularFactor p * w p) *
        Finset.prod P (fun p => (w p) ^ (-1 : Int)) := by
    rw [<- Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    rw [zpow_neg_one]
    field_simp [(hw p hp).ne']
  rw [hIdentity]
  have hBound := mul_le_mul (hWeighted.trans hExp) hEuler
    (Finset.prod_nonneg (fun p hp => by rw [zpow_neg_one]; exact inv_nonneg.mpr (hw p hp).le))
    (by norm_num : (0 : Real) <= 9)
  nlinarith only [hBound, hLog]

end PrimeFactorOscillations.LPF
