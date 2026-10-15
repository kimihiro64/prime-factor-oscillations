/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Helpers.GenericOddMertens
import PrimeFactorOscillations.Helpers.QRHPrimeRows
import PrimeFactorOscillations.Mathlib.Algebra.Order.BigOperators.Group.InverseSquare
import PrimeFactorOscillations.Mathlib.NumberTheory.DirichletCharacter.ResidueCount

/-!
# Weighted prime congruences for the LPF moment argument

The installed 7/8 estimate is summed against arbitrary nonnegative divisor
weights. Both the complete principal contribution and total error are retained.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

noncomputable def singularFactor (p : Nat) : Real := 1 + 1 / ((p : Real) - 2)

/-- Exact finite expansion; even v=0 is harmless for this truncated product. -/
theorem truncated_singular_moment_expansion (P : Finset Nat) (v q : Nat) :
    (Finset.prod (P.filter (fun p => Dvd.dvd p v)) singularFactor) ^ q =
      Finset.sum P.powerset (fun A =>
        if forall p, Membership.mem A p -> Dvd.dvd p v then
          Finset.prod A (fun p => singularFactor p ^ q - 1) else 0) := by
  classical
  rw [<- Finset.prod_pow]
  calc
    _ = Finset.prod P (fun p => 1 +
        (if Dvd.dvd p v then singularFactor p ^ q - 1 else 0)) := by
      rw [Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro p hp
      by_cases hd : Dvd.dvd p v
      next => simp only [if_pos hd]; ring
      next => simp only [if_neg hd, add_zero]
    _ = Finset.sum P.powerset (fun A => Finset.prod A
        (fun p => if Dvd.dvd p v then singularFactor p ^ q - 1 else 0)) :=
      Finset.prod_one_add P
    _ = _ := by
      apply Finset.sum_congr rfl
      intro A hA
      exact Finset.prod_ite_zero

/-- This is the full error multiplier after summing all squarefree weights. -/
theorem singular_moment_total_weight (P : Finset Nat) (q : Nat) :
    Finset.sum P.powerset (fun A => Finset.prod A (fun p => singularFactor p ^ q - 1)) =
      (Finset.prod P singularFactor) ^ q := by
  rw [<- Finset.prod_one_add, <- Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro p hp
  ring

theorem singular_moment_weight_nonneg (p q : Nat) (hp : 3 <= p) :
    0 <= singularFactor p ^ q - 1 := by
  have hpR : (3 : Real) <= (p : Real) := by exact_mod_cast hp
  have hBase : 1 <= singularFactor p := by
    have hDiv : 0 <= 1 / ((p : Real) - 2) := one_div_nonneg.mpr (by linarith)
    dsimp [singularFactor]
    linarith
  have hPow : 1 <= singularFactor p ^ q := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [pow_succ]
      have h := mul_le_mul ih hBase (by norm_num : (0 : Real) <= 1)
        (by linarith : 0 <= singularFactor p ^ q)
      simpa only [one_mul] using h
  linarith

/-- All weighted modulus errors are retained; C is independent of the weights. -/
theorem exists_weighted_prime_row_residue_bound :
    exists C : Real, And (0 < C)
      (forall {I : Type*} (X y m D : Nat) (J : Finset I)
        (modulus : I -> Nat) (w : I -> Real)
        (a : (d : I) -> Units (ZMod (modulus d))),
        (forall d, Membership.mem J d -> And (1 <= modulus d) (modulus d <= D)) ->
        (forall d, Membership.mem J d -> 0 <= w d) ->
        Finset.sum (Nat.largestPrimeFactorRow X y m) (fun (r : Nat) =>
          Finset.sum J (fun d => if (r : ZMod (modulus d)) = (a d : ZMod (modulus d)) then w d else 0)) <=
        ((Nat.largestPrimeFactorRow X y m).card : Real) *
          Finset.sum J (fun d => w d / ((modulus d).totient : Real)) +
        C * (X : Real) ^ (7 / 8 : Real) *
          (1 + Real.log D + Real.log ((X : Real) + 2)) ^ 2 * Finset.sum J w) := by
  classical
  let C : Real := Classical.choose QRH.exists_uniform_prime_row_bounds
  have hC := Classical.choose_spec QRH.exists_uniform_prime_row_bounds
  refine Exists.intro C (And.intro hC.1 ?_)
  intro I X y m D J modulus w a hJ hw
  let R := Nat.largestPrimeFactorRow X y m
  let E := C * (X : Real) ^ (7 / 8 : Real) *
    (1 + Real.log D + Real.log ((X : Real) + 2)) ^ 2
  have hCount : forall d, Membership.mem J d ->
      (((R.filter (fun (r : Nat) => (r : ZMod (modulus d)) = (a d : ZMod (modulus d)))).card : Real) <=
        (R.card : Real) / ((modulus d).totient : Real) + E) := by
    intro d hd
    have hdLow := (hJ d hd).1
    have hdD := (hJ d hd).2
    letI : NeZero (modulus d) := NeZero.mk (by omega)
    let Ed := C * (X : Real) ^ (7 / 8 : Real) *
      (1 + Real.log (modulus d) + Real.log ((X : Real) + 2)) ^ 2
    have hEd : 0 <= Ed := by
      dsimp [Ed]
      exact mul_nonneg (mul_nonneg hC.1.le (Real.rpow_nonneg (Nat.cast_nonneg X) _))
        (sq_nonneg _)
    have hResidue := DirichletCharacter.abs_residue_count_sub_unit_mean_le
      R (fun (r : Nat) => (r : ZMod (modulus d))) (a d) Ed hEd
      (fun chi hchi => hC.2 chi hchi X y m)
    have hUnitCard : ((R.filter (fun (r : Nat) => IsUnit (r : ZMod (modulus d)))).card : Real) <=
        (R.card : Real) := Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))
    have hUnitMean := div_le_div_of_nonneg_right hUnitCard (Nat.cast_nonneg (modulus d).totient)
    have hLogd : 0 <= Real.log (modulus d) := Real.log_nonneg (by exact_mod_cast hdLow)
    have hLogdD : Real.log (modulus d) <= Real.log D :=
      Real.log_le_log (by exact_mod_cast (show 0 < modulus d by omega)) (by exact_mod_cast hdD)
    have hLogX : 0 <= Real.log ((X : Real) + 2) := Real.log_nonneg (by
      have h : (0 : Real) <= (X : Real) := Nat.cast_nonneg X
      linarith)
    have hSq : (1 + Real.log (modulus d) + Real.log ((X : Real) + 2)) ^ 2 <=
        (1 + Real.log D + Real.log ((X : Real) + 2)) ^ 2 := by nlinarith
    have hEdE : Ed <= E := mul_le_mul_of_nonneg_left hSq
      (mul_nonneg hC.1.le (Real.rpow_nonneg (Nat.cast_nonneg X) _))
    have hUpper := (le_abs_self _).trans hResidue
    linarith
  have hReorder :
      Finset.sum R (fun (r : Nat) => Finset.sum J
        (fun d => if (r : ZMod (modulus d)) = (a d : ZMod (modulus d)) then w d else 0)) =
      Finset.sum J (fun d => w d *
        ((R.filter (fun (r : Nat) => (r : ZMod (modulus d)) = (a d : ZMod (modulus d)))).card : Real)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d hd
    rw [<- Finset.sum_filter]
    simp [mul_comm]
  change Finset.sum R (fun (r : Nat) => Finset.sum J
      (fun d => if (r : ZMod (modulus d)) = (a d : ZMod (modulus d)) then w d else 0)) <=
    (R.card : Real) * Finset.sum J (fun d => w d / ((modulus d).totient : Real)) + E * Finset.sum J w
  rw [hReorder]
  calc
    _ <= Finset.sum J (fun d => w d * ((R.card : Real) / ((modulus d).totient : Real) + E)) := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left (hCount d hd) (hw d hd)
    _ = _ := by
      rw [Finset.mul_sum, Finset.mul_sum, <- Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      ring

/-- The subset-product moment packet, retaining every weight and the full error. -/
theorem exists_squarefree_prime_row_moment_bound :
    exists C : Real, And (0 < C)
      (forall (X y m : Nat) (P : Finset Nat) (q : Nat)
        (a : (A : Finset Nat) -> Units (ZMod (Finset.prod A (fun p => p)))),
        (forall p, Membership.mem P p -> 3 <= p) ->
        Finset.sum (Nat.largestPrimeFactorRow X y m) (fun (r : Nat) =>
          Finset.sum P.powerset (fun A =>
            if (r : ZMod (Finset.prod A (fun p => p))) =
                (a A : ZMod (Finset.prod A (fun p => p))) then
              Finset.prod A (fun p => singularFactor p ^ q - 1) else 0)) <=
        ((Nat.largestPrimeFactorRow X y m).card : Real) *
          Finset.sum P.powerset (fun A =>
            Finset.prod A (fun p => singularFactor p ^ q - 1) /
              ((Finset.prod A (fun p => p)).totient : Real)) +
        C * (X : Real) ^ (7 / 8 : Real) *
          (1 + Real.log ((Finset.prod P (fun p => p) : Nat) : Real) +
            Real.log ((X : Real) + 2)) ^ 2 *
            (Finset.prod P singularFactor) ^ q) := by
  classical
  let C : Real := Classical.choose exists_weighted_prime_row_residue_bound
  have hC := Classical.choose_spec exists_weighted_prime_row_residue_bound
  refine Exists.intro C (And.intro hC.1 ?_)
  intro X y m P q a hP
  have hMod : forall A, Membership.mem P.powerset A ->
      And (1 <= Finset.prod A (fun p => p))
        (Finset.prod A (fun p => p) <= Finset.prod P (fun p => p)) := by
    intro A hA
    have hSub := Finset.mem_powerset.mp hA
    refine And.intro ?_ ?_
    next =>
      apply Finset.one_le_prod
      intro p hp
      have h := hP p (hSub hp)
      omega
    next =>
      apply Finset.prod_le_prod_of_subset_of_one_le hSub
      intro p hp hNot
      have h := hP p hp
      omega
  have hWeight : forall A, Membership.mem P.powerset A ->
      0 <= Finset.prod A (fun p => singularFactor p ^ q - 1) := by
    intro A hA
    apply Finset.prod_nonneg
    intro p hp
    exact singular_moment_weight_nonneg p q (hP p (Finset.mem_powerset.mp hA hp))
  have h := hC.2 X y m (Finset.prod P (fun p => p)) P.powerset
    (fun A => Finset.prod A (fun p => p))
    (fun A => Finset.prod A (fun p => singularFactor p ^ q - 1)) a hMod hWeight
  rw [singular_moment_total_weight] at h
  exact h

private theorem eventually_log_moment_budget (C : Real) (hC : 0 < C) :
    Filter.Eventually (fun t : Real => forall q : Nat,
      (q : Real) <= 10 * Real.log t ->
      Real.log C + 2 * Real.log t + (q : Real) * Real.log (C * Real.log t) <=
        (1 / 16 : Real) * t) Filter.atTop := by
  let K := abs (Real.log C) + 2 + 10 * C
  have hK : 0 <= K := by dsimp [K]; positivity
  have hSmall := (Real.isLittleO_pow_log_id_atTop (n := 2)).const_mul_left K
  filter_upwards [hSmall.bound (by norm_num : (0 : Real) < 1 / 16),
    Filter.eventually_ge_atTop (1 : Real),
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1 : Real))]
    with t hBound ht hLog
  have ht0 : 0 <= t := by linarith
  have hLog0 : 0 <= Real.log t := by linarith
  have hProduct : 0 < C * Real.log t := mul_pos hC (by linarith)
  have hLogBound : Real.log (C * Real.log t) <= C * Real.log t := by
    have h := Real.log_le_sub_one_of_pos hProduct
    linarith
  have hBound' : K * Real.log t ^ 2 <= (1 / 16 : Real) * t := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK (sq_nonneg _)),
      id_eq, abs_of_nonneg ht0] using hBound
  intro q hq
  have hTerm : (q : Real) * Real.log (C * Real.log t) <= 10 * C * Real.log t ^ 2 := by
    calc
      _ <= (q : Real) * (C * Real.log t) :=
        mul_le_mul_of_nonneg_left hLogBound (Nat.cast_nonneg q)
      _ <= (10 * Real.log t) * (C * Real.log t) :=
        mul_le_mul_of_nonneg_right hq hProduct.le
      _ = _ := by ring
  have hSq : 1 <= Real.log t ^ 2 := by nlinarith
  have hConst : abs (Real.log C) <= abs (Real.log C) * Real.log t ^ 2 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hSq (abs_nonneg (Real.log C))
  have hLinear : 2 * Real.log t <= 2 * Real.log t ^ 2 := by nlinarith
  have hAbs := le_abs_self (Real.log C)
  dsimp [K] at hBound'
  nlinarith

/-- The entire weighted error is sub-main-term uniformly for growing moments. -/
theorem eventually_complete_moment_error_le (C : Real) (hC : 0 < C) :
    Filter.Eventually (fun X : Real => forall q : Nat,
      (q : Real) <= 10 * Real.log (Real.log X) ->
      C * X ^ (7 / 8 : Real) * Real.log X ^ 2 *
        (C * Real.log (Real.log X)) ^ q <= X ^ (15 / 16 : Real)) Filter.atTop := by
  have hBudget := Real.tendsto_log_atTop.eventually (eventually_log_moment_budget C hC)
  have hLogLog := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
    (Filter.eventually_ge_atTop (1 : Real))
  filter_upwards [hBudget, hLogLog, Filter.eventually_ge_atTop (2 : Real)]
    with X hBudget hLogLog hX2
  change 1 <= Real.log (Real.log X) at hLogLog
  intro q hq
  have hX : 0 < X := by linarith
  have hLogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hLL : 0 < Real.log (Real.log X) := by linarith
  have hBase : 0 < C * Real.log (Real.log X) := mul_pos hC hLL
  have hLeft : 0 < C * X ^ (7 / 8 : Real) * Real.log X ^ 2 *
      (C * Real.log (Real.log X)) ^ q := by positivity
  have hRight : 0 < X ^ (15 / 16 : Real) := Real.rpow_pos_of_pos hX _
  apply (Real.log_le_log_iff hLeft hRight).mp
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_rpow hX, Real.log_pow, Real.log_pow, Real.log_rpow hX]
  have h := hBudget q hq
  norm_num only [Nat.cast_ofNat] at *
  linarith

private theorem pow_increment_le_twice (x : Real) (q : Nat)
    (hx : 0 <= x) (hx1 : x <= 1) (hq : (q : Real) * x <= 1 / 2) :
    (1 + x) ^ q - 1 <= 2 * (q : Real) * x := by
  have hMinus : 0 <= 1 - x := by linarith
  have hPlus : 0 <= 1 + x := by linarith
  have hBernoulli : forall k : Nat, 1 - (k : Real) * x <= (1 - x) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h := mul_le_mul_of_nonneg_right ih hMinus
      rw [pow_succ]
      push_cast
      nlinarith [mul_nonneg (Nat.cast_nonneg k) (sq_nonneg x)]
  have hBase0 : 0 <= (1 + x) * (1 - x) := mul_nonneg hPlus hMinus
  have hBase1 : (1 + x) * (1 - x) <= 1 := by nlinarith [sq_nonneg x]
  have hPair : forall k : Nat, ((1 + x) * (1 - x)) ^ k <= 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      calc
        _ <= 1 * ((1 + x) * (1 - x)) := mul_le_mul_of_nonneg_right ih hBase0
        _ <= 1 := by simpa only [one_mul] using hBase1
  have hPow0 := pow_nonneg hPlus q
  have hCoupled : (1 + x) ^ q * (1 - (q : Real) * x) <= 1 := by
    calc
      _ <= (1 + x) ^ q * (1 - x) ^ q :=
        mul_le_mul_of_nonneg_left (hBernoulli q) hPow0
      _ = ((1 + x) * (1 - x)) ^ q := (mul_pow _ _ _).symm
      _ <= 1 := hPair q
  have hHalf : 1 / 2 <= 1 - (q : Real) * x := by linarith
  have hLower := mul_le_mul_of_nonneg_left hHalf hPow0
  have hTwo : (1 + x) ^ q <= 2 := by nlinarith
  have hUpper := mul_le_mul_of_nonneg_right hTwo (mul_nonneg (Nat.cast_nonneg q) hx)
  nlinarith

/-- Uniform high-prime increment, for the split at 2q+2. -/
theorem singular_factor_high_moment_increment (p q : Nat) (hq : 1 <= q)
    (hp : 2 * q + 2 < p) :
    singularFactor p ^ q - 1 <= 2 * (q : Real) / ((p : Real) - 2) := by
  let x : Real := 1 / ((p : Real) - 2)
  have hpR : 2 * (q : Real) + 2 < (p : Real) := by exact_mod_cast hp
  have hqR : (1 : Real) <= (q : Real) := by exact_mod_cast hq
  have hDen : 0 < (p : Real) - 2 := by linarith
  have hx : 0 <= x := one_div_nonneg.mpr hDen.le
  have hCancel : ((p : Real) - 2) * x = 1 := by
    dsimp [x]
    field_simp
  have hOne := mul_le_mul_of_nonneg_right
    (show (1 : Real) <= (p : Real) - 2 by linarith) hx
  have hx1 : x <= 1 := by nlinarith
  have hMultiply := mul_le_mul_of_nonneg_right
    (show 2 * (q : Real) <= (p : Real) - 2 by linarith) hx
  have hSmall : (q : Real) * x <= 1 / 2 := by nlinarith
  have h := pow_increment_le_twice x q hx hx1 hSmall
  change (1 + x) ^ q - 1 <= 2 * (q : Real) / ((p : Real) - 2)
  calc
    _ <= 2 * (q : Real) * x := h
    _ = _ := by dsimp [x]; ring

theorem singular_high_euler_term_le (p q : Nat) (hq : 1 <= q) (hp : 2 * q + 2 < p) :
    (singularFactor p ^ q - 1) / ((p : Real) - 1) <= 6 * (q : Real) / (p : Real) ^ 2 := by
  have hpR : (5 : Real) <= (p : Real) := by
    exact_mod_cast (show 5 <= p by omega)
  have hU : (0 : Real) < p := by linarith
  have hOne : 0 < (p : Real) - 1 := by linarith
  have hTwo : 0 < (p : Real) - 2 := by linarith
  have hDen : (p : Real) ^ 2 <= 3 * (((p : Real) - 2) * ((p : Real) - 1)) := by
    nlinarith [mul_nonneg (show (0 : Real) <= (p : Real) - 4 by linarith)
      (show (0 : Real) <= 2 * (p : Real) - 1 by linarith)]
  have hCompare := div_le_div_of_nonneg_left (by positivity : (0 : Real) <= 2 * (q : Real))
    (by positivity : (0 : Real) < (p : Real) ^ 2 / 3)
    (show (p : Real) ^ 2 / 3 <= ((p : Real) - 2) * ((p : Real) - 1) by linarith)
  calc
    _ <= (2 * (q : Real) / ((p : Real) - 2)) / ((p : Real) - 1) :=
      div_le_div_of_nonneg_right (singular_factor_high_moment_increment p q hq hp) hOne.le
    _ = (2 * (q : Real)) / (((p : Real) - 2) * ((p : Real) - 1)) := div_div _ _ _
    _ <= (2 * (q : Real)) / ((p : Real) ^ 2 / 3) := hCompare
    _ = _ := by field_simp; ring

private theorem nonneg_prod_comparison (P : Finset Nat) (f g : Nat -> Real)
    (h0 : forall p, Membership.mem P p -> 0 <= f p)
    (h1 : forall p, Membership.mem P p -> f p <= g p) :
    Finset.prod P f <= Finset.prod P g := by
  classical
  revert h0 h1
  induction P using Finset.induction_on with
  | empty => intro h0 h1; simp
  | @insert p P hp ih =>
    intro h0 h1
    have h0P : forall r, Membership.mem P r -> 0 <= f r := by
      intro r hr
      exact h0 r (Finset.mem_insert_of_mem hr)
    have h1P : forall r, Membership.mem P r -> f r <= g r := by
      intro r hr
      exact h1 r (Finset.mem_insert_of_mem hr)
    have h0p := h0 p (Finset.mem_insert_self p P)
    have h1p := h1 p (Finset.mem_insert_self p P)
    rw [Finset.prod_insert hp, Finset.prod_insert hp]
    exact mul_le_mul h1p (ih h0P h1P) (Finset.prod_nonneg h0P) (h0p.trans h1p)

/-- Uniform in the outer cutoff: the high Euler product costs only a constant to q. -/
theorem singular_high_euler_product_le (P : Finset Nat) (N q : Nat) (hq : 1 <= q)
    (hP : forall p, Membership.mem P p -> And (2 * q + 2 < p) (p < N)) :
    Finset.prod P (fun p => 1 + (singularFactor p ^ q - 1) / ((p : Real) - 1)) <=
      Real.exp (12 * (q : Real)) := by
  have hSum := Finset.sum_subset_inverse_square_le P N
    (fun p hp => Finset.mem_range.mpr (hP p hp).2)
  calc
    _ <= Finset.prod P (fun p => Real.exp (6 * (q : Real) / (p : Real) ^ 2)) := by
      apply nonneg_prod_comparison
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
    _ <= Real.exp (12 * (q : Real)) := by
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left hSum (by positivity : (0 : Real) <= 6 * (q : Real))
      linarith

noncomputable def singularMertensBound : Real := abs Mertens.M +
  PrimeFactorUnimodality.mertensErrorConstant / Real.log 2 + 12

private theorem shifted_reciprocal_le (p : Nat) (hp : 3 <= p) :
    1 / ((p : Real) - 2) <= 1 / (p : Real) + 6 / (p : Real) ^ 2 := by
  have hpR : (3 : Real) <= (p : Real) := by exact_mod_cast hp
  have hU : (0 : Real) < p := by linarith
  have hDen : 0 < (p : Real) - 2 := by linarith
  have hOrder : (p : Real) ^ 2 / 3 <= (p : Real) * ((p : Real) - 2) := by
    nlinarith [mul_nonneg (show (0 : Real) <= (p : Real) by linarith)
      (show (0 : Real) <= (p : Real) - 3 by linarith)]
  have hCompare := div_le_div_of_nonneg_left (by norm_num : (0 : Real) <= 2)
    (by positivity : (0 : Real) < (p : Real) ^ 2 / 3) hOrder
  have hIdentity : 1 / ((p : Real) - 2) = 1 / (p : Real) +
      2 / ((p : Real) * ((p : Real) - 2)) := by
    field_simp
    ring
  have hNorm : (2 : Real) / ((p : Real) ^ 2 / 3) = 6 / (p : Real) ^ 2 := by
    field_simp
    ring
  rw [hNorm] at hCompare
  linarith

theorem singular_prime_reciprocal_sum_le (P : Finset Nat) (n : Nat) (hn : 2 <= n)
    (hP : forall p, Membership.mem P p -> And (Nat.Prime p) (And (3 <= p) (p <= n))) :
    Finset.sum P (fun p => 1 / ((p : Real) - 2)) <=
      Real.log (Real.log n) + singularMertensBound := by
  have hRange : forall p, Membership.mem P p -> Membership.mem (Finset.range (n + 1)) p := by
    intro p hp
    exact Finset.mem_range.mpr (by have h := (hP p hp).2.2; omega)
  have hPrimeSet : P <= Nat.primesBelow (n + 1) := by
    intro p hp
    change Membership.mem ((Finset.range (n + 1)).filter Nat.Prime) p
    exact Finset.mem_filter.mpr (And.intro (hRange p hp) (hP p hp).1)
  have hRec : Finset.sum P (fun p => 1 / (p : Real)) <=
      PrimeFactorUnimodality.reciprocalPrimeSumBelow (n + 1) := by
    unfold PrimeFactorUnimodality.reciprocalPrimeSumBelow
    exact Finset.sum_le_sum_of_subset_of_nonneg hPrimeSet
      (fun p _ _ => div_nonneg zero_le_one (Nat.cast_nonneg p))
  have hSquare := Finset.sum_subset_inverse_square_le P (n + 1) hRange
  have hCorrection : Finset.sum P (fun p => 6 / (p : Real) ^ 2) <= 12 := by
    calc
      _ = 6 * Finset.sum P (fun p => 1 / (p : Real) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
      _ <= 12 := by linarith
  have hFinite := Finset.sum_le_sum (fun p hp => shifted_reciprocal_le p (hP p hp).2.1)
  rw [Finset.sum_add_distrib] at hFinite
  have hMertens := PrimeFactorUnimodality.reciprocalPrimeSumBelow_upper_of_estimate
    PrimeFactorUnimodality.hasMertensReciprocalPrimeEstimate hn
  have hLog2 : (0 : Real) < Real.log 2 := Real.log_pos (by norm_num)
  have hLog : Real.log 2 <= Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hError := div_le_div_of_nonneg_left
    PrimeFactorUnimodality.mertensErrorConstant_nonneg hLog2 hLog
  have hAbs := le_abs_self Mertens.M
  dsimp [singularMertensBound]
  linarith

/-- A cutoff-uniform truncated singular product bound from the cached Mertens theorem. -/
theorem singular_prime_product_le (P : Finset Nat) (n : Nat) (hn : 2 <= n)
    (hP : forall p, Membership.mem P p -> And (Nat.Prime p) (And (3 <= p) (p <= n))) :
    Finset.prod P singularFactor <= Real.exp singularMertensBound * Real.log n := by
  have hLog : 0 < Real.log (n : Real) := Real.log_pos (by
    have h : (2 : Real) <= (n : Real) := by exact_mod_cast hn
    linarith)
  calc
    _ <= Finset.prod P (fun p => Real.exp (1 / ((p : Real) - 2))) := by
      apply nonneg_prod_comparison
      next =>
        intro p hp
        have hpR : (3 : Real) <= (p : Real) := by exact_mod_cast (hP p hp).2.1
        have hDen : 0 <= (p : Real) - 2 := by linarith
        exact add_nonneg zero_le_one (one_div_nonneg.mpr hDen)
      next =>
        intro p hp
        have h := Real.add_one_le_exp (1 / ((p : Real) - 2))
        dsimp [singularFactor]
        linarith
    _ = Real.exp (Finset.sum P (fun p => 1 / ((p : Real) - 2))) := (Real.exp_sum _ _).symm
    _ <= Real.exp (Real.log (Real.log n) + singularMertensBound) :=
      Real.exp_le_exp.mpr (singular_prime_reciprocal_sum_le P n hn hP)
    _ = Real.exp singularMertensBound * Real.log n := by
      rw [Real.exp_add, Real.exp_log hLog, mul_comm]

/-- Uniform in both the moment order and the outer prime cutoff. -/
theorem singular_euler_moment_le (P : Finset Nat) (N q : Nat) (hq : 1 <= q)
    (hP : forall p, Membership.mem P p -> And (Nat.Prime p) (And (3 <= p) (p < N))) :
    Finset.prod P (fun p => 1 + (singularFactor p ^ q - 1) / ((p : Real) - 1)) <=
      (2 * Real.exp (singularMertensBound + 12) * Real.log ((q : Real) + 2)) ^ q := by
  classical
  let L := P.filter (fun p => p <= 2 * q + 2)
  let H := P.filter (fun p => 2 * q + 2 < p)
  let F : Nat -> Real := fun p => 1 + (singularFactor p ^ q - 1) / ((p : Real) - 1)
  let A : Real := 2 * Real.exp singularMertensBound * Real.log ((q : Real) + 2)
  have hF : forall p, Membership.mem P p -> 0 <= F p := by
    intro p hp
    have hpR : (3 : Real) <= (p : Real) := by exact_mod_cast (hP p hp).2.1
    exact add_nonneg zero_le_one (div_nonneg
      (singular_moment_weight_nonneg p q (hP p hp).2.1) (by linarith))
  have hS : forall p, Membership.mem P p -> 0 <= singularFactor p := by
    intro p hp
    have hpR : (3 : Real) <= (p : Real) := by exact_mod_cast (hP p hp).2.1
    exact add_nonneg zero_le_one (one_div_nonneg.mpr (by linarith))
  have hLogQ : 0 <= Real.log ((q : Real) + 2) := Real.log_nonneg (by
    have h : (0 : Real) <= (q : Real) := Nat.cast_nonneg q
    linarith)
  have hA : 0 <= A := mul_nonneg (by positivity) hLogQ
  have hLogCompare : Real.log ((2 * q + 2 : Nat) : Real) <=
      2 * Real.log ((q : Real) + 2) := by
    have hInside : ((2 * q + 2 : Nat) : Real) <= ((q : Real) + 2) ^ 2 := by
      push_cast
      have h : (0 : Real) <= (q : Real) := Nat.cast_nonneg q
      nlinarith [sq_nonneg (q : Real)]
    have h := Real.log_le_log (by positivity : (0 : Real) < ((2 * q + 2 : Nat) : Real)) hInside
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    exact h
  have hLowPrime : Finset.prod L singularFactor <=
      Real.exp singularMertensBound * Real.log ((2 * q + 2 : Nat) : Real) := by
    apply singular_prime_product_le L (2 * q + 2) (by omega)
    intro p hp
    have hm := Finset.mem_filter.mp hp
    exact And.intro (hP p hm.1).1 (And.intro (hP p hm.1).2.1 hm.2)
  have hLowCore : Finset.prod L singularFactor <= A := by
    calc
      _ <= Real.exp singularMertensBound * Real.log ((2 * q + 2 : Nat) : Real) := hLowPrime
      _ <= Real.exp singularMertensBound * (2 * Real.log ((q : Real) + 2)) :=
        mul_le_mul_of_nonneg_left hLogCompare (Real.exp_pos _).le
      _ = A := by dsimp [A]; ring
  have hProd0 : 0 <= Finset.prod L singularFactor :=
    Finset.prod_nonneg (fun p hp => hS p (Finset.mem_filter.mp hp).1)
  have hPower : (Finset.prod L singularFactor) ^ q <= A ^ q := by
    simpa only [Real.rpow_natCast] using
      Real.rpow_le_rpow hProd0 hLowCore (Nat.cast_nonneg q)
  have hLow : Finset.prod L F <= A ^ q := by
    calc
      _ <= Finset.prod L (fun p => singularFactor p ^ q) := by
        apply nonneg_prod_comparison
        next => exact fun p hp => hF p (Finset.mem_filter.mp hp).1
        next =>
          intro p hp
          have hpP := (Finset.mem_filter.mp hp).1
          have hpR : (3 : Real) <= (p : Real) := by exact_mod_cast (hP p hpP).2.1
          have hWeight := singular_moment_weight_nonneg p q (hP p hpP).2.1
          have hDiv := div_le_div_of_nonneg_left hWeight (by norm_num : (0 : Real) < 1)
            (show (1 : Real) <= (p : Real) - 1 by linarith)
          simp only [div_one] at hDiv
          dsimp [F]
          linarith
      _ = (Finset.prod L singularFactor) ^ q := Finset.prod_pow _ _ _
      _ <= A ^ q := hPower
  have hHigh : Finset.prod H F <= Real.exp (12 * (q : Real)) := by
    apply singular_high_euler_product_le H N q hq
    intro p hp
    have hm := Finset.mem_filter.mp hp
    exact And.intro hm.2 (hP p hm.1).2.2
  have hSplit : Finset.prod P F = Finset.prod L F * Finset.prod H F := by
    dsimp [L, H]
    rw [Finset.prod_filter, Finset.prod_filter, <- Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    by_cases h : p <= 2 * q + 2
    next => simp only [F, if_pos h, if_neg (not_lt.mpr h), mul_one]
    next => simp only [F, if_neg h, if_pos (Nat.lt_of_not_ge h), one_mul]
  have hExp : forall k : Nat, Real.exp (12 * (k : Real)) = Real.exp 12 ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      simp only [Nat.cast_add, Nat.cast_one, mul_add, mul_one, Real.exp_add, ih, pow_succ]
  change Finset.prod P F <= _
  rw [hSplit]
  calc
    _ <= A ^ q * Real.exp (12 * (q : Real)) := mul_le_mul hLow hHigh
      (Finset.prod_nonneg (fun p hp => hF p (Finset.mem_filter.mp hp).1)) (pow_nonneg hA q)
    _ = (A * Real.exp 12) ^ q := by rw [hExp q, <- mul_pow]
    _ = _ := by
      congr 1
      dsimp [A]
      rw [Real.exp_add]
      ring

end PrimeFactorOscillations.LPF
