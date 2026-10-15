/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFPrimeTargetTruncated

/-! # The large-prime tail in the complete LPF target moment -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

/-- Distinct large prime divisors have a uniform product bound for every v>0. -/
theorem singular_large_prime_product_le (P : Finset Nat) (v : Nat) (Y : Real)
    (hv : 0 < v) (hY : 4 <= Y)
    (hP : forall p, Membership.mem P p ->
      And (Nat.Prime p) (And (Y <= (p : Real)) (Dvd.dvd p v))) :
    Finset.prod P singularFactor <= Real.exp (2 * Real.log (v : Real) / (Y * Real.log Y)) := by
  have hYpos : 0 < Y := by linarith
  have hLogY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hPpos : forall p, Membership.mem P p -> (0 : Real) < (p : Real) := by
    intro p hp
    exact hYpos.trans_le (hP p hp).2.1
  have hProdDiv := (singular_prime_product_dvd_iff P v (fun p hp => (hP p hp).1)).mpr
    (fun p hp => (hP p hp).2.2)
  have hProdLe : Finset.prod P (fun p => (p : Real)) <= (v : Real) := by
    rw [<- Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd hv hProdDiv
  have hLogCount : (P.card : Real) * Real.log Y <= Real.log (v : Real) := by
    calc
      _ = Finset.sum P (fun _ => Real.log Y) := by simp
      _ <= Finset.sum P (fun p => Real.log (p : Real)) := by
        apply Finset.sum_le_sum
        intro p hp
        exact Real.log_le_log hYpos (hP p hp).2.1
      _ = Real.log (Finset.prod P (fun p => (p : Real))) :=
        (Real.log_prod (fun p hp => ne_of_gt (hPpos p hp))).symm
      _ <= Real.log (v : Real) :=
        Real.log_le_log (Finset.prod_pos hPpos) hProdLe
  have hFactorPos : forall p, Membership.mem P p -> 0 < singularFactor p := by
    intro p hp
    have hden : 0 < (p : Real) - 2 := by have h := (hP p hp).2.1; linarith
    have hi : 0 <= 1 / ((p : Real) - 2) := one_div_nonneg.mpr hden.le
    dsimp [singularFactor]
    linarith
  have hFactorLog : forall p, Membership.mem P p ->
      Real.log (singularFactor p) <= 2 / Y := by
    intro p hp
    have hHalf : 0 < Y / 2 := by linarith
    have hden : Y / 2 <= (p : Real) - 2 := by
      have h := (hP p hp).2.1
      linarith
    have hInverse : 1 / ((p : Real) - 2) <= 2 / Y := by
      calc
        _ <= 1 / (Y / 2) := one_div_le_one_div_of_le hHalf hden
        _ = 2 / Y := by field_simp
    have hLog := Real.log_le_sub_one_of_pos (hFactorPos p hp)
    dsimp [singularFactor] at hLog
    change Real.log (1 + 1 / ((p : Real) - 2)) <= 2 / Y
    linarith
  apply (Real.log_le_iff_le_exp (Finset.prod_pos hFactorPos)).mp
  rw [Real.log_prod (fun p hp => ne_of_gt (hFactorPos p hp))]
  have hScaleNonneg : 0 <= 2 / (Y * Real.log Y) :=
    div_nonneg (by norm_num) (mul_pos hYpos hLogY).le
  calc
    _ <= Finset.sum P (fun _ => 2 / Y) :=
      Finset.sum_le_sum (fun p hp => hFactorLog p hp)
    _ = (P.card : Real) * (2 / Y) := by simp
    _ = (2 / (Y * Real.log Y)) * ((P.card : Real) * Real.log Y) := by
      field_simp [ne_of_gt hYpos, ne_of_gt hLogY]
    _ <= (2 / (Y * Real.log Y)) * Real.log (v : Real) :=
      mul_le_mul_of_nonneg_left hLogCount hScaleNonneg
    _ = _ := by ring

/-- The exceptional factor3 and the full large-prime tail are both retained. -/
theorem singular_product_le_truncated (P : Finset Nat) (v : Nat) (Y : Real)
    (hv : 0 < v) (hY : 4 <= Y)
    (hP : forall p, Membership.mem P p ->
      And (Nat.Prime p) (And (3 <= p) (Dvd.dvd p v))) :
    Finset.prod P singularFactor <=
      2 * Real.exp (2 * Real.log (v : Real) / (Y * Real.log Y)) *
        Finset.prod (P.filter (fun (p : Nat) => And (3 < p) ((p : Real) <= Y))) singularFactor := by
  classical
  have hNonneg : forall p, Membership.mem P p -> 0 <= singularFactor p := by
    intro p hp
    have hpR : (3 : Real) <= (p : Real) := by exact_mod_cast (hP p hp).2.1
    have hi : 0 <= 1 / ((p : Real) - 2) := one_div_nonneg.mpr (by linarith)
    dsimp [singularFactor]
    linarith
  have hSplit : Finset.prod P singularFactor =
      Finset.prod (P.filter (fun (p : Nat) => p = 3)) singularFactor *
        Finset.prod (P.filter (fun (p : Nat) => And (3 < p) ((p : Real) <= Y))) singularFactor *
          Finset.prod (P.filter (fun (p : Nat) => Y < (p : Real))) singularFactor := by
    rw [Finset.prod_filter, Finset.prod_filter, Finset.prod_filter,
      <- Finset.prod_mul_distrib, <- Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hp3 := (hP p hp).2.1
    by_cases hThree : p = 3
    next =>
      subst p
      have hHigh : Not (Y < (3 : Real)) := by linarith
      simp [hHigh]
    next =>
      have hLow : 3 < p := by omega
      by_cases hCut : (p : Real) <= Y
      next => simp [hThree, hLow, hCut, not_lt_of_ge hCut]
      next => simp [hThree, hLow, hCut, lt_of_not_ge hCut]
  have hThree : Finset.prod (P.filter (fun (p : Nat) => p = 3)) singularFactor <= 2 := by
    by_cases hMem : Membership.mem P 3
    next =>
      have hSet : P.filter (fun (p : Nat) => p = 3) = {3} := by
        apply Finset.ext
        intro p
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        next => intro h; exact h.2
        next => intro h; subst p; exact And.intro hMem rfl
      rw [hSet]
      norm_num [singularFactor]
    next =>
      have hSet : P.filter (fun (p : Nat) => p = 3) = Finset.empty := by
        apply Finset.ext
        intro p
        constructor
        next =>
          intro hp
          have h := Finset.mem_filter.mp hp
          have heq := h.2
          subst p
          exact False.elim (hMem h.1)
        next => intro hp; simp [Finset.empty] at hp
      rw [hSet]
      norm_num [Finset.empty]
  have hTail := singular_large_prime_product_le
    (P.filter (fun (p : Nat) => Y < (p : Real))) v Y hv hY (by
      intro p hp
      have h := Finset.mem_filter.mp hp
      exact And.intro (hP p h.1).1 (And.intro h.2.le (hP p h.1).2.2))
  have hSmallNonneg : 0 <= Finset.prod
      (P.filter (fun (p : Nat) => And (3 < p) ((p : Real) <= Y))) singularFactor :=
    Finset.prod_nonneg (fun p hp => hNonneg p (Finset.mem_filter.mp hp).1)
  have hLargeNonneg : 0 <= Finset.prod
      (P.filter (fun (p : Nat) => Y < (p : Real))) singularFactor :=
    Finset.prod_nonneg (fun p hp => hNonneg p (Finset.mem_filter.mp hp).1)
  rw [hSplit]
  calc
    _ <= 2 * Finset.prod (P.filter (fun (p : Nat) => And (3 < p) ((p : Real) <= Y))) singularFactor *
        Finset.prod (P.filter (fun (p : Nat) => Y < (p : Real))) singularFactor :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hThree hSmallNonneg) hLargeNonneg
    _ <= 2 * Finset.prod (P.filter (fun (p : Nat) => And (3 < p) ((p : Real) <= Y))) singularFactor *
        Real.exp (2 * Real.log (v : Real) / (Y * Real.log Y)) :=
      mul_le_mul_of_nonneg_left hTail (mul_nonneg (by norm_num) hSmallNonneg)
    _ = _ := by ring

/-- A crude modulus bound suffices because the character estimate loses only logs. -/
theorem log_cutoff_product_le_square (P : Finset Nat) (N : Nat)
    (hP : forall p, Membership.mem P p -> And (1 <= p) (p <= N)) :
    Real.log ((Finset.prod P (fun p => p) : Nat) : Real) <= ((N : Real) + 1) ^ 2 := by
  have hPos : forall p, Membership.mem P p -> (0 : Real) < (p : Real) := by
    intro p hp
    exact_mod_cast (show 0 < p by have h := (hP p hp).1; omega)
  have hCardNat : P.card <= N + 1 := by
    calc
      _ <= (Finset.range (N + 1)).card := Finset.card_le_card (by
        intro p hp
        exact Finset.mem_range.mpr (by have h := (hP p hp).2; omega))
      _ = N + 1 := Finset.card_range _
  have hCard : (P.card : Real) <= (N : Real) + 1 := by exact_mod_cast hCardNat
  rw [Nat.cast_prod, Real.log_prod (fun p hp => ne_of_gt (hPos p hp))]
  calc
    _ <= Finset.sum P (fun _ => (N : Real)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hLog := Real.log_le_sub_one_of_pos (hPos p hp)
      have hBound : (p : Real) <= (N : Real) := by exact_mod_cast (hP p hp).2
      linarith
    _ = (P.card : Real) * (N : Real) := by simp
    _ <= ((N : Real) + 1) * (N : Real) :=
      mul_le_mul_of_nonneg_right hCard (Nat.cast_nonneg N)
    _ <= _ := by
      have hN : (0 : Real) <= (N : Real) := Nat.cast_nonneg N
      nlinarith

end PrimeFactorOscillations.LPF
