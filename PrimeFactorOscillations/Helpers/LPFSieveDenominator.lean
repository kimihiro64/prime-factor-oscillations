/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFSieveLevel

/-!
# Logarithmic truncation of the finite arithmetic sieve denominator

Exact subset identities retain every local weight. A weighted logarithmic
bound then keeps at least half the Euler-product mass below the sieve level.
-/

namespace PrimeFactorOscillations.LPF

private theorem subset_weight_total (P : Finset Nat) (w : Nat -> Real) :
    Finset.sum P.powerset (fun S => Finset.prod S w) =
      Finset.prod P (fun p => 1 + w p) := by
  classical
  simpa [add_comm] using (Finset.prod_add w (fun _ => (1 : Real)) P).symm

private theorem subset_weighted_sum (P : Finset Nat) (w b c : Nat -> Real)
    (hc : forall p, Membership.mem P p -> w p = (1 + w p) * c p) :
    Finset.sum P.powerset (fun S => Finset.prod S w * Finset.sum S b) =
      Finset.prod P (fun p => 1 + w p) * Finset.sum P (fun p => c p * b p) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
    have hOld : forall q, Membership.mem P q -> w q = (1 + w q) * c q :=
      fun q hq => hc q (Finset.mem_insert_of_mem hq)
    have hNew : Finset.sum P.powerset
        (fun S => Finset.prod (insert p S) w * Finset.sum (insert p S) b) =
        w p * (b p * Finset.sum P.powerset (fun S => Finset.prod S w) +
          Finset.sum P.powerset (fun S => Finset.prod S w * Finset.sum S b)) := by
      rw [Finset.mul_sum, mul_add, Finset.mul_sum]
      rw [Finset.mul_sum, <- Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro S hS
      have hpS : Not (Membership.mem S p) :=
        fun h => hp (Finset.mem_powerset.mp hS h)
      rw [Finset.prod_insert hpS, Finset.sum_insert hpS]
      ring
    rw [Finset.sum_powerset_insert hp, hNew, ih hOld, subset_weight_total,
      Finset.prod_insert hp, Finset.sum_insert hp]
    have hcp := hc p (Finset.mem_insert_self p P)
    have hScaled := congrArg
      (fun z : Real => z * b p * Finset.prod P (fun q => 1 + w q)) hcp
    nlinarith only [hScaled]

noncomputable def sieveEulerProduct (P : Finset Nat)
    (A : (p : Nat) -> Finset (ZMod p)) : Real :=
  Finset.prod P (fun p => 1 + ((A p).card : Real) / ((p : Real) - (A p).card))

noncomputable def sieveLogarithmicMean (P : Finset Nat)
    (A : (p : Nat) -> Finset (ZMod p)) : Real :=
  Finset.sum P (fun p => ((A p).card : Real) / (p : Real) * Real.log (p : Real))

theorem sieveEulerProduct_eq_total (P : Finset Nat)
    (A : (p : Nat) -> Finset (ZMod p)) :
    sieveEulerProduct P A = Finset.sum P.powerset
      (fun S => Finset.prod S (fun p =>
        ((A p).card : Real) / ((p : Real) - (A p).card))) :=
  (subset_weight_total P _).symm

theorem sieveEulerProduct_pos (P : Finset Nat)
    (A : (p : Nat) -> Finset (ZMod p))
    (hA : forall p, Membership.mem P p -> And (0 < (A p).card) ((A p).card < p)) :
    0 < sieveEulerProduct P A := by
  apply Finset.prod_pos
  intro p hp
  have hlt : ((A p).card : Real) < (p : Real) := by exact_mod_cast (hA p hp).2
  have hnonneg := div_nonneg (Nat.cast_nonneg (A p).card) (le_of_lt (sub_pos.mpr hlt))
  linarith

/-- Exact logarithmic moment of all subset-product moduli. -/
theorem sieve_weighted_log_identity (P : Finset Nat)
    (A : (p : Nat) -> Finset (ZMod p))
    (hA : forall p, Membership.mem P p -> And (0 < (A p).card) ((A p).card < p)) :
    Finset.sum P.powerset (fun S =>
      Finset.prod S (fun p => ((A p).card : Real) / ((p : Real) - (A p).card)) *
        Real.log ((Finset.prod S (fun p => p) : Nat) : Real)) =
      sieveEulerProduct P A * sieveLogarithmicMean P A := by
  classical
  have hLog : forall S, Membership.mem P.powerset S ->
      Real.log ((Finset.prod S (fun p => p) : Nat) : Real) =
        Finset.sum S (fun p => Real.log (p : Real)) := by
    intro S hS
    have hCast : ((Finset.prod S (fun p => p) : Nat) : Real) =
        Finset.prod S (fun p => (p : Real)) := by simp
    rw [hCast]
    apply Real.log_prod
    intro p hp
    have hpos : 0 < p := lt_trans (hA p (Finset.mem_powerset.mp hS hp)).1
      (hA p (Finset.mem_powerset.mp hS hp)).2
    exact_mod_cast Nat.ne_of_gt hpos
  calc
    _ = Finset.sum P.powerset (fun S =>
        Finset.prod S (fun p => ((A p).card : Real) / ((p : Real) - (A p).card)) *
          Finset.sum S (fun p => Real.log (p : Real))) := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [hLog S hS]
    _ = _ := by
      apply subset_weighted_sum
      intro p hp
      have hpos : (0 : Real) < (p : Real) := by
        exact_mod_cast lt_trans (hA p hp).1 (hA p hp).2
      have hdiff : 0 < (p : Real) - ((A p).card : Real) := by
        have hlt : ((A p).card : Real) < (p : Real) := by exact_mod_cast (hA p hp).2
        linarith
      field_simp
      <;> ring

/-- At least half the Euler mass lies below the level under its explicit log-mean test. -/
theorem sieveLevelWeight_half_le (P : Finset Nat)
    (A : (p : Nat) -> Finset (ZMod p))
    (hA : forall p, Membership.mem P p -> And (0 < (A p).card) ((A p).card < p))
    {Q : Nat} (hQ : 1 < Q)
    (hMean : sieveLogarithmicMean P A <= Real.log (Q : Real) / 2) :
    sieveEulerProduct P A / 2 <= sieveLevelWeight P A Q := by
  classical
  let w := fun S : Finset Nat => Finset.prod S
    (fun p => ((A p).card : Real) / ((p : Real) - (A p).card))
  let d := fun S : Finset Nat => Finset.prod S (fun p => p)
  let B := P.powerset.filter (fun S => Not (d S <= Q))
  have hWeight : forall S, Membership.mem P.powerset S -> 0 <= w S := by
    intro S hS
    apply Finset.prod_nonneg
    intro p hp
    have hlt : ((A p).card : Real) < (p : Real) := by
      exact_mod_cast (hA p (Finset.mem_powerset.mp hS hp)).2
    exact div_nonneg (Nat.cast_nonneg _) (le_of_lt (sub_pos.mpr hlt))
  have hLog : forall S, Membership.mem P.powerset S -> 0 <= Real.log (d S : Real) := by
    intro S hS
    have hPos : 0 < d S := Finset.prod_pos (fun p hp =>
      lt_trans (hA p (Finset.mem_powerset.mp hS hp)).1
        (hA p (Finset.mem_powerset.mp hS hp)).2)
    apply Real.log_nonneg
    exact_mod_cast hPos
  have hPartition : sieveLevelWeight P A Q + Finset.sum B w = sieveEulerProduct P A := by
    have h := Finset.sum_filter_add_sum_filter_not P.powerset (fun S => d S <= Q) w
    exact h.trans (sieveEulerProduct_eq_total P A).symm
  have hLogQ : 0 < Real.log (Q : Real) := Real.log_pos (by exact_mod_cast hQ)
  have hBad : Real.log (Q : Real) * Finset.sum B w <=
      sieveEulerProduct P A * sieveLogarithmicMean P A := by
    calc
      _ = Finset.sum B (fun S => w S * Real.log (Q : Real)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S hS
        ring
      _ <= Finset.sum B (fun S => w S * Real.log (d S : Real)) := by
        apply Finset.sum_le_sum
        intro S hS
        have hs := Finset.mem_filter.mp hS
        apply mul_le_mul_of_nonneg_left _ (hWeight S hs.1)
        apply Real.log_le_log
        next => exact_mod_cast lt_trans Nat.zero_lt_one hQ
        next => exact_mod_cast le_of_lt (Nat.lt_of_not_ge hs.2)
      _ <= Finset.sum P.powerset (fun S => w S * Real.log (d S : Real)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun S hS _ => mul_nonneg (hWeight S hS) (hLog S hS))
      _ = _ := sieve_weighted_log_identity P A hA
  have hMeanBound := mul_le_mul_of_nonneg_left hMean
    (le_of_lt (sieveEulerProduct_pos P A hA))
  nlinarith

/-- The finite sieve with its denominator replaced by half the full Euler product. -/
theorem sieve_card_le_euler (P : Finset Nat)
    (A : (p : Nat) -> Finset (ZMod p))
    (hPrime : forall p, Membership.mem P p -> Nat.Prime p)
    (hA : forall p, Membership.mem P p -> And (0 < (A p).card) ((A p).card < p))
    (X : Finset Nat) {N Q : Nat} (hN : 0 < N) (hQ : 1 < Q)
    (hX : X <= Finset.range N)
    (hAvoid : forall k, Membership.mem X k ->
      forall p, Membership.mem P p -> Not (Membership.mem (A p) (k : ZMod p)))
    (hMean : sieveLogarithmicMean P A <= Real.log (Q : Real) / 2) :
    (X.card : Real) <= 72 * ((N : Real) + (Q : Real) ^ 2) / sieveEulerProduct P A := by
  have hT := sieveEulerProduct_pos P A hA
  have hHalf := sieveLevelWeight_half_le P A hA hQ hMean
  have hK : 0 <= 36 * ((N : Real) + (Q : Real) ^ 2) := by positivity
  calc
    _ <= 36 * ((N : Real) + (Q : Real) ^ 2) / sieveLevelWeight P A Q :=
      sieveLevelWeight_card_le P A hPrime hA X hN (lt_trans Nat.zero_lt_one hQ) hX hAvoid
    _ <= 36 * ((N : Real) + (Q : Real) ^ 2) / (sieveEulerProduct P A / 2) :=
      div_le_div_of_nonneg_left hK (half_pos hT) hHalf
    _ = _ := by ring

theorem sieveLevelWeight_retained_fraction (P : Finset Nat)
    (A : (p : Nat) -> Finset (ZMod p))
    (hA : forall p, Membership.mem P p -> And (0 < (A p).card) ((A p).card < p))
    {Q : Nat} (hQ : 1 < Q) (rho : Real)
    (hMean : sieveLogarithmicMean P A <= rho * Real.log (Q : Real)) :
    (1 - rho) * sieveEulerProduct P A <= sieveLevelWeight P A Q := by
  classical
  let w := fun S : Finset Nat => Finset.prod S
    (fun p => ((A p).card : Real) / ((p : Real) - (A p).card))
  let d := fun S : Finset Nat => Finset.prod S (fun p => p)
  let B := P.powerset.filter (fun S => Not (d S <= Q))
  have hWeight : forall S, Membership.mem P.powerset S -> 0 <= w S := by
    intro S hS
    apply Finset.prod_nonneg
    intro p hp
    have hlt : ((A p).card : Real) < (p : Real) := by
      exact_mod_cast (hA p (Finset.mem_powerset.mp hS hp)).2
    exact div_nonneg (Nat.cast_nonneg _) (le_of_lt (sub_pos.mpr hlt))
  have hLog : forall S, Membership.mem P.powerset S -> 0 <= Real.log (d S : Real) := by
    intro S hS
    have hPos : 0 < d S := Finset.prod_pos (fun p hp =>
      lt_trans (hA p (Finset.mem_powerset.mp hS hp)).1
        (hA p (Finset.mem_powerset.mp hS hp)).2)
    apply Real.log_nonneg
    exact_mod_cast hPos
  have hPartition : sieveLevelWeight P A Q + Finset.sum B w = sieveEulerProduct P A := by
    have h := Finset.sum_filter_add_sum_filter_not P.powerset (fun S => d S <= Q) w
    exact h.trans (sieveEulerProduct_eq_total P A).symm
  have hLogQ : 0 < Real.log (Q : Real) := Real.log_pos (by exact_mod_cast hQ)
  have hBad : Real.log (Q : Real) * Finset.sum B w <=
      sieveEulerProduct P A * sieveLogarithmicMean P A := by
    calc
      _ = Finset.sum B (fun S => w S * Real.log (Q : Real)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S hS
        ring
      _ <= Finset.sum B (fun S => w S * Real.log (d S : Real)) := by
        apply Finset.sum_le_sum
        intro S hS
        have hs := Finset.mem_filter.mp hS
        apply mul_le_mul_of_nonneg_left _ (hWeight S hs.1)
        apply Real.log_le_log
        next => exact_mod_cast lt_trans Nat.zero_lt_one hQ
        next => exact_mod_cast le_of_lt (Nat.lt_of_not_ge hs.2)
      _ <= Finset.sum P.powerset (fun S => w S * Real.log (d S : Real)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun S hS _ => mul_nonneg (hWeight S hS) (hLog S hS))
      _ = _ := sieve_weighted_log_identity P A hA
  have hBadFraction : Finset.sum B w <= rho * sieveEulerProduct P A := by
    apply (mul_le_mul_iff_of_pos_left hLogQ).mp
    calc
      _ <= sieveEulerProduct P A * sieveLogarithmicMean P A := hBad
      _ <= sieveEulerProduct P A * (rho * Real.log (Q : Real)) :=
        mul_le_mul_of_nonneg_left hMean (le_of_lt (sieveEulerProduct_pos P A hA))
      _ = _ := by ring
  linarith

theorem sieve_card_le_euler_retained_fraction (P : Finset Nat)
    (A : (p : Nat) -> Finset (ZMod p))
    (hPrime : forall p, Membership.mem P p -> Nat.Prime p)
    (hA : forall p, Membership.mem P p -> And (0 < (A p).card) ((A p).card < p))
    (X : Finset Nat) {N Q : Nat} (hN : 0 < N) (hQ : 1 < Q)
    (hX : X <= Finset.range N)
    (hAvoid : forall k, Membership.mem X k ->
      forall p, Membership.mem P p -> Not (Membership.mem (A p) (k : ZMod p)))
    (rho : Real) (hrho : rho < 1)
    (hMean : sieveLogarithmicMean P A <= rho * Real.log (Q : Real)) :
    (X.card : Real) <= (36 / (1 - rho)) *
      ((N : Real) + (Q : Real) ^ 2) / sieveEulerProduct P A := by
  have hT := sieveEulerProduct_pos P A hA
  have hFraction := sieveLevelWeight_retained_fraction P A hA hQ rho hMean
  have hR : 0 < 1 - rho := sub_pos.mpr hrho
  have hK : 0 <= 36 * ((N : Real) + (Q : Real) ^ 2) := by positivity
  calc
    _ <= 36 * ((N : Real) + (Q : Real) ^ 2) / sieveLevelWeight P A Q :=
      sieveLevelWeight_card_le P A hPrime hA X hN (lt_trans Nat.zero_lt_one hQ) hX hAvoid
    _ <= 36 * ((N : Real) + (Q : Real) ^ 2) /
        ((1 - rho) * sieveEulerProduct P A) :=
      div_le_div_of_nonneg_left hK (mul_pos hR hT) hFraction
    _ = _ := by
      field_simp [ne_of_gt hR, ne_of_gt hT]
      <;> ring

end PrimeFactorOscillations.LPF
