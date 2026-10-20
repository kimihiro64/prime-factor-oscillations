/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.DepletedMobiusUniform
import PrimeFactorOscillations.Assembly.DetectorPackets.IntegerQuadraticPrefix

/-!
# QuadraticDivisorMean

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/- 
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described by LICENSE.
Authors: Prime Factor Oscillations contributors
-/


noncomputable section
open scoped BigOperators Classical

namespace PrimeFactorOscillations.QuadraticDivisorMean

open DepletedMobius QuadraticCoprimeMean IntegerQuadraticPrefix QuadraticCarrierPacket

theorem divisor_decay_sum_le (n : Nat) (hn : 0 < n) (alpha : Real) :
    n.divisors.sum (fun d => 1 / (d : Real) ^ alpha) <= smoothMass n n alpha := by
  have hsub : n.divisors <= Finset.Ioc 0 n := by
    intro d hd
    exact Finset.mem_Ioc.mpr (And.intro (Nat.pos_of_mem_divisors hd)
      (Nat.le_of_dvd hn (Nat.mem_divisors.mp hd).1))
  have hsupport (d : Nat) (hd : Membership.mem n.divisors d) : SupportedOn n d :=
    And.intro (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd))
      (fun p _ hpd => hpd.trans (Nat.mem_divisors.mp hd).1)
  calc
    _ = n.divisors.sum (fun d => if SupportedOn n d then 1 / (d : Real) ^ alpha else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [ite_eq_left (hsupport d hd)]
    _ <= (Finset.Ioc 0 n).sum (fun d =>
        if SupportedOn n d then 1 / (d : Real) ^ alpha else 0) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro d hd hnot
      split_ifs <;> positivity
    _ = _ := rfl

theorem divisor_card_le_euler (n : Nat) (hn : 0 < n)
    (alpha : Real) (halpha : 0 < alpha) :
    (n.divisors.card : Real) <= (n : Real) ^ alpha * eulerMask n alpha := by
  have hterm (d : Nat) (hd : Membership.mem n.divisors d) :
      (1 : Real) <= (n : Real) ^ alpha * (1 / (d : Real) ^ alpha) := by
    have hdpos : 0 < (d : Real) := by exact_mod_cast Nat.pos_of_mem_divisors hd
    have hdle : (d : Real) <= (n : Real) := by
      exact_mod_cast Nat.le_of_dvd hn (Nat.mem_divisors.mp hd).1
    calc
      1 = (d : Real) ^ alpha * (1 / (d : Real) ^ alpha) := by
        field_simp
      _ <= _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hdpos.le hdle halpha.le) (by positivity)
  calc
    _ = n.divisors.sum (fun _ => (1 : Real)) := by simp
    _ <= n.divisors.sum (fun d => (n : Real) ^ alpha * (1 / (d : Real) ^ alpha)) :=
      Finset.sum_le_sum hterm
    _ = (n : Real) ^ alpha * n.divisors.sum (fun d => 1 / (d : Real) ^ alpha) :=
      (Finset.mul_sum _ _ _).symm
    _ <= (n : Real) ^ alpha * smoothMass n n alpha :=
      mul_le_mul_of_nonneg_left (divisor_decay_sum_le n hn alpha) (by positivity)
    _ <= _ := mul_le_mul_of_nonneg_left
      (smoothMass_le_eulerMask n n (Nat.ne_of_gt hn) halpha) (by positivity)

theorem divisor_card_subpower (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\ forall n : Nat, 0 < n ->
      (n.divisors.card : Real) <= C * (n : Real) ^ eps := by
  let alpha := eps / 2
  have halpha : 0 < alpha := by dsimp only [alpha]; positivity
  choose C hC hc using eulerMask_subpower alpha alpha halpha halpha
  refine Exists.intro C (And.intro hC ?_)
  intro n hn
  have hnpos : 0 < (n : Real) := by exact_mod_cast hn
  have hp : (n : Real) ^ alpha * (n : Real) ^ alpha = (n : Real) ^ eps := by
    rw [<- Real.rpow_add hnpos]
    congr 1
    dsimp only [alpha]
    ring
  calc
    _ <= (n : Real) ^ alpha * eulerMask n alpha :=
      divisor_card_le_euler n hn alpha halpha
    _ <= (n : Real) ^ alpha * (C * (n : Real) ^ alpha) :=
      mul_le_mul_of_nonneg_left (hc n (Nat.ne_of_gt hn)) (by positivity)
    _ = C * ((n : Real) ^ alpha * (n : Real) ^ alpha) := by ring
    _ = _ := by rw [hp]

def maskedMass (e : Nat) (s : Finset Nat) (a : Nat -> Complex) : Real :=
  s.sum (fun n => if Dvd.dvd e n then norm (a n) ^ 2 else 0)

theorem maskedMass_nonneg (e : Nat) (s : Finset Nat) (a : Nat -> Complex) :
    0 <= maskedMass e s a := by
  apply Finset.sum_nonneg
  intro n hn
  split_ifs
  . exact sq_nonneg _
  . exact le_refl _

theorem weighted_mass_le (eps C : Real) (heps : 0 < eps) (hC : 0 < C)
    (hc : forall n : Nat, 0 < n -> (n.divisors.card : Real) <= C * (n : Real) ^ eps)
    (J e : Nat) (s : Finset Nat) (a : Nat -> Complex)
    (hs : forall n, Membership.mem s n -> 0 < n /\ n <= J) :
    divisorWeightedMass J e s a <= C * (J : Real) ^ eps * maskedMass e s a := by
  unfold divisorWeightedMass maskedMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  by_cases he : Dvd.dvd e n
  case pos =>
    rw [ite_eq_left he, ite_eq_left he,
      divisorCount_eq_card_divisors J n (hs n hn).1 (hs n hn).2]
    have hpow : (n : Real) ^ eps <= (J : Real) ^ eps :=
      Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast (hs n hn).2) heps.le
    exact mul_le_mul_of_nonneg_right
      ((hc n (hs n hn).1).trans (mul_le_mul_of_nonneg_left hpow hC.le)) (sq_nonneg _)
  case neg =>
    rw [ite_eq_right he, ite_eq_right he, mul_zero]

theorem columns_bounds (N n : Nat) (hn : Membership.mem (columns N) n) :
    0 < n /\ n <= N := by
  have h := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
  exact And.intro h.1 h.2

theorem coprime_mean_subpower (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall (M N1 N2 e1 e2 : Nat), 0 < e1 -> 0 < e2 ->
      forall (rows s t : Finset Nat) (a b : Nat -> Complex),
      (forall r, Membership.mem rows r -> Membership.mem (columns M) r) ->
      (forall n, Membership.mem s n -> Membership.mem (columns N1) n) ->
      (forall m, Membership.mem t m -> Membership.mem (columns N2) m) ->
      rows.sum (fun r => norm (coprimeForm s t
        (fun n => (if Dvd.dvd e1 n then a n else 0) * kernel r n)
        (fun m => (if Dvd.dvd e2 m then b m else 0) * kernel r m))) <=
      C * ((max N1 N2 : Nat) : Real) ^ eps *
        Real.sqrt (prefixNorm M (N1 / e1) * maskedMass e1 s a) *
        Real.sqrt (prefixNorm M (N2 / e2) * maskedMass e2 t b) := by
  choose C hC hc using divisor_card_subpower eps heps
  refine Exists.intro C (And.intro hC ?_)
  intro M N1 N2 e1 e2 he1 he2 rows s t a b hr hs ht
  let J := max N1 N2
  let scale := C * (J : Real) ^ eps
  have hz : 0 <= scale := mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg J) eps)
  have hsJ : forall n, Membership.mem s n -> 0 < n /\ n <= J := by
    intro n hn
    have hb := columns_bounds N1 n (hs n hn)
    exact And.intro hb.1 (hb.2.trans (le_max_left _ _))
  have htJ : forall n, Membership.mem t n -> 0 < n /\ n <= J := by
    intro n hn
    have hb := columns_bounds N2 n (ht n hn)
    exact And.intro hb.1 (hb.2.trans (le_max_right _ _))
  have ha := weighted_mass_le eps C heps hC hc J e1 s a hsJ
  have hb := weighted_mass_le eps C heps hC hc J e2 t b htJ
  have hp1 : 0 <= prefixNorm M (N1 / e1) := by unfold prefixNorm; exact sq_nonneg _
  have hp2 : 0 <= prefixNorm M (N2 / e2) := by unfold prefixNorm; exact sq_nonneg _
  have h1 : Real.sqrt (prefixNorm M (N1 / e1) * divisorWeightedMass J e1 s a) <=
      Real.sqrt scale * Real.sqrt (prefixNorm M (N1 / e1) * maskedMass e1 s a) := by
    calc
      _ <= Real.sqrt (prefixNorm M (N1 / e1) * (scale * maskedMass e1 s a)) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left ha hp1)
      _ = _ := by
        rw [show prefixNorm M (N1 / e1) * (scale * maskedMass e1 s a) =
          scale * (prefixNorm M (N1 / e1) * maskedMass e1 s a) from by ring,
          Real.sqrt_mul hz]
  have h2 : Real.sqrt (prefixNorm M (N2 / e2) * divisorWeightedMass J e2 t b) <=
      Real.sqrt scale * Real.sqrt (prefixNorm M (N2 / e2) * maskedMass e2 t b) := by
    calc
      _ <= Real.sqrt (prefixNorm M (N2 / e2) * (scale * maskedMass e2 t b)) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hb hp2)
      _ = _ := by
        rw [show prefixNorm M (N2 / e2) * (scale * maskedMass e2 t b) =
          scale * (prefixNorm M (N2 / e2) * maskedMass e2 t b) from by ring,
          Real.sqrt_mul hz]
  apply (coprime_mean_prefix_bound M N1 N2 e1 e2 he1 he2 rows s t a b hr hs ht).trans
  have hm := mul_le_mul h1 h2 (Real.sqrt_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  calc
    _ <= _ := hm
    _ = _ := by
      change (Real.sqrt scale * _) * (Real.sqrt scale * _) = scale * _ * _
      have hh : Real.sqrt scale * Real.sqrt scale = scale := by
        simpa only [pow_two] using Real.sq_sqrt hz
      calc
        _ = (Real.sqrt scale * Real.sqrt scale) *
          Real.sqrt (prefixNorm M (N1 / e1) * maskedMass e1 s a) *
          Real.sqrt (prefixNorm M (N2 / e2) * maskedMass e2 t b) := by ring
        _ = _ := by rw [hh]

end PrimeFactorOscillations.QuadraticDivisorMean
