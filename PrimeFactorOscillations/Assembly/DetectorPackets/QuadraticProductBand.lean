/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticProductDivisor

/-!
# QuadraticProductBand

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

namespace PrimeFactorOscillations.QuadraticProductBand

open QuadraticCarrierPacket QuadraticCoprimeMean QuadraticDivisorBand
open QuadraticProductDivisor

def factorBand (D : Nat) : Finset (Prod Nat Nat) :=
  ((Finset.Icc 1 (2 * D)).product (Finset.Icc 1 (2 * D))).filter
    (fun p => D < p.1 * p.2 /\ p.1 * p.2 <= 2 * D)

theorem divisor_sum_extend (d H : Nat) (hd : 0 < d) (hdH : d <= H)
    (F : Nat -> Real) :
    d.divisors.sum F =
      (Finset.Icc 1 H).sum (fun e => if Dvd.dvd e d then F e else 0) := by
  have hset : d.divisors = (Finset.Icc 1 H).filter (fun e => Dvd.dvd e d) := by
    apply Finset.ext
    intro e
    constructor
    . intro he
      have hed := (Nat.mem_divisors.mp he).1
      have hepos := Nat.pos_of_dvd_of_pos hed hd
      have heH := (Nat.le_of_dvd hd hed).trans hdH
      exact Finset.mem_filter.mpr
        (And.intro (Finset.mem_Icc.mpr (And.intro hepos heH)) hed)
    . intro he
      exact Nat.mem_divisors.mpr
        (And.intro (Finset.mem_filter.mp he).2 (Nat.ne_of_gt hd))
  rw [hset, Finset.sum_filter]

theorem product_divisor_reindex (D : Nat) (F : Nat -> Nat -> Real) :
    (Finset.Ioc D (2 * D)).sum (fun d => d.divisors.sum (fun e => F e (d / e))) =
      (factorBand D).sum (fun p => F p.1 p.2) := by
  let A := ((Finset.Ioc D (2 * D)).product (Finset.Icc 1 (2 * D))).filter
    (fun p => Dvd.dvd p.2 p.1)
  have hext : (Finset.Ioc D (2 * D)).sum
      (fun d => d.divisors.sum (fun e => F e (d / e))) =
      A.sum (fun p => F p.2 (p.1 / p.2)) := by
    dsimp only [A]
    rw [Finset.sum_filter]
    calc
      _ = (Finset.Ioc D (2 * D)).sum (fun d =>
          (Finset.Icc 1 (2 * D)).sum
            (fun e => if Dvd.dvd e d then F e (d / e) else 0)) := by
        apply Finset.sum_congr rfl
        intro d hd
        have hb := Finset.mem_Ioc.mp hd
        exact divisor_sum_extend d (2 * D) ((Nat.zero_le D).trans_lt hb.1) hb.2 _
      _ = _ := (Finset.sum_product (Finset.Ioc D (2 * D)) (Finset.Icc 1 (2 * D))
        (fun p => if Dvd.dvd p.2 p.1 then F p.2 (p.1 / p.2) else 0)).symm
  rw [hext]
  apply Finset.sum_bij (fun p _ => Prod.mk p.2 (p.1 / p.2))
  . intro p hp
    have h := Finset.mem_filter.mp hp
    have hpair := Finset.mem_product.mp h.1
    have hd := Finset.mem_Ioc.mp hpair.1
    have he := Finset.mem_Icc.mp hpair.2
    have hdpos : 0 < p.1 := (Nat.zero_le D).trans_lt hd.1
    have hepos : 0 < p.2 := he.1
    have hqpos : 0 < p.1 / p.2 :=
      Nat.div_pos (Nat.le_of_dvd hdpos h.2) hepos
    have hqbound : p.1 / p.2 <= 2 * D := (Nat.div_le_self _ _).trans hd.2
    apply Finset.mem_filter.mpr
    refine And.intro (Finset.mem_product.mpr
      (And.intro hpair.2 (Finset.mem_Icc.mpr (And.intro hqpos hqbound)))) ?_
    simpa only [Nat.mul_div_cancel' h.2] using hd
  . intro p hp q hq heq
    have hpdiv := (Finset.mem_filter.mp hp).2
    have hqdiv := (Finset.mem_filter.mp hq).2
    have he : p.2 = q.2 := congrArg Prod.fst heq
    have hd : p.2 * (p.1 / p.2) = q.2 * (q.1 / q.2) :=
      congrArg (fun x : Prod Nat Nat => x.1 * x.2) heq
    rw [Nat.mul_div_cancel' hpdiv, Nat.mul_div_cancel' hqdiv] at hd
    exact Prod.ext hd he
  . intro p hp
    have h := Finset.mem_filter.mp hp
    have hpair := Finset.mem_product.mp h.1
    have hu := Finset.mem_Icc.mp hpair.1
    have hu0 : 0 < p.1 := hu.1
    refine Exists.intro (Prod.mk (p.1 * p.2) p.1) ?_
    refine Exists.intro ?_ ?_
    . apply Finset.mem_filter.mpr
      refine And.intro
        (Finset.mem_product.mpr (And.intro (Finset.mem_Ioc.mpr h.2) hpair.1)) ?_
      exact Exists.intro p.2 rfl
    . apply Prod.ext
      . rfl
      . exact Nat.mul_div_right p.2 hu0
  . intro p hp
    rfl

def productBandMean (D : Nat) (R S T : Finset Nat) (a b : Nat -> Complex) : Real :=
  (Finset.Ioc D (2 * D)).sum (fun d => R.sum (fun r => norm (divisorRow d S T a b r)))

theorem product_band_mean_le (D : Nat) (R S T : Finset Nat) (a b : Nat -> Complex) :
    productBandMean D R S T a b <=
      (factorBand D).sum (fun p => maskedRowMean R S T a b p.1 p.2) := by
  calc
    _ <= (Finset.Ioc D (2 * D)).sum
        (fun d => d.divisors.sum (fun e => maskedRowMean R S T a b e (d / e))) := by
      apply Finset.sum_le_sum
      intro d hd
      exact divisor_row_mean_le d ((Nat.zero_le D).trans_lt (Finset.mem_Ioc.mp hd).1)
        R S T a b
    _ = _ := product_divisor_reindex D (maskedRowMean R S T a b)

end PrimeFactorOscillations.QuadraticProductBand
