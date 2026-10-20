/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticDivisorBand

/-!
# QuadraticProductDivisor

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

namespace PrimeFactorOscillations.QuadraticProductDivisor

open QuadraticCarrierPacket QuadraticCoprimeMean QuadraticDivisorBand

theorem divisor_split_unique (d n m e : Nat) (hcop : Nat.Coprime n m)
    (hed : Dvd.dvd e d) (hen : Dvd.dvd e n) (hem : Dvd.dvd (d / e) m) :
    e = Nat.gcd d n := by
  apply Nat.dvd_antisymm
  . exact Nat.dvd_gcd hed hen
  . have hc : Nat.Coprime (Nat.gcd d n) (d / e) :=
      Nat.Coprime.of_dvd_right hem
        (Nat.Coprime.of_dvd_left (Nat.gcd_dvd_right d n) hcop)
    apply hc.dvd_mul_right.mp
    rw [Nat.mul_div_cancel' hed]
    exact Nat.gcd_dvd_left d n

theorem divisor_indicator_partition (d n m : Nat) (hd : 0 < d)
    (hcop : Nat.Coprime n m) (z : Complex) :
    (if Dvd.dvd d (n * m) then z else 0) =
      d.divisors.sum (fun e => if Dvd.dvd e n /\ Dvd.dvd (d / e) m then z else 0) := by
  by_cases hdiv : Dvd.dvd d (n * m)
  . rw [if_pos hdiv]
    have hg : 0 < Nat.gcd d n :=
      Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left d n) hd
    have hprod : Nat.gcd d n * Nat.gcd d m = d :=
      (Nat.Coprime.gcd_mul d hcop).symm.trans (Nat.gcd_eq_left hdiv)
    have hquot : d / Nat.gcd d n = Nat.gcd d m := by
      calc
        _ = (Nat.gcd d n * Nat.gcd d m) / Nat.gcd d n :=
          congrArg (fun t => t / Nat.gcd d n) hprod.symm
        _ = _ := Nat.mul_div_right _ hg
    have hmem : Membership.mem d.divisors (Nat.gcd d n) :=
      Nat.mem_divisors.mpr (And.intro (Nat.gcd_dvd_left d n) (Nat.ne_of_gt hd))
    have hcond : Dvd.dvd (Nat.gcd d n) n /\ Dvd.dvd (d / Nat.gcd d n) m := by
      refine And.intro (Nat.gcd_dvd_right d n) ?_
      rw [hquot]
      exact Nat.gcd_dvd_right d m
    symm
    calc
      _ = (if Dvd.dvd (Nat.gcd d n) n /\ Dvd.dvd (d / Nat.gcd d n) m then z else 0) := by
        apply Finset.sum_eq_single (Nat.gcd d n)
        . intro e he hne
          apply if_neg
          intro hc
          exact hne (divisor_split_unique d n m e hcop (Nat.mem_divisors.mp he).1 hc.1 hc.2)
        . intro hnot
          exact False.elim (hnot hmem)
      _ = z := if_pos hcond
  . rw [if_neg hdiv]
    symm
    apply Finset.sum_eq_zero
    intro e he
    apply if_neg
    intro hc
    apply hdiv
    have h := Nat.mul_dvd_mul hc.1 hc.2
    rw [Nat.mul_div_cancel' (Nat.mem_divisors.mp he).1] at h
    exact h

def divisorRow (d : Nat) (S T : Finset Nat) (a b : Nat -> Complex) (r : Nat) : Complex :=
  S.sum (fun n => T.sum (fun m =>
    if Nat.Coprime n m /\ Dvd.dvd d (n * m) then
      (a n * kernel r n) * (b m * kernel r m) else 0))

theorem divisor_row_partition (d : Nat) (hd : 0 < d)
    (S T : Finset Nat) (a b : Nat -> Complex) (r : Nat) :
    divisorRow d S T a b r =
      d.divisors.sum (fun e => coprimeForm S T
        (fun n => (if Dvd.dvd e n then a n else 0) * kernel r n)
        (fun m => (if Dvd.dvd (d / e) m then b m else 0) * kernel r m)) := by
  let F := fun e n m : Nat =>
    if Nat.Coprime n m then
      ((if Dvd.dvd e n then a n else 0) * kernel r n) *
        ((if Dvd.dvd (d / e) m then b m else 0) * kernel r m) else 0
  have hterm (n m : Nat) :
      (if Nat.Coprime n m /\ Dvd.dvd d (n * m) then
        (a n * kernel r n) * (b m * kernel r m) else 0) =
        d.divisors.sum (fun e => F e n m) := by
    by_cases hc : Nat.Coprime n m
    . calc
        _ = (if Dvd.dvd d (n * m) then
            (a n * kernel r n) * (b m * kernel r m) else 0) := by
          by_cases hx : Dvd.dvd d (n * m)
          . rw [if_pos (And.intro hc hx), if_pos hx]
          . rw [if_neg (fun h => hx h.2), if_neg hx]
        _ = d.divisors.sum (fun e => if Dvd.dvd e n /\ Dvd.dvd (d / e) m then
            (a n * kernel r n) * (b m * kernel r m) else 0) :=
          divisor_indicator_partition d n m hd hc _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro e he
          dsimp only [F]
          rw [if_pos hc]
          by_cases hn : Dvd.dvd e n
          . rw [if_pos hn]
            by_cases hm : Dvd.dvd (d / e) m
            . rw [if_pos (And.intro hn hm), if_pos hm]
            . rw [if_neg (fun h => hm h.2), if_neg hm]
              ring
          . rw [if_neg (fun h => hn h.1), if_neg hn]
            ring
    . rw [if_neg (fun h => hc h.1)]
      symm
      apply Finset.sum_eq_zero
      intro e he
      exact if_neg hc
  calc
    _ = S.sum (fun n => T.sum (fun m => d.divisors.sum (fun e => F e n m))) := by
      unfold divisorRow
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      exact hterm n m
    _ = S.sum (fun n => d.divisors.sum (fun e => T.sum (fun m => F e n m))) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact Finset.sum_comm
    _ = d.divisors.sum (fun e => S.sum (fun n => T.sum (fun m => F e n m))) :=
      Finset.sum_comm
    _ = _ := rfl

theorem divisor_row_mean_le (d : Nat) (hd : 0 < d)
    (R S T : Finset Nat) (a b : Nat -> Complex) :
    R.sum (fun r => norm (divisorRow d S T a b r)) <=
      d.divisors.sum (fun e => maskedRowMean R S T a b e (d / e)) := by
  calc
    _ <= R.sum (fun r => d.divisors.sum (fun e => norm (coprimeForm S T
        (fun n => (if Dvd.dvd e n then a n else 0) * kernel r n)
        (fun m => (if Dvd.dvd (d / e) m then b m else 0) * kernel r m)))) := by
      apply Finset.sum_le_sum
      intro r hr
      rw [divisor_row_partition d hd]
      exact norm_sum_le _ _
    _ = _ := by
      rw [Finset.sum_comm]
      rfl

end PrimeFactorOscillations.QuadraticProductDivisor
