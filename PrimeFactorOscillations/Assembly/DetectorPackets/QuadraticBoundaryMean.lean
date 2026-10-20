/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticDivisorMean
import PrimeFactorOscillations.Assembly.DetectorPackets.QuadraticMainTermCancellation

/-!
# QuadraticBoundaryMean

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

namespace PrimeFactorOscillations.QuadraticBoundaryMean

open QuadraticCarrierPacket QuadraticCoprimeMean IntegerQuadraticPrefix QuadraticDivisorMean

theorem kernel_mul_left (a b n : Nat) :
    kernel (a * b) n = kernel a n * kernel b n := by
  simp only [kernel, Nat.cast_mul, jacobiSym.mul_left, Int.cast_mul]

theorem kernel_square_mask (s n : Nat) (hn : 0 < n) :
    kernel (s ^ 2) n = if Nat.Coprime s n then 1 else 0 := by
  by_cases hc : Nat.Coprime s n
  case pos =>
    rw [ite_eq_left hc]
    exact kernel_square s n (by simpa only [Int.gcd_natCast_natCast] using hc)
  case neg =>
    rw [ite_eq_right hc]
    have hz : jacobiSym (s : Int) n = 0 :=
      jacobiSym.eq_zero_iff.mpr (And.intro (Nat.ne_of_gt hn)
        (by simpa only [Int.gcd_natCast_natCast] using hc))
    have hzK : kernel s n = 0 := by simp only [kernel, hz, Int.cast_zero]
    rw [pow_two, kernel_mul_left, hzK, zero_mul]

theorem kernel_square_factor (s r n : Nat) (hn : 0 < n) :
    kernel (s ^ 2 * r) n = if Nat.Coprime s n then kernel r n else 0 := by
  rw [kernel_mul_left, kernel_square_mask s n hn]
  split_ifs <;> simp

def coprimeColumn (s : Nat) (a : Nat -> Complex) (n : Nat) : Complex :=
  if Nat.Coprime s n then a n else 0

theorem square_row_form (S T : Finset Nat) (a b : Nat -> Complex) (s r : Nat)
    (hS : forall n, Membership.mem S n -> 0 < n)
    (hT : forall n, Membership.mem T n -> 0 < n) :
    coprimeForm S T
      (fun n => a n * kernel (s ^ 2 * r) n)
      (fun m => b m * kernel (s ^ 2 * r) m) =
    coprimeForm S T
      (fun n => coprimeColumn s a n * kernel r n)
      (fun m => coprimeColumn s b m * kernel r m) := by
  unfold coprimeForm
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  dsimp only
  rw [kernel_square_factor s r n (hS n hn), kernel_square_factor s r m (hT m hm)]
  unfold coprimeColumn
  split_ifs <;> ring

theorem coprimeColumn_mass_le (q : Nat) (S : Finset Nat) (a : Nat -> Complex) :
    maskedMass 1 S (coprimeColumn q a) <= maskedMass 1 S a := by
  unfold maskedMass
  simp only [one_dvd, ite_true]
  apply Finset.sum_le_sum
  intro n hn
  by_cases hc : Nat.Coprime q n
  case pos => simp only [coprimeColumn, ite_eq_left hc, le_refl]
  case neg => simp only [coprimeColumn, ite_eq_right hc, norm_zero, zero_pow (by decide : Not (2 = 0))]
              exact sq_nonneg _

theorem square_row_mean (eps : Real) (heps : 0 < eps) :
    exists C : Real, 0 < C /\
      forall (M N1 N2 q : Nat) (rows S T : Finset Nat) (a b : Nat -> Complex),
      (forall r, Membership.mem rows r -> Membership.mem (columns M) r) ->
      (forall n, Membership.mem S n -> Membership.mem (columns N1) n) ->
      (forall m, Membership.mem T m -> Membership.mem (columns N2) m) ->
      rows.sum (fun r => norm (coprimeForm S T
        (fun n => a n * kernel (q ^ 2 * r) n)
        (fun m => b m * kernel (q ^ 2 * r) m))) <=
      C * ((max N1 N2 : Nat) : Real) ^ eps *
        Real.sqrt (prefixNorm M N1 * maskedMass 1 S a) *
        Real.sqrt (prefixNorm M N2 * maskedMass 1 T b) := by
  choose C hC hc using coprime_mean_subpower eps heps
  refine Exists.intro C (And.intro hC ?_)
  intro M N1 N2 q rows S T a b hr hS hT
  have hb := hc M N1 N2 1 1 Nat.zero_lt_one Nat.zero_lt_one rows S T
    (coprimeColumn q a) (coprimeColumn q b) hr hS hT
  simp only [Nat.div_one, one_dvd, ite_true] at hb
  have haP : 0 <= prefixNorm M N1 := by unfold prefixNorm; exact sq_nonneg _
  have hbP : 0 <= prefixNorm M N2 := by unfold prefixNorm; exact sq_nonneg _
  have hA := Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_left (coprimeColumn_mass_le q S a) haP)
  have hB := Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_left (coprimeColumn_mass_le q T b) hbP)
  have hscale : 0 <= C * ((max N1 N2 : Nat) : Real) ^ eps := by positivity
  have hforms (r : Nat) := square_row_form S T a b q r
    (fun n hn => (columns_bounds N1 n (hS n hn)).1)
    (fun m hm => (columns_bounds N2 m (hT m hm)).1)
  simp_rw [hforms]
  apply hb.trans
  apply mul_le_mul
  . exact mul_le_mul_of_nonneg_left hA hscale
  . exact hB
  . exact Real.sqrt_nonneg _
  . exact mul_nonneg hscale (Real.sqrt_nonneg _)

end PrimeFactorOscillations.QuadraticBoundaryMean
