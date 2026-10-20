/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.MobiusDirichletReciprocal
import PrimeFactorOscillations.Assembly.DetectorPackets.RationalReciprocalRegular

/-!
# MobiusWindowMellin

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
open MeasureTheory
open PrimeFactorOscillations.MobiusDirichlet
open PrimeFactorOscillations.RationalInverseLine

namespace PrimeFactorOscillations.MobiusWindow

def positiveNorm (n : Nat) : Real := (n + 1 : Nat)

def coefficient {q : Nat} (chi : DirichletCharacter Complex q) (n : Nat) : Complex :=
  (ArithmeticFunction.moebius (n + 1) : Complex) * chi ((n + 1 : Nat) : ZMod q)

theorem positiveNorm_pos (n : Nat) : 0 < positiveNorm n := by
  change (0 : Real) < ((n + 1 : Nat) : Real)
  exact_mod_cast Nat.succ_pos n

theorem positiveNorm_cast (n : Nat) :
    (positiveNorm n : Complex) = ((n + 1 : Nat) : Complex) := by
  exact Complex.ofReal_natCast (n + 1)

theorem coefficient_norm_le {q : Nat} (chi : DirichletCharacter Complex q) (n : Nat) :
    norm (coefficient chi n) <= 1 :=
  mobius_coefficient_norm_le chi (n + 1)

theorem weighted_coefficient_summable {q : Nat} (chi : DirichletCharacter Complex q) :
    Summable (fun n : Nat => norm (coefficient chi n) * (positiveNorm n) ^ (-(2 : Real))) := by
  have hseries : Summable (LSeries.term (mobiusArithmetic chi) (2 : Complex)) :=
    mobius_LSeriesSummable chi 2 (by norm_num)
  have hnorm := hseries.norm
  have htail : Summable (fun n : Nat =>
      norm (LSeries.term (mobiusArithmetic chi) (2 : Complex) (n + 1))) :=
    hnorm.comp_injective (show Function.Injective (fun n : Nat => n + 1) by
      intro m n h
      change m + 1 = n + 1 at h
      exact Nat.add_right_cancel h)
  convert htail using 1
  ext n
  rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n)]
  change norm (coefficient chi n) * (positiveNorm n) ^ (-(2 : Real)) =
    norm (coefficient chi n / (((n + 1 : Nat) : Complex) ^ (2 : Complex)))
  rw [div_eq_mul_inv, <- Complex.cpow_neg, norm_mul, <- positiveNorm_cast n,
    Complex.norm_cpow_eq_rpow_re_of_pos (positiveNorm_pos n)]
  norm_num

theorem positive_series_eq_inverse {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : 0 < q)
    (s : Complex) (hs : 1 < s.re) :
    letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
    (tsum (fun n : Nat => coefficient chi n * (positiveNorm n : Complex) ^ (-s))) =
      Inv.inv (DirichletCharacter.LFunction chi s) := by
  letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
  have hseries : Summable (LSeries.term (mobiusArithmetic chi) s) :=
    mobius_LSeriesSummable chi s hs
  have hsum := Summable.sum_add_tsum_nat_add 1 hseries
  have htail : (tsum (fun n : Nat => LSeries.term (mobiusArithmetic chi) s (n + 1))) =
      LSeries (mobiusArithmetic chi) s := by
    simpa only [Finset.sum_range_one, LSeries.term_zero, zero_add, LSeries] using hsum
  calc
    _ = tsum (fun n : Nat => LSeries.term (mobiusArithmetic chi) s (n + 1)) := by
      apply tsum_congr
      intro n
      rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n),
        positiveNorm_cast, Complex.cpow_neg, div_eq_mul_inv]
      rfl
    _ = LSeries (mobiusArithmetic chi) s := htail
    _ = _ := by
      simpa [mobiusArithmetic, PrimeFactorOscillations.DepletedMobius.twist] using
        mobius_LSeries_eq_inverse chi hq s hs

def smoothWindow {q : Nat} (chi : DirichletCharacter Complex q)
    (W : Real -> Complex) (y : Real) : Complex :=
  tsum (fun n : Nat => coefficient chi n * W (positiveNorm n / y))

theorem smoothWindow_mellin_right {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : 0 < q)
    (W : Real -> Complex) (a b : Real) (ha : 0 < a)
    (hsupp : Function.support W <= Set.Icc a b)
    (hW : ContDiff Real ((Top.top : ENat) : WithTop ENat) W)
    (y : Real) (hy : 0 < y) :
    letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
    smoothWindow chi W y = (1 / (2 * Real.pi) : Complex) *
      integral volume (fun t : Real =>
        mellin W ((2 : Complex) + (t : Complex) * Complex.I) *
          (y : Complex) ^ ((2 : Complex) + (t : Complex) * Complex.I) *
          Inv.inv (DirichletCharacter.LFunction chi
            ((2 : Complex) + (t : Complex) * Complex.I))) := by
  letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
  unfold smoothWindow
  rw [OAI.CompletedGauss.weightedMellin_inversion positiveNorm positiveNorm_pos
    (coefficient chi) 2 (weighted_coefficient_summable chi) W a b ha hsupp hW y hy]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by
    dsimp only
    simp only [Complex.ofReal_ofNat]
    rw [positive_series_eq_inverse chi hq _ (by simp)])

end PrimeFactorOscillations.MobiusWindow
