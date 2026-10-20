/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.CoprimeCompensatedWave

/-!
# MobiusCompensatedCovariance

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

namespace PrimeFactorOscillations.MobiusCompensatedCovariance

open QuadraticCoprimeMean

theorem multipleSum_sub_scale (d : Nat) (S : Finset Nat)
    (a b : Nat -> Complex) (c : Complex) :
    multipleSum d S (fun n => a n - c * b n) =
      multipleSum d S a - c * multipleSum d S b := by
  unfold multipleSum
  rw [Finset.mul_sum, <- Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hd : Dvd.dvd d n
  . simp only [if_pos hd]
  . simp only [if_neg hd]
    ring

theorem exact_signed_divisor_packet (N : Nat) (S : Finset Nat)
    (hS : forall n, Membership.mem S n -> 0 < n /\ n <= N)
    (a b : Nat -> Complex) (c : Complex) :
    coprimeForm S S (fun n => a n - c * b n)
        (fun n => star (a n - c * b n)) =
      (Finset.Ioc 0 N).sum (fun d =>
        (ArithmeticFunction.moebius d : Complex) *
          (multipleSum d S a - c * multipleSum d S b) *
          (multipleSum d S (fun n => star (a n)) -
            star c * multipleSum d S (fun n => star (b n)))) := by
  rw [coprimeForm_factorization N S S hS]
  apply Finset.sum_congr rfl
  intro d hd
  rw [multipleSum_sub_scale]
  have hstar : (fun n => star (a n - c * b n)) =
      (fun n => star (a n) - star c * star (b n)) := by
    funext n
    simp only [star_sub, star_mul]
    ring
  rw [hstar, multipleSum_sub_scale]

theorem compensated_multiple_square_expansion (x y c : Complex) :
    (x - c * y) * star (x - c * y) =
      x * star x - c * y * star x - star c * x * star y +
        (c * star c) * y * star y := by
  simp only [star_sub, star_mul]
  ring

end PrimeFactorOscillations.MobiusCompensatedCovariance

