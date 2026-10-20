/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.IntegerQuadraticPoissonInteger

/-!
# IntegerQuadraticMask

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

/-! Exact finite Mobius masks for the shared column factor. -/


noncomputable section
namespace PrimeFactorOscillations.IntegerQuadraticMask

theorem sum_moebius_divisors (n : Nat) :
    Finset.sum n.divisors (fun e => (ArithmeticFunction.moebius e : Complex)) =
      if n = 1 then 1 else 0 := by
  have h := congrArg (fun F : ArithmeticFunction Int => F n)
    ArithmeticFunction.moebius_mul_coe_zeta
  have hi : Finset.sum n.divisors (fun e => (ArithmeticFunction.moebius e : Int)) =
      (1 : ArithmeticFunction Int) n := by
    simpa only [ArithmeticFunction.coe_mul_zeta_apply] using h
  change Finset.sum n.divisors (fun e => (ArithmeticFunction.moebius e : Int)) =
    (if n = 1 then 1 else 0) at hi
  exact_mod_cast hi

theorem common_divisors (g u : Nat) (hg : 0 < g) :
    g.divisors.filter (fun e => Dvd.dvd e u) = (Nat.gcd u g).divisors := by
  apply Finset.ext
  intro e
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  . intro h
    exact And.intro (Nat.dvd_gcd h.2 h.1.1)
      (Nat.ne_of_gt (Nat.gcd_pos_of_pos_right u hg))
  . intro h
    exact And.intro
      (And.intro (Nat.dvd_trans h.1 (Nat.gcd_dvd_right u g)) (Nat.ne_of_gt hg))
      (Nat.dvd_trans h.1 (Nat.gcd_dvd_left u g))

theorem coprime_mask (g u : Nat) (hg : 0 < g) :
    (if Nat.Coprime u g then (1 : Complex) else 0) =
      Finset.sum g.divisors (fun e => (ArithmeticFunction.moebius e : Complex) *
        (if Dvd.dvd e u then 1 else 0)) := by
  classical
  symm
  calc
    _ = Finset.sum (g.divisors.filter (fun e => Dvd.dvd e u))
        (fun e => (ArithmeticFunction.moebius e : Complex)) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e he
      by_cases hd : Dvd.dvd e u <;> simp [hd]
    _ = Finset.sum (Nat.gcd u g).divisors
        (fun e => (ArithmeticFunction.moebius e : Complex)) := by
      rw [common_divisors g u hg]
    _ = _ := by
      rw [sum_moebius_divisors]

theorem coprime_mask_int (g : Nat) (hg : 0 < g) (z : Int) :
    (if Nat.Coprime z.natAbs g then (1 : Complex) else 0) =
      Finset.sum g.divisors (fun e => (ArithmeticFunction.moebius e : Complex) *
        (if Dvd.dvd (e : Int) z then 1 else 0)) := by
  simpa only [Int.natCast_dvd] using coprime_mask g z.natAbs hg

theorem coprime_mask_weighted (g : Nat) (hg : 0 < g) (z : Int) (c : Complex) :
    (if Nat.Coprime z.natAbs g then c else 0) =
      Finset.sum g.divisors (fun e => (ArithmeticFunction.moebius e : Complex) *
        (if Dvd.dvd (e : Int) z then c else 0)) := by
  classical
  calc
    _ = (if Nat.Coprime z.natAbs g then (1 : Complex) else 0) * c := by
      by_cases hc : Nat.Coprime z.natAbs g <;> simp [hc]
    _ = _ := by
      rw [coprime_mask_int g hg z, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e he
      by_cases hd : Dvd.dvd (e : Int) z <;> simp [hd]

end PrimeFactorOscillations.IntegerQuadraticMask

