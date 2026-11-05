/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The third integral jet of a septic cyclotomic relation

This supporting ramification congruence is used on the complete signed
Jacobi beta polynomial, not on the magnitudes of its factors.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

namespace Metaplectic.CyclotomicJet

/-- A relation at a primitive seventh root has third jet divisible by seven. -/
theorem septic_third_derivative_divisible
    {K : Type*} [Field K] [CharZero K]
    (z : K) (hz : IsPrimitiveRoot z 7) (P : Polynomial Int)
    (hP : Polynomial.aeval z P = 0) :
    Dvd.dvd (7 : Int) (P.derivative.derivative.derivative.eval 1) := by
  have : Fact (Nat.Prime 7) := Fact.mk (by decide)
  have hdiv : Dvd.dvd (Polynomial.cyclotomic 7 Int) P := by
    rw [Polynomial.cyclotomic_eq_minpoly hz (by decide)]
    exact minpoly.isIntegrallyClosed_dvd (hz.isIntegral (by decide)) hP
  have hphi : Polynomial.cyclotomic 7 Int =
      Polynomial.X ^ 6 + Polynomial.X ^ 5 + Polynomial.X ^ 4 +
        Polynomial.X ^ 3 + Polynomial.X ^ 2 + Polynomial.X + 1 := by
    rw [Polynomial.cyclotomic_prime Int 7]
    norm_num [Finset.sum_range_succ]
    ring
  have h0 : (Polynomial.cyclotomic 7 Int).eval 1 = 7 := by
    rw [hphi]
    norm_num
  have h1 : (Polynomial.cyclotomic 7 Int).derivative.eval 1 = 21 := by
    rw [hphi]
    norm_num [Polynomial.derivative_add, Polynomial.derivative_X_pow]
  have h2 : (Polynomial.cyclotomic 7 Int).derivative.derivative.eval 1 = 70 := by
    rw [hphi]
    norm_num [Polynomial.derivative_add, Polynomial.derivative_mul,
      Polynomial.derivative_X_pow]
  have h3 : (Polynomial.cyclotomic 7 Int).derivative.derivative.derivative.eval 1 =
      210 := by
    rw [hphi]
    norm_num [Polynomial.derivative_add, Polynomial.derivative_mul,
      Polynomial.derivative_X_pow]
  cases hdiv with
  | intro Q hQ =>
    refine Exists.intro
      (30 * Q.eval 1 + 30 * Q.derivative.eval 1 +
        9 * Q.derivative.derivative.eval 1 +
        Q.derivative.derivative.derivative.eval 1) ?_
    rw [hQ]
    simp only [Polynomial.derivative_mul, Polynomial.derivative_add,
      Polynomial.eval_mul, Polynomial.eval_add, h0, h1, h2, h3]
    ring


private theorem triple_zero_third_jet (f g h : Polynomial Int)
    (hf : f.eval 1 = 0) (hg : g.eval 1 = 0) (hh : h.eval 1 = 0) :
    (f * g * h).derivative.derivative.derivative.eval 1 =
      6 * f.derivative.eval 1 * g.derivative.eval 1 * h.derivative.eval 1 := by
  simp only [Polynomial.derivative_mul, Polynomial.derivative_add,
    Polynomial.eval_add, Polynomial.eval_mul, hf, hg, hh,
    mul_zero, zero_mul, zero_add, add_zero]
  ring

noncomputable def septicBeta (P : Polynomial Int) : Polynomial Int :=
  (P - P.comp (Polynomial.X ^ 3)) *
    (P.comp (Polynomial.X ^ 2) - P.comp (Polynomial.X ^ 6)) *
    (P.comp (Polynomial.X ^ 4) - P.comp (Polynomial.X ^ 5))

noncomputable def septicTau : Polynomial Int :=
  Polynomial.X + Polynomial.X ^ 2 + Polynomial.X ^ 4 -
    Polynomial.X ^ 3 - Polynomial.X ^ 5 - Polynomial.X ^ 6

/-- All third-jet cross terms reduce exactly to the cube of the first moment. -/
theorem septic_beta_third_derivative (P : Polynomial Int) :
    (septicBeta P).derivative.derivative.derivative.eval 1 =
      -48 * (P.derivative.eval 1) ^ 3 := by
  let f : Polynomial Int := P - P.comp (Polynomial.X ^ 3)
  let g : Polynomial Int := P.comp (Polynomial.X ^ 2) - P.comp (Polynomial.X ^ 6)
  let h : Polynomial Int := P.comp (Polynomial.X ^ 4) - P.comp (Polynomial.X ^ 5)
  have hf : f.eval 1 = 0 := by simp [f, Polynomial.eval_comp]
  have hg : g.eval 1 = 0 := by simp [g, Polynomial.eval_comp]
  have hh : h.eval 1 = 0 := by simp [h, Polynomial.eval_comp]
  have hf1 : f.derivative.eval 1 = -2 * P.derivative.eval 1 := by
    norm_num [f, Polynomial.derivative_comp, Polynomial.derivative_X_pow]
    ring
  have hg1 : g.derivative.eval 1 = -4 * P.derivative.eval 1 := by
    norm_num [g, Polynomial.derivative_comp, Polynomial.derivative_X_pow]
    ring
  have hh1 : h.derivative.eval 1 = -P.derivative.eval 1 := by
    norm_num [h, Polynomial.derivative_comp, Polynomial.derivative_X_pow]
    ring
  change (f * g * h).derivative.derivative.derivative.eval 1 = _
  rw [triple_zero_third_jet f g h hf hg hh, hf1, hg1, hh1]
  ring

theorem septic_tau_third_derivative :
    septicTau.derivative.derivative.derivative.eval 1 = -162 := by
  norm_num [septicTau, Polynomial.derivative_add, Polynomial.derivative_sub,
    Polynomial.derivative_mul, Polynomial.derivative_X_pow]


/-- The complete signed cyclotomic packet forces divisibility of p*m. -/
theorem septic_signed_product_divisibility
    {K : Type*} [Field K] [CharZero K]
    (z : K) (hz : IsPrimitiveRoot z 7) (P : Polynomial Int) (p m : Int)
    (hR : Polynomial.aeval z
      (septicBeta P - Polynomial.C (p * m) * septicTau) = 0)
    (hS : Dvd.dvd (7 : Int) (P.derivative.eval 1)) :
    Dvd.dvd (7 : Int) (p * m) := by
  have hdiv := septic_third_derivative_divisible z hz
    (septicBeta P - Polynomial.C (p * m) * septicTau) hR
  have hjet :
      (septicBeta P - Polynomial.C (p * m) * septicTau).derivative.derivative.derivative.eval 1 =
      -48 * (P.derivative.eval 1) ^ 3 + 162 * p * m := by
    norm_num [Polynomial.derivative_mul, septic_beta_third_derivative,
      septic_tau_third_derivative]
    ring
  cases hS with
  | intro s hs =>
    cases hdiv with
    | intro t ht =>
      rw [hjet, hs] at ht
      refine Exists.intro (t + 2352 * s ^ 3 - 23 * p * m) ?_
      calc
        p * m = (-48 * (7 * s) ^ 3 + 162 * p * m) +
            16464 * s ^ 3 - 161 * p * m := by ring
        _ = 7 * (t + 2352 * s ^ 3 - 23 * p * m) := by
          rw [ht]
          ring

/-- On the split congruence class the same signed relation forces seven divides m. -/
theorem septic_signed_primary_divisibility
    {K : Type*} [Field K] [CharZero K]
    (z : K) (hz : IsPrimitiveRoot z 7) (P : Polynomial Int) (p m : Int)
    (hR : Polynomial.aeval z
      (septicBeta P - Polynomial.C (p * m) * septicTau) = 0)
    (hS : Dvd.dvd (7 : Int) (P.derivative.eval 1))
    (hp : Dvd.dvd (7 : Int) (p - 1)) :
    Dvd.dvd (7 : Int) m := by
  have hpm := septic_signed_product_divisibility z hz P p m hR hS
  cases hp with
  | intro k hk =>
    cases hpm with
    | intro t ht =>
      refine Exists.intro (t - k * m) ?_
      calc
        m = p * m - (p - 1) * m := by ring
        _ = 7 * (t - k * m) := by
          rw [ht, hk]
          ring

/-- The integral polynomial of a finite root-counting vector. -/
noncomputable def countingPolynomial (n : Nat) (v : Fin n -> Nat) : Polynomial Int :=
  Finset.univ.sum (fun j => Polynomial.C (v j : Int) * Polynomial.X ^ j.val)

theorem countingPolynomial_eval {K : Type*} [Field K] [CharZero K]
    (n : Nat) (v : Fin n -> Nat) (w : K) :
    Polynomial.aeval w (countingPolynomial n v) =
      Finset.univ.sum (fun j => (v j : K) * w ^ j.val) := by
  simp [countingPolynomial]

theorem countingPolynomial_derivative (n : Nat) (v : Fin n -> Nat) :
    (countingPolynomial n v).derivative.eval 1 =
      Finset.univ.sum (fun j => (v j : Int) * (j.val : Int)) := by
  change (Polynomial.evalRingHom (1 : Int)) (countingPolynomial n v).derivative = _
  simp [countingPolynomial, Polynomial.derivative_mul, Polynomial.derivative_X_pow,
    mul_comm]

/-- The supported product controls the first integral moment, for every order. -/
theorem countingPolynomial_first_moment_divisible
    {K : Type*} [Field K] [CharZero K]
    (n : Nat) (v : Fin n -> Nat) (z : K) (hz : IsPrimitiveRoot z n)
    (hprod : Finset.univ.prod (fun j => (z ^ j.val) ^ v j) = 1) :
    Dvd.dvd (n : Int) ((countingPolynomial n v).derivative.eval 1) := by
  have hpow : z ^ (Finset.univ.sum (fun j => j.val * v j)) = 1 := by
    simpa only [<- pow_mul, Finset.prod_pow_eq_pow_sum] using hprod
  have hdiv := (hz.pow_eq_one_iff_dvd _).mp hpow
  cases hdiv with
  | intro k hk =>
    refine Exists.intro (k : Int) ?_
    rw [countingPolynomial_derivative]
    have ht := congrArg (fun a : Nat => (a : Int)) hk
    simpa only [Nat.cast_sum, Nat.cast_mul, mul_comm] using ht

end Metaplectic.CyclotomicJet
