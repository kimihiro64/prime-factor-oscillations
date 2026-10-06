/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeProfileLogSeries
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Log.CubicRemainder

/-!
# Uniform quadratic Euler-product tail

The exact infinite logarithmic tail retains its quadratic prime-weight sum.
Its remainder is bounded uniformly for every nonnegative real tilt, with
constant and inclusive cutoff explicit.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Filter

def primeProfileQuadraticTail (N : Nat) : Real :=
  tsum (fun p : {p : Nat.Primes // N < (p : Nat)} =>
    (primeProfileWeight (p.val : Nat)) ^ (2 : Nat))

theorem primeProfileQuadraticTail_bounds (N : Nat) (hN : 1 <= N) :
    0 <= primeProfileQuadraticTail N /\
      primeProfileQuadraticTail N <= 2 / (N : Real) := by
  classical
  have hs : Summable (fun p : {p : Nat.Primes // N < (p : Nat)} =>
      (primeProfileWeight (p.val : Nat)) ^ (2 : Nat)) :=
    summable_primeProfileWeight_sq.subtype _
  refine And.intro (tsum_nonneg (fun p => sq_nonneg _)) ?_
  apply le_of_tendsto hs.hasSum
  apply Filter.Eventually.of_forall
  intro s
  let t : Finset Nat.Primes := s.image Subtype.val
  have ht : forall p, Membership.mem t p -> N < (p : Nat) := by
    intro p hp
    choose q hq using Finset.mem_image.mp hp
    rw [<- hq.2]
    exact q.property
  have hsum : t.sum (fun p => (primeProfileWeight (p : Nat)) ^ (2 : Nat)) =
      s.sum (fun p => (primeProfileWeight (p.val : Nat)) ^ (2 : Nat)) := by
    exact Finset.sum_image (fun p _ q _ h => Subtype.ext h)
  rw [<- hsum]
  exact sum_primeProfileWeight_sq_tail_le t N hN ht

private theorem profile_log_cubic_error_bound (a z : Real) (ha : 0 <= a) (hz : 0 <= z) :
    abs (Real.log (1 + a * z) - Real.log (1 + a) * z +
      (z ^ (2 : Nat) - z) / 2 * a ^ (2 : Nat)) <=
      (z ^ (3 : Nat) + z) / 3 * a ^ (3 : Nat) := by
  have h1 := Real.log_one_add_cubic_remainder_bounds (a * z) (mul_nonneg ha hz)
  have h2 := Real.log_one_add_cubic_remainder_bounds a ha
  have hz1 := mul_nonneg hz h2.1
  have hz2 := mul_le_mul_of_nonneg_left h2.2 hz
  have hp : 0 <= z ^ (3 : Nat) * a ^ (3 : Nat) := by positivity
  have hq : 0 <= z * a ^ (3 : Nat) := by positivity
  apply abs_le.mpr
  constructor <;> nlinarith

/-- The full infinite logarithmic tail has its exact quadratic main term
and a cubic remainder uniform for every nonnegative tilt. -/
theorem primeProfile_log_tail_quadratic_bound (N : Nat) (hN : 1 <= N)
    (z : Real) (hz : 0 <= z) :
    abs (Real.log (primeProfile (z : Complex)).re -
      Real.log (primePrefixProfile N (z : Complex)).re +
      (z ^ (2 : Nat) - z) / 2 * primeProfileQuadraticTail N) <=
      2 * (z ^ (3 : Nat) + z) / (3 * (N : Real) ^ (2 : Nat)) := by
  let T := {p : Nat.Primes // N < (p : Nat)}
  let w : T -> Real := fun p => primeProfileWeight (p.val : Nat)
  let f : T -> Real := fun p =>
    Real.log (1 + w p * z) - Real.log (1 + w p) * z
  let e : T -> Real := fun p => f p + (z ^ (2 : Nat) - z) / 2 * (w p) ^ (2 : Nat)
  let K : Real := (z ^ (3 : Nat) + z) / (3 * (N : Real))
  have hn : (0 : Real) < N := by exact_mod_cast (show 0 < N by omega)
  have hK : 0 <= K := by dsimp [K]; positivity
  have hs : Summable (fun p : T => (w p) ^ (2 : Nat)) :=
    summable_primeProfileWeight_sq.subtype _
  have hf : Summable f := (summable_primeProfile_logFactor z hz).subtype _
  have he : Summable e := hf.add (hs.mul_left _)
  have hPoint (p : T) : abs (e p) <= K * (w p) ^ (2 : Nat) := by
    have hp : N <= (p.val : Nat) - 1 := by omega
    have hw : w p <= 1 / (N : Real) := by
      dsimp [w, primeProfileWeight]
      exact one_div_le_one_div_of_le hn (by exact_mod_cast hp)
    have hc := profile_log_cubic_error_bound (w p) z (primeProfileWeight_nonneg _) hz
    calc
      _ <= (z ^ (3 : Nat) + z) / 3 * (w p) ^ (3 : Nat) := hc
      _ = ((z ^ (3 : Nat) + z) / 3 * w p) * (w p) ^ (2 : Nat) := by ring
      _ <= ((z ^ (3 : Nat) + z) / 3 * (1 / (N : Real))) * (w p) ^ (2 : Nat) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hw (by positivity)) (sq_nonneg _)
      _ = _ := by dsimp [K]; ring
  have hUpper : tsum e <= K * primeProfileQuadraticTail N := by
    calc
      _ <= tsum (fun p : T => K * (w p) ^ (2 : Nat)) :=
        Summable.tsum_le_tsum (fun p => (le_abs_self (e p)).trans (hPoint p)) he (hs.mul_left K)
      _ = _ := by rw [tsum_mul_left]; rfl
  have hLower : -K * primeProfileQuadraticTail N <= tsum e := by
    calc
      _ = tsum (fun p : T => -K * (w p) ^ (2 : Nat)) := by rw [tsum_mul_left]; rfl
      _ <= tsum e := Summable.tsum_le_tsum
        (fun p => by simpa only [neg_mul] using (abs_le.mp (hPoint p)).1) (hs.mul_left (-K)) he
  have hId : tsum e =
      Real.log (primeProfile (z : Complex)).re -
        Real.log (primePrefixProfile N (z : Complex)).re +
        (z ^ (2 : Nat) - z) / 2 * primeProfileQuadraticTail N := by
    rw [primeProfile_log_tail_eq_tsum N z hz]
    change tsum (fun p : T => f p + (z ^ (2 : Nat) - z) / 2 * (w p) ^ (2 : Nat)) = _
    rw [Summable.tsum_add hf (hs.mul_left _), tsum_mul_left]
    rfl
  have hb := primeProfileQuadraticTail_bounds N hN
  rw [<- hId]
  calc
    _ <= K * primeProfileQuadraticTail N := abs_le.mpr (And.intro (by linarith) hUpper)
    _ <= K * (2 / (N : Real)) := mul_le_mul_of_nonneg_left hb.2 hK
    _ = _ := by dsimp [K]; field_simp

end PrimeFactorOscillations
