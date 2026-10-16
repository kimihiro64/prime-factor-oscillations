/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PowerPolynomialLaw

/-!
# Bounded Amplitude Detector

Canonical thinned Bernoulli laws and uniform local odds estimates for bounded real marks.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.BoundedAmplitudeDetector

theorem bounded_odds (p c : Real) (hp : 1 < p) (hc0 : 0 <= c) (hc1 : c <= 1) :
    0 <= c / (p - c) /\ c / (p - c) <= 1 / (p - 1) := by
  have hd : 0 < p - c := by linarith
  have hd1 : 0 < p - 1 := by linarith
  refine And.intro (div_nonneg hc0 hd.le) ?_
  exact (div_le_div_of_nonneg_right hc1 hd.le).trans
    (one_div_le_one_div_of_le hd1 (by linarith))

theorem odds_error (p c : Real) (hp : 1 < p) (hc0 : 0 <= c) (hc1 : c <= 1) :
    abs (c / (p - c) - c / p) <= 1 / (p * (p - 1)) := by
  have hp0 : 0 < p := by linarith
  have hd : 0 < p - c := by linarith
  have hd1 : 0 < p - 1 := by linarith
  have hid : c / (p - c) - c / p = c ^ 2 / (p * (p - c)) := by
    field_simp [hd.ne', hp0.ne']
    ring
  have hc2 : c ^ 2 <= 1 := by nlinarith
  rw [hid, abs_of_nonneg (div_nonneg (sq_nonneg _) (mul_pos hp0 hd).le)]
  exact (div_le_div_of_nonneg_right hc2 (mul_pos hp0 hd).le).trans
    (one_div_le_one_div_of_le (mul_pos hp0 hd1)
      (mul_le_mul_of_nonneg_left (by linarith : p - 1 <= p - c) hp0.le))

def law (c : Nat.Primes -> Real)
    (hc0 : forall p, 0 <= c p) (hc1 : forall p, c p <= 1) : PrimeClockLaw :=
  PrimeClockLaw.ofBoundedOdds (fun p => c p / ((p : Nat) - c p)) 1
    zero_lt_one
    (fun p => (bounded_odds (p : Nat) (c p)
      (by exact_mod_cast p.property.one_lt) (hc0 p) (hc1 p)).1)
    (by
      intro p
      have h := (bounded_odds (p : Nat) (c p)
        (by exact_mod_cast p.property.one_lt) (hc0 p) (hc1 p)).2
      have hCast : ((((p : Nat) - 1 : Nat) : Real)) = (p : Nat) - 1 := by
        rw [Nat.cast_sub p.property.one_lt.le, Nat.cast_one]
      simpa only [primeProfileWeight, hCast, one_mul] using h)

theorem weight_eq_probability_odds (c : Nat.Primes -> Real)
    (hc0 : forall p, 0 <= c p) (hc1 : forall p, c p <= 1) (p : Nat.Primes) :
    (law c hc0 hc1).weight p =
      (c p / (p : Nat)) / (1 - c p / (p : Nat)) := by
  have hp : Not (((p : Nat) : Real) = 0) := by exact_mod_cast p.property.ne_zero
  change c p / ((p : Nat) - c p) = _
  rw [div_div]
  congr 1
  field_simp [hp]

theorem probability_bounds (c : Nat.Primes -> Real)
    (hc0 : forall p, 0 <= c p) (hc1 : forall p, c p <= 1) (p : Nat.Primes) :
    0 <= c p / (p : Nat) /\ c p / (p : Nat) <= 1 := by
  have hp : (1 : Real) < (p : Nat) := by exact_mod_cast p.property.one_lt
  refine And.intro (div_nonneg (hc0 p) (by linarith)) ?_
  calc
    _ <= 1 / ((p : Nat) : Real) := div_le_div_of_nonneg_right (hc1 p) (by linarith)
    _ <= 1 := by
      have h := one_div_le_one_div_of_le zero_lt_one hp.le
      simpa using h

theorem comparison (c : Nat.Primes -> Real)
    (hc0 : forall p, 0 <= c p) (hc1 : forall p, c p <= 1)
    (b : Real) (hb : 0 < b) :
    PowerPolynomialLaw.ComparisonClaim (law c hc0 hc1) b :=
  (law c hc0 hc1).exists_densityRatio_linearization b hb

theorem signed_odds_error (p u : Real) (hp : 1 < p)
    (hu0 : -1 <= u) (hu1 : u <= 1) :
    abs (max u 0 / (p - max u 0) -
      max (-u) 0 / (p - max (-u) 0) - u / p) <= 1 / (p * (p - 1)) := by
  by_cases hu : 0 <= u
  . simpa only [max_eq_left hu, max_eq_right (neg_nonpos.mpr hu), zero_div, sub_zero]
      using odds_error p u hp hu hu1
  . have huNeg : u <= 0 := le_of_lt (lt_of_not_ge hu)
    have hOther := odds_error p (-u) hp (neg_nonneg.mpr huNeg) (by linarith)
    rw [max_eq_right huNeg, max_eq_left (neg_nonneg.mpr huNeg), zero_div, zero_sub]
    have hid : -(-u / (p - -u)) - u / p =
        -((-u) / (p - -u) - (-u) / p) := by ring
    rw [hid, abs_neg]
    exact hOther


theorem anchored_odds_error (p u : Real) (hp : 1 < p)
    (hu0 : -1 <= u) (hu1 : u <= 1) :
    abs (((1 + u) / 2) / (p - (1 + u) / 2) -
      ((1 - u) / 2) / (p - (1 - u) / 2) - u / p) <=
        2 / (p * (p - 1)) := by
  let cP := (1 + u) / 2
  let cM := (1 - u) / 2
  have hcP0 : 0 <= cP := by dsimp [cP]; linarith
  have hcP1 : cP <= 1 := by dsimp [cP]; linarith
  have hcM0 : 0 <= cM := by dsimp [cM]; linarith
  have hcM1 : cM <= 1 := by dsimp [cM]; linarith
  have hP := odds_error p cP hp hcP0 hcP1
  have hM := odds_error p cM hp hcM0 hcM1
  change abs (cP / (p - cP) - cM / (p - cM) - u / p) <= _
  have hid : cP / (p - cP) - cM / (p - cM) - u / p =
      (cP / (p - cP) - cP / p) + -(cM / (p - cM) - cM / p) := by
    dsimp [cP, cM]
    ring
  rw [hid]
  calc
    _ <= abs (cP / (p - cP) - cP / p) +
        abs (-(cM / (p - cM) - cM / p)) := abs_add_le _ _
    _ = abs (cP / (p - cP) - cP / p) +
        abs (cM / (p - cM) - cM / p) := by rw [abs_neg]
    _ <= 1 / (p * (p - 1)) + 1 / (p * (p - 1)) := add_le_add hP hM
    _ = 2 / (p * (p - 1)) := by ring


end PrimeFactorOscillations.BoundedAmplitudeDetector
