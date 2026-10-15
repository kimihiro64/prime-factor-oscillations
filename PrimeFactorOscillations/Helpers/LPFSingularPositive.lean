/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFSieveScale
import PrimeFactorOscillations.Helpers.LPFSingularEuler

/-!
# Uniform positive arithmetic center for even targets

The finite odd-prime baseline is bounded below by the telescoping product
across all consecutive integers. The target-divisor factors are kept exactly,
including the prime two. The actual absolutely convergent singular series is
real and at least singularDivisorProduct for every positive even target.
This arithmetic step does not itself establish generated-state density entry.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

noncomputable def lpfSingularBaseline (p : Nat) : Real :=
  1 - 1 / ((p : Real) - 1) ^ 2

theorem lpf_singular_integer_product (L : Nat) :
    Finset.prod (Finset.range L) (fun i => 1 - 1 / (((i + 2 : Nat) : Real) ^ 2)) =
      ((L : Real) + 2) / (2 * ((L : Real) + 1)) := by
  induction L with
  | zero => norm_num
  | succ L ih =>
    rw [Finset.prod_range_succ, ih]
    push_cast
    have hOne : Not ((L : Real) + 1 = 0) := by positivity
    have hTwo : Not ((L : Real) + 2 = 0) := by positivity
    field_simp [hOne, hTwo]
    ring

theorem lpf_singular_integer_product_half (L : Nat) :
    (1 : Real) / 2 <=
      Finset.prod (Finset.range L) (fun i => 1 - 1 / (((i + 2 : Nat) : Real) ^ 2)) := by
  rw [lpf_singular_integer_product]
  have hDen : 0 < 2 * ((L : Real) + 1) := by positivity
  apply (mul_le_mul_iff_of_pos_right hDen).mp
  have hNe : Not (2 * ((L : Real) + 1) = 0) := hDen.ne'
  field_simp [hNe]
  have hL : (0 : Real) <= (L : Real) := by positivity
  nlinarith only [hL]

theorem lpf_singular_shifted_factor_bounds (i : Nat) :
    And (0 <= 1 - 1 / (((i + 2 : Nat) : Real) ^ 2))
      (1 - 1 / (((i + 2 : Nat) : Real) ^ 2) <= 1) := by
  have hTwo : (2 : Real) <= ((i + 2 : Nat) : Real) := by exact_mod_cast (by omega : 2 <= i + 2)
  have hPos : 0 < (((i + 2 : Nat) : Real) ^ 2) := by positivity
  have hSq : (1 : Real) <= (((i + 2 : Nat) : Real) ^ 2) := by nlinarith
  have hInv : 1 / (((i + 2 : Nat) : Real) ^ 2) <= (1 : Real) := by
    have h := div_le_div_of_nonneg_left (show (0 : Real) <= 1 by norm_num)
      (show (0 : Real) < 1 by norm_num) hSq
    simpa using h
  have hInvNonneg : (0 : Real) <= 1 / (((i + 2 : Nat) : Real) ^ 2) := by positivity
  exact And.intro (by linarith only [hInv]) (by linarith only [hInvNonneg])

theorem lpf_singular_prime_factor (p t : Nat) (hp : Nat.Prime p) (hOdd : 3 <= p) :
    1 + lpfRamanujanCoefficient p t = (lpfSingularBaseline p : Complex) *
      (if Dvd.dvd p t then (singularFactor p : Complex) else 1) := by
  have hOne : Not ((p : Complex) - 1 = 0) := by
    apply sub_ne_zero.mpr
    exact_mod_cast (by omega : Not (p = 1))
  have hTwo : Not ((p : Complex) - 2 = 0) := by
    apply sub_ne_zero.mpr
    exact_mod_cast (by omega : Not (p = 2))
  rw [lpfRamanujanCoefficient_prime p t hp]
  simp only [lpfSingularBaseline, singularFactor]
  push_cast
  by_cases hpt : Dvd.dvd p t <;> simp only [hpt, ite_true, ite_false] <;>
    field_simp [hOne, hTwo] <;> ring

theorem lpf_singular_two_factor (t : Nat) (ht : Dvd.dvd 2 t) :
    1 + lpfRamanujanCoefficient 2 t = 2 := by
  rw [lpfRamanujanCoefficient_prime 2 t (by decide)]
  norm_num [ht]

theorem lpf_singular_baseline_product_half (R : Nat) (S : Finset Nat)
    (hSmall : forall p, Membership.mem S p -> 3 <= p)
    (hTop : forall p, Membership.mem S p -> p < R) :
    (1 : Real) / 2 <= Finset.prod S lpfSingularBaseline := by
  classical
  let F : Nat -> Real := fun i => 1 - 1 / (((i + 2 : Nat) : Real) ^ 2)
  let J : Finset Nat := S.image (fun p => p - 3)
  have hInj : Set.InjOn (fun p : Nat => p - 3) (S : Set Nat) := by
    intro p hp q hq hEq
    change p - 3 = q - 3 at hEq
    have hp3 := hSmall p hp
    have hq3 := hSmall q hq
    omega
  have hSub : J <= Finset.range R := by
    intro i hi
    choose p hp hEq using Finset.mem_image.mp hi
    rw [<- hEq]
    apply Finset.mem_range.mpr
    have hP := hTop p hp
    omega
  have hImage : Finset.prod J F = Finset.prod S lpfSingularBaseline := by
    rw [Finset.prod_image (f := F) hInj]
    apply Finset.prod_congr rfl
    intro p hp
    have hp3 := hSmall p hp
    have hNat : p - 3 + 2 = p - 1 := by omega
    dsimp [F, lpfSingularBaseline]
    rw [hNat, Nat.cast_sub (by omega : 1 <= p), Nat.cast_one]
  have hAny (U : Finset Nat) : Finset.prod U F <= 1 := by
    induction U using Finset.induction_on with
    | empty => simp
    | @insert i U hi ih =>
      rw [Finset.prod_insert hi]
      exact (mul_le_mul (lpf_singular_shifted_factor_bounds i).2 ih
        (Finset.prod_nonneg (fun j _ => (lpf_singular_shifted_factor_bounds j).1))
        (show (0 : Real) <= 1 by norm_num)).trans_eq (by ring)
  have hNonneg : 0 <= Finset.prod J F :=
    Finset.prod_nonneg (fun i _ => (lpf_singular_shifted_factor_bounds i).1)
  have hFull : Finset.prod (Finset.range R) F <= Finset.prod J F := by
    rw [<- Finset.prod_sdiff hSub]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hAny (SDiff.sdiff (Finset.range R) J)) hNonneg
  exact (lpf_singular_integer_product_half R).trans (hFull.trans_eq hImage)

def lpfSingularOddPrimes (R : Nat) : Finset Nat :=
  (Nat.primesBelow R).filter (fun p => 3 <= p)

noncomputable def lpfSingularBaselineProduct (R : Nat) : Real :=
  Finset.prod (lpfSingularOddPrimes R) lpfSingularBaseline

theorem lpf_singular_odd_baseline_half (R : Nat) :
    (1 : Real) / 2 <= lpfSingularBaselineProduct R := by
  apply lpf_singular_baseline_product_half R (lpfSingularOddPrimes R)
  next => intro p hp; exact (Finset.mem_filter.mp hp).2
  next => intro p hp; exact (Nat.mem_primesBelow.mp (Finset.mem_filter.mp hp).1).1

theorem lpf_singular_primes_partition (R : Nat) (hR : 3 <= R) :
    Nat.primesBelow R = insert 2 (lpfSingularOddPrimes R) := by
  apply Finset.ext
  intro p
  simp only [lpfSingularOddPrimes, Nat.mem_primesBelow, Finset.mem_insert, Finset.mem_filter]
  constructor
  next =>
    intro h
    by_cases hp : p = 2
    next => exact Or.inl hp
    next =>
      have hLow := h.2.two_le
      exact Or.inr (And.intro h (by omega))
  next =>
    intro h
    rcases h with h | h
    next => subst p; exact And.intro (by omega) (by decide)
    next => exact h.1

theorem lpf_singular_divisor_prime_filter (R t : Nat) (ht : 0 < t) (hRt : t < R) :
    (lpfSingularOddPrimes R).filter (fun p => Dvd.dvd p t) =
      t.primeFactors.filter (fun p => 3 <= p) := by
  apply Finset.ext
  intro p
  simp only [lpfSingularOddPrimes, Finset.mem_filter, Nat.mem_primesBelow, Nat.mem_primeFactors]
  constructor
  next => intro h; exact And.intro (And.intro h.1.1.2 (And.intro h.2 (Nat.ne_of_gt ht))) h.1.2
  next =>
    intro h
    have hLe := Nat.le_of_dvd ht h.1.2.1
    exact And.intro (And.intro (And.intro (hLe.trans_lt hRt) h.1.1) h.2) h.1.2.1

theorem lpf_singular_prime_product_formula (R t : Nat) (ht : 0 < t)
    (hEven : Dvd.dvd 2 t) (hR : 3 <= R) (hRt : t < R) :
    Finset.prod (Nat.primesBelow R) (fun p => 1 + lpfRamanujanCoefficient p t) =
      ((2 * lpfSingularBaselineProduct R * singularDivisorProduct t : Real) : Complex) := by
  classical
  have hTwo : Not (Membership.mem (lpfSingularOddPrimes R) 2) := by
    simp [lpfSingularOddPrimes]
  rw [lpf_singular_primes_partition R hR, Finset.prod_insert hTwo, lpf_singular_two_factor t hEven]
  have hFactors : Finset.prod (lpfSingularOddPrimes R) (fun p => 1 + lpfRamanujanCoefficient p t) =
      Finset.prod (lpfSingularOddPrimes R) (fun p => (lpfSingularBaseline p : Complex) *
        (if Dvd.dvd p t then (singularFactor p : Complex) else 1)) := by
    apply Finset.prod_congr rfl
    intro p hp
    have h := Finset.mem_filter.mp hp
    exact lpf_singular_prime_factor p t (Nat.mem_primesBelow.mp h.1).2 h.2
  rw [hFactors, Finset.prod_mul_distrib, <- Finset.prod_filter,
    lpf_singular_divisor_prime_filter R t ht hRt]
  unfold lpfSingularBaselineProduct singularDivisorProduct
  push_cast
  ring

theorem lpf_singular_series_re_lower_bound (t : Nat) (ht : 0 < t) (hEven : Dvd.dvd 2 t) :
    singularDivisorProduct t <= (lpfSingularSeries t).re := by
  have hEuler := lpfSingularSeries_prime_product_limit t ht
  have hReal := (Complex.continuous_re.tendsto (lpfSingularSeries t)).comp hEuler
  apply ge_of_tendsto hReal
  filter_upwards [Filter.eventually_ge_atTop (max (t + 1) 3)] with R hR
  have hR3 : 3 <= R := (le_max_right _ _).trans hR
  have hRt : t < R := by have h := (le_max_left (t + 1) 3).trans hR; omega
  change singularDivisorProduct t <=
    (Finset.prod (Nat.primesBelow R) (fun p => 1 + lpfRamanujanCoefficient p t)).re
  rw [lpf_singular_prime_product_formula R t ht hEven hR3 hRt, Complex.ofReal_re]
  have hBase := lpf_singular_odd_baseline_half R
  have hG := sieve_singularDivisorProduct_one_le t
  have hScaled := mul_le_mul_of_nonneg_right hBase (zero_le_one.trans hG)
  nlinarith only [hScaled]

theorem lpf_singular_series_im_zero (t : Nat) (ht : 0 < t) (hEven : Dvd.dvd 2 t) :
    (lpfSingularSeries t).im = 0 := by
  have hEuler := lpfSingularSeries_prime_product_limit t ht
  have hImag := (Complex.continuous_im.tendsto (lpfSingularSeries t)).comp hEuler
  have hZero : Filter.Tendsto (fun R : Nat =>
      (Finset.prod (Nat.primesBelow R) (fun p => 1 + lpfRamanujanCoefficient p t)).im)
      Filter.atTop (nhds (0 : Real)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_ge_atTop (max (t + 1) 3)] with R hR
    have hR3 : 3 <= R := (le_max_right _ _).trans hR
    have hRt : t < R := by have h := (le_max_left (t + 1) 3).trans hR; omega
    change 0 = (Finset.prod (Nat.primesBelow R) (fun p => 1 + lpfRamanujanCoefficient p t)).im
    rw [lpf_singular_prime_product_formula R t ht hEven hR3 hRt]
    simp
  exact tendsto_nhds_unique hImag hZero

theorem lpf_singular_series_re_one_le (t : Nat) (ht : 0 < t) (hEven : Dvd.dvd 2 t) :
    (1 : Real) <= (lpfSingularSeries t).re :=
  (sieve_singularDivisorProduct_one_le t).trans (lpf_singular_series_re_lower_bound t ht hEven)

end PrimeFactorOscillations.LPF
