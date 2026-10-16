/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.UniformCarrierReal

/-!
# Uniform Carrier Complex

Four probability laws encode every bounded complex mark using one common finite reference.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.UniformCarrier

def carrierRank (alpha : Real) (P : Nat) : Nat :=
  Nat.floor (alpha * baseline.arithmeticClock (2 * P))

def carrierReference (alpha : Real) (P : Nat) : Real -> Real :=
  prefixRatio baseline (2 * P) (carrierRank alpha P)

theorem real_bounds (g : Nat.Primes -> Complex) (hg : forall p, norm (g p) <= 1) :
    forall p, -1 <= (g p).re /\ (g p).re <= 1 :=
  fun p => abs_le.mp ((Complex.abs_re_le_norm (g p)).trans (hg p))

theorem imag_bounds (g : Nat.Primes -> Complex) (hg : forall p, norm (g p) <= 1) :
    forall p, -1 <= (g p).im /\ (g p).im <= 1 :=
  fun p => abs_le.mp ((Complex.abs_im_le_norm (g p)).trans (hg p))

def weightedSum (T : Finset Nat.Primes) (g : Nat.Primes -> Complex) : Complex :=
  Complex.mk (T.sum (fun p => (g p).re / ((p : Nat) : Real)))
    (T.sum (fun p => (g p).im / ((p : Nat) : Real)))

theorem divided_components (z : Complex) (x : Real) :
    Complex.mk (z.re / x) (z.im / x) = z / (x : Complex) := by
  by_cases hx : x = 0
  . subst x
    apply Complex.ext <;> simp
  . apply Complex.ext <;> simp [Complex.div_re, Complex.div_im] <;> field_simp <;> ring

theorem weightedSum_eq (T : Finset Nat.Primes) (g : Nat.Primes -> Complex) :
    weightedSum T g = T.sum (fun p => g p / (((p : Nat) : Real) : Complex)) := by
  apply Complex.ext
  . change T.sum (fun p => (g p).re / ((p : Nat) : Real)) = _
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro p hp
    exact congrArg Complex.re (divided_components (g p) ((p : Nat) : Real))
  . change T.sum (fun p => (g p).im / ((p : Nat) : Real)) = _
    rw [Complex.im_sum]
    apply Finset.sum_congr rfl
    intro p hp
    exact congrArg Complex.im (divided_components (g p) ((p : Nat) : Real))

theorem norm_mk_sub_le (a b c d : Real) :
    norm (Complex.mk a b - Complex.mk c d) <= abs (a - c) + abs (b - d) := by
  have heq : Complex.mk a b - Complex.mk c d =
      ((a - c : Real) : Complex) + ((b - d : Real) : Complex) * Complex.I := by
    apply Complex.ext <;> simp
  rw [heq]
  have h := norm_add_le (((a - c : Real) : Complex)) (((b - d : Real) : Complex) * Complex.I)
  simpa only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] using h

theorem exists_complex_carrier (alpha : Real) (ha : 0 < alpha) :
    exists P0 : Nat, exists C : Real, 1 <= P0 /\ 0 < C /\
      forall P : Nat, P0 <= P ->
      forall T : Finset Nat.Primes, T <= primeProfilePrefixSet (2 * P) ->
      (forall p, Membership.mem T p -> P < (p : Nat)) -> T.card <= P / 100 ->
      forall g : Nat.Primes -> Complex,
      forall hg : (forall p, norm (g p) <= 1),
      (forall p, Not (Membership.mem T p) -> g p = 0) ->
      exists UP UM VP VM : Real,
        (positiveLaw (fun p => (g p).re) (real_bounds g hg)).densityRatio (2 * P) (carrierRank alpha P) =
          carrierReference alpha P UP /\
        (negativeLaw (fun p => (g p).re) (real_bounds g hg)).densityRatio (2 * P) (carrierRank alpha P) =
          carrierReference alpha P UM /\
        (positiveLaw (fun p => (g p).im) (imag_bounds g hg)).densityRatio (2 * P) (carrierRank alpha P) =
          carrierReference alpha P VP /\
        (negativeLaw (fun p => (g p).im) (imag_bounds g hg)).densityRatio (2 * P) (carrierRank alpha P) =
          carrierReference alpha P VM /\
        norm (Complex.mk (UP - UM) (VP - VM) - weightedSum T g) <=
          C * (T.card : Real) / (P : Real) ^ 2 /\
        abs (UP - baseline.arithmeticClock (2 * P)) <= 1 / 2 /\
        abs (UM - baseline.arithmeticClock (2 * P)) <= 1 / 2 /\
        abs (VP - baseline.arithmeticClock (2 * P)) <= 1 / 2 /\
        abs (VM - baseline.arithmeticClock (2 * P)) <= 1 / 2 := by
  choose P0 C hP0 hC hReal using exists_real_carrier alpha ha
  refine Exists.intro P0 (Exists.intro (2 * C)
    (And.intro hP0 (And.intro (by positivity) ?_)))
  intro P hP T hT hprime hcard g hg hSupport
  have hReSupport : forall p, Not (Membership.mem T p) -> (g p).re = 0 := by
    intro p hp
    rw [hSupport p hp]
    rfl
  have hImSupport : forall p, Not (Membership.mem T p) -> (g p).im = 0 := by
    intro p hp
    rw [hSupport p hp]
    rfl
  choose UP UM hRP hRM hRE using hReal P hP T hT hprime hcard
    (fun p => (g p).re) (real_bounds g hg) hReSupport
  choose VP VM hIP hIM hIE using hReal P hP T hT hprime hcard
    (fun p => (g p).im) (imag_bounds g hg) hImSupport
  refine Exists.intro UP ?_
  refine Exists.intro UM ?_
  refine Exists.intro VP ?_
  refine Exists.intro VM ?_
  refine And.intro hRP (And.intro hRM (And.intro hIP (And.intro hIM ?_)))
  refine And.intro ?_ (And.intro hRE.2.1 (And.intro hRE.2.2 (And.intro hIE.2.1 hIE.2.2)))
  calc
    _ <= abs (UP - UM - T.sum (fun p => (g p).re / ((p : Nat) : Real))) +
        abs (VP - VM - T.sum (fun p => (g p).im / ((p : Nat) : Real))) :=
      norm_mk_sub_le _ _ _ _
    _ <= C * (T.card : Real) / (P : Real) ^ 2 + C * (T.card : Real) / (P : Real) ^ 2 :=
      add_le_add hRE.1 hIE.1
    _ = _ := by ring

end PrimeFactorOscillations.UniformCarrier
