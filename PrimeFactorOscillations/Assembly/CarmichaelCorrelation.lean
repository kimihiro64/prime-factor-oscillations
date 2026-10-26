/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelProfileProjection
import PrimeFactorOscillations.Helpers.OddReturnCharacterSupport

/-!
# Positive character coefficients from actual return correlations

The complete signed two-base correlation is transformed before any estimate.
Its coefficients are exact norm squares. Principal mass and the native
odd-packet quadratic cancellation are retained, without a zero hypothesis.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelCorrelation

variable {G : Type*} [CommGroup G] [Fintype G]

def weightSum (w : G -> Real) : Real :=
  Finset.univ.sum w

def weightMean (w : G -> Real) : Real :=
  weightSum w / (Fintype.card G : Real)

def rawCorrelation (w : G -> Real) (g : G) : Real :=
  Finset.univ.sum (fun h : G => w h * w (h * g))

def kernel (w : G -> Real) (g : G) : Real :=
  (Fintype.card G : Real) * rawCorrelation w g / weightSum w ^ 2

def characterSum (w : G -> Real) (chi : MonoidHom G Complex) : Complex :=
  Finset.univ.sum (fun g : G => (w g : Complex) * chi g)

/-- Finite characters are unitary; no analytic zero-free statement is needed. -/
theorem character_norm_one (chi : MonoidHom G Complex) (g : G) :
    norm (chi g) = 1 := by
  classical
  let M : Real := Finset.univ.sum (fun h : G => norm (chi h))
  have hM : 1 <= M := by
    calc
      1 = norm (chi 1) := by simp
      _ <= M := Finset.single_le_sum (fun h _ => norm_nonneg (chi h)) (Finset.mem_univ 1)
  have hTranslate := Equiv.sum_comp (Equiv.mulLeft g) (fun h : G => norm (chi h))
  have hScale : norm (chi g) * M = M := by
    calc
      _ = Finset.univ.sum (fun h : G => norm (chi (g * h))) := by
        simp only [M, Finset.mul_sum, map_mul, norm_mul]
      _ = M := hTranslate
  nlinarith

theorem character_mul_conj_one (chi : MonoidHom G Complex) (g : G) :
    chi g * (starRingEnd Complex) (chi g) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, character_norm_one]
  norm_num

theorem raw_correlation_character_sum (w : G -> Real) (chi : MonoidHom G Complex) :
    characterSum (rawCorrelation w) chi =
      (Complex.normSq (characterSum w chi) : Complex) := by
  classical
  let F := characterSum w chi
  have hInner (h : G) :
      Finset.univ.sum (fun g : G => (w (h * g) : Complex) * chi g) =
        (starRingEnd Complex) (chi h) * F := by
    calc
      _ = Finset.univ.sum (fun g : G =>
          (starRingEnd Complex) (chi h) * ((w (h * g) : Complex) * chi (h * g))) := by
        apply Finset.sum_congr rfl
        intro g _
        rw [map_mul]
        have hUnit : (starRingEnd Complex) (chi h) * chi h = 1 := by
          rw [mul_comm, character_mul_conj_one]
        calc
          _ = ((starRingEnd Complex) (chi h) * chi h) *
              ((w (h * g) : Complex) * chi g) := by rw [hUnit, one_mul]
          _ = _ := by ring
      _ = (starRingEnd Complex) (chi h) * F := by
        rw [<- Finset.mul_sum]
        congr 1
        exact Equiv.sum_comp (Equiv.mulLeft h) (fun g : G => (w g : Complex) * chi g)
  have hConj : Finset.univ.sum (fun h : G =>
      (w h : Complex) * (starRingEnd Complex) (chi h)) =
        (starRingEnd Complex) F := by
    simp only [F, characterSum, map_sum, map_mul, Complex.conj_ofReal]
  calc
    _ = Finset.univ.sum (fun h : G => (w h : Complex) *
        Finset.univ.sum (fun g : G => (w (h * g) : Complex) * chi g)) := by
      unfold characterSum rawCorrelation
      simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      ring
    _ = Finset.univ.sum (fun h : G =>
        ((w h : Complex) * (starRingEnd Complex) (chi h)) * F) := by
      simp_rw [hInner]
      apply Finset.sum_congr rfl
      intro h _
      ring
    _ = (starRingEnd Complex) F * F := by rw [<- Finset.sum_mul, hConj]
    _ = (Complex.normSq F : Complex) := by rw [mul_comm, Complex.mul_conj]

theorem kernel_character_sum (w : G -> Real) (chi : MonoidHom G Complex) :
    characterSum (kernel w) chi =
      ((Fintype.card G : Real) : Complex) / (weightSum w : Complex) ^ 2 *
        (Complex.normSq (characterSum w chi) : Complex) := by
  have hPoint (g : G) : (kernel w g : Complex) * chi g =
      ((Fintype.card G : Real) : Complex) / (weightSum w : Complex) ^ 2 *
        ((rawCorrelation w g : Complex) * chi g) := by
    unfold kernel
    push_cast
    ring
  unfold characterSum
  simp_rw [hPoint]
  rw [<- Finset.mul_sum]
  exact congrArg (fun z : Complex => ((Fintype.card G : Real) : Complex) /
    (weightSum w : Complex) ^ 2 * z) (raw_correlation_character_sum w chi)

/-- A positive real coefficient, obtained from the whole signed sum. -/
theorem kernel_coefficient_eq (w : G -> Real) (chi : MonoidHom G Complex) :
    characterSum (kernel w) chi / ((Fintype.card G : Real) : Complex) =
      ((Complex.normSq (characterSum w chi) / weightSum w ^ 2 : Real) : Complex) := by
  have hn : Not (((Fintype.card G : Real) : Complex) = 0) := by
    exact_mod_cast Fintype.card_ne_zero
  rw [kernel_character_sum]
  push_cast
  field_simp

theorem sum_rawCorrelation (w : G -> Real) :
    Finset.univ.sum (rawCorrelation w) = weightSum w ^ 2 := by
  classical
  unfold rawCorrelation
  rw [Finset.sum_comm]
  calc
    _ = Finset.univ.sum (fun h : G => w h * Finset.univ.sum (fun g : G => w (h * g))) := by
      apply Finset.sum_congr rfl
      intro h _
      rw [Finset.mul_sum]
    _ = Finset.univ.sum (fun h : G => w h * weightSum w) := by
      apply Finset.sum_congr rfl
      intro h _
      exact congrArg (fun z : Real => w h * z) (Equiv.sum_comp (Equiv.mulLeft h) w)
    _ = weightSum w ^ 2 := by
      rw [<- Finset.sum_mul]
      change weightSum w * weightSum w = weightSum w ^ 2
      ring

theorem kernel_mean_one (w : G -> Real) (hSum : 0 < weightSum w) :
    Finset.univ.sum (kernel w) / (Fintype.card G : Real) = 1 := by
  have hn : Not ((Fintype.card G : Real) = 0) := by exact_mod_cast Fintype.card_ne_zero
  unfold kernel
  rw [<- Finset.sum_div, <- Finset.mul_sum, sum_rawCorrelation]
  field_simp [ne_of_gt hSum]

theorem kernel_bounds (w : G -> Real)
    (hw : forall g, And (0 <= w g) (w g <= 1)) (hSum : 0 < weightSum w) (g : G) :
    And (0 <= kernel w g) (kernel w g <= 1 / weightMean w) := by
  have hRaw0 : 0 <= rawCorrelation w g :=
    Finset.sum_nonneg (fun h _ => mul_nonneg (hw h).1 (hw (h * g)).1)
  have hRaw1 : rawCorrelation w g <= weightSum w := by
    apply Finset.sum_le_sum
    intro h _
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hw (h * g)).2 (hw h).1
  have hn : (0 : Real) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hTop : (Fintype.card G : Real) * weightSum w / weightSum w ^ 2 =
      1 / weightMean w := by
    unfold weightMean
    field_simp [ne_of_gt hSum, ne_of_gt hn]
  exact And.intro (div_nonneg (mul_nonneg hn.le hRaw0) (sq_nonneg _))
    ((div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hRaw1 hn.le) (sq_nonneg _)).trans_eq hTop)

theorem kernel_at_one (w : G -> Real) (hSum : 0 < weightSum w)
    (hIdem : forall g, w g * w g = w g) :
    kernel w 1 = 1 / weightMean w := by
  have hRaw : rawCorrelation w 1 = weightSum w := by
    unfold rawCorrelation weightSum
    simp_rw [mul_one, hIdem]
  have hn : Not ((Fintype.card G : Real) = 0) := by exact_mod_cast Fintype.card_ne_zero
  unfold kernel weightMean
  rw [hRaw]
  field_simp [ne_of_gt hSum]

def vacancyWeight (L : Nat) (S : Finset Nat.Primes) (g : G) : Real := by
  classical
  exact if OddReturnCharacterSupport.vacancy L S g then 1 else 0

omit [Fintype G] in
theorem vacancyWeight_bounds (L : Nat) (S : Finset Nat.Primes) (g : G) :
    And (0 <= vacancyWeight L S g) (vacancyWeight L S g <= 1) := by
  classical
  unfold vacancyWeight
  split_ifs <;> norm_num

omit [Fintype G] in
theorem vacancyWeight_idempotent (L : Nat) (S : Finset Nat.Primes) (g : G) :
    vacancyWeight L S g * vacancyWeight L S g = vacancyWeight L S g := by
  classical
  unfold vacancyWeight
  split_ifs <;> norm_num

theorem canonical_vacancy_weightSum_pos (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent G)) :
    0 < weightSum (vacancyWeight (G := G) (Monoid.exponent G) S) := by
  have hMean := OddReturnCharacterSupport.canonical_vacancy_mean_pos S hDiv
  have hn : (0 : Real) <= Fintype.card G := Nat.cast_nonneg _
  by_contra hNot
  have hNon : weightSum (vacancyWeight (G := G) (Monoid.exponent G) S) /
      (Fintype.card G : Real) <= 0 := div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hNot) hn
  exact (not_le_of_gt hMean) hNon

/-- The quadratic support cancellation survives the positive correlation operation. -/
theorem odd_vacancy_kernel_quadratic_sum_eq_zero (L : Nat) (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) L)
    (hOdd : forall p : S, Not ((p.val : Nat) = 2))
    (hAnn : forall g : G, g ^ L = 1)
    (chi : MonoidHom G Complex) (hchi : Not (chi = 1))
    (hSquare : forall g : G, (chi g) ^ 2 = 1) :
    characterSum (kernel (vacancyWeight (G := G) L S)) chi = 0 := by
  classical
  have h := OddReturnCharacterSupport.odd_vacancy_quadratic_sum_eq_zero
    L S hDiv hOdd hAnn chi hchi hSquare
  have hWeight (g : G) : (vacancyWeight (G := G) L S g : Complex) =
      if OddReturnCharacterSupport.vacancy L S g then (1 : Complex) else 0 := by
    classical
    unfold vacancyWeight
    split_ifs <;> norm_num
  have hZero : characterSum (vacancyWeight (G := G) L S) chi = 0 := by
    unfold characterSum
    simp_rw [hWeight]
    exact h
  rw [kernel_character_sum, hZero]
  simp

end PrimeFactorOscillations.CarmichaelCorrelation
