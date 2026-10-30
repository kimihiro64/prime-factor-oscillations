/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairEuler
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairTwists
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPolynomialPairs

/-!
# Actual quadratic-pair counts and their Euler reference

The normalization uses the complete sum of actual irreducible polynomial
pair counts. Both exceptional discriminant rows are retained in the exact
rational factorization and its relative square-root-trace error estimate.
The numerical trace bound is an explicit hypothesis, not a formal Hasse proof.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

open scoped BigOperators

namespace FiniteField.QuadraticPairEuler

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def normalizedPairCount (c h : F) : Real :=
  (Fintype.card F : Real) * (monicQuadraticPairCount c h : Real) /
    Finset.univ.sum (fun t : F => (monicQuadraticPairCount t h : Real))

theorem quadraticChar_real_signs (z : F) (hz : Not (z = 0)) :
    ((quadraticChar F) z : Real) = 1 \/ ((quadraticChar F) z : Real) = -1 := by
  have hi := quadraticChar_sq_one hz
  have hr : ((quadraticChar F) z : Real) ^ 2 = 1 := by exact_mod_cast hi
  have hmul : (((quadraticChar F) z : Real) - 1) *
      (((quadraticChar F) z : Real) + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hmul with h | h
  . exact Or.inl (by linarith)
  . exact Or.inr (by linarith)

theorem normalizedPairCount_eq_rational
    (hF : Not (ringChar F = 2)) (c h : F)
    (hc : Not (c = 0)) (hch : Not (c + h = 0)) (hh : Not (h = 0))
    (hq : 16 <= (Fintype.card F : Real)) :
    normalizedPairCount c h =
      ((Fintype.card F : Real) + 1 - (splitCubicPointTrace c (c + h) : Real) -
        correction ((quadraticChar F) h) ((quadraticChar F) (-h))
          ((quadraticChar F) c) ((quadraticChar F) (c + h))) /
        ((Fintype.card F : Real) -
          offset ((quadraticChar F) h) ((quadraticChar F) (-h))) := by
  classical
  let q : Real := Fintype.card F
  let a : Real := splitCubicPointTrace c (c + h)
  let e : Real := (quadraticChar F) h
  let f : Real := (quadraticChar F) (-h)
  let x : Real := (quadraticChar F) c
  let y : Real := (quadraticChar F) (c + h)
  let S : Real := Finset.univ.sum (fun t : F => (monicQuadraticPairCount t h : Real))
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hqne : Not (q = 0) := ne_of_gt hq0
  have ht : 4 * (monicQuadraticPairCount c h : Real) =
      q + 1 - a - correction e f x y := by
    dsimp [q, a, e, f, x, y, correction]
    have hi := monicQuadraticPairCount_eq_trace hF c h hc hch hh
    have hr :
        4 * (monicQuadraticPairCount c h : Real) =
          (Fintype.card F : Real) + 1 - (splitCubicPointTrace c (c + h) : Real) -
            (1 + ((quadraticChar F) c : Real)) *
              (1 - ((quadraticChar F) (-h) : Real)) -
            (1 + ((quadraticChar F) (c + h) : Real)) *
              (1 - ((quadraticChar F) h : Real)) := by exact_mod_cast hi
    linarith only [hr]
  have hsum : 4 * S = q * (q - offset e f) := by
    have hi := sum_monicQuadraticPairCount_eq hF h hh
    have hr : 4 * S = q * (q - 3 + e + f) := by
      dsimp [S, q, e, f]
      exact_mod_cast hi
    dsimp [offset]
    nlinarith only [hr]
  change q * (monicQuadraticPairCount c h : Real) / S =
    (q + 1 - a - correction e f x y) / (q - offset e f)
  have hw : (monicQuadraticPairCount c h : Real) =
      (q + 1 - a - correction e f x y) / 4 := by linarith only [ht]
  have hSval : S = q * (q - offset e f) / 4 := by linarith only [hsum]
  rw [hw, hSval]
  by_cases hd : q - offset e f = 0
  . simp only [hd, mul_zero, zero_div, div_zero]
  . field_simp [hd, hqne]
    <;> ring

theorem normalizedPairCount_factorization
    (hF : Not (ringChar F = 2)) (c h : F)
    (hc : Not (c = 0)) (hch : Not (c + h = 0)) (hh : Not (h = 0))
    (hq : 16 <= (Fintype.card F : Real))
    (ha : |(splitCubicPointTrace c (c + h) : Real)| <= (Fintype.card F : Real) / 2) :
    let q : Real := Fintype.card F
    let a : Real := splitCubicPointTrace c (c + h)
    let e : Real := (quadraticChar F) h
    let f : Real := (quadraticChar F) (-h)
    let x : Real := (quadraticChar F) c
    let y : Real := (quadraticChar F) (c + h)
    normalizedPairCount c h =
      ellipticFactor q a * dirichletFactor q e f x y * carrier q a e f x y := by
  dsimp only
  rw [normalizedPairCount_eq_rational hF c h hc hch hh hq]
  exact rational_factorization _ _ _ _ _ _ hq ha
    (quadraticChar_real_signs h hh)
    (quadraticChar_real_signs (-h) (neg_ne_zero.mpr hh))
    (quadraticChar_real_signs c hc)
    (quadraticChar_real_signs (c + h) hch)

theorem normalizedPairCount_relative_error
    (hF : Not (ringChar F = 2)) (c h : F)
    (hc : Not (c = 0)) (hch : Not (c + h = 0)) (hh : Not (h = 0))
    (hq : 16 <= (Fintype.card F : Real))
    (ha : |(splitCubicPointTrace c (c + h) : Real)| <=
      2 * Real.sqrt (Fintype.card F)) :
    let q : Real := Fintype.card F
    let a : Real := splitCubicPointTrace c (c + h)
    let e : Real := (quadraticChar F) h
    let f : Real := (quadraticChar F) (-h)
    let x : Real := (quadraticChar F) c
    let y : Real := (quadraticChar F) (c + h)
    |normalizedPairCount c h - ellipticFactor q a * dirichletFactor q e f x y| <=
      (ellipticFactor q a * dirichletFactor q e f x y) *
        (512 / (q * Real.sqrt q)) := by
  let q : Real := Fintype.card F
  let a : Real := splitCubicPointTrace c (c + h)
  let e : Real := (quadraticChar F) h
  let f : Real := (quadraticChar F) (-h)
  let x : Real := (quadraticChar F) c
  let y : Real := (quadraticChar F) (c + h)
  change |normalizedPairCount c h - ellipticFactor q a * dirichletFactor q e f x y| <=
    (ellipticFactor q a * dirichletFactor q e f x y) *
      (512 / (q * Real.sqrt q))
  have hp0 : 0 < q := by dsimp [q]; linarith
  have hr0 := Real.sqrt_nonneg q
  have hr2 := Real.sq_sqrt (le_of_lt hp0)
  have hr4 : 4 <= Real.sqrt q := by dsimp [q] at *; nlinarith
  have hhalf : |a| <= q / 2 := by
    change |a| <= 2 * Real.sqrt q at ha
    nlinarith [mul_nonneg (sub_nonneg.mpr hr4) hr0]
  have he := quadraticChar_real_signs h hh
  have hf := quadraticChar_real_signs (-h) (neg_ne_zero.mpr hh)
  have hx := quadraticChar_real_signs c hc
  have hy := quadraticChar_real_signs (c + h) hch
  have href := reference_pos q a e f x y hq hhalf he hf hx hy
  have hfactor := normalizedPairCount_factorization hF c h hc hch hh hq hhalf
  change normalizedPairCount c h =
    ellipticFactor q a * dirichletFactor q e f x y * carrier q a e f x y at hfactor
  have hdiff : normalizedPairCount c h - ellipticFactor q a * dirichletFactor q e f x y =
      (ellipticFactor q a * dirichletFactor q e f x y) * (carrier q a e f x y - 1) := by
    rw [hfactor]
    ring
  rw [hdiff, abs_mul, abs_of_pos href]
  exact mul_le_mul_of_nonneg_left
    (carrier_hasse_defect q a e f x y hq ha he hf hx hy) (le_of_lt href)

theorem normalizedPairCount_corrected_factorization
    (hF : Not (ringChar F = 2)) (c h : F)
    (hc : Not (c = 0)) (hch : Not (c + h = 0)) (hh : Not (h = 0))
    (hq : 16 <= (Fintype.card F : Real))
    (hasq : (splitCubicPointTrace c (c + h) : Real) ^ 2 <= 4 * (Fintype.card F : Real)) :
    let q : Real := Fintype.card F
    let a : Real := splitCubicPointTrace c (c + h)
    let e : Real := (quadraticChar F) h
    let f : Real := (quadraticChar F) (-h)
    let x : Real := (quadraticChar F) c
    let y : Real := (quadraticChar F) (c + h)
    normalizedPairCount c h =
      ellipticFactor q a * dirichletFactor q e f x y *
        twistCorrection q a e f x y * correctedCarrier q a e f x y := by
  let q : Real := Fintype.card F
  let a : Real := splitCubicPointTrace c (c + h)
  let e : Real := (quadraticChar F) h
  let f : Real := (quadraticChar F) (-h)
  let x : Real := (quadraticChar F) c
  let y : Real := (quadraticChar F) (c + h)
  change normalizedPairCount c h =
    ellipticFactor q a * dirichletFactor q e f x y *
      twistCorrection q a e f x y * correctedCarrier q a e f x y
  have ha := trace_half_of_square q a hq hasq
  have he := quadraticChar_real_signs h hh
  have hf := quadraticChar_real_signs (-h) (neg_ne_zero.mpr hh)
  have hx := quadraticChar_real_signs c hc
  have hy := quadraticChar_real_signs (c + h) hch
  have hk := activeRows_twice_cases e f x y he hf hx hy
  have hTl := scalarTwist_lower q a hq ha (2 * activeRows e f x y) hk
  change (1 / 2 : Real) <= twistCorrection q a e f x y at hTl
  have hTpos : 0 < twistCorrection q a e f x y := by linarith
  have hTne := ne_of_gt hTpos
  have hcarrier : carrier q a e f x y =
      twistCorrection q a e f x y * correctedCarrier q a e f x y := by
    unfold correctedCarrier
    field_simp [hTne]
  have hb := normalizedPairCount_factorization hF c h hc hch hh hq ha
  change normalizedPairCount c h =
    ellipticFactor q a * dirichletFactor q e f x y * carrier q a e f x y at hb
  rw [hb, hcarrier]
  ring

theorem normalizedPairCount_corrected_relative_error
    (hF : Not (ringChar F = 2)) (c h : F)
    (hc : Not (c = 0)) (hch : Not (c + h = 0)) (hh : Not (h = 0))
    (hq : 16 <= (Fintype.card F : Real))
    (hasq : (splitCubicPointTrace c (c + h) : Real) ^ 2 <= 4 * (Fintype.card F : Real)) :
    let q : Real := Fintype.card F
    let a : Real := splitCubicPointTrace c (c + h)
    let e : Real := (quadraticChar F) h
    let f : Real := (quadraticChar F) (-h)
    let x : Real := (quadraticChar F) c
    let y : Real := (quadraticChar F) (c + h)
    |normalizedPairCount c h -
      ellipticFactor q a * dirichletFactor q e f x y * twistCorrection q a e f x y| <=
        (ellipticFactor q a * dirichletFactor q e f x y * twistCorrection q a e f x y) *
          (32832 / q ^ 2) := by
  let q : Real := Fintype.card F
  let a : Real := splitCubicPointTrace c (c + h)
  let e : Real := (quadraticChar F) h
  let f : Real := (quadraticChar F) (-h)
  let x : Real := (quadraticChar F) c
  let y : Real := (quadraticChar F) (c + h)
  change |normalizedPairCount c h -
    ellipticFactor q a * dirichletFactor q e f x y * twistCorrection q a e f x y| <=
      (ellipticFactor q a * dirichletFactor q e f x y * twistCorrection q a e f x y) *
        (32832 / q ^ 2)
  have ha := trace_half_of_square q a hq hasq
  have he := quadraticChar_real_signs h hh
  have hf := quadraticChar_real_signs (-h) (neg_ne_zero.mpr hh)
  have hx := quadraticChar_real_signs c hc
  have hy := quadraticChar_real_signs (c + h) hch
  have hk := activeRows_twice_cases e f x y he hf hx hy
  have hTl := scalarTwist_lower q a hq ha (2 * activeRows e f x y) hk
  change (1 / 2 : Real) <= twistCorrection q a e f x y at hTl
  have hTpos : 0 < twistCorrection q a e f x y := by linarith
  have href : 0 < ellipticFactor q a * dirichletFactor q e f x y * twistCorrection q a e f x y :=
    mul_pos (reference_pos q a e f x y hq ha he hf hx hy) hTpos
  have hb := normalizedPairCount_corrected_factorization hF c h hc hch hh hq hasq
  change normalizedPairCount c h =
    ellipticFactor q a * dirichletFactor q e f x y *
      twistCorrection q a e f x y * correctedCarrier q a e f x y at hb
  have hdiff : normalizedPairCount c h -
      ellipticFactor q a * dirichletFactor q e f x y * twistCorrection q a e f x y =
        (ellipticFactor q a * dirichletFactor q e f x y * twistCorrection q a e f x y) *
          (correctedCarrier q a e f x y - 1) := by
    rw [hb]
    ring
  rw [hdiff, abs_mul, abs_of_pos href]
  exact mul_le_mul_of_nonneg_left
    (corrected_carrier_bound q a e f x y hq hasq he hf hx hy) (le_of_lt href)

end FiniteField.QuadraticPairEuler
