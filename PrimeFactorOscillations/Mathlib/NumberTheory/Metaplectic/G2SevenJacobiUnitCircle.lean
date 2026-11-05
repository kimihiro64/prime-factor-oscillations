/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.LinearCombination
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.G2SevenJacobiEdgeAlgebra

/-!
# Exact signed unit-circle certificate for the septic Jacobi edge

This universal ring identity keeps all six Laurent squares. The prime-field
nonvanishing input is a separate arithmetic theorem, not an assumption here.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace Metaplectic.G2Seven.Edge

theorem unit_sos_identity {R : Type*} [CommRing R]
    (b bb c cc d dd : R)
    (hb : b * bb = 1) (hc : c * cc = 1) (hd : d * dd = 1) :
    let a := b * d * cc
    let aa := bb * dd * c
    let u1 := bb * dd
    let v1 := b * d
    let u2 := d * cc
    let v2 := dd * c
    let u3 := c * bb
    let v3 := cc * b
    let e1 := (1 - b * d) * (1 - bb * dd)
    let e2 := (b - c) * (bb - cc)
    let e3 := (c - d) * (cc - dd)
    let l1 := 2 * (1 + u1) - u1 * (a + b + c + d)
    let k1 := 2 * (1 + v1) - v1 * (aa + bb + cc + dd)
    let l2 := 2 * (1 + u2) - (a + d + bb + cc)
    let k2 := 2 * (1 + v2) - (aa + dd + b + c)
    let l3 := 2 * (1 + u3) - (aa + bb + c + d)
    let k3 := 2 * (1 + v3) - (a + b + cc + dd)
    let r1 := (1 + u1) * (1 - u2)
    let s1 := (1 + v1) * (1 - v2)
    let r2 := (1 + u2) * (1 - u3)
    let s2 := (1 + v2) * (1 - v3)
    let r3 := (1 + u3) * (1 - u1)
    let s3 := (1 + v3) * (1 - v1)
    4 * (60 - 6 * (b + bb + c + cc + d + dd) -
      12 * (a + aa) - 4 * (e1 + e2 + e3)) =
      2 * (l1 * k1 + l2 * k2 + l3 * k3 +
        r1 * s1 + r2 * s2 + r3 * s3) +
      24 * (1 - a) * (1 - aa) := by
  dsimp only
  linear_combination
    ((-30) * d * dd +
    (-20) * 1 +
    (8) * c * d * dd +
    (4) * d +
    (4) * bb * c * d * (dd ^ 2) +
    (4) * bb * d * dd +
    (8) * cc * d * dd +
    (4) * d * (dd ^ 2) +
    (4) * b * cc * (d ^ 2) * dd +
    (-2) * b * bb * c * cc * (d ^ 2) * (dd ^ 2) +
    (-2) * b * bb * cc * (d ^ 2) * dd +
    (-2) * b * (cc ^ 2) * (d ^ 2) * dd +
    (-2) * b * cc * (d ^ 2) * (dd ^ 2) +
    (4) * dd +
    (4) * b * d * dd +
    (-2) * b * bb * c * d * (dd ^ 2) +
    (-2) * b * bb * d * dd +
    (-4) * b * cc * d * dd +
    (-2) * b * d * (dd ^ 2) +
    (-2) * bb * (c ^ 2) * d * (dd ^ 2) +
    (-4) * bb * c * d * dd +
    (-32) * c * cc * d * dd +
    (4) * (d ^ 2) * dd +
    (-2) * bb * c * (d ^ 2) * (dd ^ 2) +
    (-2) * bb * (d ^ 2) * dd +
    (-2) * (d ^ 2) * (dd ^ 2) +
    (-12) * c * cc +
    (4) * c * cc * d +
    (4) * c +
    (4) * c * cc * dd +
    (-2) * c * dd +
    (4) * cc +
    (-2) * cc * d +
    (-4) * c * cc * (d ^ 2) * (dd ^ 2) +
    (-2) * (c ^ 2) * cc * dd +
    (-2) * c * (cc ^ 2) * d +
    (-2) * (c ^ 2) * (cc ^ 2) * d * dd +
    (2) * cc * dd +
    (2) * c * d +
    (2) * b * c * cc * d +
    (2) * bb * c * cc * dd +
    (-2) * b * bb * c * cc * d * dd +
    (-2) * cc * (d ^ 2) * dd +
    (-2) * c * d * (dd ^ 2)) * hb +
    ((-48) * 1 +
    (-46) * d * dd +
    (4) * bb * d * dd +
    (8) * d +
    (4) * b * d * dd +
    (-2) * b * d +
    (8) * dd +
    (-2) * bb * dd +
    (4) * bb +
    (4) * b +
    (-2) * b * (d ^ 2) * dd +
    (-2) * bb * d * (dd ^ 2) +
    (2) * b * dd +
    (2) * b * cc * d * dd +
    (2) * bb * d +
    (2) * bb * c * d * dd +
    (-4) * (d ^ 2) * (dd ^ 2) +
    (-2) * c * dd +
    (-2) * cc * d +
    (-2) * c * cc * d * dd) * hc +
    ((-102) * 1 +
    (12) * b +
    (12) * bb +
    (12) * cc +
    (-6) * b * cc +
    (12) * c +
    (-6) * bb * c +
    (2) * b * c +
    (2) * bb * cc +
    (4) * bb * c * dd +
    (4) * dd +
    (4) * b * cc * d +
    (-2) * b * (cc ^ 2) * d +
    (-2) * b * cc * d * dd +
    (-2) * b * dd +
    (-2) * bb * (c ^ 2) * dd +
    (4) * d +
    (-2) * bb * c * d * dd +
    (-2) * bb * d +
    (-6) * d * dd +
    (-2) * cc * d +
    (-2) * c * dd +
    (-2) * b * d +
    (-2) * bb * dd) * hd

local notation "bar" => starRingEnd Complex

/-- Full signed Laurent certificate implies a phase gap without a sector restriction. -/
theorem unit_phase_gap (b c d : Complex)
    (hb : Complex.normSq b = 1)
    (hc : Complex.normSq c = 1)
    (hd : Complex.normSq d = 1) :
    2 * (Complex.normSq (1 - b * d) +
      Complex.normSq (b - c) + Complex.normSq (c - d)) <=
      30 - 6 * (b.re + c.re + d.re) - 12 * (b * d * bar c).re := by
  let a := b * d * bar c
  let u1 := bar b * bar d
  let u2 := d * bar c
  let u3 := c * bar b
  let l1 := 2 * (1 + u1) - u1 * (a + b + c + d)
  let l2 := 2 * (1 + u2) - (a + d + bar b + bar c)
  let l3 := 2 * (1 + u3) - (bar a + bar b + c + d)
  let r1 := (1 + u1) * (1 - u2)
  let r2 := (1 + u2) * (1 - u3)
  let r3 := (1 + u3) * (1 - u1)
  have hbb : b * bar b = 1 := by rw [Complex.mul_conj, hb]; rfl
  have hcc : c * bar c = 1 := by rw [Complex.mul_conj, hc]; rfl
  have hdd : d * bar d = 1 := by rw [Complex.mul_conj, hd]; rfl
  have h := unit_sos_identity b (bar b) c (bar c) d (bar d) hbb hcc hdd
  have heq :
      4 * (60 - 6 * (b + bar b + c + bar c + d + bar d) -
        12 * (a + bar a) -
        4 * ((Complex.normSq (1 - b * d) : Complex) +
          (Complex.normSq (b - c) : Complex) +
          (Complex.normSq (c - d) : Complex))) =
        2 * ((Complex.normSq l1 : Complex) +
          (Complex.normSq l2 : Complex) +
          (Complex.normSq l3 : Complex) +
          (Complex.normSq r1 : Complex) +
          (Complex.normSq r2 : Complex) +
          (Complex.normSq r3 : Complex)) +
        24 * (Complex.normSq (1 - a) : Complex) := by
    simp only [<- Complex.mul_conj]
    simpa only [a, u1, u2, u3, l1, l2, l3, r1, r2, r3,
      map_add, map_sub, map_mul, map_one, map_ofNat,
      Complex.conj_conj, mul_assoc] using h
  have hre := congrArg Complex.re heq
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re] at hre
  norm_num at hre
  have h1 := Complex.normSq_nonneg l1
  have h2 := Complex.normSq_nonneg l2
  have h3 := Complex.normSq_nonneg l3
  have h4 := Complex.normSq_nonneg r1
  have h5 := Complex.normSq_nonneg r2
  have h6 := Complex.normSq_nonneg r3
  have h7 := Complex.normSq_nonneg (1 - a)
  change 2 * (Complex.normSq (1 - b * d) +
    Complex.normSq (b - c) + Complex.normSq (c - d)) <=
    30 - 6 * (b.re + c.re + d.re) - 12 * a.re
  linarith

/-- The three coupled squared distances give a cubic separation from the upper edge. -/
theorem unit_cubic_gap (b c d : Complex)
    (hb : Complex.normSq b = 1)
    (hc : Complex.normSq c = 1)
    (hd : Complex.normSq d = 1) :
    216 * Complex.normSq (1 - b * d) *
      Complex.normSq (b - c) * Complex.normSq (c - d) <=
      (30 - 6 * (b.re + c.re + d.re) -
        12 * (b * d * bar c).re) ^ 3 := by
  let s := Complex.normSq (1 - b * d) +
    Complex.normSq (b - c) + Complex.normSq (c - d)
  let delta := 30 - 6 * (b.re + c.re + d.re) -
    12 * (b * d * bar c).re
  have hgap : 2 * s <= delta := unit_phase_gap b c d hb hc hd
  have htriple := triple_product_bound
    (Complex.normSq (1 - b * d)) (Complex.normSq (b - c))
    (Complex.normSq (c - d)) (Complex.normSq_nonneg _)
    (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  have hquad : 0 <= delta ^ 2 + 2 * delta * s + 4 * s ^ 2 := by
    nlinarith only [sq_nonneg (delta + s), sq_nonneg s]
  have hfactor := mul_nonneg (sub_nonneg.mpr hgap) hquad
  change 216 * Complex.normSq (1 - b * d) *
    Complex.normSq (b - c) * Complex.normSq (c - d) <= delta ^ 3
  change 27 * Complex.normSq (1 - b * d) *
    Complex.normSq (b - c) * Complex.normSq (c - d) <= s ^ 3 at htriple
  nlinarith only [htriple, hfactor]

/-- Arithmetic product separation is carried through the full cubic consumer. -/
theorem unit_arithmetic_gap (b c d : Complex) (p : Real)
    (hb : Complex.normSq b = 1)
    (hc : Complex.normSq c = 1)
    (hd : Complex.normSq d = 1)
    (hp : 0 <= p)
    (hproduct : 7 <= p * Complex.normSq (1 - b * d) *
      Complex.normSq (b - c) * Complex.normSq (c - d)) :
    1512 <= p * (30 - 6 * (b.re + c.re + d.re) -
      12 * (b * d * bar c).re) ^ 3 := by
  have hgap := unit_cubic_gap b c d hb hc hd
  have hscaled := mul_nonneg hp (sub_nonneg.mpr hgap)
  nlinarith only [hproduct, hscaled]

/-- Both edges are controlled by the same retained arithmetic product. -/
theorem unit_absolute_gap (b c d : Complex) (p : Real)
    (hb : Complex.normSq b = 1)
    (hc : Complex.normSq c = 1)
    (hd : Complex.normSq d = 1)
    (hp : 0 <= p)
    (hproduct : 7 <= p * Complex.normSq (1 - b * d) *
      Complex.normSq (b - c) * Complex.normSq (c - d)) :
    1512 <= p * (30 - abs (6 * (b.re + c.re + d.re) +
      12 * (b * d * bar c).re)) ^ 3 := by
  have hupper := unit_arithmetic_gap b c d p hb hc hd hp hproduct
  have he1 : Complex.normSq (1 - (-b) * (-d)) =
      Complex.normSq (1 - b * d) := by rw [neg_mul_neg]
  have he2 : Complex.normSq ((-b) - (-c)) =
      Complex.normSq (b - c) := by
    rw [show (-b) - (-c) = -(b - c) by ring, Complex.normSq_neg]
  have he3 : Complex.normSq ((-c) - (-d)) =
      Complex.normSq (c - d) := by
    rw [show (-c) - (-d) = -(c - d) by ring, Complex.normSq_neg]
  have hprodneg : 7 <= p * Complex.normSq (1 - (-b) * (-d)) *
      Complex.normSq ((-b) - (-c)) * Complex.normSq ((-c) - (-d)) := by
    rw [he1, he2, he3]
    exact hproduct
  have hlower := unit_arithmetic_gap (-b) (-c) (-d) p
    (by rw [Complex.normSq_neg]; exact hb)
    (by rw [Complex.normSq_neg]; exact hc)
    (by rw [Complex.normSq_neg]; exact hd) hp hprodneg
  have hnegprod : (-b) * (-d) * bar (-c) = -(b * d * bar c) := by
    simp only [map_neg]
    ring
  simp only [hnegprod, Complex.neg_re] at hlower
  let t := 6 * (b.re + c.re + d.re) + 12 * (b * d * bar c).re
  have hupperid : 30 - 6 * (b.re + c.re + d.re) -
      12 * (b * d * bar c).re = 30 - t := by dsimp [t]; ring
  have hlowerid : 30 - 6 * (-b.re + -c.re + -d.re) -
      12 * -(b * d * bar c).re = 30 + t := by dsimp [t]; ring
  rw [hupperid] at hupper
  rw [hlowerid] at hlower
  change 1512 <= p * (30 - abs t) ^ 3
  by_cases ht : 0 <= t
  . rw [abs_of_nonneg ht]
    exact hupper
  . rw [abs_of_neg (lt_of_not_ge ht)]
    simpa only [sub_neg_eq_add] using hlower

end Metaplectic.G2Seven.Edge
