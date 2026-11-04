/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.G2SevenFermatReadout

/-!
# Sharp stability in the Paley sector of the sevenfold cubic source

The full three-phase inequality is not assumed. This file treats the exact
sector g = h = inverse j through its real circle coordinates.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace Metaplectic.G2Seven.Paley

noncomputable def quartic (t c : Real) : Real :=
  -16 * c ^ 4 + 16 * t * c ^ 3 + (2 - 2 * t) * c ^ 2 -
    (3 + 16 * t) * c + (19 / 4 + 2 * t)

theorem half_root_bounds (t : Real) (hpos : 0 < t) (hsq : t ^ 2 = 1 / 2) :
    7 / 10 <= t /\ t <= 71 / 100 := by
  constructor
  case left =>
    by_contra h
    have hlt : t < 7 / 10 := lt_of_not_ge h
    have hm := mul_nonneg hpos.le (sub_nonneg.mpr hlt.le)
    nlinarith
  case right =>
    by_contra h
    have hlt : 71 / 100 < t := lt_of_not_ge h
    have hm := mul_nonneg (sub_nonneg.mpr hlt.le)
      (show 0 <= t + 71 / 100 by linarith)
    nlinarith

theorem quartic_bernstein (t z : Real) (hsq : t ^ 2 = 1 / 2) :
    quartic t (-7 / 8 + (7 / 8 + t / 2) * z) =
      (-121 / 256 + 15 / 4 * t) * (1 - z) ^ 4 +
      4 * (9 + 1741 / 128 * t) * z * (1 - z) ^ 3 +
      6 * (893 / 192 + 1247 / 192 * t) * z ^ 2 * (1 - z) ^ 2 +
      4 * (23 / 8 + 27 / 8 * t) * z ^ 3 * (1 - z) +
      (5 / 4 + t / 4) * z ^ 4 := by
  have ht3 : t ^ 3 = t / 2 := by
    calc
      t ^ 3 = t * t ^ 2 := by ring
      _ = t / 2 := by rw [hsq]; ring
  have ht4 : t ^ 4 = 1 / 4 := by
    calc
      t ^ 4 = (t ^ 2) ^ 2 := by ring
      _ = 1 / 4 := by rw [hsq]; norm_num
  unfold quartic
  ring_nf
  simp only [hsq, ht3, ht4]
  ring

theorem quartic_nonneg (t c : Real) (hpos : 0 < t) (hsq : t ^ 2 = 1 / 2)
    (hlo : -7 / 8 <= c) (hhi : c <= t / 2) : 0 <= quartic t c := by
  have hb := half_root_bounds t hpos hsq
  have hd : 0 < 7 / 8 + t / 2 := by linarith
  let z := (c + 7 / 8) / (7 / 8 + t / 2)
  have hz0 : 0 <= z := div_nonneg (by linarith) hd.le
  have hz1 : z <= 1 := (div_le_one hd).mpr (by linarith)
  have hcz : c = -7 / 8 + (7 / 8 + t / 2) * z := by
    dsimp [z]
    field_simp
    ring
  rw [hcz, quartic_bernstein t z hsq]
  have h0 : 0 <= -121 / 256 + 15 / 4 * t := by linarith [hb.1]
  have h1 : 0 <= 9 + 1741 / 128 * t := by positivity
  have h2 : 0 <= 893 / 192 + 1247 / 192 * t := by positivity
  have h3 : 0 <= 23 / 8 + 27 / 8 * t := by positivity
  have h4 : 0 <= 5 / 4 + t / 4 := by positivity
  have hz : 0 <= 1 - z := by linarith
  positivity

theorem residual_factorization (t c : Real) (hsq : t ^ 2 = 1 / 2) :
    7 * (6 + 3 * t) ^ 2 * (1 - c ^ 2) -
      (6 + 18 * t + (-12 + 3 * t) * c + 48 * c ^ 3) ^ 2 =
      144 * (c + t / 2) ^ 2 * quartic t c := by
  have ht3 : t ^ 3 = t / 2 := by
    calc
      t ^ 3 = t * t ^ 2 := by ring
      _ = t / 2 := by rw [hsq]; ring
  unfold quartic
  ring_nf
  simp only [hsq, ht3]
  ring

/-- The negative-c tail has a direct signed bound before squaring. -/
theorem tail_nonpos (t c : Real) (hpos : 0 < t) (hsq : t ^ 2 = 1 / 2)
    (hc : c <= -7 / 8) :
    6 + 18 * t + (-12 + 3 * t) * c + 48 * c ^ 3 <= 0 := by
  have hb := half_root_bounds t hpos hsq
  let w := -7 / 8 - c
  have hw : 0 <= w := by dsimp [w]; linarith
  have he : 6 + 18 * t + (-12 + 3 * t) * c + 48 * c ^ 3 =
      -501 / 32 + 123 / 8 * t -
        ((393 / 4 + 3 * t) * w + 126 * w ^ 2 + 48 * w ^ 3) := by
    dsimp [w]
    ring
  have ht : -501 / 32 + 123 / 8 * t <= 0 := by linarith [hb.2]
  have hwterm : 0 <= (393 / 4 + 3 * t) * w + 126 * w ^ 2 + 48 * w ^ 3 := by
    positivity
  linarith only [he, ht, hwterm]

/-- Sharp stability for every point of the real circle in the Paley sector. -/
theorem sharp_stability (t v c s : Real) (ht : 0 < t) (ht2 : t ^ 2 = 1 / 2)
    (hv : 0 <= v) (hv2 : v ^ 2 = 7) (hs : 0 <= s) (hcircle : c ^ 2 + s ^ 2 = 1) :
    (6 + 3 * t) * min (6 - 6 * c) (6 + c - v * s) <=
      30 + 18 * c - 48 * c ^ 3 := by
  have hk : 0 <= 6 + 3 * t := by positivity
  have hc1 : c <= 1 := by nlinarith [sq_nonneg (c - 1), sq_nonneg s]
  by_cases hcut : t / 2 <= c
  case pos =>
    have hcp : 0 <= c + t / 2 := by linarith
    have hprod := mul_nonneg (sub_nonneg.mpr hcut) hcp
    have hpoly : 0 <= 8 * c ^ 2 + 8 * c - 1 - 3 * t := by
      nlinarith
    have hf : 0 <= 6 * (1 - c) * (8 * c ^ 2 + 8 * c - 1 - 3 * t) :=
      mul_nonneg (by linarith) hpoly
    have hb : (6 + 3 * t) * (6 - 6 * c) <= 30 + 18 * c - 48 * c ^ 3 := by
      nlinarith only [hf]
    exact le_trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hk) hb
  case neg =>
    have hupper : c <= t / 2 := le_of_lt (lt_of_not_ge hcut)
    let A := 6 + 18 * t + (-12 + 3 * t) * c + 48 * c ^ 3
    have hB : 0 <= (6 + 3 * t) * v * s := by positivity
    have hA : A <= (6 + 3 * t) * v * s := by
      by_cases htail : c <= -7 / 8
      case pos =>
        exact le_trans (tail_nonpos t c ht ht2 htail) hB
      case neg =>
        have hq := quartic_nonneg t c ht ht2 (le_of_lt (lt_of_not_ge htail)) hupper
        have hp : 0 <= 7 * (6 + 3 * t) ^ 2 * (1 - c ^ 2) - A ^ 2 := by
          dsimp [A]
          rw [residual_factorization t c ht2]
          positivity
        have hss : s ^ 2 = 1 - c ^ 2 := by linarith
        have he : ((6 + 3 * t) * v * s) ^ 2 =
            7 * (6 + 3 * t) ^ 2 * (1 - c ^ 2) := by
          simp only [mul_pow, hv2, hss]
          ring
        by_contra h
        have hlt : (6 + 3 * t) * v * s < A := lt_of_not_ge h
        have hprod : 0 < (A - (6 + 3 * t) * v * s) *
            (A + (6 + 3 * t) * v * s) :=
          mul_pos (by linarith) (by linarith)
        nlinarith only [hp, he, hprod]
    have hb : (6 + 3 * t) * (6 + c - v * s) <=
        30 + 18 * c - 48 * c ^ 3 := by
      dsimp [A] at hA
      nlinarith only [hA]
    exact le_trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hk) hb

/-- The noncoherent equality point has strictly positive distance. -/
theorem attainer (t v : Real) (ht : 0 < t) (ht2 : t ^ 2 = 1 / 2)
    (hv : 0 <= v) (hv2 : v ^ 2 = 7) :
    0 <= v * t / 2 /\ (-t / 2) ^ 2 + (v * t / 2) ^ 2 = 1 /\
    min (6 - 6 * (-t / 2)) (6 + (-t / 2) - v * (v * t / 2)) = 6 - 4 * t /\
    0 < 6 - 4 * t /\
    30 + 18 * (-t / 2) - 48 * (-t / 2) ^ 3 = (6 + 3 * t) * (6 - 4 * t) := by
  have hb := half_root_bounds t ht ht2
  have ht3 : t ^ 3 = t / 2 := by
    calc
      t ^ 3 = t * t ^ 2 := by ring
      _ = t / 2 := by rw [ht2]; ring
  have he1 : (-t / 2) ^ 2 + (v * t / 2) ^ 2 = 1 := by
    simp only [div_pow, neg_sq, mul_pow, hv2, ht2]
    norm_num
  have he2 : 6 + (-t / 2) - v * (v * t / 2) = 6 - 4 * t := by
    calc
      _ = 6 - t / 2 - v ^ 2 * t / 2 := by ring
      _ = 6 - 4 * t := by rw [hv2]; ring
  have hm : min (6 - 6 * (-t / 2)) (6 + (-t / 2) - v * (v * t / 2)) =
      6 - 4 * t := by
    rw [he2, min_eq_right (by linarith)]
  have hd : 0 < 6 - 4 * t := by linarith [hb.2]
  have he3 : 30 + 18 * (-t / 2) - 48 * (-t / 2) ^ 3 =
      (6 + 3 * t) * (6 - 4 * t) := by
    ring_nf
    simp only [ht2, ht3]
    ring
  exact And.intro (by positivity) (And.intro he1 (And.intro hm (And.intro hd he3)))

/-- No larger uniform constant works, even within this one-parameter sector. -/
theorem optimal_constant (t v K : Real) (ht : 0 < t) (ht2 : t ^ 2 = 1 / 2)
    (hv : 0 <= v) (hv2 : v ^ 2 = 7)
    (hK : forall c s : Real, 0 <= s -> c ^ 2 + s ^ 2 = 1 ->
      K * min (6 - 6 * c) (6 + c - v * s) <= 30 + 18 * c - 48 * c ^ 3) :
    K <= 6 + 3 * t := by
  have ha := attainer t v ht ht2 hv hv2
  have he := hK (-t / 2) (v * t / 2) ha.1 ha.2.1
  rw [ha.2.2.1, ha.2.2.2.2] at he
  by_contra h
  have hlt : 6 + 3 * t < K := lt_of_not_ge h
  have hp : 0 < (K - (6 + 3 * t)) * (6 - 4 * t) :=
    mul_pos (sub_pos.mpr hlt) ha.2.2.2.1
  nlinarith only [he, hp]

/-- The full multiplicity-weighted source, with both cubic sectors retained. -/
theorem sector_phase_total (g : Complex) (hg : Not (g = 0)) :
    Fermat.phaseTotal g g (g ^ (-1 : Int)) =
      6 * (g + g ^ (-1 : Int)) ^ 3 - 9 * (g + g ^ (-1 : Int)) := by
  norm_num [Fermat.phaseTotal, Jacobi.multiplicity, Jacobi.phase,
    Fin.sum_univ_succ, zpow_neg_one]
  field_simp [hg]
  ring

/-- Unit-circle coordinates evaluate the actual eight-sector phase table. -/
theorem unit_sector_trace (g : Complex) (hcircle : g.re ^ 2 + g.im ^ 2 = 1) :
    Fermat.phaseTotal g g (g ^ (-1 : Int)) =
      ((48 * g.re ^ 3 - 18 * g.re : Real) : Complex) := by
  have hunit : g * star g = 1 := by
    apply Complex.ext <;>
      simp only [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re,
        Complex.conj_im, Complex.one_re, Complex.one_im]
    all_goals nlinarith only [hcircle]
  have hg : Not (g = 0) := by
    intro he
    rw [he, zero_mul] at hunit
    exact zero_ne_one hunit
  have hinv : g ^ (-1 : Int) = star g := by
    rw [zpow_neg_one]
    calc
      Inv.inv g = Inv.inv g * (g * star g) := by rw [hunit]; simp
      _ = star g := by simp [hg]
  have hsum : g + g ^ (-1 : Int) = 2 * (g.re : Complex) := by
    rw [hinv]
    apply Complex.ext <;> simp <;> ring
  rw [sector_phase_total g hg, hsum]
  push_cast
  ring

/-- The sharp scalar inequality controls the full cubic source on this sector. -/
theorem cubic_source_stability (g : Complex) (hcircle : g.re ^ 2 + g.im ^ 2 = 1) :
    (6 + 3 * (Real.sqrt 2 / 2)) *
      min (6 - 6 * g.re) (6 + g.re - Real.sqrt 7 * |g.im|) <=
      30 - (Fermat.phaseTotal g g (g ^ (-1 : Int))).re := by
  have ht : 0 < Real.sqrt 2 / 2 := by positivity
  have ht2 : (Real.sqrt 2 / 2) ^ 2 = (1 / 2 : Real) := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hv2 : (Real.sqrt 7) ^ 2 = (7 : Real) := Real.sq_sqrt (by norm_num)
  have hc : g.re ^ 2 + |g.im| ^ 2 = 1 := by simpa only [sq_abs] using hcircle
  have he := sharp_stability (Real.sqrt 2 / 2) (Real.sqrt 7) g.re |g.im|
    ht ht2 (Real.sqrt_nonneg 7) hv2 (abs_nonneg g.im) hc
  rw [unit_sector_trace g hcircle]
  simp only [Complex.ofReal_re]
  linarith only [he]

end Metaplectic.G2Seven.Paley
