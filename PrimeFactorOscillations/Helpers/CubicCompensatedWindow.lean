/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Helpers.DirichletCompensatedProbe

/-!
# Explicit compensated Gaussian Mellin windows

Computes the convergent polynomial-Gamma multiplier, its moments, reflection
and affine scaling. No anti-Fourier or full detector-to-carrier transfer is
assumed from these polynomial identities.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.CubicCompensatedWindow

open MeasureTheory

def expWindow (v : Real) : Complex := Complex.exp (-(v : Complex))

def monomialWindow (k : Nat) (v : Real) : Complex :=
  (v : Complex) ^ k * expWindow v

def rootPolynomial (d s : Complex) : Complex :=
  s * (s - 1) * (s - 2) * (s + d - 1) * (s - d - 1)

def radialWindow (d : Complex) (v : Real) : Complex :=
  32 * monomialWindow 5 v - 400 * monomialWindow 4 v +
    (1352 - 8 * d ^ 2) * monomialWindow 3 v +
    (36 * d ^ 2 - 1284) * monomialWindow 2 v +
    (216 - 24 * d ^ 2) * monomialWindow 1 v

def primeWindow (d : Complex) (u : Real) : Complex :=
  radialWindow d (u ^ 2)

theorem rootPolynomial_reflection (d s : Complex) :
    rootPolynomial d (2 - s) = -rootPolynomial d s := by
  dsimp [rootPolynomial]
  ring

theorem rootPolynomial_affine_endpoints (d : Complex) :
    rootPolynomial d 0 = 0 /\ rootPolynomial d 1 = 0 /\
      rootPolynomial d 2 = 0 /\ rootPolynomial d (1 - d) = 0 /\
        rootPolynomial d (1 + d) = 0 := by
  simp [rootPolynomial]

theorem rootPolynomial_ne_zero (d : Real) (hd : 2 <= d) (s : Complex)
    (hs : (1 / 2 : Real) < s.re) (hs1 : s.re < 1) :
    Not (rootPolynomial (d : Complex) s = 0) := by
  have h0 : Not (s = 0) := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.zero_re] at this
    linarith
  have h1 : Not (s - 1 = 0) := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at this
    linarith
  have h2 : Not (s - 2 = 0) := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
    linarith
  have hp : Not (s + (d : Complex) - 1 = 0) := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.one_re, Complex.zero_re] at this
    linarith
  have hm : Not (s - (d : Complex) - 1 = 0) := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.ofReal_re,
      Complex.one_re, Complex.zero_re] at this
    linarith
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h0 h1) h2) hp) hm

theorem expWindow_convergent (s : Complex) (hs : 0 < s.re) :
    MellinConvergent expWindow s := by
  simpa only [MellinConvergent, expWindow, smul_eq_mul, Complex.ofReal_exp,
    Complex.ofReal_neg, mul_comm] using Complex.GammaIntegral_convergent hs

theorem expWindow_mellin (s : Complex) (hs : 0 < s.re) :
    mellin expWindow s = Complex.Gamma s := by
  have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi hs
    (by norm_num : (0 : Real) < 1)
  simpa [mellin, expWindow, smul_eq_mul] using h

theorem monomialWindow_convergent (k : Nat) (s : Complex) (hs : 0 < s.re) :
    MellinConvergent (monomialWindow k) s := by
  have hpos : 0 < (s + (k : Complex)).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    linarith [show (0 : Real) <= (k : Real) from Nat.cast_nonneg k]
  have h := (MellinConvergent.cpow_smul (f := expWindow) (s := s)
    (a := (k : Complex))).2 (expWindow_convergent _ hpos)
  change MellinConvergent (fun v : Real => (v : Complex) ^ k * expWindow v) s
  simpa only [Complex.cpow_natCast, smul_eq_mul] using h

theorem monomialWindow_mellin (k : Nat) (s : Complex) (hs : 0 < s.re) :
    mellin (monomialWindow k) s = Complex.Gamma (s + (k : Complex)) := by
  have hpos : 0 < (s + (k : Complex)).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    linarith [show (0 : Real) <= (k : Real) from Nat.cast_nonneg k]
  have h := mellin_cpow_smul expWindow s (k : Complex)
  simp only [Complex.cpow_natCast, smul_eq_mul] at h
  exact h.trans (expWindow_mellin _ hpos)

theorem gamma_polynomial (d s : Complex) (hs : 0 < s.re) :
    32 * Complex.Gamma (s + 5) - 400 * Complex.Gamma (s + 4) +
      (1352 - 8 * d ^ 2) * Complex.Gamma (s + 3) +
      (36 * d ^ 2 - 1284) * Complex.Gamma (s + 2) +
      (216 - 24 * d ^ 2) * Complex.Gamma (s + 1) =
        rootPolynomial d (2 * s) * Complex.Gamma s := by
  have hn (j : Nat) : Not (s + (j : Complex) = 0) := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at he
    linarith [show (0 : Real) <= (j : Real) from Nat.cast_nonneg j]
  have h1 := Complex.Gamma_add_one s (by simpa using hn 0)
  have h2 := Complex.Gamma_add_one (s + 1) (by simpa using hn 1)
  have h3 := Complex.Gamma_add_one (s + 2) (by simpa using hn 2)
  have h4 := Complex.Gamma_add_one (s + 3) (by simpa using hn 3)
  have h5 := Complex.Gamma_add_one (s + 4) (by simpa using hn 4)
  have e2 : s + 1 + 1 = s + 2 := by ring
  have e3 : s + 2 + 1 = s + 3 := by ring
  have e4 : s + 3 + 1 = s + 4 := by ring
  have e5 : s + 4 + 1 = s + 5 := by ring
  rw [e2] at h2
  rw [e3] at h3
  rw [e4] at h4
  rw [e5] at h5
  rw [h5, h4, h3, h2, h1]
  dsimp [rootPolynomial]
  ring

theorem radialWindow_hasMellin (d s : Complex) (hs : 0 < s.re) :
    HasMellin (radialWindow d) s
      (rootPolynomial d (2 * s) * Complex.Gamma s) := by
  have hk (k : Nat) (c : Complex) :
      HasMellin (fun v : Real => c * monomialWindow k v) s
        (c * Complex.Gamma (s + (k : Complex))) := by
    have h := hasMellin_const_smul (monomialWindow_convergent k s hs) c
    simpa only [smul_eq_mul, monomialWindow_mellin k s hs] using h
  have h5 := hk 5 32
  have h4 := hk 4 400
  have h3 := hk 3 (1352 - 8 * d ^ 2)
  have h2 := hk 2 (36 * d ^ 2 - 1284)
  have h1 := hk 1 (216 - 24 * d ^ 2)
  have h54 := hasMellin_sub h5.1 h4.1
  rw [h5.2, h4.2] at h54
  have h543 := hasMellin_add h54.1 h3.1
  rw [h54.2, h3.2] at h543
  have h5432 := hasMellin_add h543.1 h2.1
  rw [h543.2, h2.2] at h5432
  have h54321 := hasMellin_add h5432.1 h1.1
  rw [h5432.2, h1.2] at h54321
  have he := h54321.2
  norm_num only [Nat.cast_ofNat] at he
  rw [gamma_polynomial d s hs] at he
  exact And.intro h54321.1 he

theorem primeWindow_hasMellin (d s : Complex) (hs : 0 < s.re) :
    HasMellin (primeWindow d) s
      (HSMul.hSMul (Inv.inv (2 : Real))
        (rootPolynomial d s * Complex.Gamma (s / 2))) := by
  have hs2 : 0 < (s / 2).re := by
    simp only [Complex.div_ofNat_re]
    linarith
  have hRad := radialWindow_hasMellin d (s / 2) hs2
  have hc : MellinConvergent
      (fun u : Real => radialWindow d (u ^ (2 : Real))) s :=
    (MellinConvergent.comp_rpow (by norm_num : Not ((2 : Real) = 0))).2
      (by simpa only [Complex.ofReal_ofNat] using hRad.1)
  have hpow : (fun u : Real => radialWindow d (u ^ (2 : Real))) =
      (fun u : Real => radialWindow d (u ^ 2)) := by
    funext u
    exact congrArg (radialWindow d) (Real.rpow_natCast u 2)
  rw [hpow] at hc
  have hm := mellin_comp_rpow (radialWindow d) s (2 : Real)
  rw [hpow] at hm
  have hp : (2 : Complex) * (s / 2) = s := by ring
  have he : mellin (primeWindow d) s =
      HSMul.hSMul (Inv.inv (2 : Real))
        (rootPolynomial d s * Complex.Gamma (s / 2)) := by
    change mellin (fun u : Real => radialWindow d (u ^ 2)) s = _
    simpa only [Complex.ofReal_ofNat, abs_of_pos (by norm_num :
      (0 : Real) < 2), hRad.2, hp] using hm
  exact And.intro hc he

theorem radialWindow_zero (d : Complex) : radialWindow d 0 = 0 := by
  norm_num [radialWindow, monomialWindow, expWindow]

theorem primeWindow_mellin_one (d : Complex) :
    mellin (primeWindow d) 1 = 0 := by
  have h := (primeWindow_hasMellin d 1 (by norm_num)).2
  simpa only [rootPolynomial, sub_self, mul_zero, zero_mul, smul_zero] using h

theorem primeWindow_mellin_two (d : Complex) :
    mellin (primeWindow d) 2 = 0 := by
  have h := (primeWindow_hasMellin d 2 (by norm_num)).2
  simpa only [rootPolynomial, sub_self, mul_zero, zero_mul, smul_zero] using h

theorem rootPolynomial_affine_scale (d s : Complex) (hd : Not (d = 0)) :
    rootPolynomial d (d * (s - 1) + 1) =
      d ^ 5 * rootPolynomial (Inv.inv d) s := by
  dsimp [rootPolynomial]
  field_simp
  ring

theorem quarticPolynomial_reference (s : Complex) :
    rootPolynomial 4 s =
      (4 : Complex) ^ 5 *
        rootPolynomial (Inv.inv 4) (DirichletCompensatedProbe.quarticMap s) := by
  have h := rootPolynomial_affine_scale (4 : Complex)
    (DirichletCompensatedProbe.quarticMap s) (by norm_num)
  have he : (4 : Complex) * (DirichletCompensatedProbe.quarticMap s - 1) + 1 = s := by
    dsimp [DirichletCompensatedProbe.quarticMap]
    ring
  rw [he] at h
  exact h

end PrimeFactorOscillations.CubicCompensatedWindow
