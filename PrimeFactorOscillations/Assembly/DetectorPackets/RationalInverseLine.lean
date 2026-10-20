/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional
import OAI.NumberTheory.DirichletL.Hecke.Dirichlet
import OAI.NumberTheory.DirichletL.Hecke.ReciprocalGrowth
import PrimeFactorOscillations.Assembly.DetectorPackets.DirichletCompanionIdentity

/-!
# RationalInverseLine

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described by LICENSE.
Authors: Prime Factor Oscillations contributors
-/


noncomputable section
open scoped Classical
open PrimeFactorOscillations.PeriodicCompanion

namespace PrimeFactorOscillations.RationalInverseLine

def lineConstant (q : Nat) (a : Real) : Real :=
  (a + 1) * (1 / (1 - a) + (2 * (q : Real) + 1) / a)

theorem dirichlet_LFunction_line_bound {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : 0 < q)
    (a : Real) (ha : 0 < a) (ha1 : a < 1) (t : Real) :
    letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
    norm (DirichletCharacter.LFunction chi ((a : Complex) + (t : Complex) * Complex.I)) <=
      lineConstant q a * (1 + t ^ 2) := by
  letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
  let s : Complex := (a : Complex) + (t : Complex) * Complex.I
  have hsre : s.re = a := by simp [s]
  have hs1 : Not (s = 1) := by
    intro he
    have hr := congrArg Complex.re he
    rw [hsre] at hr
    exact (ne_of_lt ha1) (by simpa only [Complex.one_re] using hr)
  have hden : 1 - a <= norm (s - 1) := by
    calc
      _ = abs (s - 1).re := by
        rw [Complex.sub_re, Complex.one_re, hsre, abs_of_neg (sub_neg.mpr ha1)]
        ring
      _ <= _ := Complex.abs_re_le_norm _
  have hrecip := one_div_le_one_div_of_le (sub_pos.mpr ha1) hden
  have hn : norm s <= a + abs t := by
    calc
      _ <= norm (a : Complex) + norm ((t : Complex) * Complex.I) := norm_add_le _ _
      _ = _ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
          mul_one, abs_of_pos ha]
  have habs : abs t <= 1 + t ^ 2 := by
    nlinarith [sq_abs t, sq_nonneg (abs t - (1 / 2 : Real))]
  have hsbound : norm s <= (a + 1) * (1 + t ^ 2) := by
    apply hn.trans
    nlinarith [mul_nonneg ha.le (sq_nonneg t)]
  have hpos : 0 < 1 - a := sub_pos.mpr ha1
  have hL := dirichlet_LFunction_norm_bound chi hq s (by rwa [hsre]) hs1
  change norm (DirichletCharacter.LFunction chi s) <= _
  calc
    _ <= norm s * (1 / norm (s - 1) + (2 * (q : Real) + 1) / a) := by
      simpa only [hsre] using hL
    _ <= norm s * (1 / (1 - a) + (2 * (q : Real) + 1) / a) :=
      mul_le_mul_of_nonneg_left (add_le_add hrecip (le_refl _)) (norm_nonneg _)
    _ <= ((a + 1) * (1 + t ^ 2)) *
        (1 / (1 - a) + (2 * (q : Real) + 1) / a) :=
      mul_le_mul_of_nonneg_right hsbound (by positivity)
    _ = _ := by unfold lineConstant; ring

theorem dirichlet_inverse_eq_baseChange_product {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : 0 < q) (s : Complex)
    (hs : OAI.SevenEighths.HeckeZeroSupremum.beta < s.re)
    (hs0 : Not (s = 0)) (hs1 : Not (s = 1)) :
    letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
    Inv.inv (DirichletCharacter.LFunction chi s) =
      DirichletCharacter.LFunction (OAI.ShortDraftHeckeBridge.baseChangeChar chi) s *
        OAI.SevenEighths.HeckeReciprocal.reciprocal
          (OAI.SevenEighths.HeckeDirichlet.character chi) s := by
  letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
  have hH := OAI.SevenEighths.HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt
    (OAI.SevenEighths.HeckeDirichlet.character chi) hs (Or.inl hs1)
  have hprod : Not (DirichletCharacter.LFunction chi s *
      DirichletCharacter.LFunction (OAI.ShortDraftHeckeBridge.baseChangeChar chi) s = 0) := by
    rw [<- OAI.SevenEighths.HeckeDirichlet.LFunction_eq_dirichlet_product chi hs0 hs1]
    exact hH
  have hA := (mul_ne_zero_iff.mp hprod).1
  have hB := (mul_ne_zero_iff.mp hprod).2
  rw [OAI.SevenEighths.HeckeReciprocal.reciprocal_eq_inv _ hs0 hs1,
    OAI.SevenEighths.HeckeDirichlet.LFunction_eq_dirichlet_product chi hs0 hs1]
  field_simp [hA, hB]
  <;> ring

theorem unconditional_dirichlet_inverse_line_bound {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : 0 < q)
    (a : Real) (ha : (7 / 8 : Real) < a) (ha1 : a < 1) :
    letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
    Exists (fun K : Real => 0 <= K /\ forall t : Real,
      norm (Inv.inv (DirichletCharacter.LFunction chi
        ((a : Complex) + (t : Complex) * Complex.I))) <= K * (1 + t ^ 2) ^ 2) := by
  letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
  have hbeta : OAI.SevenEighths.HeckeZeroSupremum.beta <= (7 / 8 : Real) :=
    OAI.SevenEighths.HeckeCommonProbe.beta_le_seven_eighths
      (OAI.SevenEighths.ProbeFinalAssembly.common_probe_of_chosen_moments
        (OAI.SevenEighths.ProbeFinalAssemblyCertifiedBands.chosen_moments_of_certified
          OAI.SevenEighths.ProbeFinalAssemblyUnconditional.detector_certified_bands))
  let eta := OAI.SevenEighths.HeckeDirichlet.character chi
  choose C hC using OAI.SevenEighths.HeckeReciprocalGrowth.polynomial_reciprocal_bound
    eta a (hbeta.trans_lt ha)
  have ha0 : 0 < a := by linarith
  have hpos : 0 < 1 - a := sub_pos.mpr ha1
  have hnum : 0 <= lineConstant (q * 3) a := by
    unfold lineConstant
    positivity
  let K : Real := lineConstant (q * 3) a * C
  refine Exists.intro K (And.intro (mul_nonneg hnum hC.1) ?_)
  intro t
  let s : Complex := (a : Complex) + (t : Complex) * Complex.I
  have hsre : s.re = a := by simp [s]
  have hsim : s.im = t := by simp [s]
  have hs0 : Not (s = 0) := by
    intro he
    have hr := congrArg Complex.re he
    rw [hsre] at hr
    exact (ne_of_gt ha0) (by simpa only [Complex.zero_re] using hr)
  have hs1 : Not (s = 1) := by
    intro he
    have hr := congrArg Complex.re he
    rw [hsre] at hr
    exact (ne_of_lt ha1) (by simpa only [Complex.one_re] using hr)
  have hp := dirichlet_LFunction_line_bound
    (OAI.ShortDraftHeckeBridge.baseChangeChar chi)
    (Nat.mul_pos hq (by norm_num)) a ha0 ha1 t
  have hi := hC.2 s (by rw [hsre])
  rw [hsim, sq_abs] at hi
  change norm (Inv.inv (DirichletCharacter.LFunction chi s)) <= _
  rw [dirichlet_inverse_eq_baseChange_product chi hq s
    (by rw [hsre]; exact hbeta.trans_lt ha) hs0 hs1, norm_mul]
  calc
    _ <= (lineConstant (q * 3) a * (1 + t ^ 2)) * (C * (1 + t ^ 2)) :=
      mul_le_mul hp hi (norm_nonneg _) (mul_nonneg hnum (by positivity))
    _ = _ := by dsimp [K]; ring

end PrimeFactorOscillations.RationalInverseLine
