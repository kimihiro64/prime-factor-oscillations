/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.G2SevenCubicSpectrum

/-!
# Individual compensated Jacobi readouts from the sevenfold source model

All eight nondegenerate triple types are extracted with their actual
multiplicities and torus weights. Every mask keeps the entire principal
channel. Both coherent periods are compensated before the cubic operation.
This is a local arithmetic theorem, not a global Hecke identification.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace Metaplectic.G2Seven.Jacobi

open Cubic Spectrum

private theorem tripleEntry_lt : forall (i : Fin 8) (j : Fin 3),
    tripleEntry i j < 7 := by decide

def grade (i : Fin 8) (j : Fin 3) : Fin 7 :=
  Fin.mk (tripleEntry i j) (tripleEntry_lt i j)

def mask (i : Fin 8) (r : Fin 7) : Bool :=
  decide (r.val = 0 \/ r.val = tripleEntry i 0 \/
    r.val = tripleEntry i 1 \/ r.val = tripleEntry i 2)

def multiplicity (i : Fin 8) : Nat :=
  if i.val = 1 \/ i.val = 5 then 6 else 3

def masked (i : Fin 8) (v : Fin 7 -> Complex) (r : Fin 7) : Complex :=
  if mask i r then v r else 0

def tripleProduct (i : Fin 8) (v : Fin 7 -> Complex) : Complex :=
  v (grade i 0) * v (grade i 1) * v (grade i 2)

private theorem amplitudes_eta (v : Fin 7 -> Complex) :
    amplitudes (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) = v := by
  funext r
  fin_cases r <;> rfl

/-- Exact masked cube for every spectrum entry and arbitrary principal amplitude. -/
theorem masked_cubic_mean (i : Fin 8) (v : Fin 7 -> Complex) :
    mean (fun a => (signal (masked i v) a) ^ 3) =
      (v 0) ^ 3 + (multiplicity i : Complex) * tripleProduct i v := by
  rw [<- amplitudes_eta (masked i v), complete_cubic_mean]
  fin_cases i <;>
    norm_num [masked, mask, multiplicity, tripleProduct, grade, tripleEntry] <;> ring
  all_goals simp

def negNonprincipal (v : Fin 7 -> Complex) (r : Fin 7) : Complex :=
  if r.val = 0 then v r else -v r

theorem masked_negation (i : Fin 8) (v : Fin 7 -> Complex) (a : ZMod 7) :
    2 * v 0 - signal (masked i v) a =
      signal (masked i (negNonprincipal v)) a := by
  fin_cases i <;>
    norm_num [signal, masked, mask, negNonprincipal, tripleEntry,
      Fin.sum_univ_succ] <;> ring

private theorem tripleProduct_neg (i : Fin 8) (v : Fin 7 -> Complex) :
    tripleProduct i (negNonprincipal v) = -tripleProduct i v := by
  fin_cases i <;>
    norm_num [tripleProduct, negNonprincipal, grade, tripleEntry] <;> ring

private theorem multiplicity_ne_zero (i : Fin 8) :
    Not ((multiplicity i : Complex) = 0) := by
  fin_cases i <;> norm_num [multiplicity]

noncomputable def probe (i : Fin 8) (v : Fin 7 -> Complex) (a : ZMod 7) : Complex :=
  1 + ((2 * v 0 - signal (masked i v) a) ^ 3 - (v 0) ^ 3) /
    (multiplicity i : Complex)

/-- All binomial cross terms cancel, with divisor three or six as appropriate. -/
theorem probe_mean (i : Fin 8) (v : Fin 7 -> Complex) :
    mean (probe i v) = 1 - tripleProduct i v := by
  have hc : mean (fun a => (signal (masked i (negNonprincipal v)) a) ^ 3) =
      (v 0) ^ 3 - (multiplicity i : Complex) * tripleProduct i v := by
    rw [masked_cubic_mean, tripleProduct_neg]
    change (v 0) ^ 3 + (multiplicity i : Complex) * (-tripleProduct i v) = _
    ring
  unfold mean at hc
  have hsum := (div_eq_iff (by norm_num : Not ((7 : Complex) = 0))).mp hc
  unfold mean probe
  simp_rw [masked_negation]
  rw [Finset.sum_add_distrib, <- Finset.sum_div, Finset.sum_sub_distrib, hsum]
  norm_num
  field_simp [multiplicity_ne_zero i]
  ring

noncomputable def physical (t g h j X Y : Complex) : Fin 7 -> Complex :=
  amplitudes (principal t X Y) (t * g * X) (t ^ 3 * h * X ^ 4 * Y ^ 4)
    (t * j * Y) (t ^ 3 / j * X ^ 3 * Y ^ 5)
    (t ^ 3 / h * X ^ 6 * Y ^ 2) (t ^ 3 / g * X ^ 2 * Y ^ 6)

/-- Each actual source mask retains all six principal coordinates. -/
theorem source_masked_carrier (i : Fin 8) (t g h j X Y : Complex)
    (hg : Not (g = 0)) (hh : Not (h = 0)) (hj : Not (j = 0)) (a : ZMod 7) :
    torusProjection (mask i) t g h j X Y a =
      signal (masked i (physical t g h j X Y)) a := by
  fin_cases i <;>
    norm_num [torusProjection, signal, masked, mask, physical, amplitudes,
      principal, Fintype.sum_prod_type, Fin.sum_univ_succ, signedBase,
      supported, degree, row, phaseValue, phase, twistClass, tripleEntry, zpow_neg_one] <;>
    field_simp [hg, hh, hj] <;> ring

noncomputable def phase (i : Fin 8) (g h j : Complex) : Complex :=
  match i.val with
  | 0 => g ^ 2 / h
  | 1 => g * h / j
  | 2 => g * j ^ 2
  | 3 => h ^ 2 * j
  | 4 => h / g ^ 2
  | 5 => j / (g * h)
  | 6 => 1 / (g * j ^ 2)
  | _ => 1 / (j * h ^ 2)

def powers (i : Fin 8) (k : Fin 3) : Nat :=
  match i.val, k.val with
  | 0, 0 => 5
  | 0, 1 => 8
  | 0, _ => 2
  | 1, 0 => 7
  | 1, 1 => 8
  | 1, _ => 9
  | 2, 0 => 3
  | 2, 1 => 1
  | 2, _ => 2
  | 3, 0 => 7
  | 3, 1 => 8
  | 3, _ => 9
  | 4, 0 => 9
  | 4, 1 => 8
  | 4, _ => 16
  | 5, 0 => 7
  | 5, 1 => 8
  | 5, _ => 9
  | 6, 0 => 9
  | 6, 1 => 8
  | 6, _ => 16
  | _, 0 => 9
  | _, 1 => 15
  | _, _ => 9

def weight (i : Fin 8) (t X Y : Complex) : Complex :=
  t ^ powers i 0 * X ^ powers i 1 * Y ^ powers i 2

theorem physical_product (i : Fin 8) (t g h j X Y : Complex)
    (hg : Not (g = 0)) (hh : Not (h = 0)) (hj : Not (j = 0)) :
    tripleProduct i (physical t g h j X Y) =
      phase i g h j * weight i t X Y := by
  fin_cases i <;>
    norm_num [tripleProduct, physical, amplitudes, grade, tripleEntry, phase, weight, powers] <;>
    field_simp [hg, hh, hj] <;> ring

noncomputable def finiteProbe (i : Fin 8) (t g h j X Y : Complex)
    (a : ZMod 7) : Complex :=
  1 + ((2 * principal t X Y - torusProjection (mask i) t g h j X Y a) ^ 3 -
    (principal t X Y) ^ 3) / (multiplicity i : Complex)

theorem finite_probe_mean (i : Fin 8) (t g h j X Y : Complex)
    (hg : Not (g = 0)) (hh : Not (h = 0)) (hj : Not (j = 0)) :
    mean (finiteProbe i t g h j X Y) = 1 - phase i g h j * weight i t X Y := by
  unfold finiteProbe
  simp_rw [source_masked_carrier i t g h j X Y hg hh hj]
  change mean (probe i (physical t g h j X Y)) = _
  rw [probe_mean, physical_product i t g h j X Y hg hh hj]

noncomputable def coherentProbe (i : Fin 8) (t g h j X Y : Complex)
    (a : ZMod 7) : Complex :=
  1 + ((2 * principal t X Y -
    periodDenominator t X Y * coherentProjection (mask i) t g h j X Y a) ^ 3 -
    (principal t X Y) ^ 3) / (multiplicity i : Complex)

theorem coherent_probe_eq (i : Fin 8) (t g h j X Y : Complex)
    (hD : Not (periodDenominator t X Y = 0)) (a : ZMod 7) :
    coherentProbe i t g h j X Y a = finiteProbe i t g h j X Y a := by
  have hc : periodDenominator t X Y * coherentProjection (mask i) t g h j X Y a =
      torusProjection (mask i) t g h j X Y a := by
    unfold coherentProjection
    field_simp [hD]
  unfold coherentProbe finiteProbe
  rw [hc]

/-- Uniform readout across all eight Jacobi types, with both full periods compensated. -/
theorem coherent_probe_mean (i : Fin 8) (t g h j X Y : Complex)
    (hg : Not (g = 0)) (hh : Not (h = 0)) (hj : Not (j = 0))
    (hD : Not (periodDenominator t X Y = 0)) :
    mean (coherentProbe i t g h j X Y) = 1 - phase i g h j * weight i t X Y := by
  unfold mean
  simp_rw [coherent_probe_eq i t g h j X Y hD]
  exact finite_probe_mean i t g h j X Y hg hh hj

end Metaplectic.G2Seven.Jacobi
