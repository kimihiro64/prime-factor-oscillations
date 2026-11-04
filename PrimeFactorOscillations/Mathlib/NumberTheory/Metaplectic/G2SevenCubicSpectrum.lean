/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.G2SevenReadout

/-!
# Complete cubic spectrum of the sevenfold coordinate model

All principal and repeated-frequency terms remain. The eight nonprincipal
resonance types split into two formal scaling orbits of sizes two and six.
The finite multiset and Hodge data are arithmetic classifications, not a
global Hecke-character or automorphic identification.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace Metaplectic.G2Seven.Spectrum

open Cubic

def amplitudes (u a b c d e f : Complex) (r : Fin 7) : Complex :=
  match r.val with
  | 0 => u
  | 1 => a
  | 2 => b
  | 3 => c
  | 4 => d
  | 5 => e
  | _ => f

noncomputable def signal (v : Fin 7 -> Complex) (a : ZMod 7) : Complex :=
  Finset.univ.sum (fun r : Fin 7 =>
    ZMod.stdAddChar (a * (r.val : ZMod 7)) * v r)

private theorem frequency_sum (r : ZMod 7) :
    Finset.univ.sum (fun a : ZMod 7 => ZMod.stdAddChar (r * a)) =
      if r = 0 then 7 else 0 := by
  by_cases hz : r = 0
  . simp [hz]
  . rw [if_neg hz]
    exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar 7 hz)

theorem cubic_sum (v : Fin 7 -> Complex) :
    Finset.univ.sum (fun a : ZMod 7 => (signal v a) ^ 3) =
      7 * Finset.univ.sum (fun r : Fin 7 => Finset.univ.sum (fun s : Fin 7 =>
        Finset.univ.sum (fun k : Fin 7 =>
          if (r.val : ZMod 7) + (s.val : ZMod 7) + (k.val : ZMod 7) = 0
          then v r * v s * v k else 0))) := by
  have hc (a : ZMod 7) (r s k : Fin 7) :
      ZMod.stdAddChar (a * (r.val : ZMod 7)) *
        ZMod.stdAddChar (a * (s.val : ZMod 7)) *
        ZMod.stdAddChar (a * (k.val : ZMod 7)) =
      ZMod.stdAddChar (((r.val : ZMod 7) + (s.val : ZMod 7) +
        (k.val : ZMod 7)) * a) := by
    rw [<- AddChar.map_add_eq_mul, <- AddChar.map_add_eq_mul]
    congr 1
    ring
  have hp (a : ZMod 7) :
      (signal v a) ^ 3 =
        Finset.univ.sum (fun r : Fin 7 => Finset.univ.sum (fun s : Fin 7 =>
          Finset.univ.sum (fun k : Fin 7 =>
            ZMod.stdAddChar (((r.val : ZMod 7) + (s.val : ZMod 7) +
              (k.val : ZMod 7)) * a) * (v r * v s * v k)))) := by
    simp only [signal, pow_succ, pow_zero, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro k _
    calc
      _ = (ZMod.stdAddChar (a * (r.val : ZMod 7)) *
          ZMod.stdAddChar (a * (s.val : ZMod 7)) *
          ZMod.stdAddChar (a * (k.val : ZMod 7))) * (v r * v s * v k) := by ring
      _ = _ := by rw [hc]
  simp_rw [hp]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext r
    rw [Finset.sum_comm]
    arg 2
    ext s
    rw [Finset.sum_comm]
  simp_rw [<- Finset.sum_mul, frequency_sum]
  simp [ite_mul, Finset.mul_sum]

theorem frequency_resonance : forall r s k : Fin 7,
    ((r.val : ZMod 7) + (s.val : ZMod 7) + (k.val : ZMod 7) = 0) <->
      (r.val + s.val + k.val) % 7 = 0 := by decide

/-- All 49 resonant ordered terms, including 19 with principal factors. -/
theorem complete_cubic_mean (u a b c d e f : Complex) :
    mean (fun x => (signal (amplitudes u a b c d e f) x) ^ 3) =
      u ^ 3 + 6 * u * (a * f + b * e + c * d) +
      3 * (a ^ 2 * e + a * c ^ 2 + b ^ 2 * c + b * f ^ 2 +
        d ^ 2 * f + d * e ^ 2) +
      6 * (a * b * d + c * e * f) := by
  unfold mean
  rw [cubic_sum]
  simp_rw [frequency_resonance]
  norm_num [Fin.sum_univ_succ, amplitudes]
  ring

/-- The eight sorted nonzero zero-sum triples. -/
def tripleEntry (i : Fin 8) (j : Fin 3) : Nat :=
  match i.val, j.val with
  | 0, 0 => 1
  | 0, 1 => 1
  | 0, _ => 5
  | 1, 0 => 1
  | 1, 1 => 2
  | 1, _ => 4
  | 2, 0 => 1
  | 2, _ => 3
  | 3, 2 => 3
  | 3, _ => 2
  | 4, 0 => 2
  | 4, _ => 6
  | 5, 0 => 3
  | 5, 1 => 5
  | 5, _ => 6
  | 6, 2 => 6
  | 6, _ => 4
  | _, 0 => 4
  | _, _ => 5

def scaledMultiplicity (i : Fin 8) (u : Fin 6) (r : Fin 7) : Nat :=
  Finset.univ.sum (fun j : Fin 3 =>
    if ((u.val + 1) * tripleEntry i j) % 7 = r.val then 1 else 0)

def stabilizes (i : Fin 8) (u : Fin 6) : Prop :=
  forall r : Fin 7, scaledMultiplicity i u r = scaledMultiplicity i 0 r

instance (i : Fin 8) (u : Fin 6) : Decidable (stabilizes i u) := by
  unfold stabilizes
  infer_instance

/-- Formal scaling stabilizer: order three on 124/356, trivial on the other six. -/
theorem stabilizer_classification : forall (i : Fin 8) (u : Fin 6),
    stabilizes i u <->
      if i.val = 1 \/ i.val = 5
      then u.val = 0 \/ u.val = 1 \/ u.val = 3 else u.val = 0 := by decide

/-- Every triple belongs to exactly the residue sector or the repeated-entry sector. -/
theorem sector_orbits : forall i : Fin 8,
    Exists fun u : Fin 6 => forall r : Fin 7,
      scaledMultiplicity i u r =
        scaledMultiplicity (if i.val = 1 \/ i.val = 5 then 1 else 0) 0 r := by decide

/-- The two formal scaling sectors never intersect. -/
theorem sector_disjoint : forall u v : Fin 6,
    Not (forall r : Fin 7, scaledMultiplicity 1 u r = scaledMultiplicity 0 v r) := by decide

def hodgeIndex (i : Fin 8) (u : Fin 6) : Nat :=
  (Finset.univ.sum (fun j : Fin 3 =>
    ((u.val + 1) * tripleEntry i j) % 7)) / 7 - 1

theorem hodge_conjugation : forall (i : Fin 8) (u : Fin 6),
    hodgeIndex i u + hodgeIndex i u.rev = 1 := by decide

theorem hodge_repeated_representative : forall u : Fin 6,
    hodgeIndex 0 u = if u.val < 3 then 0 else 1 := by decide

theorem hodge_residue_representative : forall u : Fin 6,
    hodgeIndex 1 u = if u.val = 0 \/ u.val = 1 \/ u.val = 3 then 0 else 1 := by decide

/-- The integer index is exactly the fractional-part sum minus one, without rounding loss. -/
theorem hodge_integral : forall (i : Fin 8) (u : Fin 6),
    Finset.univ.sum (fun j : Fin 3 => ((u.val + 1) * tripleEntry i j) % 7) =
      7 * (1 + hodgeIndex i u) := by decide

/-- The signal is the full source-coordinate projection, including every principal coordinate. -/
theorem source_full_carrier (t g h j X Y : Complex)
    (hg : Not (g = 0)) (hh : Not (h = 0)) (hj : Not (j = 0)) (a : ZMod 7) :
    torusProjection (fun _ => true) t g h j X Y a =
      signal (amplitudes (principal t X Y)
        (t * g * X) (t ^ 3 * h * X ^ 4 * Y ^ 4) (t * j * Y)
        (t ^ 3 / j * X ^ 3 * Y ^ 5) (t ^ 3 / h * X ^ 6 * Y ^ 2)
        (t ^ 3 / g * X ^ 2 * Y ^ 6)) a := by
  norm_num [torusProjection, signal, amplitudes, principal,
    Fintype.sum_prod_type, Fin.sum_univ_succ, signedBase,
    supported, degree, row, phaseValue, phase, twistClass, zpow_neg_one]
  field_simp [hg, hh, hj]
  ring

noncomputable def phaseSpectrum (t g h j X Y : Complex) : Complex :=
  3 * t ^ 5 * (g ^ 2 / h) * X ^ 8 * Y ^ 2 +
  6 * t ^ 7 * (g * h / j + j / (g * h)) * X ^ 8 * Y ^ 9 +
  3 * t ^ 3 * (g * j ^ 2) * X * Y ^ 2 +
  3 * t ^ 7 * (h ^ 2 * j) * X ^ 8 * Y ^ 9 +
  3 * t ^ 9 * (h / g ^ 2 + 1 / (g * j ^ 2)) * X ^ 8 * Y ^ 16 +
  3 * t ^ 9 / (j * h ^ 2) * X ^ 15 * Y ^ 9

/-- Exact physical cubic moment: the full principal cross term and both formal Galois sectors. -/
theorem source_cubic_mean (t g h j X Y : Complex)
    (hg : Not (g = 0)) (hh : Not (h = 0)) (hj : Not (j = 0)) :
    mean (fun a => (torusProjection (fun _ => true) t g h j X Y a) ^ 3) =
      (principal t X Y) ^ 3 +
      6 * principal t X Y * (2 * t ^ 4 * X ^ 3 * Y ^ 6 +
        t ^ 6 * X ^ 10 * Y ^ 6) +
      phaseSpectrum t g h j X Y := by
  simp_rw [source_full_carrier t g h j X Y hg hh hj]
  rw [complete_cubic_mean]
  unfold phaseSpectrum
  field_simp [hg, hh, hj]
  ring

/-- Complete sorted classification; it covers every nondegenerate level-seven Jacobi triple. -/
theorem resonant_triples_classified : forall r s k : Fin 7,
    (0 < r.val /\ r.val <= s.val /\ s.val <= k.val /\
      (r.val + s.val + k.val) % 7 = 0) <->
      Exists fun i : Fin 8 => tripleEntry i 0 = r.val /\
        tripleEntry i 1 = s.val /\ tripleEntry i 2 = k.val := by decide

end Metaplectic.G2Seven.Spectrum
