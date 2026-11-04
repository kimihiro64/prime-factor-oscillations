/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.G2TwelveLocal

/-!
# Complete additive-twist energy of the twelvefold G2 coordinate model

All twelve coordinates are grouped into their six quadratic classes.
Character orthogonality retains every same-class cross term. The final
Gauss-product algebra keeps its duplication and triplication hypotheses
explicit; it does not formalize Hasse-Davenport or the representation-
theoretic identification. No global analytic estimate is asserted.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace Metaplectic.G2Twelve

private theorem character_orthogonality (r s : ZMod 12) :
    Finset.univ.sum (fun a : ZMod 12 =>
      (starRingEnd Complex) (ZMod.stdAddChar (a * r)) * ZMod.stdAddChar (a * s)) =
      if r = s then 12 else 0 := by
  have ht (a : ZMod 12) :
      (starRingEnd Complex) (ZMod.stdAddChar (a * r)) * ZMod.stdAddChar (a * s) =
        ZMod.stdAddChar ((s - r) * a) := by
    rw [<- AddChar.map_neg_eq_conj, <- AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [ht]
  by_cases h : r = s
  case pos => simp [h]
  case neg =>
    rw [if_neg h]
    exact AddChar.sum_eq_zero_of_ne_one
      (ZMod.isPrimitive_stdAddChar 12 (sub_ne_zero.mpr (Ne.symm h)))

noncomputable def finiteSignal (v : ZMod 12 -> Complex) (a : ZMod 12) : Complex :=
  Finset.univ.sum (fun r : ZMod 12 => ZMod.stdAddChar (a * r) * v r)

theorem finiteSignal_parseval (v : ZMod 12 -> Complex) :
    Finset.univ.sum (fun a : ZMod 12 => Complex.normSq (finiteSignal v a)) =
      12 * Finset.univ.sum (fun r : ZMod 12 => Complex.normSq (v r)) := by
  have hp (a : ZMod 12) :
      (starRingEnd Complex) (finiteSignal v a) * finiteSignal v a =
        Finset.univ.sum (fun r : ZMod 12 => Finset.univ.sum (fun s : ZMod 12 =>
          ((starRingEnd Complex) (ZMod.stdAddChar (a * r)) *
            ZMod.stdAddChar (a * s)) * ((starRingEnd Complex) (v r) * v s))) := by
    simp only [finiteSignal, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    ring
  have hc : Finset.univ.sum (fun a : ZMod 12 =>
      (starRingEnd Complex) (finiteSignal v a) * finiteSignal v a) =
      12 * Finset.univ.sum (fun r : ZMod 12 => (starRingEnd Complex) (v r) * v r) := by
    simp_rw [hp]
    rw [Finset.sum_comm]
    conv_lhs =>
      arg 2
      ext r
      rw [Finset.sum_comm]
    simp_rw [<- Finset.sum_mul, character_orthogonality]
    simp [ite_mul, Finset.mul_sum]
  have hcast := congrArg Complex.re hc
  norm_num [<- Complex.normSq_eq_conj_mul_self, <- Complex.ofReal_sum,
    Complex.mul_re] at hcast
  exact hcast

def pairCoefficient {R : Type*} [Field R] (t g h j k e : R) (r : ZMod 12) : R :=
  let A := g * k * e
  let B := k * e * j / h
  let C := h * j / (g * e)
  match r.val with
  | 0 => 1 + t ^ 3 * A
  | 1 => t * g * (1 + t ^ 2 * B)
  | 3 => t * h * (1 + t ^ 2 * B)
  | 4 => t * j * (1 + t ^ 3 * A)
  | 7 => t ^ 2 * g * e * (1 + C)
  | 9 => t ^ 2 * A / h * (1 + C)
  | _ => 0

/-- Each coherent channel is exactly the sum of all coordinates in its class. -/
theorem pairCoefficient_eq_sum {R : Type*} [Field R]
    (t g h j k e : R) (hg : Not (g = 0)) (hh : Not (h = 0))
    (he : Not (e = 0)) (r : ZMod 12) :
    pairCoefficient t g h j k e r =
      Finset.univ.sum (fun s : State =>
        if ((twistClass s).val : ZMod 12) = r then signedBase t g h j k e s else 0) := by
  have ht (s : State) :
      (((twistClass s).val : ZMod 12) = r) <-> (twistClass s).val = r.val := by
    constructor
    case mp =>
      intro hsr
      have hv := congrArg (fun z : ZMod 12 => z.val) hsr
      simpa only [ZMod.val_natCast_of_lt (twistClass s).isLt] using hv
    case mpr =>
      intro hsr
      rw [hsr]
      exact ZMod.natCast_zmod_val r
  simp_rw [ht]
  have hr : Exists (fun p : Fin 12 => (p.val : ZMod 12) = r) :=
    Exists.intro (Fin.mk r.val (ZMod.val_lt r)) (ZMod.natCast_zmod_val r)
  cases hr with
  | intro p hp =>
    rw [<- hp]
    unfold pairCoefficient
    simp only [ZMod.val_natCast_of_lt p.isLt]
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, signedBase,
      supported, degree, row, phaseValue, phase, twistClass, zpow_neg_one]
    fin_cases p <;> norm_num [pairCoefficient, ZMod.val_natCast] <;>
      field_simp [hg, hh, he] <;> ring

/-- The signal is the full coordinate sum, with no lost same-class cross term. -/
theorem finiteSignal_pairCoefficient (t g h j k e : Complex)
    (hg : Not (g = 0)) (hh : Not (h = 0)) (he : Not (e = 0)) (a : ZMod 12) :
    finiteSignal (pairCoefficient t g h j k e) a =
      Finset.univ.sum (fun s : State =>
        ZMod.stdAddChar (a * ((twistClass s).val : ZMod 12)) *
          signedBase t g h j k e s) := by
  simp only [finiteSignal, pairCoefficient_eq_sum t g h j k e hg hh he,
    Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  simp

theorem pairCoefficient_energy (t : Real) (g h j k e : Complex)
    (hg : Complex.normSq g = 1) (hh : Complex.normSq h = 1)
    (hj : Complex.normSq j = 1) (hk : Complex.normSq k = 1)
    (he : Complex.normSq e = 1) :
    Finset.univ.sum (fun r : ZMod 12 =>
      Complex.normSq (pairCoefficient (t : Complex) g h j k e r)) =
      (1 + t ^ 2) * Complex.normSq (1 + (t : Complex) ^ 3 * (g * k * e)) +
      2 * t ^ 2 * Complex.normSq (1 + (t : Complex) ^ 2 * (k * e * j / h)) +
      2 * t ^ 4 * Complex.normSq (1 + h * j / (g * e)) := by
  have hi : forall r : Fin 12,
      (ZMod.finEquiv 12) r = (r.val : ZMod 12) := by
    intro r
    fin_cases r <;> decide
  have hs := Fintype.sum_equiv (ZMod.finEquiv 12).toEquiv
    (fun r : Fin 12 => Complex.normSq
      (pairCoefficient (t : Complex) g h j k e (r.val : ZMod 12)))
    (fun r : ZMod 12 => Complex.normSq (pairCoefficient (t : Complex) g h j k e r))
    (fun r => by
      change Complex.normSq (pairCoefficient (t : Complex) g h j k e (r.val : ZMod 12)) =
        Complex.normSq (pairCoefficient (t : Complex) g h j k e ((ZMod.finEquiv 12) r))
      rw [hi r])
  rw [<- hs]
  have hv (r : Fin 12) : (r.val : ZMod 12).val = r.val := ZMod.val_natCast_of_lt r.isLt
  simp only [pairCoefficient, hv]
  norm_num [Fin.sum_univ_succ, Complex.normSq_mul,
    Complex.normSq_div, map_pow, Complex.normSq_ofReal, hg, hh, hj, hk, he]
  ring

/-- Exact local averaging, retaining all six coherent pairs. -/
theorem additive_twist_energy (t : Real) (g h j k e : Complex)
    (hg : Complex.normSq g = 1) (hh : Complex.normSq h = 1)
    (hj : Complex.normSq j = 1) (hk : Complex.normSq k = 1)
    (he : Complex.normSq e = 1) :
    Finset.univ.sum (fun a : ZMod 12 =>
      Complex.normSq (finiteSignal (pairCoefficient (t : Complex) g h j k e) a)) =
      12 * ((1 + t ^ 2) * Complex.normSq (1 + (t : Complex) ^ 3 * (g * k * e)) +
      2 * t ^ 2 * Complex.normSq (1 + (t : Complex) ^ 2 * (k * e * j / h)) +
      2 * t ^ 4 * Complex.normSq (1 + h * j / (g * e))) := by
  rw [finiteSignal_parseval, pairCoefficient_energy t g h j k e hg hh hj hk he]

private theorem normSq_one_add_scaled (t : Real) (z : Complex)
    (hz : Complex.normSq z = 1) :
    Complex.normSq (1 + (t : Complex) * z) = 1 + t ^ 2 + 2 * t * z.re := by
  rw [Complex.normSq_add]
  simp [Complex.normSq_mul, Complex.normSq_ofReal, hz, Complex.mul_re]
  ring

/-- All surviving interference starts at order t^3, with its exact signs. -/
theorem pairCoefficient_energy_expansion (t : Real) (g h j k e : Complex)
    (hg : Complex.normSq g = 1) (hh : Complex.normSq h = 1)
    (hj : Complex.normSq j = 1) (hk : Complex.normSq k = 1)
    (he : Complex.normSq e = 1) :
    Finset.univ.sum (fun r : ZMod 12 =>
      Complex.normSq (pairCoefficient (t : Complex) g h j k e r)) =
      1 + 3 * t ^ 2 + 4 * t ^ 4 + 3 * t ^ 6 + t ^ 8 +
      2 * t ^ 3 * (1 + t ^ 2) * (g * k * e).re +
      4 * t ^ 4 * ((k * e * j / h).re + (h * j / (g * e)).re) := by
  have hA : Complex.normSq (g * k * e) = 1 := by
    simp [Complex.normSq_mul, hg, hk, he]
  have hB : Complex.normSq (k * e * j / h) = 1 := by
    simp [Complex.normSq_mul, hk, he, hj, hh]
  have hC : Complex.normSq (h * j / (g * e)) = 1 := by
    simp [Complex.normSq_mul, hh, hj, hg, he]
  rw [pairCoefficient_energy t g h j k e hg hh hj hk he]
  have h3 := normSq_one_add_scaled (t ^ 3) (g * k * e) hA
  have h2 := normSq_one_add_scaled (t ^ 2) (k * e * j / h) hB
  have h0 := normSq_one_add_scaled 1 (h * j / (g * e)) hC
  push_cast at h3 h2
  norm_num only [Complex.ofReal_one, one_mul, one_pow] at h0
  rw [h3, h2, h0]
  ring

/-- The duplication relation forces the last two coherence phases to be reciprocal.
The hypothesis is explicit; Hasse-Davenport is not reproved by this algebra lemma. -/
theorem coherence_product {R : Type*} [Field R] (g h j k e : R)
    (hg : Not (g = 0)) (hh : Not (h = 0)) (he : Not (e = 0))
    (hdup : g = k * j ^ 2) :
    (k * e * j / h) * (h * j / (g * e)) = 1 := by
  calc
    (k * e * j / h) * (h * j / (g * e)) = k * j ^ 2 / g := by
      field_simp [hg, hh, he]
    _ = 1 := by rw [<- hdup]; exact div_self hg

/-- Duplication and triplication leave a fourth root of unity, not a free phase. -/
theorem coherence_square {R : Type*} [Field R] (g h j k e u : R)
    (hg : Not (g = 0)) (he : Not (e = 0))
    (hdup : g = k * j ^ 2) (htrip : g * k = u * h ^ 2)
    (he2 : e ^ 2 = 1) (hu2 : u ^ 2 = 1) :
    (h * j / (g * e)) ^ 2 = u := by
  have hgg : g ^ 2 = u * h ^ 2 * j ^ 2 := by
    calc
      g ^ 2 = g * k * j ^ 2 := by rw [hdup]; ring
      _ = u * h ^ 2 * j ^ 2 := by rw [htrip]
  have hc : (h * j) ^ 2 = u * (g * e) ^ 2 := by
    calc
      (h * j) ^ 2 = u ^ 2 * (h ^ 2 * j ^ 2) := by rw [hu2]; ring
      _ = u * (u * h ^ 2 * j ^ 2) * e ^ 2 := by rw [he2]; ring
      _ = u * (g * e) ^ 2 := by rw [<- hgg]; ring
  rw [div_pow]
  exact (div_eq_iff (pow_ne_zero 2 (mul_ne_zero hg he))).mpr hc

theorem coherence_fourth {R : Type*} [Field R] (g h j k e u : R)
    (hg : Not (g = 0)) (he : Not (e = 0))
    (hdup : g = k * j ^ 2) (htrip : g * k = u * h ^ 2)
    (he2 : e ^ 2 = 1) (hu2 : u ^ 2 = 1) :
    (h * j / (g * e)) ^ 4 = 1 := by
  calc
    (h * j / (g * e)) ^ 4 = ((h * j / (g * e)) ^ 2) ^ 2 := by ring
    _ = u ^ 2 := by rw [coherence_square g h j k e u hg he hdup htrip he2 hu2]
    _ = 1 := hu2

private theorem reciprocal_re (B C : Complex) (hc : Complex.normSq C = 1)
    (hbc : B * C = 1) : B.re = C.re := by
  have hcc : C * (starRingEnd Complex) C = 1 := by
    rw [mul_comm, <- Complex.normSq_eq_conj_mul_self, hc]
    norm_num
  have hb : B = (starRingEnd Complex) C := by
    calc
      B = B * (C * (starRingEnd Complex) C) := by rw [hcc]; ring
      _ = (B * C) * (starRingEnd Complex) C := by ring
      _ = (starRingEnd Complex) C := by rw [hbc]; ring
  rw [hb]
  simp

/-- The source duplication relation couples the surviving order-t^4 cross terms. -/
theorem pairCoefficient_reciprocal_energy (t : Real) (g h j k e : Complex)
    (hg : Complex.normSq g = 1) (hh : Complex.normSq h = 1)
    (hj : Complex.normSq j = 1) (hk : Complex.normSq k = 1)
    (he : Complex.normSq e = 1) (hdup : g = k * j ^ 2) :
    Finset.univ.sum (fun r : ZMod 12 =>
      Complex.normSq (pairCoefficient (t : Complex) g h j k e r)) =
      1 + 3 * t ^ 2 + 4 * t ^ 4 + 3 * t ^ 6 + t ^ 8 +
      2 * t ^ 3 * (1 + t ^ 2) * (g * k * e).re +
      8 * t ^ 4 * (h * j / (g * e)).re := by
  have hg0 : Not (g = 0) := by intro hz; rw [hz] at hg; norm_num at hg
  have hh0 : Not (h = 0) := by intro hz; rw [hz] at hh; norm_num at hh
  have he0 : Not (e = 0) := by intro hz; rw [hz] at he; norm_num at he
  have hc : Complex.normSq (h * j / (g * e)) = 1 := by
    simp [Complex.normSq_mul, hh, hj, hg, he]
  have hr := reciprocal_re _ _ hc (coherence_product g h j k e hg0 hh0 he0 hdup)
  rw [pairCoefficient_energy_expansion t g h j k e hg hh hj hk he, hr]
  ring

end Metaplectic.G2Twelve
