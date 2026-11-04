/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.G2SevenLocal

/-!
# Phase-free complete sevenfold G2 energy

All six grade-zero coordinates interfere constructively. Each other
grade contains a single Gauss phase. The complete finite and infinite
coherent energies are independent of all three unit Gauss inputs.
This is an arithmetic coordinate theorem, not a global QRH estimate.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace Metaplectic.G2Seven

private theorem character_orthogonality (r s : ZMod 7) :
    Finset.univ.sum (fun a : ZMod 7 =>
      (starRingEnd Complex) (ZMod.stdAddChar (a * r)) * ZMod.stdAddChar (a * s)) =
      if r = s then 7 else 0 := by
  have ht (a : ZMod 7) :
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
      (ZMod.isPrimitive_stdAddChar 7 (sub_ne_zero.mpr (Ne.symm h)))

noncomputable def finiteSignal (v : ZMod 7 -> Complex) (a : ZMod 7) : Complex :=
  Finset.univ.sum (fun r : ZMod 7 => ZMod.stdAddChar (a * r) * v r)

theorem finiteSignal_parseval (v : ZMod 7 -> Complex) :
    Finset.univ.sum (fun a : ZMod 7 => Complex.normSq (finiteSignal v a)) =
      7 * Finset.univ.sum (fun r : ZMod 7 => Complex.normSq (v r)) := by
  have hp (a : ZMod 7) :
      (starRingEnd Complex) (finiteSignal v a) * finiteSignal v a =
        Finset.univ.sum (fun r : ZMod 7 => Finset.univ.sum (fun s : ZMod 7 =>
          ((starRingEnd Complex) (ZMod.stdAddChar (a * r)) *
            ZMod.stdAddChar (a * s)) * ((starRingEnd Complex) (v r) * v s))) := by
    simp only [finiteSignal, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    ring
  have hc : Finset.univ.sum (fun a : ZMod 7 =>
      (starRingEnd Complex) (finiteSignal v a) * finiteSignal v a) =
      7 * Finset.univ.sum (fun r : ZMod 7 => (starRingEnd Complex) (v r) * v r) := by
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



def pairCoefficient {R : Type*} [Field R] (t g h j : R) (r : ZMod 7) : R :=
  match r.val with
  | 0 => 1 + 3 * t ^ 2 + 2 * t ^ 4
  | 1 => t * g
  | 2 => t ^ 3 * h
  | 3 => t * j
  | 4 => t ^ 3 / j
  | 5 => t ^ 3 / h
  | 6 => t ^ 3 / g
  | _ => 0

theorem pairCoefficient_eq_sum {R : Type*} [Field R]
    (t g h j : R) (hg : Not (g = 0)) (hh : Not (h = 0))
    (hj : Not (j = 0)) (r : ZMod 7) :
    pairCoefficient t g h j r =
      Finset.univ.sum (fun s : State =>
        if ((twistClass s).val : ZMod 7) = r then signedBase t g h j s else 0) := by
  have ht (s : State) :
      (((twistClass s).val : ZMod 7) = r) <-> (twistClass s).val = r.val := by
    constructor
    case mp =>
      intro hsr
      have hv := congrArg (fun z : ZMod 7 => z.val) hsr
      simpa only [ZMod.val_natCast_of_lt (twistClass s).isLt] using hv
    case mpr =>
      intro hsr
      rw [hsr]
      exact ZMod.natCast_zmod_val r
  simp_rw [ht]
  have hr : Exists (fun p : Fin 7 => (p.val : ZMod 7) = r) :=
    Exists.intro (Fin.mk r.val (ZMod.val_lt r)) (ZMod.natCast_zmod_val r)
  cases hr with
  | intro p hp =>
    rw [<- hp]
    unfold pairCoefficient
    simp only [ZMod.val_natCast_of_lt p.isLt]
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, signedBase,
      supported, degree, row, phaseValue, phase, twistClass, zpow_neg_one]
    fin_cases p <;> norm_num [pairCoefficient, ZMod.val_natCast] <;>
      field_simp [hg, hh, hj] <;> ring

theorem finiteSignal_pairCoefficient (t g h j : Complex)
    (hg : Not (g = 0)) (hh : Not (h = 0)) (hj : Not (j = 0)) (a : ZMod 7) :
    finiteSignal (pairCoefficient t g h j) a =
      Finset.univ.sum (fun s : State =>
        ZMod.stdAddChar (a * ((twistClass s).val : ZMod 7)) *
          signedBase t g h j s) := by
  simp only [finiteSignal, pairCoefficient_eq_sum t g h j hg hh hj,
    Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  simp

def energy (t : Real) : Real := 1 + 8 * t ^ 2 + 13 * t ^ 4 + 16 * t ^ 6 + 4 * t ^ 8

/-- Every same-grade cross term is retained; none depends on a Gauss phase. -/
theorem pairCoefficient_energy (t : Real) (g h j : Complex)
    (hg : Complex.normSq g = 1) (hh : Complex.normSq h = 1)
    (hj : Complex.normSq j = 1) :
    Finset.univ.sum (fun r : ZMod 7 =>
      Complex.normSq (pairCoefficient (t : Complex) g h j r)) = energy t := by
  have hi : forall r : Fin 7,
      (ZMod.finEquiv 7) r = (r.val : ZMod 7) := by
    intro r
    fin_cases r <;> decide
  have hs := Fintype.sum_equiv (ZMod.finEquiv 7).toEquiv
    (fun r : Fin 7 => Complex.normSq
      (pairCoefficient (t : Complex) g h j (r.val : ZMod 7)))
    (fun r : ZMod 7 => Complex.normSq (pairCoefficient (t : Complex) g h j r))
    (fun r => by
      change Complex.normSq (pairCoefficient (t : Complex) g h j (r.val : ZMod 7)) =
        Complex.normSq (pairCoefficient (t : Complex) g h j ((ZMod.finEquiv 7) r))
      rw [hi r])
  rw [<- hs]
  have hv (r : Fin 7) : (r.val : ZMod 7).val = r.val := ZMod.val_natCast_of_lt r.isLt
  have hc : 1 + 3 * (t : Complex) ^ 2 + 2 * (t : Complex) ^ 4 =
      ((1 + 3 * t ^ 2 + 2 * t ^ 4 : Real) : Complex) := by
    push_cast
    ring
  have hz : Complex.normSq (1 + 3 * (t : Complex) ^ 2 + 2 * (t : Complex) ^ 4) =
      (1 + 3 * t ^ 2 + 2 * t ^ 4) ^ 2 := by
    rw [hc, Complex.normSq_ofReal]
    ring
  have hz' : Complex.normSq (1 + (t : Complex) ^ 2 * 3 + (t : Complex) ^ 4 * 2) =
      (1 + 3 * t ^ 2 + 2 * t ^ 4) ^ 2 := by
    convert hz using 1 <;> congr 1 <;> ring
  simp only [pairCoefficient, hv]
  norm_num [Fin.sum_univ_succ, hz, hz', Complex.normSq_mul,
    Complex.normSq_div, map_pow, Complex.normSq_ofReal, hg, hh, hj, energy]
  ring

theorem additive_twist_energy (t : Real) (g h j : Complex)
    (hg : Complex.normSq g = 1) (hh : Complex.normSq h = 1)
    (hj : Complex.normSq j = 1) :
    Finset.univ.sum (fun a : ZMod 7 =>
      Complex.normSq (finiteSignal (pairCoefficient (t : Complex) g h j) a)) =
      7 * energy t := by
  rw [finiteSignal_parseval, pairCoefficient_energy t g h j hg hh hj]

noncomputable def coherentSignal (t : Real) (g h j : Complex) (a : ZMod 7) : Complex :=
  finiteSignal (pairCoefficient (t : Complex) g h j) a / (1 - (t : Complex) ^ 2) ^ 2

/-- Every infinite-period overlap is retained in the exact phase-free energy. -/
theorem coherentSignal_energy (t : Real) (g h j : Complex)
    (hg : Complex.normSq g = 1) (hh : Complex.normSq h = 1)
    (hj : Complex.normSq j = 1) :
    Finset.univ.sum (fun a : ZMod 7 => Complex.normSq (coherentSignal t g h j a)) =
      7 * energy t / (1 - t ^ 2) ^ 4 := by
  have hd : (1 - (t : Complex) ^ 2) ^ 2 =
      (((1 - t ^ 2) ^ 2 : Real) : Complex) := by
    push_cast
    ring
  simp only [coherentSignal, hd, Complex.normSq_div, Complex.normSq_ofReal]
  rw [<- Finset.sum_div, additive_twist_energy t g h j hg hh hj]
  ring

/-- The complete coherent period expansion converges for 0<=t<1. -/
theorem coherentSignal_hasSum (t : Real) (g h j : Complex) (a : ZMod 7)
    (ht0 : 0 <= t) (ht1 : t < 1) :
    HasSum (fun p : Period =>
      ((t : Complex) ^ 2) ^ p.1 * ((t : Complex) ^ 2) ^ p.2 *
        finiteSignal (pairCoefficient (t : Complex) g h j) a)
      (coherentSignal t g h j a) := by
  have ht2 : t ^ 2 < 1 := by nlinarith
  have hn : norm ((t : Complex) ^ 2) < 1 := by
    simpa [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0] using ht2
  have hgeom := hasSum_geometric_of_norm_lt_one hn
  have ha : Summable (fun n : Nat => norm (((t : Complex) ^ 2) ^ n)) := by
    simpa only [norm_pow] using
      (hasSum_geometric_of_lt_one (norm_nonneg ((t : Complex) ^ 2)) hn).summable
  have hp := hgeom.mul hgeom (ha.mul_norm ha).of_norm
  have hm := hp.mul_right (finiteSignal (pairCoefficient (t : Complex) g h j) a)
  have hnz : Not (1 - (t : Complex) ^ 2 = 0) := by
    intro hzero
    have heq : (t : Complex) ^ 2 = 1 := (sub_eq_zero.mp hzero).symm
    rw [heq] at hn
    norm_num at hn
  convert hm using 1
  unfold coherentSignal
  field_simp [hnz]

end Metaplectic.G2Seven
