/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.Sp4EightLocal

/-!
# Central compensation for the eightfold Sp4 coordinate model

Every same-grade interference term is retained. The two exceptional
central characters have different coherent period denominators.
The normalized compensating mixture is proved to be the unique mixture
independent of the free Jacobi phase. This is a local arithmetic result,
not a global character estimate or a new zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace Metaplectic.Sp4Eight

private theorem character_orthogonality (r s : ZMod 8) :
    Finset.univ.sum (fun a : ZMod 8 =>
      (starRingEnd Complex) (ZMod.stdAddChar (a * r)) * ZMod.stdAddChar (a * s)) =
      if r = s then 8 else 0 := by
  have ht (a : ZMod 8) :
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
      (ZMod.isPrimitive_stdAddChar 8 (sub_ne_zero.mpr (Ne.symm h)))

noncomputable def finiteSignal (v : ZMod 8 -> Complex) (a : ZMod 8) : Complex :=
  Finset.univ.sum (fun r : ZMod 8 => ZMod.stdAddChar (a * r) * v r)

theorem finiteSignal_parseval (v : ZMod 8 -> Complex) :
    Finset.univ.sum (fun a : ZMod 8 => Complex.normSq (finiteSignal v a)) =
      8 * Finset.univ.sum (fun r : ZMod 8 => Complex.normSq (v r)) := by
  have hp (a : ZMod 8) :
      (starRingEnd Complex) (finiteSignal v a) * finiteSignal v a =
        Finset.univ.sum (fun r : ZMod 8 => Finset.univ.sum (fun s : ZMod 8 =>
          ((starRingEnd Complex) (ZMod.stdAddChar (a * r)) *
            ZMod.stdAddChar (a * s)) * ((starRingEnd Complex) (v r) * v s))) := by
    simp only [finiteSignal, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    ring
  have hc : Finset.univ.sum (fun a : ZMod 8 =>
      (starRingEnd Complex) (finiteSignal v a) * finiteSignal v a) =
      8 * Finset.univ.sum (fun r : ZMod 8 => (starRingEnd Complex) (v r) * v r) := by
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


def pairCoefficient {R : Type*} [Field R] (t g h j e sigma : R) (r : ZMod 8) : R :=
  let A := g * j * e
  let B := h * j * e / g
  match r.val with
  | 0 => 1 + sigma * t ^ 2 * A
  | 1 => t * g * (1 + t ^ 2 * B)
  | 2 => t * h * (1 + sigma * t ^ 2 * A)
  | 5 => t ^ 2 * g * e * (1 + B)
  | _ => 0

theorem pairCoefficient_eq_sum {R : Type*} [Field R]
    (t g h j e sigma : R) (hg : Not (g = 0)) (he : Not (e = 0))
    (he2 : e ^ 2 = 1) (r : ZMod 8) :
    pairCoefficient t g h j e sigma r =
      Finset.univ.sum (fun s : State =>
        if ((twistClass s).val : ZMod 8) = r then signedBase t g h j e sigma s else 0) := by
  have ht (s : State) :
      (((twistClass s).val : ZMod 8) = r) <-> (twistClass s).val = r.val := by
    constructor
    case mp =>
      intro hsr
      have hv := congrArg (fun z : ZMod 8 => z.val) hsr
      simpa only [ZMod.val_natCast_of_lt (twistClass s).isLt] using hv
    case mpr =>
      intro hsr
      rw [hsr]
      exact ZMod.natCast_zmod_val r
  simp_rw [ht]
  have hr : Exists (fun p : Fin 8 => (p.val : ZMod 8) = r) :=
    Exists.intro (Fin.mk r.val (ZMod.val_lt r)) (ZMod.natCast_zmod_val r)
  cases hr with
  | intro p hp =>
    rw [<- hp]
    unfold pairCoefficient
    simp only [ZMod.val_natCast_of_lt p.isLt]
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, signedBase,
      supported, degree, row, phaseValue, phase, twistClass]
    fin_cases p <;> norm_num [pairCoefficient, ZMod.val_natCast] <;>
      field_simp [hg, he] <;> ring_nf <;> simp only [he2] <;> ring

theorem finiteSignal_pairCoefficient (t g h j e sigma : Complex)
    (hg : Not (g = 0)) (he : Not (e = 0)) (he2 : e ^ 2 = 1) (a : ZMod 8) :
    finiteSignal (pairCoefficient t g h j e sigma) a =
      Finset.univ.sum (fun s : State =>
        ZMod.stdAddChar (a * ((twistClass s).val : ZMod 8)) *
          signedBase t g h j e sigma s) := by
  simp only [finiteSignal, pairCoefficient_eq_sum t g h j e sigma hg he he2,
    Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  simp

/-- The diagonal is exactly 1 + 2 t^2 + 3 t^4 + 2 t^6. -/
theorem pairCoefficient_energy (t : Real) (g h j e sigma : Complex)
    (hg : Complex.normSq g = 1) (hh : Complex.normSq h = 1)
    (he : Complex.normSq e = 1) :
    Finset.univ.sum (fun r : ZMod 8 =>
      Complex.normSq (pairCoefficient (t : Complex) g h j e sigma r)) =
      (1 + t ^ 2) * Complex.normSq (1 + sigma * (t : Complex) ^ 2 * (g * j * e)) +
      t ^ 2 * Complex.normSq (1 + (t : Complex) ^ 2 * (h * j * e / g)) +
      t ^ 4 * Complex.normSq (1 + h * j * e / g) := by
  have hi : forall r : Fin 8,
      (ZMod.finEquiv 8) r = (r.val : ZMod 8) := by
    intro r
    fin_cases r <;> decide
  have hs := Fintype.sum_equiv (ZMod.finEquiv 8).toEquiv
    (fun r : Fin 8 => Complex.normSq
      (pairCoefficient (t : Complex) g h j e sigma (r.val : ZMod 8)))
    (fun r : ZMod 8 => Complex.normSq (pairCoefficient (t : Complex) g h j e sigma r))
    (fun r => by
      change Complex.normSq (pairCoefficient (t : Complex) g h j e sigma (r.val : ZMod 8)) =
        Complex.normSq (pairCoefficient (t : Complex) g h j e sigma ((ZMod.finEquiv 8) r))
      rw [hi r])
  rw [<- hs]
  have hv (r : Fin 8) : (r.val : ZMod 8).val = r.val := ZMod.val_natCast_of_lt r.isLt
  simp only [pairCoefficient, hv]
  norm_num [Fin.sum_univ_succ, Complex.normSq_mul,
    Complex.normSq_div, map_pow, Complex.normSq_ofReal, hg, hh, he]
  ring

private theorem normSq_one_add_scaled (t : Real) (z : Complex)
    (hz : Complex.normSq z = 1) :
    Complex.normSq (1 + (t : Complex) * z) = 1 + t ^ 2 + 2 * t * z.re := by
  rw [Complex.normSq_add]
  simp [Complex.normSq_mul, Complex.normSq_ofReal, hz, Complex.mul_re]
  ring

def diagonal (t : Real) : Real := 1 + 2 * t ^ 2 + 3 * t ^ 4 + 2 * t ^ 6

def rectangleEnergy (t sigma a b : Real) : Real :=
  diagonal t + 2 * sigma * t ^ 2 * (1 + t ^ 2) * a + 4 * t ^ 4 * b

theorem pairCoefficient_energy_expansion (t sigma : Real) (g h j e : Complex)
    (hg : Complex.normSq g = 1) (hh : Complex.normSq h = 1)
    (hj : Complex.normSq j = 1) (he : Complex.normSq e = 1)
    (hsigma : sigma ^ 2 = 1) :
    Finset.univ.sum (fun r : ZMod 8 =>
      Complex.normSq (pairCoefficient (t : Complex) g h j e (sigma : Complex) r)) =
      rectangleEnergy t sigma (g * j * e).re (h * j * e / g).re := by
  have hA : Complex.normSq (g * j * e) = 1 := by
    simp [Complex.normSq_mul, hg, hj, he]
  have hB : Complex.normSq (h * j * e / g) = 1 := by
    simp [Complex.normSq_mul, hh, hj, he, hg]
  rw [pairCoefficient_energy t g h j e (sigma : Complex) hg hh he]
  have h2A := normSq_one_add_scaled (sigma * t ^ 2) (g * j * e) hA
  have h2B := normSq_one_add_scaled (t ^ 2) (h * j * e / g) hB
  have h0 := normSq_one_add_scaled 1 (h * j * e / g) hB
  push_cast at h2A h2B
  norm_num only [Complex.ofReal_one, one_mul, one_pow] at h0
  rw [h2A, h2B, h0]
  simp only [rectangleEnergy, diagonal, mul_pow, hsigma, one_mul]
  ring

theorem additive_twist_energy (t sigma : Real) (g h j e : Complex)
    (hg : Complex.normSq g = 1) (hh : Complex.normSq h = 1)
    (hj : Complex.normSq j = 1) (he : Complex.normSq e = 1)
    (hsigma : sigma ^ 2 = 1) :
    Finset.univ.sum (fun a : ZMod 8 =>
      Complex.normSq (finiteSignal (pairCoefficient (t : Complex) g h j e (sigma : Complex)) a)) =
      8 * rectangleEnergy t sigma (g * j * e).re (h * j * e / g).re := by
  rw [finiteSignal_parseval, pairCoefficient_energy_expansion t sigma g h j e hg hh hj he hsigma]

/-- Both period directions are retained, including the sign in the first one. -/
noncomputable def coherentEnergy (t sigma a b : Real) : Real :=
  rectangleEnergy t sigma a b / ((1 - sigma * t) ^ 2 * (1 - t ^ 2) ^ 2)

noncomputable def mixture (t w a b : Real) : Real :=
  w * coherentEnergy t 1 a b + (1 - w) * coherentEnergy t (-1) a b

noncomputable def compensatingWeight (t : Real) : Real := (1 - t) ^ 2 / (2 * (1 + t ^ 2))

private theorem period_nonzero (t : Real) (ht0 : 0 <= t) (ht1 : t < 1) :
    Not (1 - t = 0) /\ Not (1 + t = 0) /\ Not (1 - t ^ 2 = 0) /\
      Not (1 + t ^ 2 = 0) := by
  constructor
  case left => nlinarith
  case right =>
    constructor
    case left => nlinarith
    case right =>
      constructor <;> nlinarith [sq_nonneg t]

/-- Equal weighting of the complete expressions retains a Jacobi-phase term. -/
theorem equal_coherent_trace (t a b : Real) (ht0 : 0 <= t) (ht1 : t < 1) :
    mixture t (1 / 2) a b =
      ((1 + t ^ 2) * (diagonal t + 4 * t ^ 4 * b) +
        4 * t ^ 3 * (1 + t ^ 2) * a) / (1 - t ^ 2) ^ 4 := by
  have h := period_nonzero t ht0 ht1
  unfold mixture coherentEnergy rectangleEnergy
  field_simp [h.1, h.2.1, h.2.2.1]
  ring

/-- The unique normalized compensation cancels the free CM phase exactly. -/
theorem compensated_coherent_trace (t a b : Real) (ht0 : 0 <= t) (ht1 : t < 1) :
    mixture t (compensatingWeight t) a b =
      (diagonal t + 4 * t ^ 4 * b) / ((1 + t ^ 2) * (1 - t ^ 2) ^ 2) := by
  have h := period_nonzero t ht0 ht1
  unfold mixture coherentEnergy rectangleEnergy compensatingWeight
  field_simp [h.1, h.2.1, h.2.2.1, h.2.2.2]
  ring

theorem compensatingWeight_pos (t : Real) (ht0 : 0 <= t) (ht1 : t < 1) :
    0 < compensatingWeight t /\ compensatingWeight t < 1 := by
  have h1 : 0 < (1 - t) ^ 2 := sq_pos_of_pos (sub_pos.mpr ht1)
  have h2 : 0 < 2 * (1 + t ^ 2) := by nlinarith [sq_nonneg t]
  unfold compensatingWeight
  constructor
  case left => exact div_pos h1 h2
  case right =>
    apply (div_lt_one h2).mpr
    nlinarith [sq_nonneg t]

theorem mixture_phase_difference (t w b : Real) (ht0 : 0 <= t) (ht1 : t < 1) :
    mixture t w 1 b - mixture t w (-1) b =
      4 * t ^ 2 * (1 + t ^ 2) * (2 * w * (1 + t ^ 2) - (1 - t) ^ 2) /
        (1 - t ^ 2) ^ 4 := by
  have h := period_nonzero t ht0 ht1
  unfold mixture coherentEnergy rectangleEnergy
  field_simp [h.1, h.2.1, h.2.2.1]
  ring

/-- Testing the two possible extreme phases already forces the compensation. -/
theorem compensatingWeight_unique (t w b : Real) (ht0 : 0 < t) (ht1 : t < 1) :
    (mixture t w 1 b = mixture t w (-1) b) <-> w = compensatingWeight t := by
  constructor
  case mp =>
    intro hw
    have hz := mixture_phase_difference t w b (le_of_lt ht0) ht1
    rw [hw, sub_self] at hz
    have h := period_nonzero t (le_of_lt ht0) ht1
    have hn : 4 * t ^ 2 * (1 + t ^ 2) *
        (2 * w * (1 + t ^ 2) - (1 - t) ^ 2) = 0 := by
      have hz' := hz.symm
      field_simp [h.2.2.1] at hz'
      convert hz' using 1 <;> ring
    have hp : 0 < 4 * t ^ 2 * (1 + t ^ 2) := by
      have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht0
      exact mul_pos (mul_pos (by norm_num) ht2) (by nlinarith [sq_nonneg t])
    have hc := (mul_eq_zero.mp hn).resolve_left (ne_of_gt hp)
    unfold compensatingWeight
    apply (eq_div_iff (ne_of_gt (show 0 < 2 * (1 + t ^ 2) by nlinarith [sq_nonneg t]))).mpr
    nlinarith [hc]
  case mpr =>
    intro hw
    rw [hw, compensated_coherent_trace t 1 b (le_of_lt ht0) ht1,
      compensated_coherent_trace t (-1) b (le_of_lt ht0) ht1]

/-- The unit coordinate is not removed by central compensation. -/
theorem unit_coordinate_survives (t g h j e sigma : Complex) :
    signedBase t g h j e sigma (0, 0) = 1 := by
  norm_num [signedBase, supported, row, degree, phaseValue, phase]

noncomputable def coherentSignal (t sigma : Real) (g h j e : Complex)
    (a : ZMod 8) : Complex :=
  finiteSignal (pairCoefficient (t : Complex) g h j e (sigma : Complex)) a /
    (((1 - sigma * t) * (1 - t ^ 2) : Real) : Complex)

/-- The compensated expression is attached to the full coherent rational signal. -/
theorem coherentSignal_energy (t sigma : Real) (g h j e : Complex)
    (hg : Complex.normSq g = 1) (hh : Complex.normSq h = 1)
    (hj : Complex.normSq j = 1) (he : Complex.normSq e = 1)
    (hsigma : sigma ^ 2 = 1) :
    Finset.univ.sum (fun a : ZMod 8 => Complex.normSq (coherentSignal t sigma g h j e a)) =
      8 * coherentEnergy t sigma (g * j * e).re (h * j * e / g).re := by
  simp only [coherentSignal, Complex.normSq_div, Complex.normSq_ofReal]
  rw [<- Finset.sum_div, additive_twist_energy t sigma g h j e hg hh hj he hsigma]
  unfold coherentEnergy
  ring

private theorem geometricPeriod_hasSum (r s : Complex)
    (hr : norm r < 1) (hs : norm s < 1) :
    HasSum (fun p : Period => r ^ p.1 * s ^ p.2) ((1 - r) ^ (-1 : Int) * (1 - s) ^ (-1 : Int)) := by
  have h1 := hasSum_geometric_of_norm_lt_one hr
  have h2 := hasSum_geometric_of_norm_lt_one hs
  have ha1 : Summable (fun n : Nat => norm (r ^ n)) := by
    simpa only [norm_pow] using (hasSum_geometric_of_lt_one (norm_nonneg r) hr).summable
  have ha2 : Summable (fun n : Nat => norm (s ^ n)) := by
    simpa only [norm_pow] using (hasSum_geometric_of_lt_one (norm_nonneg s) hs).summable
  simpa only [zpow_neg_one] using h1.mul h2 (ha1.mul_norm ha2).of_norm

/-- Absolute convergence keeps every overlap of the two infinite periods. -/
theorem coherentSignal_hasSum (t sigma : Real) (g h j e : Complex) (a : ZMod 8)
    (ht0 : 0 <= t) (ht1 : t < 1) (hsigma : sigma ^ 2 = 1) :
    HasSum (fun p : Period =>
      (((sigma * t : Real) : Complex) ^ p.1 * ((t ^ 2 : Real) : Complex) ^ p.2) *
        finiteSignal (pairCoefficient (t : Complex) g h j e (sigma : Complex)) a)
      (coherentSignal t sigma g h j e a) := by
  have hprod : (sigma - 1) * (sigma + 1) = 0 := by nlinarith [hsigma]
  have hsign : sigma = 1 \/ sigma = -1 := by
    cases mul_eq_zero.mp hprod with
    | inl h => exact Or.inl (by linarith)
    | inr h => exact Or.inr (by linarith)
  have h1 : norm ((sigma * t : Real) : Complex) < 1 := by
    cases hsign with
    | inl h =>
      simpa [h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0] using ht1
    | inr h =>
      simpa [h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0] using ht1
  have ht2 : t ^ 2 < 1 := by nlinarith
  have h2 : norm ((t ^ 2 : Real) : Complex) < 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)] using ht2
  have hp := geometricPeriod_hasSum ((sigma * t : Real) : Complex)
    ((t ^ 2 : Real) : Complex) h1 h2
  have hm := hp.mul_right (finiteSignal (pairCoefficient (t : Complex) g h j e
    (sigma : Complex)) a)
  convert hm using 1
  simp only [coherentSignal, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_one, Complex.ofReal_pow, div_eq_mul_inv, mul_inv, zpow_neg_one]
  ring

end Metaplectic.Sp4Eight
