/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.G2SevenCubic

/-!
# Principal-preserving cubic readout from the full sevenfold coordinates

Both masks include the entire grade-zero channel. Exact cubic
compensation produces reciprocal phase factors at the same torus
bidegree (8,9). Both coherent periods and their convergence domain are
retained. No global automorphic coefficient or QRH estimate is asserted.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace Metaplectic.G2Seven.Cubic

def principal (t X Y : Complex) : Complex :=
  (1 + t ^ 2 * X ^ 2 * Y ^ 4) * (1 + t ^ 2 * X * Y ^ 2 + t ^ 2 * X ^ 4 * Y)

def residueMask (r : Fin 7) : Bool :=
  decide (r.val = 0 \/ r.val = 1 \/ r.val = 2 \/ r.val = 4)

def nonresidueMask (r : Fin 7) : Bool :=
  decide (r.val = 0 \/ r.val = 3 \/ r.val = 5 \/ r.val = 6)

noncomputable def torusProjection (mask : Fin 7 -> Bool)
    (t g h j X Y : Complex) (a : ZMod 7) : Complex :=
  Finset.univ.sum (fun s : State =>
    if mask (twistClass s) then
      ZMod.stdAddChar (a * ((twistClass s).val : ZMod 7)) *
        signedBase t g h j s * X ^ s.1.val * Y ^ s.2.val
    else 0)

/-- The projection includes all six principal coordinates, with their overlaps. -/
theorem source_residue_carrier (t g h j X Y : Complex)
    (hg : Not (g = 0)) (hh : Not (h = 0)) (hj : Not (j = 0)) (a : ZMod 7) :
    torusProjection residueMask t g h j X Y a =
      carrier residueFrequency (principal t X Y)
        (t * g * X) (t ^ 3 * h * X ^ 4 * Y ^ 4) (t ^ 3 / j * X ^ 3 * Y ^ 5) a := by
  norm_num [torusProjection, residueMask, carrier, residueFrequency, coefficient,
    principal, Fintype.sum_prod_type, Fin.sum_univ_succ, signedBase,
    supported, degree, row, phaseValue, phase, twistClass, zpow_neg_one]
  field_simp [hg, hh, hj]
  ring

theorem source_nonresidue_carrier (t g h j X Y : Complex)
    (hg : Not (g = 0)) (hh : Not (h = 0)) (hj : Not (j = 0)) (a : ZMod 7) :
    torusProjection nonresidueMask t g h j X Y a =
      carrier nonresidueFrequency (principal t X Y)
        (t * j * Y) (t ^ 3 / h * X ^ 6 * Y ^ 2) (t ^ 3 / g * X ^ 2 * Y ^ 6) a := by
  norm_num [torusProjection, nonresidueMask, carrier, nonresidueFrequency, coefficient,
    principal, Fintype.sum_prod_type, Fin.sum_univ_succ, signedBase,
    supported, degree, row, phaseValue, phase, twistClass, zpow_neg_one]
  field_simp [hg, hh, hj]
  ring

private theorem residue_negation (u A B C : Complex) (a : ZMod 7) :
    2 * u - carrier residueFrequency u A B C a =
      carrier residueFrequency u (-A) (-B) (-C) a := by
  norm_num [carrier, residueFrequency, coefficient, Fin.sum_univ_succ]
  ring

private theorem nonresidue_negation (u A B C : Complex) (a : ZMod 7) :
    2 * u - carrier nonresidueFrequency u A B C a =
      carrier nonresidueFrequency u (-A) (-B) (-C) a := by
  norm_num [carrier, nonresidueFrequency, coefficient, Fin.sum_univ_succ]
  ring

noncomputable def projectedProbe (mask : Fin 7 -> Bool)
    (t g h j X Y : Complex) (a : ZMod 7) : Complex :=
  1 + ((2 * principal t X Y - torusProjection mask t g h j X Y a) ^ 3 -
    (principal t X Y) ^ 3) / 6

def readoutMonomial (t X Y : Complex) : Complex := t ^ 7 * X ^ 8 * Y ^ 9

/-- The same torus bidegree carries both phase and inverse phase. -/
theorem residue_probe_mean (t g h j X Y : Complex)
    (hg : Not (g = 0)) (hh : Not (h = 0)) (hj : Not (j = 0)) :
    mean (projectedProbe residueMask t g h j X Y) =
      1 - (g * h / j) * readoutMonomial t X Y := by
  unfold projectedProbe
  simp_rw [source_residue_carrier t g h j X Y hg hh hj]
  simp_rw [residue_negation]
  change mean (compensatedCarrier residueFrequency (principal t X Y)
    (t * g * X) (t ^ 3 * h * X ^ 4 * Y ^ 4) (t ^ 3 / j * X ^ 3 * Y ^ 5)) = _
  rw [residue_compensated_mean]
  unfold readoutMonomial
  field_simp [hg, hh, hj] <;> ring

theorem nonresidue_probe_mean (t g h j X Y : Complex)
    (hg : Not (g = 0)) (hh : Not (h = 0)) (hj : Not (j = 0)) :
    mean (projectedProbe nonresidueMask t g h j X Y) =
      1 - (j / (g * h)) * readoutMonomial t X Y := by
  unfold projectedProbe
  simp_rw [source_nonresidue_carrier t g h j X Y hg hh hj]
  simp_rw [nonresidue_negation]
  change mean (compensatedCarrier nonresidueFrequency (principal t X Y)
    (t * j * Y) (t ^ 3 / h * X ^ 6 * Y ^ 2) (t ^ 3 / g * X ^ 2 * Y ^ 6)) = _
  rw [nonresidue_compensated_mean]
  unfold readoutMonomial
  field_simp [hg, hh, hj] <;> ring

theorem paired_probe_mean (t g h j X Y : Complex)
    (hg : Not (g = 0)) (hh : Not (h = 0)) (hj : Not (j = 0)) :
    mean (projectedProbe residueMask t g h j X Y) *
        mean (projectedProbe nonresidueMask t g h j X Y) =
      1 - (g * h / j + j / (g * h)) * readoutMonomial t X Y +
        (readoutMonomial t X Y) ^ 2 := by
  rw [residue_probe_mean t g h j X Y hg hh hj,
    nonresidue_probe_mean t g h j X Y hg hh hj]
  field_simp [hg, hh, hj]
  ring

/-- The paired readout has real trace and unit determinant under unit Gauss inputs. -/
theorem paired_probe_unitary (t g h j X Y : Complex)
    (hg : Complex.normSq g = 1) (hh : Complex.normSq h = 1)
    (hj : Complex.normSq j = 1) :
    mean (projectedProbe residueMask t g h j X Y) *
        mean (projectedProbe nonresidueMask t g h j X Y) =
      1 - ((2 * (g * h / j).re : Real) : Complex) * readoutMonomial t X Y +
        (readoutMonomial t X Y) ^ 2 := by
  have hg0 : Not (g = 0) := by intro heq; rw [heq] at hg; norm_num at hg
  have hh0 : Not (h = 0) := by intro heq; rw [heq] at hh; norm_num at hh
  have hj0 : Not (j = 0) := by intro heq; rw [heq] at hj; norm_num at hj
  let A := g * h / j
  let B := j / (g * h)
  have hA : Complex.normSq A = 1 := by simp [A, Complex.normSq_mul, hg, hh, hj]
  have hunit : (starRingEnd Complex) A * A = 1 := by
    rw [<- Complex.normSq_eq_conj_mul_self, hA]
    norm_num
  have hpair : A * B = 1 := by
    dsimp [A, B]
    field_simp [hg0, hh0, hj0]
  have hc : B = (starRingEnd Complex) A := by
    calc
      B = 1 * B := by ring
      _ = ((starRingEnd Complex) A * A) * B := by rw [hunit]
      _ = (starRingEnd Complex) A * (A * B) := by ring
      _ = (starRingEnd Complex) A := by rw [hpair]; ring
  have htrace : A + B = ((2 * A.re : Real) : Complex) := by
    rw [hc]
    apply Complex.ext <;> simp <;> ring
  rw [paired_probe_mean t g h j X Y hg0 hh0 hj0]
  change 1 - (A + B) * readoutMonomial t X Y + (readoutMonomial t X Y) ^ 2 = _
  rw [htrace]

def periodDenominator (t X Y : Complex) : Complex :=
  (1 - t ^ 2 * X ^ 7) * (1 - t ^ 2 * Y ^ 7)

noncomputable def coherentProjection (mask : Fin 7 -> Bool)
    (t g h j X Y : Complex) (a : ZMod 7) : Complex :=
  torusProjection mask t g h j X Y a / periodDenominator t X Y

noncomputable def coherentProbe (mask : Fin 7 -> Bool)
    (t g h j X Y : Complex) (a : ZMod 7) : Complex :=
  1 + ((2 * principal t X Y -
    periodDenominator t X Y * coherentProjection mask t g h j X Y a) ^ 3 -
      (principal t X Y) ^ 3) / 6

/-- Both complete period factors are compensated before cubing the carrier. -/
theorem coherentProbe_eq (mask : Fin 7 -> Bool) (t g h j X Y : Complex)
    (hD : Not (periodDenominator t X Y = 0)) (a : ZMod 7) :
    coherentProbe mask t g h j X Y a = projectedProbe mask t g h j X Y a := by
  have hc : periodDenominator t X Y * coherentProjection mask t g h j X Y a =
      torusProjection mask t g h j X Y a := by
    unfold coherentProjection
    field_simp [hD]
  unfold coherentProbe projectedProbe
  rw [hc]

theorem coherent_residue_probe_mean (t g h j X Y : Complex)
    (hg : Not (g = 0)) (hh : Not (h = 0)) (hj : Not (j = 0))
    (hD : Not (periodDenominator t X Y = 0)) :
    mean (coherentProbe residueMask t g h j X Y) =
      1 - (g * h / j) * readoutMonomial t X Y := by
  unfold mean
  simp_rw [coherentProbe_eq residueMask t g h j X Y hD]
  exact residue_probe_mean t g h j X Y hg hh hj

theorem coherent_nonresidue_probe_mean (t g h j X Y : Complex)
    (hg : Not (g = 0)) (hh : Not (h = 0)) (hj : Not (j = 0))
    (hD : Not (periodDenominator t X Y = 0)) :
    mean (coherentProbe nonresidueMask t g h j X Y) =
      1 - (j / (g * h)) * readoutMonomial t X Y := by
  unfold mean
  simp_rw [coherentProbe_eq nonresidueMask t g h j X Y hD]
  exact nonresidue_probe_mean t g h j X Y hg hh hj

private theorem period_hasSum (r s v : Complex)
    (hr : norm r < 1) (hs : norm s < 1) :
    HasSum (fun p : Period => r ^ p.1 * s ^ p.2 * v)
      (v / ((1 - r) * (1 - s))) := by
  have h1 := hasSum_geometric_of_norm_lt_one hr
  have h2 := hasSum_geometric_of_norm_lt_one hs
  have ha1 : Summable (fun n : Nat => norm (r ^ n)) := by
    simpa only [norm_pow] using (hasSum_geometric_of_lt_one (norm_nonneg r) hr).summable
  have ha2 : Summable (fun n : Nat => norm (s ^ n)) := by
    simpa only [norm_pow] using (hasSum_geometric_of_lt_one (norm_nonneg s) hs).summable
  have hp := h1.mul h2 (ha1.mul_norm ha2).of_norm
  have hm := hp.mul_right v
  have hr0 : Not (1 - r = 0) := by
    intro hz
    have heq : r = 1 := (sub_eq_zero.mp hz).symm
    rw [heq] at hr
    norm_num at hr
  have hs0 : Not (1 - s = 0) := by
    intro hz
    have heq : s = 1 := (sub_eq_zero.mp hz).symm
    rw [heq] at hs
    norm_num at hs
  convert hm using 1
  field_simp [hr0, hs0] <;> ring

/-- The variable-torus carrier is the full convergent double period series. -/
theorem coherentProjection_hasSum (mask : Fin 7 -> Bool)
    (t g h j X Y : Complex) (a : ZMod 7)
    (hX : norm (t ^ 2 * X ^ 7) < 1) (hY : norm (t ^ 2 * Y ^ 7) < 1) :
    HasSum (fun p : Period =>
      (t ^ 2 * X ^ 7) ^ p.1 * (t ^ 2 * Y ^ 7) ^ p.2 *
        torusProjection mask t g h j X Y a)
      (coherentProjection mask t g h j X Y a) := by
  simpa only [coherentProjection, periodDenominator] using
    period_hasSum (t ^ 2 * X ^ 7) (t ^ 2 * Y ^ 7)
      (torusProjection mask t g h j X Y a) hX hY

/-- Exact scalar range of the absolute period box with the physical Gauss scale. -/
theorem absolute_period_box (s : Real) :
    (Exists fun u : Real => Exists fun v : Real =>
      u < 1 / 7 /\ v < 1 / 7 /\ 8 * u + 9 * v = 7 / 2 - s) <->
      15 / 14 < s := by
  constructor
  . intro hs
    cases hs with
    | intro u hu =>
      cases hu with
      | intro v hv => linarith [hv.1, hv.2.1, hv.2.2]
  . intro hs
    apply Exists.intro ((7 / 2 - s) / 17)
    apply Exists.intro ((7 / 2 - s) / 17)
    constructor
    . linarith
    constructor
    . linarith
    . ring

end Metaplectic.G2Seven.Cubic
