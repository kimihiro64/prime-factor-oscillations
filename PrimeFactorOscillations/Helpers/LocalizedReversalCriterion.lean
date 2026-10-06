/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeProfileWindowBands

/-!
# Localized reversal-count RH criteria under arithmetic sampling

The counts use actual tilted densities and the full-profile reference on the
same prescribed cells. The sampling premise spells out only prime positions,
gap widths, separation and a positive-power number of cells. It contains no
RH premise and no assertion about density signs or centered errors.

Both eventual domination and the one-sided X^(1/10) excess bound are
proved equivalent to RH under that explicit arithmetic premise. Constructing
such a sampling from an all-short-interval prime-pair theorem is a separate
consumer; the published source is not asserted as a project axiom here.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Filter PrimeFactorUnimodality

def localTiltRank (H : Nat) (X : Nat) : Nat :=
  Nat.floor (((H : Real) + 2) * (Real.eulerMascheroniConstant +
    Real.log (Real.log (Chebyshev.theta (X : Real)))))

def localTiltMesh (X : Nat) : Nat := Nat.ceil ((X : Real) ^ (1 / 2 : Real))

def localTiltReference (H X i : Nat) : Real :=
  let L := Real.eulerMascheroniConstant +
    Real.log (Real.log (Chebyshev.theta ((primeAt i - 1 : Nat) : Real)))
  Nat.factorialConvolution primeProfileRealCoefficient (localTiltRank H X - 1) L /
    Nat.factorialConvolution primeProfileRealCoefficient (localTiltRank H X) L

def localReversalCount (H : Nat) (m : Nat -> Nat)
    (d a : (X : Nat) -> Fin (m X) -> Nat) (X : Nat) : Nat :=
  prescribedTiltReversalCount H (localTiltMesh X) (localTiltRank H X) (m X) (d X) (a X)

def localReferenceCount (H : Nat) (m : Nat -> Nat)
    (a : (X : Nat) -> Fin (m X) -> Nat) (X : Nat) : Nat :=
  prescribedTiltReferenceCount H (localTiltMesh X) (m X)
    (fun i => localTiltReference H X (a X i)) (a X)

/-- Explicit arithmetic sampling requirements, with no density or RH premise. -/
def LocalReversalSampling (H : Nat) (m : Nat -> Nat)
    (d a : (X : Nat) -> Fin (m X) -> Nat) : Prop :=
  exists c : Real, 0 < c /\ Filter.Eventually (fun X : Nat =>
    c * (X : Real) ^ (1 / 10 : Real) <= (m X : Real) /\
    (forall i, d X i < a X i /\
      H + 3 <= primeGap (d X i) /\
      2 <= primeGap (a X i) /\ primeGap (a X i) <= H /\
      (X : Real) <= ((primeAt (d X i) - 1 : Nat) : Real) /\
      ((primeAt (d X i) - 1 : Nat) : Real) <= X + (X : Real) ^ (7 / 10 : Real) /\
      (X : Real) <= ((primeAt (a X i) - 1 : Nat) : Real) /\
      ((primeAt (a X i) - 1 : Nat) : Real) <= X + (X : Real) ^ (7 / 10 : Real)) /\
    (forall i j, i < j -> a X i + 1 < d X j)) atTop

theorem localReversalCount_le_reference_eventually_of_RH
    (H : Nat) (m : Nat -> Nat) (d a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalReversalSampling H m d a) (hRH : RiemannHypothesis) :
    Filter.Eventually (fun X : Nat => localReversalCount H m d a X <=
      localReferenceCount H m a X) atTop := by
  choose c hc hCells using hs
  have hReal := eventually_prescribedTiltReversalCount_le_reference_of_RH
    hRH ((H : Real) + 2) (by positivity)
  have hCast : Tendsto (fun n : Nat => (n : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hNat := hCast.eventually hReal
  filter_upwards [hNat, hCells, eventually_ge_atTop (1 : Nat)] with X hUpper hCell hOne
  have hXOne : (1 : Real) <= X := by exact_mod_cast hOne
  have hPow : (X : Real) ^ (7 / 10 : Real) <= X := by
    calc
      _ <= (X : Real) ^ (1 : Real) :=
        Real.rpow_le_rpow_of_exponent_le hXOne (by norm_num)
      _ = _ := Real.rpow_one _
  apply hUpper H (localTiltMesh X) (m X) (d X) (a X)
  intro i
  have hi := hCell.2.1 i
  exact And.intro hi.2.2.2.2.2.2.1 (by linarith [hi.2.2.2.2.2.2.2])

theorem localReversalCount_excess_unbounded_of_not_RH
    (H : Nat) (m : Nat -> Nat) (d a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalReversalSampling H m d a) (hNotRH : Not RiemannHypothesis)
    (C X0 : Real) (hC : 0 < C) :
    exists n : Nat, X0 < (n : Real) /\
      C * (n : Real) ^ (1 / 10 : Real) <
        (localReversalCount H m d a n : Real) - (localReferenceCount H m a n : Real) := by
  choose c hc hCells using hs
  let alpha : Real := (H : Real) + 2
  have ha : 0 < alpha := by dsimp [alpha]; positivity
  have hCast : Tendsto (fun n : Nat => (n : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hBands := hCast.eventually (eventually_primeProfile_fixed_window_bands alpha ha)
  choose N hN using eventually_atTop.mp (hCells.and hBands)
  let T := C / c + 2
  have hT : 0 < T := by dsimp [T]; positivity
  choose n hn hnSix hEx using exists_densityRatio_uniform_mesh_excess_of_not_RH
    hNotRH (alpha / 3) (2 * alpha) (by linarith) (by linarith)
    (7 / 10) (by norm_num) T (max X0 (N : Real)) hT
  have hnN : N <= n := by
    have hh := (le_max_right X0 (N : Real)).trans hn.le
    exact_mod_cast hh
  have hCell := (hN n hnN).1
  have hBand := (hN n hnN).2
  have hnPos : (0 : Real) < n := by exact_mod_cast (by omega : 0 < n)
  have hnOne : (1 : Real) <= n := by exact_mod_cast (by omega : 1 <= n)
  have hPow : (n : Real) ^ (7 / 10 : Real) <= n := by
    calc
      _ <= (n : Real) ^ (1 : Real) :=
        Real.rpow_le_rpow_of_exponent_le hnOne (by norm_num)
      _ = _ := Real.rpow_one _
  let r := localTiltRank H n
  let M := localTiltMesh n
  let delta := T * (n : Real) ^ (-(1 / 2 : Real))
  have hMle : (n : Real) ^ (1 / 2 : Real) <= (M : Real) := Nat.le_ceil _
  have hMPos : 0 < M := by
    have h := (Real.rpow_pos_of_pos hnPos (1 / 2 : Real)).trans_le hMle
    exact_mod_cast h
  have hDelta : 0 <= delta := by dsimp [delta]; positivity
  have hMesh : T <= (M : Real) * delta := by
    have h := mul_le_mul_of_nonneg_right hMle hDelta
    have he : (n : Real) ^ (1 / 2 : Real) * delta = T := by
      dsimp [delta]
      rw [mul_left_comm, <- Real.rpow_add hnPos]
      norm_num
    rwa [he] at h
  have hPoint : forall i : Fin (m n),
      r <= (primesBelow (primeAt (d n i))).length /\
      r <= (primesBelow (primeAt (a n i))).length /\
      (densityRatio (primesBelow (primeAt (d n i))) r : Real) <
        (primeGap (d n i) : Real) + 1 /\
      1 <= (densityRatio (primesBelow (primeAt (a n i))) r : Real) - primeGap (a n i) /\
      (densityRatio (primesBelow (primeAt (a n i))) r : Real) - primeGap (a n i) <= H + 1 /\
      1 <= localTiltReference H n (a n i) - primeGap (a n i) /\
      localTiltReference H n (a n i) - primeGap (a n i) <= H + 1 /\
      delta <= (densityRatio (primesBelow (primeAt (a n i))) r : Real) -
        localTiltReference H n (a n i) := by
    intro i
    have hi := hCell.2.1 i
    let yd : Real := ((primeAt (d n i) - 1 : Nat) : Real)
    let ya : Real := ((primeAt (a n i) - 1 : Nat) : Real)
    have hdLow : (n : Real) <= yd := hi.2.2.2.2.1
    have hdHigh : yd <= n + (n : Real) ^ (7 / 10 : Real) := hi.2.2.2.2.2.1
    have haLow : (n : Real) <= ya := hi.2.2.2.2.2.2.1
    have haHigh : ya <= n + (n : Real) ^ (7 / 10 : Real) := hi.2.2.2.2.2.2.2
    have hdB := hBand.2 yd hdLow (by linarith)
    have haB := hBand.2 ya haLow (by linarith)
    have hDiff := (hEx ya haLow haHigh).2 r haB.1 haB.2.1
    have hdCut : Nat.floor yd + 1 = primeAt (d n i) := by
      dsimp [yd]
      rw [Nat.floor_natCast, Nat.sub_add_cancel (prime_primeAt (d n i)).one_lt.le]
    have haCut : Nat.floor ya + 1 = primeAt (a n i) := by
      dsimp [ya]
      rw [Nat.floor_natCast, Nat.sub_add_cancel (prime_primeAt (a n i)).one_lt.le]
    rw [hdCut] at hdB
    rw [haCut] at haB hDiff
    have hdG : (H : Real) + 3 <= primeGap (d n i) := by exact_mod_cast hi.2.1
    have haG : (2 : Real) <= primeGap (a n i) := by exact_mod_cast hi.2.2.1
    have haGH : (primeGap (a n i) : Real) <= H := by exact_mod_cast hi.2.2.2.1
    have hdNear := (abs_le.mp hdB.2.2.2.2).2
    have hRNear := abs_le.mp haB.2.2.2.2
    have hUNear := abs_le.mp haB.2.2.2.1
    change - (1 / 2 : Real) <= localTiltReference H n (a n i) - alpha /\
      localTiltReference H n (a n i) - alpha <= 1 / 2 at hUNear
    change (densityRatio (primesBelow (primeAt (d n i))) r : Real) -
      ((H : Real) + 2) <= 1 / 2 at hdNear
    change - (1 / 2 : Real) <=
      (densityRatio (primesBelow (primeAt (a n i))) r : Real) - ((H : Real) + 2) /\
      (densityRatio (primesBelow (primeAt (a n i))) r : Real) - ((H : Real) + 2) <=
        1 / 2 at hRNear
    dsimp only [alpha] at hUNear
    refine And.intro (weightEsymm_positive_degree_supported _ _ hdB.2.2.1)
      (And.intro (weightEsymm_positive_degree_supported _ _ haB.2.2.1) ?_)
    refine And.intro (by linarith) ?_
    refine And.intro (by linarith) ?_
    refine And.intro (by linarith) ?_
    refine And.intro (by linarith) ?_
    refine And.intro (by linarith) ?_
    exact hDiff.2.2.le
  have hLower := prescribedTiltReversalCount_signed_lower H M r (m n) hMPos
    (d n) (a n) (fun i => localTiltReference H n (a n i)) delta hBand.1
    (fun i => (hCell.2.1 i).1)
    (fun i => (hPoint i).1) (fun i => (hPoint i).2.1)
    (fun i => (hPoint i).2.2.1) (fun i => (hPoint i).2.2.2.1)
    (fun i => (hPoint i).2.2.2.2.1) (fun i => (hPoint i).2.2.2.2.2.1)
    (fun i => (hPoint i).2.2.2.2.2.2.1) (fun i => (hPoint i).2.2.2.2.2.2.2)
  refine Exists.intro n (And.intro ((le_max_left _ _).trans_lt hn) ?_)
  have hp : 0 < (n : Real) ^ (1 / 10 : Real) := Real.rpow_pos_of_pos hnPos _
  have hTOne : 0 <= T - 1 := by
    dsimp [T]
    have hNon : 0 <= C / c := div_nonneg hC.le hc.le
    linarith
  have hStep := mul_le_mul hCell.1 (show T - 1 <= (M : Real) * delta - 1 by linarith)
    hTOne (Nat.cast_nonneg _)
  have he : c * (n : Real) ^ (1 / 10 : Real) * (T - 1) =
      (C + c) * (n : Real) ^ (1 / 10 : Real) := by
    dsimp [T]
    field_simp [hc.ne']
    <;> ring
  rw [he] at hStep
  change (m n : Real) * ((M : Real) * delta - 1) <=
    (localReversalCount H m d a n : Real) - (localReferenceCount H m a n : Real) at hLower
  have hStrict := mul_lt_mul_of_pos_right (show C < C + c by linarith) hp
  exact hStrict.trans_le (hStep.trans hLower)

theorem riemannHypothesis_iff_eventually_localReversalCount_le_reference
    (H : Nat) (m : Nat -> Nat) (d a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalReversalSampling H m d a) :
    RiemannHypothesis <->
      Filter.Eventually (fun X : Nat => localReversalCount H m d a X <=
        localReferenceCount H m a X) atTop := by
  constructor
  . exact localReversalCount_le_reference_eventually_of_RH H m d a hs
  . intro hEvent
    by_contra hNotRH
    choose X0 hX0 using eventually_atTop.mp hEvent
    choose n hn hEx using localReversalCount_excess_unbounded_of_not_RH
      H m d a hs hNotRH 1 (X0 : Real) (by norm_num)
    have hn0 : X0 <= n := by exact_mod_cast hn.le
    have hLe : (localReversalCount H m d a n : Real) <= localReferenceCount H m a n := by
      exact_mod_cast hX0 n hn0
    have hNon : 0 <= (n : Real) ^ (1 / 10 : Real) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    linarith

theorem riemannHypothesis_iff_eventually_localReversalCount_power_upper
    (H : Nat) (m : Nat -> Nat) (d a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalReversalSampling H m d a) :
    RiemannHypothesis <->
      exists C : Real, 0 < C /\ Filter.Eventually (fun X : Nat =>
        (localReversalCount H m d a X : Real) - (localReferenceCount H m a X : Real) <=
          C * (X : Real) ^ (1 / 10 : Real)) atTop := by
  constructor
  . intro hRH
    refine Exists.intro 1 (And.intro (by norm_num) ?_)
    filter_upwards [localReversalCount_le_reference_eventually_of_RH H m d a hs hRH] with X hX
    have hLe : (localReversalCount H m d a X : Real) <= localReferenceCount H m a X := by
      exact_mod_cast hX
    have hNon : 0 <= (X : Real) ^ (1 / 10 : Real) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    linarith
  . intro h
    choose C hC hEvent using h
    by_contra hNotRH
    choose X0 hX0 using eventually_atTop.mp hEvent
    choose n hn hEx using localReversalCount_excess_unbounded_of_not_RH
      H m d a hs hNotRH C (X0 : Real) hC
    have hn0 : X0 <= n := by exact_mod_cast hn.le
    exact (not_lt_of_ge (hX0 n hn0)) hEx


end PrimeFactorOscillations
