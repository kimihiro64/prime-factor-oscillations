/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.AscentSamplingGrowth
import PrimeFactorOscillations.Helpers.LocalizedAscentCount

/-!
# Ascent-only local count criteria for RH

A uniform false-RH power excursion survives the square-root tilt grid and
all frequency and rounding losses. For the same actual selected pairs,
both eventual reference domination and a one-sided X^(7/10) excess bound
are equivalent to RH under the explicit arithmetic sampling premise.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations
open Filter PrimeFactorUnimodality

theorem localAscentCount_excess_unbounded_of_not_RH
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalAscentSampling H m a) (hNotRH : Not RiemannHypothesis)
    (C X0 : Real) (hC : 0 < C) :
    exists n : Nat, X0 < (n : Real) /\
      C * (n : Real) ^ (7 / 10 : Real) <
        (localAscentCount H m a n : Real) - (localReferenceCount H m a n : Real) := by
  let alpha : Real := (H : Real) + 2
  have ha : 0 < alpha := by dsimp [alpha]; positivity
  choose b hb hbHalf hWindows using exists_densityRatio_uniform_power_excess_of_not_RH
    hNotRH (alpha / 3) (2 * alpha) (by linarith) (by linarith)
  have hCast : Tendsto (fun n : Nat => (n : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hBands := hCast.eventually (eventually_primeProfile_fixed_window_bands alpha ha)
  have hAmplify := power_subpower_mesh_amplification m hs.1 b C hbHalf hC
  have hScalar := localAscentCount_eq_scalar_eventually H m a hs
  choose N hN using eventually_atTop.mp (hs.2.and (hBands.and (hScalar.and hAmplify)))
  choose n hn hnSix hEx using hWindows (3 / 4) (by norm_num) 1
    (max X0 (N : Real)) (by norm_num)
  have hnN : N <= n := by
    have hh := (le_max_right X0 (N : Real)).trans hn.le
    exact_mod_cast hh
  have hPairData := (hN n hnN).1
  have hBand := (hN n hnN).2.1
  have hScalarN := (hN n hnN).2.2.1
  have hAmplitude := (hN n hnN).2.2.2
  have hnPos : (0 : Real) < n := by exact_mod_cast (by omega : 0 < n)
  have hnOne : (1 : Real) <= n := by exact_mod_cast (by omega : 1 <= n)
  have hPow : (n : Real) ^ (3 / 4 : Real) <= n := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hnOne
      (by norm_num : (3 / 4 : Real) <= 1)
  let r := localTiltRank H n
  let M := localTiltMesh n
  let R : Fin (m n) -> Real := fun i => (densityRatio (primesBelow (primeAt (a n i))) r : Real)
  let U : Fin (m n) -> Real := fun i => localTiltReference H n (a n i)
  let g : Fin (m n) -> Real := fun i => (primeGap (a n i) : Real)
  have hMle : (n : Real) ^ (1 / 2 : Real) <= (M : Real) := Nat.le_ceil _
  have hMPos : 0 < M := by
    have h := (Real.rpow_pos_of_pos hnPos (1 / 2 : Real)).trans_le hMle
    exact_mod_cast h
  have hPoint : forall i : Fin (m n),
      1 <= R i - g i /\ R i - g i <= H + 1 /\
      1 <= U i - g i /\ U i - g i <= H + 1 /\
      (n : Real) ^ (-b) <= R i - U i := by
    intro i
    have hi := hPairData.2 i
    let y : Real := ((primeAt (a n i) - 1 : Nat) : Real)
    have hyLow : (n : Real) <= y := hi.2.2.1
    have hyHigh : y <= n + (n : Real) ^ (3 / 4 : Real) := hi.2.2.2
    have hB := hBand.2 y hyLow (by linarith)
    have hDiff := (hEx y hyLow hyHigh).2 r hB.1 hB.2.1
    have hCut : Nat.floor y + 1 = primeAt (a n i) := by
      dsimp [y]
      rw [Nat.floor_natCast, Nat.sub_add_cancel (prime_primeAt (a n i)).one_lt.le]
    rw [hCut] at hB hDiff
    have hG : (2 : Real) <= g i := by dsimp [g]; exact_mod_cast hi.1
    have hGH : g i <= H := by dsimp [g]; exact_mod_cast hi.2.1
    have hRNear : -(1 / 2 : Real) <= R i - alpha /\ R i - alpha <= 1 / 2 :=
      abs_le.mp hB.2.2.2.2
    have hUNear : -(1 / 2 : Real) <= U i - alpha /\ U i - alpha <= 1 / 2 :=
      abs_le.mp hB.2.2.2.1
    dsimp only [alpha] at hRNear hUNear
    refine And.intro (by linarith) (And.intro (by linarith)
      (And.intro (by linarith) (And.intro (by linarith) ?_)))
    simpa only [one_mul, R, U, r, localTiltReference, y] using hDiff.2.2.le
  have hLower := tiltAscentSet_sum_lower (Finset.univ : Finset (Fin (m n))) H M hMPos
    R U g ((n : Real) ^ (-b))
    (fun i _ => (hPoint i).1) (fun i _ => (hPoint i).2.1)
    (fun i _ => (hPoint i).2.2.1) (fun i _ => (hPoint i).2.2.2.1)
    (fun i _ => (hPoint i).2.2.2.2)
  simp only [Finset.card_univ, Fintype.card_fin] at hLower
  have hExact : Finset.sum Finset.univ (fun i =>
      ((tiltAscentSet H M (R i) (g i)).card : Real) -
        ((tiltAscentSet H M (U i) (g i)).card : Real)) =
      (localAscentCount H m a n : Real) - (localReferenceCount H m a n : Real) := by
    rw [hScalarN, localReferenceCount, prescribedTiltReferenceCount,
      Nat.cast_sum, Nat.cast_sum, <- Finset.sum_sub_distrib]
  rw [hExact] at hLower
  exact Exists.intro n (And.intro ((le_max_left _ _).trans_lt hn)
    (hAmplitude.trans_le hLower))

theorem riemannHypothesis_iff_eventually_localAscentCount_le_reference
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalAscentSampling H m a) :
    RiemannHypothesis <->
      Filter.Eventually (fun X : Nat => localAscentCount H m a X <=
        localReferenceCount H m a X) atTop := by
  constructor
  . exact localAscentCount_le_reference_eventually_of_RH H m a hs
  . intro hEvent
    by_contra hNotRH
    choose X0 hX0 using eventually_atTop.mp hEvent
    choose n hn hEx using localAscentCount_excess_unbounded_of_not_RH
      H m a hs hNotRH 1 (X0 : Real) (by norm_num)
    have hn0 : X0 <= n := by exact_mod_cast hn.le
    have hLe : (localAscentCount H m a n : Real) <= localReferenceCount H m a n := by
      exact_mod_cast hX0 n hn0
    have hNon : 0 <= (n : Real) ^ (7 / 10 : Real) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    linarith

theorem riemannHypothesis_iff_eventually_localAscentCount_power_upper
    (H : Nat) (m : Nat -> Nat) (a : (X : Nat) -> Fin (m X) -> Nat)
    (hs : LocalAscentSampling H m a) :
    RiemannHypothesis <->
      exists C : Real, 0 < C /\ Filter.Eventually (fun X : Nat =>
        (localAscentCount H m a X : Real) - (localReferenceCount H m a X : Real) <=
          C * (X : Real) ^ (7 / 10 : Real)) atTop := by
  constructor
  . intro hRH
    refine Exists.intro 1 (And.intro (by norm_num) ?_)
    filter_upwards [localAscentCount_le_reference_eventually_of_RH H m a hs hRH] with X hX
    have hLe : (localAscentCount H m a X : Real) <= localReferenceCount H m a X := by
      exact_mod_cast hX
    have hNon : 0 <= (X : Real) ^ (7 / 10 : Real) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    linarith
  . intro h
    choose C hC hEvent using h
    by_contra hNotRH
    choose X0 hX0 using eventually_atTop.mp hEvent
    choose n hn hEx using localAscentCount_excess_unbounded_of_not_RH
      H m a hs hNotRH C (X0 : Real) hC
    have hn0 : X0 <= n := by exact_mod_cast hn.le
    exact (not_lt_of_ge (hX0 n hn0)) hEx

end PrimeFactorOscillations


