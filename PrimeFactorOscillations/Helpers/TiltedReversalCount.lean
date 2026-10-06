/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Definitions.Reversals
import PrimeFactorOscillations.Helpers.PrimeWindowPairs
import PrimeFactorOscillations.Helpers.TiltedAscentCount
import PrimeFactorOscillations.Helpers.TiltedDensity

/-!
# Actual prescribed reversal counts over a finite tilt grid

The count tests both signs of the real density, at fixed chosen descent
and ascent indices. When every chosen descent is valid throughout the
grid, it equals the scalar ascent detector exactly. The signed count
therefore retains the full residual with at most one unit of rounding
loss per cell. An ordered subfamily also gives actual strictly separated
reversal witnesses for each individual tilt.

All selection, support, and band hypotheses are explicit. The eventual
RH count equivalences and the short-interval prime supply are separate
analytic consumers, not assumptions hidden in these finite identities.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open PrimeFactorUnimodality

theorem oddsTilt_rank_ascent_index_iff (t : Real) (ht : 0 < t) (i r : Nat)
    (hr : 1 <= r) (hsupport : r <= (primesBelow (primeAt i)).length) :
    (oddsTiltLaw t ht).rankDensity (r + 1) i <
      (oddsTiltLaw t ht).rankDensity (r + 1) (i + 1) <->
      (primeGap i : Real) + t < (densityRatio (primesBelow (primeAt i)) r : Real) := by
  have hlt := primeAt_strictMono (Nat.lt_succ_self i)
  have hgap : forall n : Nat, primeAt i < n -> n < primeAt (i + 1) ->
      Not (Nat.Prime n) := by
    intro n hn hn' hprime
    have heq := primeAt_primeCounting' n hprime
    have hlow : i < Nat.primeCounting' n :=
      primeAt_strictMono.lt_iff_lt.mp (by rwa [heq])
    have hhigh : Nat.primeCounting' n < i + 1 :=
      primeAt_strictMono.lt_iff_lt.mp (by rwa [heq])
    omega
  unfold ReciprocalSmoothLaw.rankDensity
  rw [oddsTilt_rank_ascent_iff t ht _ _ r (prime_primeAt i)
    (prime_primeAt (i + 1)) hlt hgap hr hsupport]
  unfold primeGap
  rw [Nat.cast_sub hlt.le]

theorem oddsTilt_rank_descent_index_iff (t : Real) (ht : 0 < t) (i r : Nat)
    (hr : 1 <= r) (hsupport : r <= (primesBelow (primeAt i)).length) :
    (oddsTiltLaw t ht).rankDensity (r + 1) (i + 1) <
      (oddsTiltLaw t ht).rankDensity (r + 1) i <->
      (densityRatio (primesBelow (primeAt i)) r : Real) < (primeGap i : Real) + t := by
  have hlt := primeAt_strictMono (Nat.lt_succ_self i)
  have hgap : forall n : Nat, primeAt i < n -> n < primeAt (i + 1) ->
      Not (Nat.Prime n) := by
    intro n hn hn' hprime
    have heq := primeAt_primeCounting' n hprime
    have hlow : i < Nat.primeCounting' n :=
      primeAt_strictMono.lt_iff_lt.mp (by rwa [heq])
    have hhigh : Nat.primeCounting' n < i + 1 :=
      primeAt_strictMono.lt_iff_lt.mp (by rwa [heq])
    omega
  unfold ReciprocalSmoothLaw.rankDensity
  rw [oddsTilt_rank_descent_iff t ht _ _ r (prime_primeAt i)
    (prime_primeAt (i + 1)) hlt hgap hr hsupport]
  unfold primeGap
  rw [Nat.cast_sub hlt.le]

def tiltGridValue (M j : Nat) : Real := 1 + (j : Real) / M

theorem tiltGridValue_pos (M j : Nat) : 0 < tiltGridValue M j := by
  unfold tiltGridValue
  positivity

def prescribedTiltReversalSet (H M r d a : Nat) : Finset Nat := by
  classical
  exact (Finset.range (H * M + 1)).filter (fun j =>
    IsReversal ((oddsTiltLaw (tiltGridValue M j) (tiltGridValue_pos M j)).rankDensity
      (r + 1)) d a)

theorem prescribedTiltReversalSet_eq_ascentSet (H M r d a : Nat)
    (hr : 1 <= r) (hda : d < a)
    (hdSupport : r <= (primesBelow (primeAt d)).length)
    (haSupport : r <= (primesBelow (primeAt a)).length)
    (hdRatio : (densityRatio (primesBelow (primeAt d)) r : Real) <
      (primeGap d : Real) + 1) :
    prescribedTiltReversalSet H M r d a =
      tiltAscentSet H M (densityRatio (primesBelow (primeAt a)) r : Real)
        (primeGap a : Real) := by
  classical
  apply Finset.ext
  intro j
  have hDescent : (oddsTiltLaw (tiltGridValue M j) (tiltGridValue_pos M j)).rankDensity
      (r + 1) (d + 1) <
      (oddsTiltLaw (tiltGridValue M j) (tiltGridValue_pos M j)).rankDensity
      (r + 1) d := by
    apply (oddsTilt_rank_descent_index_iff _ _ d r hr hdSupport).mpr
    have hnonneg : 0 <= (j : Real) / M := by positivity
    dsimp [tiltGridValue]
    linarith
  simp only [prescribedTiltReversalSet, tiltAscentSet, Finset.mem_filter,
    IsReversal, hda, hDescent, true_and]
  rw [oddsTilt_rank_ascent_index_iff _ _ a r hr haSupport]
  simp only [tiltGridValue, add_assoc]


def prescribedTiltReversalCount (H M r m : Nat) (d a : Fin m -> Nat) : Nat :=
  Finset.sum Finset.univ (fun i => (prescribedTiltReversalSet H M r (d i) (a i)).card)

def prescribedTiltReferenceCount (H M m : Nat) (U : Fin m -> Real)
    (a : Fin m -> Nat) : Nat :=
  Finset.sum Finset.univ (fun i => (tiltAscentSet H M (U i) (primeGap (a i) : Real)).card)

theorem prescribedTiltReversalCount_le_reference (H M r m : Nat)
    (d a : Fin m -> Nat) (U : Fin m -> Real) (hr : 1 <= r)
    (hda : forall i, d i < a i)
    (hdSupport : forall i, r <= (primesBelow (primeAt (d i))).length)
    (haSupport : forall i, r <= (primesBelow (primeAt (a i))).length)
    (hdRatio : forall i, (densityRatio (primesBelow (primeAt (d i))) r : Real) <
      (primeGap (d i) : Real) + 1)
    (hRU : forall i, (densityRatio (primesBelow (primeAt (a i))) r : Real) <= U i) :
    prescribedTiltReversalCount H M r m d a <= prescribedTiltReferenceCount H M m U a := by
  unfold prescribedTiltReversalCount prescribedTiltReferenceCount
  apply Finset.sum_le_sum
  intro i hi
  rw [prescribedTiltReversalSet_eq_ascentSet H M r (d i) (a i) hr
    (hda i) (hdSupport i) (haSupport i) (hdRatio i)]
  exact tiltAscentSet_card_le H M (U i) _ _ (hRU i)

theorem prescribedTiltReversalCount_signed_lower (H M r m : Nat)
    (hM : 0 < M) (d a : Fin m -> Nat) (U : Fin m -> Real)
    (delta : Real) (hr : 1 <= r)
    (hda : forall i, d i < a i)
    (hdSupport : forall i, r <= (primesBelow (primeAt (d i))).length)
    (haSupport : forall i, r <= (primesBelow (primeAt (a i))).length)
    (hdRatio : forall i, (densityRatio (primesBelow (primeAt (d i))) r : Real) <
      (primeGap (d i) : Real) + 1)
    (hRLow : forall i, 1 <= (densityRatio (primesBelow (primeAt (a i))) r : Real) -
      (primeGap (a i) : Real))
    (hRHigh : forall i, (densityRatio (primesBelow (primeAt (a i))) r : Real) -
      (primeGap (a i) : Real) <= (H : Real) + 1)
    (hULow : forall i, 1 <= U i - (primeGap (a i) : Real))
    (hUHigh : forall i, U i - (primeGap (a i) : Real) <= (H : Real) + 1)
    (hDelta : forall i, delta <=
      (densityRatio (primesBelow (primeAt (a i))) r : Real) - U i) :
    (m : Real) * ((M : Real) * delta - 1) <=
      (prescribedTiltReversalCount H M r m d a : Real) -
        (prescribedTiltReferenceCount H M m U a : Real) := by
  have h := tiltAscentSet_sum_lower (Finset.univ : Finset (Fin m)) H M hM
    (fun i => (densityRatio (primesBelow (primeAt (a i))) r : Real))
    U (fun i => (primeGap (a i) : Real)) delta
    (fun i _ => hRLow i) (fun i _ => hRHigh i)
    (fun i _ => hULow i) (fun i _ => hUHigh i) (fun i _ => hDelta i)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  rw [prescribedTiltReversalCount, prescribedTiltReferenceCount,
    Nat.cast_sum, Nat.cast_sum, <- Finset.sum_sub_distrib]
  convert h using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [prescribedTiltReversalSet_eq_ascentSet H M r (d i) (a i) hr
    (hda i) (hdSupport i) (haSupport i) (hdRatio i)]

theorem prescribedTilt_cells_have_reversals (H M r m j : Nat)
    (d a : Fin m -> Nat)
    (hsep : forall i l, i < l -> a i + 1 < d l) :
    HasAtLeastReversals
      ((oddsTiltLaw (tiltGridValue M j) (tiltGridValue_pos M j)).rankDensity (r + 1))
      ((Finset.univ : Finset (Fin m)).filter
        (fun i => Membership.mem (prescribedTiltReversalSet H M r (d i) (a i)) j)).card := by
  classical
  let s : Finset (Fin m) := Finset.univ.filter
    (fun i => Membership.mem (prescribedTiltReversalSet H M r (d i) (a i)) j)
  let e : Fin s.card -> Fin m := s.orderEmbOfFin rfl
  change HasAtLeastReversals _ s.card
  refine Exists.intro (fun i => d (e i)) (Exists.intro (fun i => a (e i))
    (And.intro ?_ ?_))
  next =>
    intro i
    have hi := (Finset.mem_filter.mp (s.orderEmbOfFin_mem rfl i)).2
    exact (Finset.mem_filter.mp hi).2
  next =>
    intro i l hil
    exact hsep (e i) (e l) ((s.orderEmbOfFin rfl).strictMono hil)

end PrimeFactorOscillations
