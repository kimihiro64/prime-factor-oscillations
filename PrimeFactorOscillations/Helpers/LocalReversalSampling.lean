/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LocalizedReversalCriterion
import PrimeFactorOscillations.Helpers.PrimeDensitySteps
import PrimeFactorOscillations.Mathlib.Data.Nat.Prime.ThreeWindowCells

/-!
# Explicit short-interval sampling for the reversal-count criteria

A fixed schedule starts cells at X+1 so every selected prime prefix is at
least X. Short pairs are selected by Nat.find; factorial crossings are
fixed by choice from an arithmetic predicate independent of RH and densities.
The cell number is at least X^(1/10)/80 eventually, and all prefixes lie
inside [X,X+X^(7/10)]. Strict separation and both gap bounds are retained.

Both RH count equivalences are assembled from the qualitative all-short-
interval prime-pair input at exponent3/5. That exact source premise remains
explicit; no project axiom or unproved analytic claim is installed.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Filter PrimeFactorUnimodality

def localCellWidth (X : Nat) : Nat := Nat.ceil (3 * (X : Real) ^ (3 / 5 : Real))

def localCellNumber (X : Nat) : Nat :=
  Nat.floor ((X : Real) ^ (7 / 10 : Real) / (10 * (localCellWidth X : Real)))

def localCellStart (X : Nat) (i : Fin (localCellNumber X)) : Nat :=
  X + 1 + 10 * localCellWidth X * i.val

/-- The precise short-interval consequence used here. It is an explicit
arithmetic input; the published Alweiss--Luo theorem is not an axiom. -/
def ShortIntervalPairInput (H : Nat) : Prop :=
  Filter.Eventually (fun X : Nat => forall z : Nat, X <= z -> z <= 2 * X ->
    exists i : Nat, z <= primeAt i /\
      primeAt (i + 1) <= z + localCellWidth X /\ primeGap i <= H) atTop

def selectedShortPair (H X z : Nat) : Nat := by
  classical
  exact if h : exists i : Nat, z <= primeAt i /\
      primeAt (i + 1) <= z + localCellWidth X /\ primeGap i <= H
    then Nat.find h else 0

theorem selectedShortPair_spec (H X z : Nat)
    (h : exists i : Nat, z <= primeAt i /\
      primeAt (i + 1) <= z + localCellWidth X /\ primeGap i <= H) :
    z <= primeAt (selectedShortPair H X z) /\
      primeAt (selectedShortPair H X z + 1) <= z + localCellWidth X /\
      primeGap (selectedShortPair H X z) <= H := by
  classical
  unfold selectedShortPair
  rw [dif_pos h]
  exact Nat.find_spec h

def selectedCellAscent (H X : Nat) (i : Fin (localCellNumber X)) : Nat :=
  selectedShortPair H X (localCellStart X i + 6 * localCellWidth X)

def CellDescentGeometry (H X : Nat) (d : Fin (localCellNumber X) -> Nat) : Prop :=
  (forall i, d i < selectedCellAscent H X i /\
    primeAt (d i) + (H + 3) <= primeAt (d i + 1) /\
    localCellStart X i <= primeAt (d i) /\
    primeAt (d i + 1) <= localCellStart X i + 4 * localCellWidth X) /\
  (forall i j, i < j -> selectedCellAscent H X i + 1 < d j)

def selectedCellDescent (H X : Nat) : Fin (localCellNumber X) -> Nat := by
  classical
  exact if h : exists d, CellDescentGeometry H X d then Classical.choose h else fun _ => 0

theorem selectedCellDescent_spec (H X : Nat)
    (h : exists d, CellDescentGeometry H X d) :
    CellDescentGeometry H X (selectedCellDescent H X) := by
  classical
  unfold selectedCellDescent
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem eventually_localCell_schedule (H : Nat) :
    Filter.Eventually (fun X : Nat => 3 <= X /\
      Nat.factorial (H + 3) + 2 <= localCellWidth X /\
      (1 / 80 : Real) * (X : Real) ^ (1 / 10 : Real) <= localCellNumber X /\
      ((10 * localCellWidth X * localCellNumber X : Nat) : Real) <=
        (X : Real) ^ (7 / 10 : Real)) atTop := by
  have hCast : Tendsto (fun n : Nat => (n : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hPower := (tendsto_rpow_atTop (by norm_num : (0 : Real) < 3 / 5)).comp hCast
  have hCount := (tendsto_rpow_atTop (by norm_num : (0 : Real) < 1 / 10)).comp hCast
  filter_upwards [eventually_ge_atTop (3 : Nat),
    hPower.eventually_ge_atTop ((Nat.factorial (H + 3) + 2 : Nat) : Real),
    hCount.eventually_ge_atTop 80] with X hX hBig hN
  dsimp only [Function.comp_def] at hBig hN
  have hx : (1 : Real) <= X := by exact_mod_cast (by omega : 1 <= X)
  have hxp : (0 : Real) < X := by linarith
  have hp : 0 < (X : Real) ^ (3 / 5 : Real) := Real.rpow_pos_of_pos hxp _
  have hpOne : (1 : Real) <= (X : Real) ^ (3 / 5 : Real) :=
    Real.one_le_rpow hx (by norm_num)
  have hLow : 3 * (X : Real) ^ (3 / 5 : Real) <= (localCellWidth X : Real) := Nat.le_ceil _
  have hHigh : (localCellWidth X : Real) <= 4 * (X : Real) ^ (3 / 5 : Real) := by
    have h := Nat.ceil_lt_add_one (show 0 <= 3 * (X : Real) ^ (3 / 5 : Real) by positivity)
    change (localCellWidth X : Real) < 3 * (X : Real) ^ (3 / 5 : Real) + 1 at h
    linarith
  have hh : 0 < (localCellWidth X : Real) := by linarith
  have hSpace : Nat.factorial (H + 3) + 2 <= localCellWidth X := by
    have h : ((Nat.factorial (H + 3) + 2 : Nat) : Real) <= localCellWidth X := by linarith
    exact_mod_cast h
  have hProduct : (X : Real) ^ (7 / 10 : Real) =
      (X : Real) ^ (1 / 10 : Real) * (X : Real) ^ (3 / 5 : Real) := by
    rw [<- Real.rpow_add hxp]
    norm_num
  have hDivLow : (X : Real) ^ (1 / 10 : Real) / 40 <=
      (X : Real) ^ (7 / 10 : Real) / (10 * (localCellWidth X : Real)) := by
    calc
      _ = (X : Real) ^ (7 / 10 : Real) / (40 * (X : Real) ^ (3 / 5 : Real)) := by
        rw [hProduct]
        field_simp [hp.ne']
      _ <= _ := div_le_div_of_nonneg_left (Real.rpow_nonneg hxp.le _)
        (by positivity) (by linarith)
  have hFloorLow := Nat.lt_floor_add_one
    ((X : Real) ^ (7 / 10 : Real) / (10 * (localCellWidth X : Real)))
  change (X : Real) ^ (7 / 10 : Real) / (10 * (localCellWidth X : Real)) <
    (localCellNumber X : Real) + 1 at hFloorLow
  have hNumber : (1 / 80 : Real) * (X : Real) ^ (1 / 10 : Real) <= localCellNumber X := by
    linarith
  have hFloorHigh : (localCellNumber X : Real) <=
      (X : Real) ^ (7 / 10 : Real) / (10 * (localCellWidth X : Real)) :=
    Nat.floor_le (by positivity)
  have hSpan := mul_le_mul_of_nonneg_left hFloorHigh
    (show 0 <= 10 * (localCellWidth X : Real) by positivity)
  have he : 10 * (localCellWidth X : Real) *
      ((X : Real) ^ (7 / 10 : Real) / (10 * (localCellWidth X : Real))) =
      (X : Real) ^ (7 / 10 : Real) := by field_simp [hh.ne']
  rw [he] at hSpan
  refine And.intro hX (And.intro hSpace (And.intro hNumber ?_))
  exact_mod_cast hSpan

theorem localReversalSampling_of_shortIntervalPairInput
    (H : Nat) (hSource : ShortIntervalPairInput H) :
    LocalReversalSampling H localCellNumber (selectedCellDescent H) (selectedCellAscent H) := by
  classical
  refine Exists.intro (1 / 80) (And.intro (by norm_num) ?_)
  filter_upwards [hSource, eventually_localCell_schedule H] with X hPairs hSchedule
  let h := localCellWidth X
  let m := localCellNumber X
  have hh : 0 < h := by dsimp [h]; omega
  have hxOne : (1 : Real) <= X := by exact_mod_cast (by omega : 1 <= X)
  have hPow : (X : Real) ^ (7 / 10 : Real) <= X := by
    calc
      _ <= (X : Real) ^ (1 : Real) :=
        Real.rpow_le_rpow_of_exponent_le hxOne (by norm_num)
      _ = _ := Real.rpow_one _
  have hSpan : 10 * h * m <= X := by
    have h := hSchedule.2.2.2.trans hPow
    exact_mod_cast h
  have hTop : forall i : Fin m, localCellStart X i + 7 * h <= X + 10 * h * m := by
    intro i
    have hmul := Nat.mul_le_mul_left (10 * h) (Nat.succ_le_of_lt i.isLt)
    rw [Nat.mul_succ] at hmul
    dsimp [localCellStart]
    change X + 1 + 10 * h * i.val + 7 * h <= X + 10 * h * m
    omega
  have hRange : forall i : Fin m, forall q : Nat, q <= 7 ->
      X <= localCellStart X i + q * h /\
      localCellStart X i + q * h <= 2 * X := by
    intro i q hq
    have hmul := Nat.mul_le_mul_right h hq
    have ht := hTop i
    have hz : X < localCellStart X i := by dsimp [localCellStart]; omega
    constructor <;> omega
  let u : Fin m -> Nat := fun i => selectedShortPair H X (localCellStart X i)
  let v : Fin m -> Nat := fun i => selectedShortPair H X (localCellStart X i + 3 * h)
  let a : Fin m -> Nat := selectedCellAscent H X
  have hleft : forall i, X + 1 + 10 * h * i.val <= primeAt (u i) /\
      primeAt (u i) <= X + 1 + 10 * h * i.val + h := by
    intro i
    have hrange := hRange i 0 (by omega)
    simp only [Nat.zero_mul, Nat.add_zero] at hrange
    have hi := selectedShortPair_spec H X (localCellStart X i)
      (hPairs _ hrange.1 hrange.2)
    have hmono := primeAt_strictMono (Nat.lt_succ_self (u i))
    change localCellStart X i <= primeAt (u i) /\
      primeAt (u i) <= localCellStart X i + h
    exact And.intro hi.1 (hmono.le.trans hi.2.1)
  have hmid : forall i, X + 1 + 10 * h * i.val + 3 * h <= primeAt (v i) /\
      primeAt (v i) <= X + 1 + 10 * h * i.val + 4 * h := by
    intro i
    have hrange := hRange i 3 (by omega)
    have hi := selectedShortPair_spec H X (localCellStart X i + 3 * h)
      (hPairs _ hrange.1 hrange.2)
    have hmono := primeAt_strictMono (Nat.lt_succ_self (v i))
    change localCellStart X i + 3 * h <= primeAt (v i) /\
      primeAt (v i) <= localCellStart X i + 4 * h
    refine And.intro hi.1 ?_
    have hUpper : primeAt (v i + 1) <= localCellStart X i + 3 * h + h := hi.2.1
    have he : localCellStart X i + 3 * h + h = localCellStart X i + 4 * h := by omega
    rw [he] at hUpper
    exact hmono.le.trans hUpper
  have hRight : forall i, localCellStart X i + 6 * h <= primeAt (a i) /\
      primeAt (a i + 1) <= localCellStart X i + 7 * h /\ primeGap (a i) <= H := by
    intro i
    have hrange := hRange i 6 (by omega)
    have hi := selectedShortPair_spec H X (localCellStart X i + 6 * h)
      (hPairs _ hrange.1 hrange.2)
    change localCellStart X i + 6 * h <= primeAt (a i) /\
      primeAt (a i + 1) <= localCellStart X i + 6 * h + h /\ primeGap (a i) <= H at hi
    exact And.intro hi.1 (And.intro (by omega) hi.2.2)
  have hExists : exists d, CellDescentGeometry H X d := by
    exact Nat.separated_gap_pairs_of_three_windows primeAt prime_primeAt primeAt_strictMono
      (X + 1) h (H + 3) m hSchedule.2.1 u v a hleft hmid
      (fun i => And.intro (hRight i).1 (hRight i).2.1)
  have hd := selectedCellDescent_spec H X hExists
  have hPrefix : forall i : Fin m, forall p : Nat,
      localCellStart X i <= p -> p <= localCellStart X i + 7 * h ->
      (X : Real) <= ((p - 1 : Nat) : Real) /\
      ((p - 1 : Nat) : Real) <= X + (X : Real) ^ (7 / 10 : Real) := by
    intro i p hlo hhi
    have hz : X < localCellStart X i := by dsimp [localCellStart]; omega
    have hLower : X <= p - 1 := by omega
    have hUpper : p - 1 <= X + 10 * h * m := by have ht := hTop i; omega
    have hUpperR : ((p - 1 : Nat) : Real) <= X + ((10 * h * m : Nat) : Real) := by
      exact_mod_cast hUpper
    refine And.intro (by exact_mod_cast hLower) ?_
    exact hUpperR.trans (add_le_add le_rfl hSchedule.2.2.2)
  refine And.intro hSchedule.2.2.1 (And.intro ?_ hd.2)
  intro i
  have hdi := hd.1 i
  have hai := hRight i
  have hmonoD := primeAt_strictMono (Nat.lt_succ_self (selectedCellDescent H X i))
  have hmonoA := primeAt_strictMono (Nat.lt_succ_self (a i))
  have hpd := hPrefix i (primeAt (selectedCellDescent H X i)) hdi.2.2.1 (by omega)
  have hpa := hPrefix i (primeAt (a i)) (by omega) (hmonoA.le.trans hai.2.1)
  have hGapD : H + 3 <= primeGap (selectedCellDescent H X i) := by
    unfold primeGap
    omega
  have hGapA : 2 <= primeGap (a i) := by
    apply primeGap_ge_two
    have hz : X < localCellStart X i := by dsimp [localCellStart]; omega
    omega
  exact And.intro hdi.1 (And.intro hGapD
    (And.intro hGapA (And.intro hai.2.2
    (And.intro hpd.1 (And.intro hpd.2 (And.intro hpa.1 hpa.2))))))

theorem shortIntervalPairInput_rh_iff_local_count (H : Nat)
    (hSource : ShortIntervalPairInput H) :
    RiemannHypothesis <->
      Filter.Eventually (fun X : Nat =>
        localReversalCount H localCellNumber (selectedCellDescent H) (selectedCellAscent H) X <=
          localReferenceCount H localCellNumber (selectedCellAscent H) X) atTop :=
  riemannHypothesis_iff_eventually_localReversalCount_le_reference H localCellNumber
    (selectedCellDescent H) (selectedCellAscent H)
    (localReversalSampling_of_shortIntervalPairInput H hSource)

theorem shortIntervalPairInput_rh_iff_local_count_power (H : Nat)
    (hSource : ShortIntervalPairInput H) :
    RiemannHypothesis <->
      exists C : Real, 0 < C /\ Filter.Eventually (fun X : Nat =>
        (localReversalCount H localCellNumber (selectedCellDescent H) (selectedCellAscent H) X : Real) -
          (localReferenceCount H localCellNumber (selectedCellAscent H) X : Real) <=
            C * (X : Real) ^ (1 / 10 : Real)) atTop :=
  riemannHypothesis_iff_eventually_localReversalCount_power_upper H localCellNumber
    (selectedCellDescent H) (selectedCellAscent H)
    (localReversalSampling_of_shortIntervalPairInput H hSource)


/-- Qualitative all-short-interval input: both endpoints are in [Y-h,Y].
This follows from Alweiss--Luo Corollary1.2 at exponent3/5, but that
analytic theorem has no installed proof in the current dependency closure. -/
def AllShortIntervalPairs (H : Nat) : Prop :=
  exists Y0 : Nat, forall Y h : Nat, Y0 <= Y ->
    (Y : Real) ^ (3 / 5 : Real) <= (h : Real) -> h <= Y ->
    exists i : Nat, Y - h <= primeAt i /\
      primeAt (i + 1) <= Y /\ primeGap i <= H

theorem shortIntervalPairInput_of_allShortIntervalPairs
    (H : Nat) (hSource : AllShortIntervalPairs H) : ShortIntervalPairInput H := by
  choose Y0 hY0 using hSource
  have hCast : Tendsto (fun n : Nat => (n : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hPower := (tendsto_rpow_atTop (by norm_num : (0 : Real) < 2 / 5)).comp hCast
  filter_upwards [eventually_ge_atTop (max Y0 1), hPower.eventually_ge_atTop 4] with X hx hBig
  dsimp only [Function.comp_def] at hBig
  have hxOne : (1 : Real) <= X := by exact_mod_cast (le_max_right Y0 1).trans hx
  have hxp : (0 : Real) < X := by linarith
  have hp : 0 < (X : Real) ^ (3 / 5 : Real) := Real.rpow_pos_of_pos hxp _
  have hpOne : (1 : Real) <= (X : Real) ^ (3 / 5 : Real) :=
    Real.one_le_rpow hxOne (by norm_num)
  have hLow : 3 * (X : Real) ^ (3 / 5 : Real) <= (localCellWidth X : Real) := Nat.le_ceil _
  have hHigh : (localCellWidth X : Real) <= 4 * (X : Real) ^ (3 / 5 : Real) := by
    have h := Nat.ceil_lt_add_one (show 0 <= 3 * (X : Real) ^ (3 / 5 : Real) by positivity)
    change (localCellWidth X : Real) < 3 * (X : Real) ^ (3 / 5 : Real) + 1 at h
    linarith
  have hWidth : localCellWidth X <= X := by
    have h := mul_le_mul_of_nonneg_right hBig hp.le
    have he : (X : Real) ^ (2 / 5 : Real) * (X : Real) ^ (3 / 5 : Real) = X := by
      rw [<- Real.rpow_add hxp]
      norm_num
    rw [he] at h
    exact_mod_cast hHigh.trans h
  intro z hxz hz
  have hyNat : z + localCellWidth X <= 3 * X := by omega
  have hyReal : ((z + localCellWidth X : Nat) : Real) <= 3 * (X : Real) := by exact_mod_cast hyNat
  have hThree : (3 : Real) ^ (3 / 5 : Real) <= 3 := by
    calc
      _ <= (3 : Real) ^ (1 : Real) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = _ := Real.rpow_one _
  have hPow : ((z + localCellWidth X : Nat) : Real) ^ (3 / 5 : Real) <= localCellWidth X := by
    calc
      _ <= (3 * (X : Real)) ^ (3 / 5 : Real) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hyReal (by norm_num)
      _ = (3 : Real) ^ (3 / 5 : Real) * (X : Real) ^ (3 / 5 : Real) :=
        Real.mul_rpow (by norm_num) hxp.le
      _ <= 3 * (X : Real) ^ (3 / 5 : Real) := mul_le_mul_of_nonneg_right hThree hp.le
      _ <= _ := hLow
  have h := hY0 (z + localCellWidth X) (localCellWidth X)
    (by have hcut := (le_max_left Y0 1).trans hx; omega) hPow (by omega)
  simpa only [Nat.add_sub_cancel] using h

theorem allShortIntervalPairs_rh_iff_local_count (H : Nat)
    (hSource : AllShortIntervalPairs H) :
    RiemannHypothesis <->
      Filter.Eventually (fun X : Nat =>
        localReversalCount H localCellNumber (selectedCellDescent H) (selectedCellAscent H) X <=
          localReferenceCount H localCellNumber (selectedCellAscent H) X) atTop :=
  shortIntervalPairInput_rh_iff_local_count H
    (shortIntervalPairInput_of_allShortIntervalPairs H hSource)

theorem allShortIntervalPairs_rh_iff_local_count_power (H : Nat)
    (hSource : AllShortIntervalPairs H) :
    RiemannHypothesis <->
      exists C : Real, 0 < C /\ Filter.Eventually (fun X : Nat =>
        (localReversalCount H localCellNumber (selectedCellDescent H) (selectedCellAscent H) X : Real) -
          (localReferenceCount H localCellNumber (selectedCellAscent H) X : Real) <=
            C * (X : Real) ^ (1 / 10 : Real)) atTop :=
  shortIntervalPairInput_rh_iff_local_count_power H
    (shortIntervalPairInput_of_allShortIntervalPairs H hSource)


end PrimeFactorOscillations
