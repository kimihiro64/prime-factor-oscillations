/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.ShiftedPrincipalRemainders

/-!
# ShiftedPrincipalNormalization

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-!
The shifted principal residue and zero signal have the same exact scale
factor. The final theorem compares the actual normalized ray principal
packet with its shifted signal uniformly over the live geometry parameter.
-/


noncomputable section

open scoped Classical BigOperators Topology ContDiff
open OAI
open OAI.SevenEighths
open Complex MeasureTheory Filter

namespace PrimeFactorOscillations.ShiftedPrincipalNormalization

open HeckeFamily ProbePhysical ProbeFiniteProductBounds ProbeRaySlots
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
open ProbePrincipalNormalizer ProbePrincipalNormalized
open PrimeFactorOscillations.FlexibleMomentInput
open PrimeFactorOscillations.ShiftedPrincipalRemainders
open OAI.CompletedGauss

lemma shifted_x_residue_power (Z theta : Real) (hZ : 0 < Z) :
    ((Z ^ (17 / 48 - theta / 2) : Real) : Complex) ^ (1 / 3 : Complex) =
      (Z ^ (-theta / 6) : Real) *
        ((Z ^ (17 / 48 : Real) : Real) : Complex) ^ (1 / 3 : Complex) := by
  have hz : Not ((Z : Complex) = 0) := Complex.ofReal_ne_zero.mpr (ne_of_gt hZ)
  rw [<- Complex.cpow_mul_ofReal_nonneg hZ.le (17 / 48 - theta / 2) (1 / 3),
    <- Complex.cpow_mul_ofReal_nonneg hZ.le (17 / 48) (1 / 3),
    Complex.ofReal_cpow hZ.le, <- Complex.cpow_add _ _ hz]
  congr 1
  push_cast
  ring

lemma double_residue_shift (W0 W1 : SchwartzMap Real Complex)
    (M : Ideal HeckeFamily.O) [NeZero M] (chi : Character)
    (Z theta Ynew Yold : Real) (hZ : 0 < Z) (s : Complex)
    (H B : Complex -> Complex -> Complex) :
    fixedPrincipalResidue M ^ 2 / 6 *
        sourceMultiplier W0 W1 (Z ^ (17 / 48 - theta / 2)) Ynew Z chi s H B 1 (1 / 6) =
      (Z ^ (-theta / 6) : Real) *
        (fixedPrincipalResidue M ^ 2 / 6 *
          sourceMultiplier W0 W1 (Z ^ (17 / 48 : Real)) Yold Z chi s H B 1 (1 / 6)) := by
  rw [source_double_residue, source_double_residue, shifted_x_residue_power Z theta hZ]
  ring

lemma residue_integral_shift (W0 W1 : SchwartzMap Real Complex)
    (M : Ideal HeckeFamily.O) [NeZero M] (chi : Character)
    (Z theta Ynew Yold a : Real) (hZ : 0 < Z)
    (H B : Complex -> Complex -> Complex -> Complex) :
    sourceResidueIntegral W0 W1 M chi a (Z ^ (17 / 48 - theta / 2)) Ynew Z H B =
      (Z ^ (-theta / 6) : Real) *
        sourceResidueIntegral W0 W1 M chi a (Z ^ (17 / 48 : Real)) Yold Z H B := by
  unfold sourceResidueIntegral
  simp_rw [double_residue_shift W0 W1 M chi Z theta Ynew Yold hZ]
  unfold verticalIntegral
  rw [integral_const_mul]
  ring

lemma signal_shift (chi : Character) (H : Complex -> Complex)
    (c Z theta : Real) (hZ : 0 < Z) :
    HeckeSignal.signal chi H (c - theta / 6) Z =
      (Z ^ (-theta / 6) : Real) * HeckeSignal.signal chi H c Z := by
  have hz : Not ((Z : Complex) = 0) := Complex.ofReal_ne_zero.mpr (ne_of_gt hZ)
  unfold HeckeSignal.signal
  rw [Complex.ofReal_cpow hZ.le]
  have heq : ((c - theta / 6 : Real) : Complex) =
      ((-theta / 6 : Real) : Complex) + (c : Complex) := by
    push_cast
    ring
  rw [heq, Complex.cpow_add _ _ hz]
  ring

theorem actual_ray_principal_comparison_shifted {K : Nat}
    (M : Ideal HeckeFamily.O) [NeZero M] [Finite (HasQuotient.Quotient HeckeFamily.O M)]
    (H : Subgroup (Units (HasQuotient.Quotient HeckeFamily.O M)))
    (hH : RayOrthogonality.globalUnits M <= H)
    (eta : Character) (S : Finset (Ideal HeckeFamily.O)) (hS : SourceExclusions S)
    (c d B ellMin : Real) (hc : 0 < c) (hd : c <= d) (hB : 0 <= B)
    (hmin : 0 < ellMin) (ell : Fin K -> Real)
    (hell : forall j, ellMin <= ell j) (hdis : Function.Injective ell)
    (hsum : Finset.univ.sum ell = (1 / 6 : Real))
    (W : Fin K -> Real -> Real)
    (hW : forall j, ContDiff Real ((Top.top : ENat) : WithTop ENat) (W j))
    (hcompact : forall j, HasCompactSupport (W j))
    (hsupp : forall j, Set.Subset (Function.support (W j)) (Set.Ioo c d))
    (hWbounds : forall j y, 0 <= W j y /\ W j y <= B)
    (hne : forall j, Not (W j = 0))
    (W0 W1 : SchwartzMap Real Complex) (a0 b0 a1 b1 : Real)
    (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Set.Subset (Function.support W0) (Set.Icc a0 b0))
    (hW1 : Set.Subset (Function.support W1) (Set.Icc a1 b1))
    (hr0 : forall y, (W0 y).im = 0) (hr1 : forall y, (W1 y).im = 0)
    (hp0 : forall y, 0 <= (W0 y).re) (hp1 : forall y, 0 <= (W1 y).re)
    (hn0 : Not (W0 = 0)) (hn1 : Not (W1 = 0))
    (e nu : Real) (he : 0 < e) (hehi : e <= (1 / 1000 : Real)) (hnu : 0 < nu) :
    letI : NeZero (S.prod (fun P => P)) :=
      NeZero.mk (fixedPrimeProduct_ne_zero S hS.prime)
    exists C : Real, 0 < C /\
      Filter.Eventually (fun Z : Real =>
        forall theta : Real, 0 <= theta -> theta <= (1 / 30 : Real) ->
        let T := fun j =>
          pool (RayQuotient.identityClass M H) S c d (Z ^ (ell j))
        let normer := sourceResidueConstant W0 W1 (S.prod (fun P => P)) *
          (Probe.principalScalar Finset.univ Z (1 / 6)
            (slotMass T (residueWeights W (fun j => Z ^ (ell j)))) : Complex)
        Not (normer = 0) /\
          norm ((Finset.univ.sum (fun P : (forall j, T j) =>
              (Finset.univ.prod (fun j =>
                (W j ((Ideal.absNorm (P j).val.val : Real) / Z ^ (ell j)) : Complex))) *
              principalRowIntegral eta S (fun j => primaryGenerator (P j).val.val)
                W0 W1 (Z ^ (17 / 48 - theta / 2))
                (Z ^ (23 / 48 - theta / 2)) Z)) / normer -
            HeckeSignal.signal (eta.excludePrimes S hS.prime) (sourceCorrection eta S)
              (-11 / 16 - theta / 6) Z) <=
            C * (Z ^ (3 / 16 - theta / 6 - 17 / 48000 + nu : Real) +
              Z ^ (3 / 16 - theta / 6 + e - (7 / 8) * ellMin : Real)))
        Filter.atTop := by
  let : NeZero (S.prod (fun P => P)) :=
    NeZero.mk (fixedPrimeProduct_ne_zero S hS.prime)
  refine Exists.elim (shifted_physical_principal_remainder eta S hS c d B hc hd hB
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 e he hehi (K := K)) ?_
  intro C0 hC0
  have hC0pos : 0 < C0 := hC0.1
  refine Exists.elim (normalized_actual_window_residue S hS eta
    (by linarith only [he] : (7 / 8 : Real) < (7 / 8 : Real) + e)
    (by linarith only [hehi]) (by linarith only [reference_beta_upper, he])
    (Finset.univ : Finset (Fin K))) ?_
  intro D hD
  have hDnonneg : 0 <= D := hD.1
  let cs := sourceResidueConstant W0 W1 (S.prod (fun P => P))
  let C := C0 / e * norm (Inv.inv cs) + D * c ^ (-(7 / 8 : Real)) + 1
  refine Exists.intro C (And.intro (by dsimp [C]; positivity) ?_)
  have hpos (j : Fin K) : Set.Subset (tsupport (W j)) (Set.Ioi (0 : Real)) := by
    apply Set.Subset.trans
      (closure_minimal (Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self) isClosed_Icc)
    intro y hy
    exact hc.trans_le hy.1
  filter_upwards [
    power_pool_thresholds (RayQuotient.identityClass M H) S eta c d ellMin
      hc hd hmin ell hell,
    power_ray_mass_and_normalizer M H hH S W c d hc hd hsupp hW hcompact hpos
      (fun j y => (hWbounds j y).1) hne ell
      (fun j => hmin.trans_le (hell j)) nu hnu,
    power_pool_tuples_eventually_injective (RayQuotient.identityClass M H) S
      (fun _ => c) (fun _ => d) ell (fun _ => hc) (fun _ => hd) hdis
    ] with Z hthreshold hmass htuple
  intro theta htheta hthetaHi
  have hZ : 1 <= Z := hthreshold.1
  have h480 := hthreshold.2.1
  have hsmall := hthreshold.2.2.1
  have hslot := hthreshold.2.2.2.1
  have hpool := hthreshold.2.2.2.2
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  let T := fun j => pool (RayQuotient.identityClass M H) S c d (Z ^ (ell j))
  let BK := windowMultiplier eta Finset.univ T (fun j x => (W j x : Complex))
    (fun j => Z ^ (ell j))
  let normer := cs * (Probe.principalScalar Finset.univ Z (1 / 6)
    (slotMass T (residueWeights W (fun j => Z ^ (ell j)))) : Complex)
  let q : Complex := (Z ^ (-theta / 6) : Real)
  have hr := hD.2 W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    T W (fun j => Z ^ (ell j)) (c * Z ^ ellMin)
    (Z ^ (23 / 48 - theta / 2)) Z h480 hsmall
    (fun j _ p _ => (hWbounds j _).1) (fun j _ p hp => (hpool j p hp).1)
    (fun j _ p hp => (hpool j p hp).2.1) (fun j _ => hmass.1 j) hZ
  dsimp only at hr
  have hErrorEq :
      sourceResidueIntegral W0 W1 (S.prod (fun P => P)) (eta.excludePrimes S hS.prime)
        ((7 / 8 : Real) + e) (Z ^ (17 / 48 - theta / 2))
        (Z ^ (23 / 48 - theta / 2)) Z (globalClosedCorrection eta S) BK / normer -
        HeckeSignal.signal (eta.excludePrimes S hS.prime) (sourceCorrection eta S)
          (-11 / 16 - theta / 6) Z =
      q * (sourceResidueIntegral W0 W1 (S.prod (fun P => P))
          (eta.excludePrimes S hS.prime) ((7 / 8 : Real) + e)
          (Z ^ (17 / 48 : Real)) (Z ^ (23 / 48 - theta / 2)) Z
          (globalClosedCorrection eta S) BK / normer -
        HeckeSignal.signal (eta.excludePrimes S hS.prime) (sourceCorrection eta S)
          (-11 / 16) Z) := by
    rw [residue_integral_shift W0 W1 (S.prod (fun P => P))
      (eta.excludePrimes S hS.prime) Z theta
      (Z ^ (23 / 48 - theta / 2)) (Z ^ (23 / 48 - theta / 2))
      ((7 / 8 : Real) + e) hZ0]
    rw [signal_shift (eta.excludePrimes S hS.prime) (sourceCorrection eta S)
      (-11 / 16) Z theta hZ0]
    dsimp only [q]
    ring
  have hq : norm q = Z ^ (-theta / 6) := by
    dsimp only [q]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hZ0.le _)]
  have hResidueError :
      norm (sourceResidueIntegral W0 W1 (S.prod (fun P => P))
        (eta.excludePrimes S hS.prime) ((7 / 8 : Real) + e)
        (Z ^ (17 / 48 - theta / 2)) (Z ^ (23 / 48 - theta / 2)) Z
        (globalClosedCorrection eta S) BK / normer -
        HeckeSignal.signal (eta.excludePrimes S hS.prime) (sourceCorrection eta S)
          (-11 / 16 - theta / 6) Z) <=
      D * Z ^ (((7 / 8 : Real) + e) - 11 / 16 - theta / 6) *
        (c * Z ^ ellMin) ^ (-(7 / 8 : Real)) := by
    rw [hErrorEq, norm_mul, hq]
    calc
      _ <= Z ^ (-theta / 6) *
          (D * Z ^ (((7 / 8 : Real) + e) - 11 / 16) *
            (c * Z ^ ellMin) ^ (-(7 / 8 : Real))) :=
        mul_le_mul_of_nonneg_left hr.2.2 (Real.rpow_nonneg hZ0.le _)
      _ = _ := by
        rw [show (((7 / 8 : Real) + e) - 11 / 16 - theta / 6) =
          (-theta / 6) + (((7 / 8 : Real) + e) - 11 / 16) by ring, Real.rpow_add hZ0]
        ring
  dsimp only
  refine And.intro hr.1 ?_
  have hraw := hC0.2 theta htheta hthetaHi ell hsum W hWbounds
    (fun j => Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self)
    T (fun j p hp => (hpool j p hp).2.2) htuple Z hZ
    (fun j => (hslot j).1) (fun j => (hslot j).2)
  have hinv : norm (Inv.inv normer) <= norm (Inv.inv cs) * Z ^ nu := by
    dsimp only [normer]
    rw [mul_inv_rev, norm_mul, <- Complex.ofReal_inv, Complex.norm_real]
    simpa only [hsum, Real.norm_eq_abs, mul_comm] using
      mul_le_mul_of_nonneg_left hmass.2 (norm_nonneg (Inv.inv cs))
  have hh := ProbePrincipalNormalized.normalized_error _ _ _ normer _ _ _
    (by positivity) hraw hinv hResidueError
  have hpw : (c * Z ^ ellMin) ^ (-(7 / 8 : Real)) =
      c ^ (-(7 / 8 : Real)) * Z ^ (-(7 / 8 : Real) * ellMin) := by
    rw [Real.mul_rpow hc.le (Real.rpow_nonneg hZ0.le _), <- Real.rpow_mul hZ0.le]
    congr 2
    ring
  have heq1 :
      (C0 / e * Z ^ (3 / 16 - theta / 6 - 17 / 48000 : Real)) *
        (norm (Inv.inv cs) * Z ^ nu) =
      (C0 / e * norm (Inv.inv cs)) *
        Z ^ (3 / 16 - theta / 6 - 17 / 48000 + nu : Real) := by
    rw [Real.rpow_add hZ0]
    ring
  have heq2 :
      D * Z ^ (((7 / 8 : Real) + e) - 11 / 16 - theta / 6) *
        (c * Z ^ ellMin) ^ (-(7 / 8 : Real)) =
      (D * c ^ (-(7 / 8 : Real))) *
        Z ^ (3 / 16 - theta / 6 + e - (7 / 8) * ellMin : Real) := by
    rw [hpw, show (3 / 16 - theta / 6 + e - (7 / 8) * ellMin : Real) =
      (((7 / 8 : Real) + e) - 11 / 16 - theta / 6) +
        (-(7 / 8 : Real) * ellMin) by ring, Real.rpow_add hZ0]
    ring
  apply hh.trans
  rw [heq1, heq2]
  have h1 : C0 / e * norm (Inv.inv cs) <= C := by
    dsimp only [C]
    have hp : 0 <= D * c ^ (-(7 / 8 : Real)) :=
      mul_nonneg hD.1 (Real.rpow_nonneg hc.le _)
    linarith only [hp]
  have h2 : D * c ^ (-(7 / 8 : Real)) <= C := by
    dsimp only [C]
    have hp : 0 <= C0 / e * norm (Inv.inv cs) :=
      mul_nonneg (div_nonneg hC0.1.le he.le) (norm_nonneg _)
    linarith only [hp]
  calc
    _ <= C * Z ^ (3 / 16 - theta / 6 - 17 / 48000 + nu : Real) +
        C * Z ^ (3 / 16 - theta / 6 + e - (7 / 8) * ellMin : Real) :=
      add_le_add
        (mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hZ0.le _))
        (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hZ0.le _))
    _ = _ := by ring

end PrimeFactorOscillations.ShiftedPrincipalNormalization
