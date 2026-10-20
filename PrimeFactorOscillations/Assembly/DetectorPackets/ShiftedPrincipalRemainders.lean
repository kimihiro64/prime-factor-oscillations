/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Proof.DetectorPackets.IndependentMomentInput

/-!
# ShiftedPrincipalRemainders

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-!
Actual principal remainder integrals at shifted physical scales. The
reference contour uses the proved beta<=7/8. Constants are chosen before
the live theta and finite slot/window data. No stronger zero-free boundary
is asserted by this component theorem.
-/


noncomputable section

open scoped Classical BigOperators
open Complex MeasureTheory
open OAI.SevenEighths

namespace PrimeFactorOscillations.ShiftedPrincipalRemainders

open HeckeFamily ProbePhysical ProbeFiniteProductBounds
open PrincipalMellinResidues PrincipalSignalComparison ProbeMellinBoundary
open ProbePrincipalRemainderBounds ProbePrincipalPhysical
open PrimeFactorOscillations.FlexibleMomentInput
open OAI.CompletedGauss

lemma shifted_scale_identity {iota : Type*} (J : Finset iota) (ell : iota -> Real)
    (hell : J.sum ell = (1 / 6 : Real)) (Z a theta xi upsilon : Real) (hZ : 0 < Z) :
    scalePower (Z ^ (17 / 48 - theta / 2)) (Z ^ (23 / 48 - theta / 2))
        Z a xi upsilon * J.prod (fun j => (Z ^ (ell j)) ^ xi) =
      Z ^ (a - 11 / 16 - theta / 6 +
        (13 / 16 + theta / 2) * (xi - 1 / 6) +
        (23 / 48 - theta / 2) * (upsilon - 1)) := by
  have hp : J.prod (fun j => (Z ^ (ell j)) ^ xi) = Z ^ ((1 / 6) * xi) := by
    simp only [<- Real.rpow_mul hZ.le]
    rw [<- Real.rpow_sum_of_pos hZ, <- Finset.sum_mul, hell]
  rw [hp, scalePower, <- Real.rpow_mul hZ.le, <- Real.rpow_mul hZ.le]
  rw [<- Real.rpow_add hZ, <- Real.rpow_add hZ, <- Real.rpow_add hZ]
  congr 1
  ring

lemma shifted_w_scale_identity {iota : Type*} (J : Finset iota) (ell : iota -> Real)
    (hell : J.sum ell = (1 / 6 : Real)) (Z a theta e : Real) (hZ : 0 < Z) :
    scalePower (Z ^ (17 / 48 - theta / 2)) (Z ^ (23 / 48 - theta / 2))
        Z a (1 / 6 + e) (19 / 20) *
        J.prod (fun j => (Z ^ (ell j)) ^ (1 / 6 + e)) =
      Z ^ (a - 11 / 16 - theta / 6 +
        (13 / 16 + theta / 2) * e - (23 / 48 - theta / 2) / 20) := by
  rw [shifted_scale_identity J ell hell Z a theta (1 / 6 + e) (19 / 20) hZ]
  congr 1
  ring

lemma shifted_z_scale_identity {iota : Type*} (J : Finset iota) (ell : iota -> Real)
    (hell : J.sum ell = (1 / 6 : Real)) (Z a theta : Real) (hZ : 0 < Z) :
    scalePower (Z ^ (17 / 48 - theta / 2)) (Z ^ (23 / 48 - theta / 2))
        Z a (33 / 200) 1 * J.prod (fun j => (Z ^ (ell j)) ^ (33 / 200 : Real)) =
      Z ^ (a - 11 / 16 - theta / 6 - (13 / 16 + theta / 2) / 600) := by
  rw [shifted_scale_identity J ell hell Z a theta (33 / 200) 1 hZ]
  congr 1
  ring

lemma shifted_w_exponent (theta e : Real) (htheta : 0 <= theta)
    (hthetaHi : theta <= (1 / 30 : Real)) (he : e <= (1 / 1000 : Real)) :
    ((7 / 8 : Real) + e) - 11 / 16 - theta / 6 +
        (13 / 16 + theta / 2) * e - (23 / 48 - theta / 2) / 20 <=
      3 / 16 - theta / 6 - 17 / 48000 := by
  have hWeight : 0 <= (13 / 16 : Real) + theta / 2 := by linarith only [htheta]
  have hm := mul_le_mul_of_nonneg_left he hWeight
  nlinarith only [he, hm, hthetaHi]

lemma shifted_z_exponent (theta e : Real) (htheta : 0 <= theta)
    (he : e <= (1 / 1000 : Real)) :
    ((7 / 8 : Real) + e) - 11 / 16 - theta / 6 -
        (13 / 16 + theta / 2) / 600 <=
      3 / 16 - theta / 6 - 17 / 48000 := by
  linarith only [htheta, he]

theorem shifted_ordered_remainders {iota : Type*}
    (eta : Character) (S : Finset (Ideal HeckeFamily.O)) (hS : SourceExclusions S)
    (J : Finset iota) (c d B : Real) (hc : 0 < c) (hd : c <= d) (hB : 0 <= B)
    (W0 W1 : SchwartzMap Real Complex) (a0 b0 a1 b1 : Real)
    (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Set.Subset (Function.support W0) (Set.Icc a0 b0))
    (hW1 : Set.Subset (Function.support W1) (Set.Icc a1 b1))
    (e : Real) (he : 0 < e) (hehi : e <= (1 / 1000 : Real)) :
    exists C : Real, 0 < C /\
      forall theta : Real, 0 <= theta -> theta <= (1 / 30 : Real) ->
      forall ell : iota -> Real, J.sum ell = (1 / 6 : Real) ->
      forall W : iota -> Real -> Real,
        (forall j, Membership.mem J j -> forall x, 0 <= W j x /\ W j x <= B) ->
        (forall j, Membership.mem J j ->
          Set.Subset (Function.support (W j)) (Set.Icc c d)) ->
      forall T : iota -> Finset PrimeIdeal,
        (forall j, Membership.mem J j -> forall p, Membership.mem (T j) p ->
          Not (Membership.mem S p.val)) ->
      forall Z : Real, 1 <= Z ->
        (forall j, Membership.mem J j -> 480 <= c * Z ^ (ell j)) ->
        (forall j, Membership.mem J j ->
          (Ideal.absNorm eta.modulus : Real) < c * Z ^ (ell j)) ->
      let K0 := fun s =>
        sourceMultiplier W0 W1 (Z ^ (17 / 48 - theta / 2))
          (Z ^ (23 / 48 - theta / 2)) Z (eta.excludePrimes S hS.prime) s
          (globalClosedCorrection eta S s)
          (windowMultiplier eta J T (fun j x => (W j x : Complex))
            (fun j => Z ^ (ell j)) s)
      let pi := fixedSourcePrincipal S hS.prime
      norm (verticalIntegral ((7 / 8 : Real) + e) (fun s =>
        verticalIntegral (1 / 6 + e) (fun z =>
          verticalIntegral (19 / 20) (fun w =>
            K0 s w z * LFunction pi (6 * z) * LFunction pi w)))) <=
          C / e * Z ^ (3 / 16 - theta / 6 - 17 / 48000 : Real) /\
      norm (HeckeReciprocal.regularizedL pi 1 *
        verticalIntegral ((7 / 8 : Real) + e) (fun s =>
          verticalIntegral (33 / 200) (fun z =>
            K0 s 1 z * LFunction pi (6 * z)))) <=
          C * Z ^ (3 / 16 - theta / 6 - 17 / 48000 : Real) := by
  refine Exists.elim (ordered_remainders_scale_bound eta S hS J c d B hc hd hB
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 ((7 / 8 : Real) + e) e
    (And.intro (by linarith only [he]) (by linarith only [hehi]))
    (by linarith only [reference_beta_upper, he]) he
    (by linarith only [hehi])) ?_
  intro C hC
  refine Exists.intro C (And.intro hC.1 ?_)
  intro theta htheta hthetaHi ell hell W hW hsupp T hT Z hZ hthreshold hmod
  dsimp only
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have hh := hC.2 W hW hsupp (fun j => Z ^ (ell j))
    (fun _ _ => Real.rpow_pos_of_pos hZ0 _) hthreshold hmod T hT
    (Z ^ (17 / 48 - theta / 2)) (Z ^ (23 / 48 - theta / 2)) Z
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0
  dsimp only at hh
  rw [shifted_w_scale_identity J ell hell Z ((7 / 8 : Real) + e) theta e hZ0,
    shifted_z_scale_identity J ell hell Z ((7 / 8 : Real) + e) theta hZ0] at hh
  exact And.intro
    (hh.1.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (shifted_w_exponent theta e htheta hthetaHi hehi))
      (div_nonneg hC.1.le he.le)))
    (hh.2.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (shifted_z_exponent theta e htheta hehi))
      hC.1.le))

theorem shifted_physical_principal_remainder {K : Nat}
    (eta : Character) (S : Finset (Ideal HeckeFamily.O)) (hS : SourceExclusions S)
    (c d B : Real) (hc : 0 < c) (hd : c <= d) (hB : 0 <= B)
    (W0 W1 : SchwartzMap Real Complex) (a0 b0 a1 b1 : Real)
    (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Set.Subset (Function.support W0) (Set.Icc a0 b0))
    (hW1 : Set.Subset (Function.support W1) (Set.Icc a1 b1))
    (e : Real) (he : 0 < e) (hehi : e <= (1 / 1000 : Real)) :
    letI : NeZero (S.prod (fun P => P)) :=
      NeZero.mk (fixedPrimeProduct_ne_zero S hS.prime)
    exists C : Real, 0 < C /\
      forall theta : Real, 0 <= theta -> theta <= (1 / 30 : Real) ->
      forall ell : Fin K -> Real, Finset.univ.sum ell = (1 / 6 : Real) ->
      forall W : Fin K -> Real -> Real,
        (forall j x, 0 <= W j x /\ W j x <= B) ->
        (forall j, Set.Subset (Function.support (W j)) (Set.Icc c d)) ->
      forall T : Fin K -> Finset PrimeIdeal,
        (forall j p, Membership.mem (T j) p -> Not (Membership.mem S p.val)) ->
        (forall P : (forall j, T j), Function.Injective (fun j => (P j).val)) ->
      forall Z : Real, 1 <= Z ->
        (forall j, 480 <= c * Z ^ (ell j)) ->
        (forall j, (Ideal.absNorm eta.modulus : Real) < c * Z ^ (ell j)) ->
      norm ((Finset.univ.sum (fun P : (forall j, T j) =>
          (Finset.univ.prod (fun j =>
            (W j ((Ideal.absNorm (P j).val.val : Real) / Z ^ (ell j)) : Complex))) *
          principalRowIntegral eta S
            (fun j => primaryGenerator (P j).val.val) W0 W1
            (Z ^ (17 / 48 - theta / 2)) (Z ^ (23 / 48 - theta / 2)) Z)) -
        sourceResidueIntegral W0 W1 (S.prod (fun P => P))
          (eta.excludePrimes S hS.prime) ((7 / 8 : Real) + e)
          (Z ^ (17 / 48 - theta / 2)) (Z ^ (23 / 48 - theta / 2)) Z
          (globalClosedCorrection eta S)
          (windowMultiplier eta Finset.univ T (fun j x => (W j x : Complex))
            (fun j => Z ^ (ell j)))) <=
        C / e * Z ^ (3 / 16 - theta / 6 - 17 / 48000 : Real) := by
  let : NeZero (S.prod (fun P => P)) :=
    NeZero.mk (fixedPrimeProduct_ne_zero S hS.prime)
  refine Exists.elim (shifted_ordered_remainders eta S hS
    (Finset.univ : Finset (Fin K)) c d B hc hd hB
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 e he hehi) ?_
  intro C hC
  refine Exists.intro (2 * C) (And.intro (by linarith only [hC.1]) ?_)
  intro theta htheta hthetaHi ell hell W hW hsupp T hT hdis Z hZ hthreshold hmod
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have hb := hC.2 theta htheta hthetaHi ell hell W
    (fun j _ => hW j) (fun j _ => hsupp j) T (fun j _ p hp => hT j p hp)
    Z hZ (fun j _ => hthreshold j) (fun j _ => hmod j)
  dsimp only at hb
  have heq := principal_physical_pool_ordered eta S hS T hT hdis
    (fun j p => (W j ((Ideal.absNorm p.val : Real) / Z ^ (ell j)) : Complex))
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (Z ^ (17 / 48 - theta / 2)) (Z ^ (23 / 48 - theta / 2)) Z
    ((7 / 8 : Real) + e) e (Real.rpow_pos_of_pos hZ0 _)
    (Real.rpow_pos_of_pos hZ0 _) hZ0
    (by linarith only [he]) (by linarith only [hehi])
    (by linarith only [reference_beta_upper, he]) he (by linarith only [hehi])
  dsimp only at heq
  have hres (F : Complex -> Complex) :
      (HeckeReciprocal.regularizedL (fixedSourcePrincipal S hS.prime) 1) ^ 2 / 6 *
          verticalIntegral ((7 / 8 : Real) + e) F =
        verticalIntegral ((7 / 8 : Real) + e)
          (fun s => fixedPrincipalResidue (S.prod (fun P => P)) ^ 2 / 6 * F s) := by
    rw [verticalIntegral, verticalIntegral, integral_const_mul]
    dsimp only [fixedPrincipalResidue, fixedPrincipal, fixedSourcePrincipal]
    ring
  rw [heq]
  unfold sourceResidueIntegral windowMultiplier
  rw [hres, add_sub_cancel_right]
  have hn := (norm_add_le _ _).trans (add_le_add hb.1 hb.2)
  have hCe : C <= C / e := by
    calc
      C = C / 1 := by ring
      _ <= C / e := div_le_div_of_nonneg_left hC.1.le he (by linarith only [hehi])
  have hp : 0 <= Z ^ (3 / 16 - theta / 6 - 17 / 48000 : Real) :=
    Real.rpow_nonneg hZ0.le _
  apply hn.trans
  calc
    _ <= C / e * Z ^ (3 / 16 - theta / 6 - 17 / 48000 : Real) +
        (C / e) * Z ^ (3 / 16 - theta / 6 - 17 / 48000 : Real) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hCe hp)
    _ = (2 * C) / e * Z ^ (3 / 16 - theta / 6 - 17 / 48000 : Real) := by ring

end PrimeFactorOscillations.ShiftedPrincipalRemainders
