/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Detector.LowGaussianSum
import PrimeFactorOscillations.Assembly.DetectorPackets.GeneralLowCentralEnergy

/-!
# GeneralLowGaussianEnergy

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

/-!
# Variable-geometry Gaussian central dyads

The complete compensated tuple bound is integrated against the actual joint
Gaussian density and summed over central dyads. Its leading variable-geometry
exponent is retained, with the full moment and height costs.
This is an unconditional probe input, not a zero-free theorem.
-/


noncomputable section
namespace PrimeFactorOscillations.GeneralLowGeometry
open scoped Classical SchwartzMap
open OAI OAI.SevenEighths
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic
open CanonicalQuadraticSieve InverseTerminalWidths InverseMoment InverseReflectedPhase
open CanonicalRowCompletion RayFourExpansion OAI.SevenEighths.ProbePhysical
local notation "Eis" => ActualEisensteinCubic.O
local notation "Id" => Ideal Eis
local instance : Fintype (Units Eis) :=
  @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

theorem low_central_gaussian_dyad_general (eta : HeckeFamily.Character) (S : Finset Id)
    (hS : forall P, Membership.mem S P -> P.IsMaximal) (hbad : fixedBadPrimes<=S)
    {K : Nat} (ell : Fin K->Real) (hell : forall i, 0<=ell i)
    (a b eps : Real) (ha : 0<a) (heps : 0<eps) (heps1 : eps<1)
    (W0 W1 : Real->Complex) (a0 b0 a1 b1 M : Real) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hM : 0<=M)
    (hW0 : Set.Subset (Function.support W0) (Set.Icc a0 b0))
    (hW1 : Set.Subset (Function.support W1) (Set.Icc a1 b1))
    (hW0s : ContDiff Real ((Top.top : ENat) : WithTop ENat) W0)
    (hW1s : ContDiff Real ((Top.top : ENat) : WithTop ENat) W1)
    (hWM : forall x, norm (W1 x)<=M) :
    Exists fun degree : Nat=>Exists fun C : Real=>
    0<C /\ Filter.Eventually (fun Z : Real=>1<Z /\
    forall Lambda : Real, 0<=Lambda -> Lambda<=1/5 -> (Finset.univ.sum ell)<=Lambda ->
    forall T : Fin K->Finset PrimeIdeal,
      (forall i P, Membership.mem (T i) P -> Supported P.val) ->
      (forall i P, Membership.mem (T i) P -> Not (Membership.mem S P.val)) ->
      Pairwise (fun i j=>Disjoint (T i) (T j)) ->
      (forall i P, Membership.mem (T i) P ->
        a*Z^(ell i)<=(Ideal.absNorm P.val:Real) /\
          (Ideal.absNorm P.val:Real)<=b*Z^(ell i)) ->
    forall (J : Finset (Fin K)) (X : Real), 0<X ->
      Z^(1+lowSelectedLength ell J-eps/2)<=X ->
      X<=Z^(1+lowSelectedLength ell J+eps/2) ->
    forall W : Fin K->Real->Complex, (forall i x, norm (W i x)<=1) ->
    forall (V : SchwartzMap Real Complex) (hV : HasCompactSupport (V:Real->Complex)),
      norm (lowCommonDyad eta (calibrationForSet S hS) W0 W1
        (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(ell i)) J
        (Z^(7/16-Lambda/2)) (Z^(9/16-Lambda/2)) X
        (Z^(1+lowSelectedLength ell J)) V hV)<=
        C*Z^(11/48-Lambda/4+254*eps)*
          gaussianJointMoment V hV degree (X/Z^(1+lowSelectedLength ell J))) Filter.atTop := by
  have hb := low_central_compensated_tuple_general eta S hS hbad ell hell
    a b eps ha heps heps1 W0 W1 a0 b0 a1 b1 M ha0 ha1 hab1 hM hW0 hW1 hW0s hW1s hWM
  choose degree C hC he using hb
  refine Exists.intro degree (Exists.intro C (And.intro hC ?_))
  filter_upwards [he] with Z hZ
  refine And.intro hZ.1 ?_
  intro Lambda hLambda0 hLambda1 hsum T hT hout hdis hnorm J X hX hXlo hXhi W hW V hV
  apply lowCommonDyad_norm_of_bound
  intro t
  simpa only [mul_assoc,mul_left_comm,mul_comm] using
    hZ.2 Lambda hLambda0 hLambda1 hsum T hT hout hdis hnorm J X hX hXlo hXhi W hW t

theorem low_central_gaussian_dyads_general (eta : HeckeFamily.Character) (S : Finset Id)
    (hS : forall P, Membership.mem S P -> P.IsMaximal) (hbad : fixedBadPrimes<=S)
    {K : Nat} (ell : Fin K->Real) (hell : forall i, 0<=ell i)
    (a b eps : Real) (ha : 0<a) (heps : 0<eps) (heps1 : eps<1)
    (W0 W1 : Real->Complex) (a0 b0 a1 b1 M : Real) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hM : 0<=M)
    (hW0 : Set.Subset (Function.support W0) (Set.Icc a0 b0))
    (hW1 : Set.Subset (Function.support W1) (Set.Icc a1 b1))
    (hW0s : ContDiff Real ((Top.top : ENat) : WithTop ENat) W0)
    (hW1s : ContDiff Real ((Top.top : ENat) : WithTop ENat) W1)
    (hWM : forall x, norm (W1 x)<=M)
    (V : SchwartzMap Real Complex) (hV : HasCompactSupport (V:Real->Complex)) :
    Exists fun C : Real=>0<C /\
    Filter.Eventually (fun Z : Real=>1<Z /\
    forall Lambda : Real, 0<=Lambda -> Lambda<=1/5 -> (Finset.univ.sum ell)<=Lambda ->
    forall T : Fin K->Finset PrimeIdeal,
      (forall i P, Membership.mem (T i) P -> Supported P.val) ->
      (forall i P, Membership.mem (T i) P -> Not (Membership.mem S P.val)) ->
      Pairwise (fun i j=>Disjoint (T i) (T j)) ->
      (forall i P, Membership.mem (T i) P ->
        a*Z^(ell i)<=(Ideal.absNorm P.val:Real) /\
          (Ideal.absNorm P.val:Real)<=b*Z^(ell i)) ->
    forall (J : Finset (Fin K)) (W : Fin K->Real->Complex),
      (forall i x, norm (W i x)<=1) ->
      let f := fun j : Nat=>if lowRemote Z (lowSelectedLength ell J) eps ((2:Real)^j) then 0 else
        norm (lowCommonDyad eta (calibrationForSet S hS) W0 W1
          (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(ell i)) J
          (Z^(7/16-Lambda/2)) (Z^(9/16-Lambda/2)) ((2:Real)^j)
          (Z^(1+lowSelectedLength ell J)) V hV)
      Summable f /\ tsum f<=C*Z^(11/48-Lambda/4+256*eps)) Filter.atTop := by
  have hb := low_central_gaussian_dyad_general eta S hS hbad ell hell
    a b eps ha heps heps1 W0 W1 a0 b0 a1 b1 M ha0 ha1 hab1 hM hW0 hW1 hW0s hW1s hWM
  choose degree C hC he using hb
  have hmb := gaussianJointMoment_summed V hV degree eps heps
  choose Cm hCm hm using hmb
  refine Exists.intro (C*Cm) (And.intro (mul_pos hC hCm) ?_)
  filter_upwards [he] with Z hZ
  refine And.intro hZ.1 ?_
  intro Lambda hLambda0 hLambda1 hsum T hT hout hdis hnorm J W hW
  let R := Z^(1+lowSelectedLength ell J)
  let f := fun j : Nat=>if lowRemote Z (lowSelectedLength ell J) eps ((2:Real)^j) then 0 else
    norm (lowCommonDyad eta (calibrationForSet S hS) W0 W1 (fun i=>canonicalSlotSupport (T i))
      W (fun i=>Z^(ell i)) J (Z^(7/16-Lambda/2)) (Z^(9/16-Lambda/2)) ((2:Real)^j) R V hV)
  have hz : 0<Z := lt_trans zero_lt_one hZ.1
  have hmoment := hm R (by dsimp [R];positivity)
  cases hmoment with
  | intro hsm hmb =>
    have hpow (k : Nat) : 1<=(2:Real)^k := by
      induction k with
      | zero => simp
      | succ k hk =>
        simpa only [pow_succ] using
          one_le_mul_of_one_le_of_one_le hk (show (1:Real)<=2 by norm_num)
    have hb (j : Nat) : f j<=(C*Z^(11/48-Lambda/4+254*eps))*
        (((2:Real)^j)^eps*gaussianJointMoment V hV degree ((2:Real)^j/R)) := by
      dsimp only [f]
      split_ifs with hj
      . exact mul_nonneg (by positivity)
          (mul_nonneg (by positivity) (gaussianJointMoment_nonneg V hV degree _))
      . have hcentral := not_lowRemote_bounds Z (lowSelectedLength ell J) eps ((2:Real)^j) hz hj
        apply (hZ.2 Lambda hLambda0 hLambda1 hsum T hT hout hdis hnorm J ((2:Real)^j)
          (by positivity) hcentral.1 hcentral.2 W hW V hV).trans
        have hp : 1<=((2:Real)^j)^eps := Real.one_le_rpow (hpow j) heps.le
        apply mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact le_mul_of_one_le_left (gaussianJointMoment_nonneg V hV degree _) hp
    have hn (j : Nat) : 0<=f j := by dsimp [f];split_ifs <;>positivity
    have hsumf := Summable.of_nonneg_of_le hn hb
      (hsm.mul_left (C*Z^(11/48-Lambda/4+254*eps)))
    refine And.intro hsumf ?_
    calc
      _ <= tsum (fun j : Nat=>(C*Z^(11/48-Lambda/4+254*eps))*
          (((2:Real)^j)^eps*gaussianJointMoment V hV degree ((2:Real)^j/R))) :=
        hsumf.tsum_le_tsum hb (hsm.mul_left _)
      _ = (C*Z^(11/48-Lambda/4+254*eps))*
          (tsum fun j : Nat=>((2:Real)^j)^eps*gaussianJointMoment V hV degree ((2:Real)^j/R)) :=
        tsum_mul_left
      _ <= (C*Z^(11/48-Lambda/4+254*eps))*(Cm*R^eps) :=
        mul_le_mul_of_nonneg_left hmb (by positivity)
      _ <= _ := by
        dsimp only [R]
        rw [<-Real.rpow_mul hz.le]
        calc
          _ = (C*Cm)*(Z^(11/48-Lambda/4+254*eps)*Z^((1+lowSelectedLength ell J)*eps)) := by ring
          _ <= _ := by
            rw [<-Real.rpow_add hz]
            apply mul_le_mul_of_nonneg_left ?_ (mul_pos hC hCm).le
            have hl := lowLength_bounds_general ell hell Lambda hsum J
            have hsel : lowSelectedLength ell J<=1/5 := by linarith [hl.1,hl.2.2.2]
            have hs : (1+lowSelectedLength ell J)*eps<=2*eps :=
              mul_le_mul_of_nonneg_right (by linarith) heps.le
            exact Real.rpow_le_rpow_of_exponent_le hZ.1.le (by linarith)

end PrimeFactorOscillations.GeneralLowGeometry

