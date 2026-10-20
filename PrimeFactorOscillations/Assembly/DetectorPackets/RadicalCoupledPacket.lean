/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.PrimeRows.CentralTargetCost
import PrimeFactorOscillations.Proof.DetectorPackets.QuadraticLowKernelConductor

/-!
# RadicalCoupledPacket

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
# Reduced primitive conductor in the complete low-row packet

Use the actual primitive presentation before the reflected numerator is
bounded. The reciprocal, calibration and all fixed masks remain in the
same source packet. This replaces the leading row norm by the radical
norm; the remaining row-norm powers are epsilon losses only.

The detector-bin hypothesis is explicit. No RH hypothesis, new moment
assumption, or inverse Dirichlet-polynomial truncation is introduced.
The global high packet and the physical transfer of new twists stay open.
-/

set_option maxHeartbeats 1200000

noncomputable section
namespace OAI.SevenEighths.RadicalCoupledPacket

open scoped Classical
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open ProbeRowRadicalConductor ProbeRowReflectedAllocation ProbeCentralRepeatedProduct
open HeckeReciprocalGrowth HeckeDeletionBounds

local notation "O" => HeckeFamily.O

def radicalNorm (u : FreeRow) : Real :=
  (Ideal.span {u.val}:Ideal O).radical.absNorm

theorem calibrated_radical_rowCost (e eps : Real)
    (he : 0<e) (hehi : e<1/1000) (heps : 0<eps) :
    exists C : Real, 0<C /\
    forall (S : Finset (Ideal O)) (hS : forall P, Membership.mem S P -> Prime P)
      (hmax : forall P, Membership.mem S P -> P.IsMaximal),
      CanonicalQuadraticSieve.fixedBadPrimes <= S ->
    forall u : FreeRow, Not (u.val=1) ->
    forall {iota : Type*} [Fintype iota] (eta : Character) (twists : iota->Character)
      (B a : Real) (i : Nat), 2<B -> 51/100<=a -> a<=1 ->
      detectorMaximum (sourceDetectorFamily S hS eta u twists) (3*(i+1:Nat)*B)<a+2*e ->
    forall w : Complex, w.re=1-a-6*e -> abs w.im<=(3*i+2:Nat)*B ->
      norm (star ((calibrationForSet S hmax).residueMonoid u.val)*
        HeckeOrigin.continued (rowCharacter S hS u) w) <=
      C*(radicalNorm u/rowNorm u)^(a-1/2+6*e)*
        rowCost S hS u a e eps ((3*i+2:Nat)*B) := by
  choose C hC hb using buffered_same_primitive_reflected e eps he hehi heps
  refine Exists.intro C (And.intro hC ?_)
  intro S hS hmax hbad u hu iota _ eta twists B a i hB ha ha1 hbin w hw hwi
  let psi := Classical.choose (rowCharacter_primitive_radical S hS u)
  have ht := Classical.choose_spec (rowCharacter_primitive_radical S hS u)
  by_cases hc : (calibrationForSet S hmax).residueMonoid u.val=0
  . simp only [hc, star_zero, zero_mul, norm_zero]
    have hr := rowCost_nonneg S hS u a e eps ((3*i+2:Nat)*B)
    have hratio : 0<=(radicalNorm u/rowNorm u)^(a-1/2+6*e) :=
      Real.rpow_nonneg (div_nonneg (by unfold radicalNorm; positivity)
        (zero_le_one.trans (rowNorm_ge_one u))) _
    exact mul_nonneg (mul_nonneg hC.le hratio) hr
  . have hn := calibrated_row_nonprincipal S hS hmax hbad u hu hc
    have hL := hb (sourceDetectorFamily S hS eta u twists) B a i hB ha ha1 hbin
      (Sum.inl true) psi ht.2.1 hn ht.2.2.2 w hw hwi
    simp only [sourceDetectorFamily_numerator] at hL
    have hcal : norm (star ((calibrationForSet S hmax).residueMonoid u.val))<=1 := by
      rw [norm_star]
      exact (calibrationForSet S hmax).residueMonoid_norm_le_one _
    have hwgt :
        norm (star ((calibrationForSet S hmax).residueMonoid u.val)*
          HeckeOrigin.continued (rowCharacter S hS u) w)<=
          norm (LFunction (rowCharacter S hS u) w) := by
      rw [HeckeOrigin.continued, ite_eq_right hn, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) hcal
    have hU : 0<rowNorm u := zero_lt_one.trans_le (rowNorm_ge_one u)
    have hR : 0<=radicalNorm u := by unfold radicalNorm; positivity
    have hF : 0<((fixedConductorConstant S):Real) := by
      exact_mod_cast fixedConductorConstant_pos S hS
    have hN : (psi.modulus.absNorm:Real)<=
        (fixedConductorConstant S:Real)*radicalNorm u := by
      dsimp only [psi, radicalNorm]
      exact_mod_cast ht.2.2.1
    have hA : 0<=a-1/2+6*e := by linarith
    have hp : ((fixedConductorConstant S:Real)*radicalNorm u)^(a-1/2+6*e)=
        (radicalNorm u/rowNorm u)^(a-1/2+6*e)*
          ((fixedConductorConstant S:Real)*rowNorm u)^(a-1/2+6*e) := by
      have hi : (radicalNorm u/rowNorm u)*((fixedConductorConstant S:Real)*rowNorm u)=
          (fixedConductorConstant S:Real)*radicalNorm u := by
        field_simp [hU.ne']
      rw [<-hi, Real.mul_rpow (div_nonneg hR hU.le) (mul_nonneg hF.le hU.le)]
    have hpc : 0<=presentationComplexity (rowCharacter S hS u) ((3*i+2:Nat)*B) := by
      unfold presentationComplexity HeckeLogarithmic.complexity
      positivity
    calc
      _ <= C*((fixedConductorConstant S:Real)*radicalNorm u)^(a-1/2+6*e)*
          ((radical (rowCharacter S hS u).modulus).absNorm:Real)^(6*e+2*eps)*
          (3+(3*i+2:Nat)*B)^2*
          (presentationComplexity (rowCharacter S hS u) ((3*i+2:Nat)*B))^eps := by
        apply (hwgt.trans hL).trans
        gcongr
      _ = _ := by rw [hp]; unfold rowCost rowNorm; ring

theorem central_radical_pair_bound (e eps : Real)
    (he : 0<e) (hehi : e<1/1000) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : forall P, Membership.mem S P -> P.IsMaximal)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes <= S)
    (hfirst : FirstTail (4*e) S) :
    exists C : Real, 0<C /\
    forall (eta : Character) (u : FreeRow), Not (u.val=1) ->
    forall {iota : Type*} [Fintype iota] (twists : iota->Character)
      (B a : Real) (i : Nat), 2<B -> 51/100<=a -> a<=1 ->
      detectorMaximum (sourceDetectorFamily S hS.prime eta u twists) (3*(i+1:Nat)*B)<a+2*e ->
    forall x w z : Complex, x.re=a+16*e -> w.re=1-a-6*e -> z.re=17/50 ->
      abs x.im<=(3*i+2:Nat)*B -> abs w.im<=(3*i+2:Nat)*B ->
      norm (star ((calibrationForSet S hmax).residueMonoid u.val)*
          HeckeOrigin.continued (rowCharacter S hS.prime u) w)*
        norm (centralRemainingScalar S hS eta u x w z) <=
      C*(eta.modulus.absNorm:Real)^(2*eps)*
        (radicalNorm u)^(a-1/2+6*e)*(rowNorm u)^(6*e+7*eps)*
        (3+(3*i+2:Nat)*B)^(2+4*eps) := by
  choose C hC hb using calibrated_radical_rowCost e eps he hehi heps
  choose D hD hd using central_remaining_rowCost_bound e eps he hehi heps S hS hfirst
  refine Exists.intro (C*D) (And.intro (mul_pos hC hD) ?_)
  intro eta u hu iota _ twists B a i hB ha ha1 hbin x w z hx hw hz hxi hwi
  have h1 := hb S hS.prime hmax hbad u hu eta twists B a i hB ha ha1 hbin w hw hwi
  have h2 := hd eta u twists B a ((3*i+2:Nat)*B) i hB ha ha1 le_rfl hbin
    x w z hx hw hz hxi
  have hU : 0<rowNorm u := zero_lt_one.trans_le (rowNorm_ge_one u)
  have hR : 0<=radicalNorm u := by unfold radicalNorm; positivity
  have hp : (radicalNorm u/rowNorm u)^(a-1/2+6*e)*
      (rowNorm u)^(a-1/2+12*e+7*eps)=
      (radicalNorm u)^(a-1/2+6*e)*(rowNorm u)^(6*e+7*eps) := by
    have hspl : (rowNorm u)^(a-1/2+12*e+7*eps)=
        (rowNorm u)^(a-1/2+6*e)*(rowNorm u)^(6*e+7*eps) := by
      rw [<-Real.rpow_add hU]
      congr 1
      ring
    rw [Real.div_rpow hR hU.le, hspl]
    field_simp [(Real.rpow_pos_of_pos hU (a-1/2+6*e)).ne']
  calc
    _ <= (C*(radicalNorm u/rowNorm u)^(a-1/2+6*e)*
        rowCost S hS.prime u a e eps ((3*i+2:Nat)*B))*
        norm (centralRemainingScalar S hS eta u x w z) :=
      mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = C*(radicalNorm u/rowNorm u)^(a-1/2+6*e)*
        (norm (centralRemainingScalar S hS eta u x w z)*
          rowCost S hS.prime u a e eps ((3*i+2:Nat)*B)) := by ring
    _ <= C*(radicalNorm u/rowNorm u)^(a-1/2+6*e)*
        (D*(eta.modulus.absNorm:Real)^(2*eps)*
          (rowNorm u)^(a-1/2+12*e+7*eps)*(3+(3*i+2:Nat)*B)^(2+4*eps)) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by
      calc
        _ = (C*D)*(eta.modulus.absNorm:Real)^(2*eps)*
            ((radicalNorm u/rowNorm u)^(a-1/2+6*e)*
              (rowNorm u)^(a-1/2+12*e+7*eps))*(3+(3*i+2:Nat)*B)^(2+4*eps) := by ring
        _ = _ := by rw [hp]; ring

end OAI.SevenEighths.RadicalCoupledPacket

