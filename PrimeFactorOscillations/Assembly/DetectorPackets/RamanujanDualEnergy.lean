/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.RamanujanFourthSector

/-!
# RamanujanDualEnergy

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

set_option maxHeartbeats 2000000

noncomputable section
namespace OAI.SevenEighths.RamanujanIncidenceGram
open scoped Classical BigOperators
open FiniteSieveOperator
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem finite_energy_dual {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (G : Matrix A B Complex) (L : Real) (hL : 0<=L)
    (hG : forall v : B -> Complex,
      (Finset.univ.sum fun a=>norm (Finset.univ.sum fun b=>G a b*v b)^2)<=
        L*(Finset.univ.sum fun b=>norm (v b)^2)) :
    forall u : A -> Complex,
      (Finset.univ.sum fun b=>norm (Finset.univ.sum fun a=>star (G a b)*u a)^2)<=
        L*(Finset.univ.sum fun a=>norm (u a)^2) := by
  have hOp : norm (operator G)<=Real.sqrt L := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg L)
    intro x
    have hh := hG (fun b=>x b)
    have hx : norm (operator G x)^2<=L*norm x^2 := by
      simpa only [EuclideanSpace.norm_sq_eq,operator_apply] using hh
    have hs := Real.sq_sqrt hL
    have hx0 := norm_nonneg x
    have hy0 := norm_nonneg (operator G x)
    have hr0 := Real.sqrt_nonneg L
    have hx' : norm (operator G x)^2<=(Real.sqrt L*norm x)^2 := by
      simpa only [mul_pow,hs] using hx
    have hp := mul_nonneg hr0 hx0
    nlinarith
  intro u
  have hh := energy_bound G.conjTranspose u
  rw [operator_conjTranspose_norm] at hh
  have hn : norm (operator G)^2<=L := by
    have hn0 := norm_nonneg (operator G)
    have hr0 := Real.sqrt_nonneg L
    have hs := Real.sq_sqrt hL
    nlinarith
  exact hh.trans (mul_le_mul_of_nonneg_right hn
    (Finset.sum_nonneg fun a _=>sq_nonneg _))

theorem normalized_subtype_energy (eps : Real) (heps : 0<eps) :
    Exists fun K : Real => 0<K /\
    forall (R C : Finset Id) (M Q : Real), 1<=M -> 1<=Q ->
    (forall A, Membership.mem R A -> Not (A=0) /\ (A.absNorm:Real)<=M) ->
    (forall I, Membership.mem C I -> Not (I=0) /\ (I.absNorm:Real)<=Q) ->
    forall G : R -> C -> Complex,
    (forall A I, norm (G A I)<=sharedMass A.val I.val/Real.sqrt (I.val.absNorm:Real)) ->
    forall b : C -> Complex,
    (Finset.univ.sum fun A=>norm (Finset.univ.sum fun I=>G A I*b I)^2)<=
      K*M*(M*Q)^eps*(Finset.univ.sum fun I=>norm (b I)^2) := by
  choose K hK hb using normalized_energy eps heps
  refine Exists.intro K (And.intro hK ?_)
  intro R C M Q hM hQ hR hC G hG b
  let F : Id -> Id -> Complex := fun A I=>
    if hA : Membership.mem R A then
      if hI : Membership.mem C I then G {val:=A,property:=hA} {val:=I,property:=hI} else 0
    else 0
  let v : Id -> Complex := fun I=>if hI : Membership.mem C I then b {val:=I,property:=hI} else 0
  have hF : forall A, Membership.mem R A -> forall I, Membership.mem C I ->
      norm (F A I)<=sharedMass A I/Real.sqrt (I.absNorm:Real) := by
    intro A hA I hI
    simpa only [F,dif_pos hA,dif_pos hI] using hG {val:=A,property:=hA} {val:=I,property:=hI}
  have hh := hb R C M Q hM hQ hR hC F hF v
  have hr (A : R) :
      (C.sum fun I=>v I*F A.val I)=(Finset.univ.sum fun I:C=>G A I*b I) := by
    rw [<-Finset.sum_coe_sort C (fun I=>v I*F A.val I)]
    apply Finset.sum_congr rfl
    intro I hI
    simp only [F,v,dif_pos A.property,dif_pos I.property]
    ring
  rw [<-Finset.sum_coe_sort R (fun A=>norm (C.sum fun I=>v I*F A I)^2)] at hh
  rw [<-Finset.sum_coe_sort C (fun I=>norm (v I)^2)] at hh
  have hv (I : C) : v I.val=b I := by
    simp only [v,dif_pos I.property]
  simpa only [hr,hv] using hh

theorem normalized_dual_energy (eps : Real) (heps : 0<eps) :
    Exists fun K : Real => 0<K /\
    forall (R C : Finset Id) (M Q : Real), 1<=M -> 1<=Q ->
    (forall A, Membership.mem R A -> Not (A=0) /\ (A.absNorm:Real)<=M) ->
    (forall I, Membership.mem C I -> Not (I=0) /\ (I.absNorm:Real)<=Q) ->
    forall G : R -> C -> Complex,
    (forall A I, norm (G A I)<=sharedMass A.val I.val/Real.sqrt (I.val.absNorm:Real)) ->
    forall a : R -> Complex,
    (Finset.univ.sum fun I=>norm (Finset.univ.sum fun A=>G A I*a A)^2)<=
      K*M*(M*Q)^eps*(Finset.univ.sum fun A=>norm (a A)^2) := by
  choose K hK hb using normalized_subtype_energy eps heps
  refine Exists.intro K (And.intro hK ?_)
  intro R C M Q hM hQ hR hC G hG a
  let F : Matrix R C Complex := fun A I=>star (G A I)
  have hF : forall A I, norm (F A I)<=sharedMass A.val I.val/Real.sqrt (I.val.absNorm:Real) := by
    intro A I
    simpa only [F,norm_star] using hG A I
  have hL : 0<=K*M*(M*Q)^eps := by positivity
  have hh := finite_energy_dual F (K*M*(M*Q)^eps) hL (hb R C M Q hM hQ hR hC F hF) a
  simpa only [F,star_star] using hh

end OAI.SevenEighths.RamanujanIncidenceGram
