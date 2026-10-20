/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.RamanujanDualEnergy

/-!
# RamanujanProductEnergy

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

set_option maxHeartbeats 2200000

noncomputable section
namespace OAI.SevenEighths.RamanujanIncidenceGram
open scoped Classical BigOperators
open IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "PairId" => Prod Id Id

theorem pair_fiber_card (P : Finset PairId) (A : Id) (hA : Not (A=0))
    (hP : forall p, Membership.mem P p -> Not (p.1=0)) :
    (P.filter fun p=>p.1*p.2=A).card<=(idealDivisors A).card := by
  apply Finset.card_le_card_of_injOn (fun p:PairId=>p.1)
  . intro p hp
    have he := (Finset.mem_filter.mp hp).2
    apply (mem_idealDivisors hA).mpr
    exact Exists.intro p.2 he.symm
  . intro p hp q hq he
    change p.1=q.1 at he
    have hp0 := hP p (Finset.mem_filter.mp hp).1
    have hm : p.1*p.2=q.1*q.2 :=
      (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
    have hb : p.2=q.2 := by
      rw [<-he] at hm
      exact (mul_right_inj' hp0).mp hm
    exact Prod.ext he hb

theorem image_mass {A B : Type*} [DecidableEq B] (P : Finset A) (f : A -> B)
    (h : B -> Real) (D : Real)
    (hh : forall a, Membership.mem P a -> 0<=h (f a))
    (hc : forall b, Membership.mem (P.image f) b ->
      ((P.filter fun a=>f a=b).card:Real)<=D) :
    (P.sum fun a=>h (f a))<=D*((P.image f).sum h) := by
  have he := Finset.sum_fiberwise_of_maps_to (s:=P) (t:=P.image f) (g:=f)
    (fun a ha=>Finset.mem_image_of_mem f ha) (fun a=>h (f a))
  rw [<-he]
  calc
    _ <= (P.image f).sum (fun b=>D*h b) := by
      apply Finset.sum_le_sum
      intro b hb
      have heq : (P.filter fun a=>f a=b).sum (fun a=>h (f a))=
          ((P.filter fun a=>f a=b).card:Real)*h b := by
        calc
          _ = (P.filter fun a=>f a=b).sum (fun _=>h b) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [(Finset.mem_filter.mp ha).2]
          _ = _ := by simp
      rw [heq]
      choose a ha hab using Finset.mem_image.mp hb
      have hb0 : 0<=h b := by simpa only [<-hab] using hh a ha
      exact mul_le_mul_of_nonneg_right (hc b hb) hb0
    _ = _ := (Finset.mul_sum ..).symm

theorem product_primal_energy (eps : Real) (heps : 0<eps) :
    Exists fun K : Real => 0<K /\
    forall (P : Finset PairId) (C : Finset Id) (U B Q : Real), 1<=U -> 1<=B -> 1<=Q ->
    (forall p, Membership.mem P p ->
      Not (p.1=0) /\ Not (p.2=0) /\ (p.1.absNorm:Real)<=U /\ (p.2.absNorm:Real)<=B) ->
    (forall I, Membership.mem C I -> Not (I=0) /\ (I.absNorm:Real)<=Q) ->
    forall G : P -> C -> Complex,
    (forall p I, norm (G p I)<=sharedMass (p.val.1*p.val.2) I.val/Real.sqrt (I.val.absNorm:Real)) ->
    forall b : C -> Complex,
    (Finset.univ.sum fun p=>norm (Finset.univ.sum fun I=>G p I*b I)^2)<=
      K*(U*B)*(U*B*Q)^eps*(Finset.univ.sum fun I=>norm (b I)^2) := by
  let delta := eps/2
  have hd : 0<delta := by dsimp [delta];positivity
  choose K0 hK0 hb using normalized_subtype_energy delta hd
  choose D hD hdv using IdealDivisorBound.ideal_divisor_small_power delta hd
  refine Exists.intro (D*K0) (And.intro (mul_pos hD hK0) ?_)
  intro P C U B Q hU hB hQ hP hC G hG b
  let W := P.image (fun p:PairId=>p.1*p.2)
  have hM : 1<=U*B := one_le_mul_of_one_le_of_one_le hU hB
  have hW (A : Id) (hA : Membership.mem W A) : Not (A=0) /\ (A.absNorm:Real)<=U*B := by
    choose p hp he using Finset.mem_image.mp hA
    have hh := hP p hp
    rw [<-he]
    refine And.intro (mul_ne_zero hh.1 hh.2.1) ?_
    rw [map_mul,Nat.cast_mul]
    exact mul_le_mul hh.2.2.1 hh.2.2.2 (Nat.cast_nonneg _) (zero_le_one.trans hU)
  let k := fun A I:Id=>sharedMass A I/Real.sqrt (I.absNorm:Real)
  have hk (A I : Id) : 0<=k A I := div_nonneg (sharedMass_nonneg _ _) (Real.sqrt_nonneg _)
  let h := fun A:Id=>(Finset.univ.sum fun I:C=>norm (b I)*k A I.val)^2
  have hpoint (p : P) : norm (Finset.univ.sum fun I=>G p I*b I)^2<=h (p.val.1*p.val.2) := by
    have hh : norm (Finset.univ.sum fun I=>G p I*b I)<=
        (Finset.univ.sum fun I:C=>norm (b I)*k (p.val.1*p.val.2) I.val) := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun I _=>by
        rw [norm_mul,mul_comm]
        exact mul_le_mul_of_nonneg_left (hG p I) (norm_nonneg _))
    have hn0 := norm_nonneg (Finset.univ.sum fun I=>G p I*b I)
    change norm (Finset.univ.sum fun I:C=>G p I*b I)^2<=
      (Finset.univ.sum fun I:C=>norm (b I)*k (p.val.1*p.val.2) I.val)^2
    have hs0 : 0<=(Finset.univ.sum fun I:C=>norm (b I)*k (p.val.1*p.val.2) I.val) :=
      Finset.sum_nonneg fun I _=>mul_nonneg (norm_nonneg _) (hk _ _)
    simpa only [pow_two] using mul_le_mul hh hh hn0 hs0
  have hfiber (A : Id) (hA : Membership.mem W A) :
      ((P.filter fun p=>p.1*p.2=A).card:Real)<=D*(U*B)^delta := by
    have hc : ((P.filter fun p=>p.1*p.2=A).card:Real)<=((idealDivisors A).card:Real) := by
      exact_mod_cast pair_fiber_card P A (hW A hA).1 (fun p hp=>(hP p hp).1)
    exact hc.trans ((hdv A (hW A hA).1).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (hW A hA).2 hd.le) hD.le))
  have hmass : (Finset.univ.sum fun p:P=>h (p.val.1*p.val.2))<=
      (D*(U*B)^delta)*(Finset.univ.sum fun A:W=>h A.val) := by
    rw [Finset.sum_coe_sort P (fun p:PairId=>h (p.1*p.2)),
      Finset.sum_coe_sort W h]
    exact image_mass P (fun p:PairId=>p.1*p.2) h (D*(U*B)^delta)
      (fun p _=>sq_nonneg _) hfiber
  have hkernel (A : W) (I : C) : norm (k A.val I.val:Complex)<=k A.val I.val := by
    rw [Complex.norm_real,Real.norm_of_nonneg (hk _ _)]
  have hbase := hb W C (U*B) Q hM hQ hW hC
    (fun A I=>(k A.val I.val:Complex)) hkernel (fun I=>(norm (b I):Complex))
  have he (A : W) :
      norm (Finset.univ.sum fun I:C=>(k A.val I.val:Complex)*(norm (b I):Complex))^2=h A.val := by
    have hs : (Finset.univ.sum fun I:C=>(k A.val I.val:Complex)*(norm (b I):Complex))=
        ((Finset.univ.sum fun I:C=>norm (b I)*k A.val I.val):Real) := by
      rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro I hI
      simp only [Complex.ofReal_mul]
      ring
    rw [hs,Complex.norm_real,Real.norm_of_nonneg
      (Finset.sum_nonneg fun I _=>mul_nonneg (norm_nonneg _) (hk _ _))]
  have hbNorm (I : C) : norm (norm (b I):Complex)=norm (b I) := by
    rw [Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _)]
  simp_rw [he,hbNorm] at hbase
  have hpower : (U*B)^delta*(U*B*Q)^delta<=(U*B*Q)^eps := by
    have h1 : U*B<=U*B*Q := le_mul_of_one_le_right (by positivity) hQ
    have hh := Real.rpow_le_rpow (by positivity) h1 hd.le
    have hp : 0<U*B*Q := by positivity
    have heq : (U*B*Q)^delta*(U*B*Q)^delta=(U*B*Q)^eps := by
      rw [<-Real.rpow_add hp]
      congr 1
      dsimp [delta]
      ring
    exact (mul_le_mul_of_nonneg_right hh (by positivity)).trans_eq heq
  calc
    _ <= (Finset.univ.sum fun p:P=>h (p.val.1*p.val.2)) := Finset.sum_le_sum fun p _=>hpoint p
    _ <= _ := hmass
    _ <= (D*(U*B)^delta)*(K0*(U*B)*(U*B*Q)^delta*
        (Finset.univ.sum fun I:C=>norm (b I)^2)) :=
      mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = (D*K0)*(U*B)*((U*B)^delta*(U*B*Q)^delta)*
        (Finset.univ.sum fun I:C=>norm (b I)^2) := by ring
    _ <= _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpower (by positivity))
      (Finset.sum_nonneg fun I _=>sq_nonneg _)

theorem product_dual_energy (eps : Real) (heps : 0<eps) :
    Exists fun K : Real => 0<K /\
    forall (P : Finset PairId) (C : Finset Id) (U B Q : Real), 1<=U -> 1<=B -> 1<=Q ->
    (forall p, Membership.mem P p ->
      Not (p.1=0) /\ Not (p.2=0) /\ (p.1.absNorm:Real)<=U /\ (p.2.absNorm:Real)<=B) ->
    (forall I, Membership.mem C I -> Not (I=0) /\ (I.absNorm:Real)<=Q) ->
    forall G : P -> C -> Complex,
    (forall p I, norm (G p I)<=sharedMass (p.val.1*p.val.2) I.val/Real.sqrt (I.val.absNorm:Real)) ->
    forall a : P -> Complex,
    (Finset.univ.sum fun I=>norm (Finset.univ.sum fun p=>G p I*a p)^2)<=
      K*(U*B)*(U*B*Q)^eps*(Finset.univ.sum fun p=>norm (a p)^2) := by
  choose K hK hb using product_primal_energy eps heps
  refine Exists.intro K (And.intro hK ?_)
  intro P C U B Q hU hB hQ hP hC G hG a
  let F : Matrix P C Complex := fun p I=>star (G p I)
  have hF : forall p I, norm (F p I)<=sharedMass (p.val.1*p.val.2) I.val/Real.sqrt (I.val.absNorm:Real) := by
    intro p I
    simpa only [F,norm_star] using hG p I
  have hL : 0<=K*(U*B)*(U*B*Q)^eps := by positivity
  have hh := finite_energy_dual F (K*(U*B)*(U*B*Q)^eps) hL
    (hb P C U B Q hU hB hQ hP hC F hF) a
  simpa only [F,star_star] using hh

theorem fourth_product_dual_energy (eps : Real) (heps : 0<eps) :
    Exists fun K : Real => 0<K /\
    forall (P : Finset PairId) (C : Finset Id) (U B Q : Real), 1<=U -> 1<=B -> 1<=Q ->
    (forall p, Membership.mem P p ->
      Not (p.1=0) /\ Not (p.2=0) /\ (p.1.absNorm:Real)<=U /\ (p.2.absNorm:Real)<=B) ->
    (forall I, Membership.mem C I -> Squarefree I /\ (I.absNorm:Real)<=Q) ->
    forall phase : P -> C -> Complex, (forall p I, norm (phase p I)<=1) ->
    forall a : P -> Complex,
    (Finset.univ.sum fun I=>norm (Finset.univ.sum fun p=>
      phase p I*fourthPacket (p.val.1*p.val.2^3) I.val*a p)^2)<=
      K*(U*B)*(U*B*Q)^eps*(Finset.univ.sum fun p=>norm (a p)^2) := by
  choose K hK hb using product_dual_energy eps heps
  refine Exists.intro K (And.intro hK ?_)
  intro P C U B Q hU hB hQ hP hC phase hp a
  have hG (p : P) (I : C) :
      norm (phase p I*fourthPacket (p.val.1*p.val.2^3) I.val)<=
        sharedMass (p.val.1*p.val.2) I.val/Real.sqrt (I.val.absNorm:Real) := by
    rw [fourthPacket_cube,fourthPacket_eq _ _ (hC I.val I.property).1,norm_mul]
    have hh := hP p.val p.property
    exact (mul_le_of_le_one_left (norm_nonneg _) (hp p I)).trans
      (primePacket_bound _ _ (mul_ne_zero hh.1 hh.2.1) (hC I.val I.property).1.ne_zero)
  exact hb P C U B Q hU hB hQ hP
    (fun I hI=>And.intro (hC I hI).1.ne_zero (hC I hI).2)
    (fun p I=>phase p I*fourthPacket (p.val.1*p.val.2^3) I.val) hG a

end OAI.SevenEighths.RamanujanIncidenceGram
