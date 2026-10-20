/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.CubicSieve.RowCaps
import PrimeFactorOscillations.Assembly.DetectorPackets.RamanujanPrimePacket

/-!
# RamanujanFourthSector

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

set_option maxHeartbeats 1600000

noncomputable section
namespace OAI.SevenEighths.RamanujanIncidenceGram
open scoped Classical BigOperators
open IdealMobiusDivisorSum LocalReflectionBrackets
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

local instance quotientFintype (P : Id) [P.IsMaximal] :
    Fintype (HasQuotient.Quotient O P) := Fintype.ofFinite _
local instance quotientField (P : Id) [P.IsMaximal] :
    Field (HasQuotient.Quotient O P) := Ideal.Quotient.field P

def fourthFactor (A P : Id) : Complex :=
  (Real.sqrt (P.absNorm:Real):Complex) ^ (-1:Int) *
    (if Dvd.dvd P A then (P.absNorm:Complex)-1 else -1)

theorem source_fourth_factor (P : Id) [P.IsMaximal]
    (chi : MulChar (HasQuotient.Quotient O P) Complex) (n : O) :
    bracket chi 4 (Ideal.Quotient.mk P n)=fourthFactor (Ideal.span {n}) P := by
  have hr : 0<Real.sqrt (P.absNorm:Real) := by
    rw [<-CompletedGauss.rootCard_eq_sqrt_absNorm]
    exact rootCard_pos
  have hr0 : Not ((Real.sqrt (P.absNorm:Real):Complex)=0) :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  have hs : (Real.sqrt (P.absNorm:Real):Complex)^2=(P.absNorm:Complex) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg P.absNorm)
  rw [bracket_four_split,CompletedGauss.rootCard_eq_sqrt_absNorm]
  unfold fourthFactor
  by_cases hn : Membership.mem P n
  . have hz : Ideal.Quotient.mk P n=0 := Ideal.Quotient.eq_zero_iff_mem.mpr hn
    have hd : Dvd.dvd P (Ideal.span {n}) := Ideal.dvd_span_singleton.mpr hn
    simp only [hz,ite_true,if_pos hd,zpow_neg_one,mul_one]
    field_simp
    rw [<-hs]
    ring
  . have hz : Not (Ideal.Quotient.mk P n=0) := Ideal.Quotient.eq_zero_iff_mem.not.mpr hn
    have hd : Not (Dvd.dvd P (Ideal.span {n})) := Ideal.dvd_span_singleton.not.mpr hn
    simp only [if_neg hz,if_neg hd,zpow_neg_one,mul_zero,add_zero,mul_neg,mul_one]

def fourthPacket (A Q : Id) : Complex :=
  (primeSupport Q).prod (fun P=>fourthFactor A P)

theorem fourthPacket_eq (A Q : Id) (hQ : Squarefree Q) :
    fourthPacket A Q=primePacket A Q := by
  have hnorm : (primeSupport Q).prod (fun P=>(P.absNorm:Real))=(Q.absNorm:Real) := by
    simpa only [map_prod,Nat.cast_prod] using
      congrArg (fun I:Id=>(I.absNorm:Real)) (squarefree_support_product_self hQ)
  have hden : (primeSupport Q).prod (fun P=>(Real.sqrt (P.absNorm:Real):Complex))=
      (Real.sqrt (Q.absNorm:Real):Complex) := by
    rw [<-Complex.ofReal_prod,<-Real.sqrt_prod _ (fun P _=>Nat.cast_nonneg _),hnorm]
  have hnum : (primeSupport Q).prod
      (fun P=>if Dvd.dvd P A then (P.absNorm:Complex)-1 else -1)=(primeNumerator A Q:Complex) := by
    rw [primeNumerator,Complex.ofReal_prod]
    apply Finset.prod_congr rfl
    intro P hP
    split_ifs <;> simp
  unfold fourthPacket fourthFactor primePacket
  simp only [zpow_neg_one]
  rw [Finset.prod_mul_distrib,Finset.prod_inv_distrib,hden,hnum,div_eq_mul_inv]
  ring

theorem fourthPacket_energy (eps : Real) (heps : 0<eps) :
    Exists fun K : Real => 0<K /\
    forall (R C : Finset Id) (M Q : Real), 1<=M -> 1<=Q ->
    (forall A, Membership.mem R A -> Not (A=0) /\ (A.absNorm:Real)<=M) ->
    (forall I, Membership.mem C I -> Squarefree I /\ (I.absNorm:Real)<=Q) ->
    forall phase : Id -> Id -> Complex,
    (forall A, Membership.mem R A -> forall I, Membership.mem C I -> norm (phase A I)<=1) ->
    forall b : Id -> Complex,
    (R.sum fun A=>norm (C.sum fun I=>b I*(phase A I*fourthPacket A I))^2)<=
      K*M*(M*Q)^eps*(C.sum fun I=>norm (b I)^2) := by
  choose K hK hb using primePacket_energy eps heps
  refine Exists.intro K (And.intro hK ?_)
  intro R C M Q hM hQ hR hC phase hp b
  have he : forall A, (C.sum fun I=>b I*(phase A I*fourthPacket A I))=
      (C.sum fun I=>b I*(phase A I*primePacket A I)) := by
    intro A
    apply Finset.sum_congr rfl
    intro I hI
    rw [fourthPacket_eq A I (hC I hI).1]
  simp_rw [he]
  exact hb R C M Q hM hQ hR
    (fun I hI=>And.intro (hC I hI).1.ne_zero (hC I hI).2) phase hp b

theorem fourthPacket_cube (A B Q : Id) :
    fourthPacket (A*B^3) Q=fourthPacket (A*B) Q := by
  unfold fourthPacket
  apply Finset.prod_congr rfl
  intro P hP
  have hp := support_prime hP
  have he : Dvd.dvd P (B^3) <-> Dvd.dvd P B := by
    constructor
    . exact fun h=>hp.dvd_of_dvd_pow h
    . intro h
      exact h.trans (dvd_pow_self B (by decide))
  have hf : Dvd.dvd P (A*B^3) <-> Dvd.dvd P (A*B) := by
    rw [hp.dvd_mul,hp.dvd_mul,he]
  unfold fourthFactor
  rw [hf]

end OAI.SevenEighths.RamanujanIncidenceGram
