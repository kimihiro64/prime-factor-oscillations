/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldIntegerMass
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairCubicLift

/-!
# Cubic transport of the complete integer pair packet

The canonical actual packet retains every prime row, including its
small-prime fallback. Its cubic transport is exactly multiplication
by the mask of newly introduced prime divisors. No row is discarded
and no positive integer prime-pair mass is assumed.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.FiniteFieldCubicLift
attribute [local instance] Classical.propDecidable
open PrimeFactorOscillations.FiniteFieldIntegerMass
open PrimeFactorOscillations.FiniteFieldIntegerTail

def primeBlockMask {Q : Nat} (q : BoundedModulus Q) (n : Nat) : Real :=
  if Nat.Prime q.val /\ Dvd.dvd q.val (Nat.TwinCubic.block n) then 0 else 1

def blockMask (Q n : Nat) : Real :=
  (Finset.Icc 1 Q).attach.prod (fun q => primeBlockMask q n)

theorem integer_mask_product {Q : Nat} (q : BoundedModulus Q)
    (hp : Nat.Prime q.val) (c : ZMod q.val) :
    integerMask 2 q c=if c*(c+2)=0 then 0 else 1 := by
  letI : Fact (Nat.Prime q.val) := Fact.mk hp
  have he : (c+2=0) <-> c=-(2 : ZMod q.val) := add_eq_zero_iff_eq_neg
  simp only [integerMask,Int.cast_ofNat,mul_eq_zero,he]
  by_cases hz : c=0 <;> by_cases hn : c=-(2 : ZMod q.val) <;> simp [hz,hn]

theorem block_cast_zero_iff {Q : Nat} (q : BoundedModulus Q) (n : Nat) :
    (2*(n : ZMod q.val)+1)*(2*(n : ZMod q.val)+3)=0 <->
      Dvd.dvd q.val (Nat.TwinCubic.block n) := by
  have hc := CharP.cast_eq_zero_iff (ZMod q.val) q.val (Nat.TwinCubic.block n)
  simpa only [Nat.TwinCubic.block,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,
    Nat.cast_one] using hc

theorem integer_mask_cubic_lift {Q : Nat} (q : BoundedModulus Q)
    (hp : Nat.Prime q.val) (n : Nat) :
    integerMask 2 q ((Nat.TwinCubic.step n : Nat) : ZMod q.val)=
      integerMask 2 q (n : ZMod q.val)*primeBlockMask q n := by
  letI : Fact (Nat.Prime q.val) := Fact.mk hp
  have he := congrArg (fun m : Nat => (m : ZMod q.val))
    (Nat.TwinCubic.endpointProduct_step n)
  simp only [Nat.TwinCubic.endpointProduct,Nat.cast_mul,Nat.cast_add,
    Nat.cast_pow,Nat.cast_ofNat] at he
  rw [integer_mask_product q hp,integer_mask_product q hp,he]
  have hb := CharP.cast_eq_zero_iff (ZMod q.val) q.val (Nat.TwinCubic.block n)
  by_cases hz : (n : ZMod q.val)*((n : ZMod q.val)+2)=0
  . simp [hz]
  . by_cases hd : Dvd.dvd q.val (Nat.TwinCubic.block n)
    . simp [hb.mpr hd,primeBlockMask,hp,hd]
    . have hb0 : Not (((Nat.TwinCubic.block n : Nat) : ZMod q.val)=0) :=
        fun he0 => hd (hb.mp he0)
      have hprod := mul_ne_zero hz (pow_ne_zero 2 hb0)
      simp [hprod,hz,primeBlockMask,hp,hd]

theorem actual_local_cubic_lift {Q : Nat} (q : BoundedModulus Q) (n : Nat) :
    actualLocal 2 q ((Nat.TwinCubic.step n : Nat) : ZMod q.val)=
      actualLocal 2 q (n : ZMod q.val)*primeBlockMask q n := by
  by_cases hp : Nat.Prime q.val
  . letI : Fact (Nat.Prime q.val) := Fact.mk hp
    by_cases hg : 5<=q.val /\ Not (((2 : Int) : ZMod q.val)=0)
    . simp only [actualLocal,dite_eq_left hp]
      simp only [ite_eq_left hg]
      norm_num only [Int.cast_ofNat,Nat.cast_ofNat]
      change _root_.FiniteField.traceFreePairWeight
        ((Nat.TwinCubic.step n : Nat) : ZMod q.val) 2=
        _root_.FiniteField.traceFreePairWeight (n : ZMod q.val) 2*primeBlockMask q n
      rw [_root_.FiniteField.cast_twinCubic_step,
        _root_.FiniteField.traceFreePairWeight_cubic_lift]
      have hb := block_cast_zero_iff q n
      by_cases hd : Dvd.dvd q.val (Nat.TwinCubic.block n)
      . simp [hb.mpr hd,primeBlockMask,hp,hd]
      . have hz : Not ((2*(n : ZMod q.val)+1)*(2*(n : ZMod q.val)+3)=0) :=
          fun he => hd (hb.mp he)
        simp [hz,primeBlockMask,hp,hd]
    . simp only [actualLocal,dite_eq_left hp,ite_eq_right hg,flatFallback]
      rw [integer_mask_cubic_lift q hp n]
      ring
  . simp [actualLocal,primeBlockMask,hp]

theorem actual_packet_cubic_lift (Q n : Nat) :
    actualPacket 2 Q (Nat.TwinCubic.step n)=actualPacket 2 Q n*blockMask Q n := by
  unfold actualPacket blockMask
  simp_rw [actual_local_cubic_lift]
  rw [Finset.prod_mul_distrib]

theorem block_mask_eq_one (Q n : Nat)
    (havoid : forall p : Nat, Nat.Prime p -> p<=Q ->
      Not (Dvd.dvd p (Nat.TwinCubic.block n))) :
    blockMask Q n=1 := by
  unfold blockMask
  apply Finset.prod_eq_one
  intro q _
  have hq := (Finset.mem_Icc.mp q.property).2
  by_cases hp : Nat.Prime q.val
  . simp [primeBlockMask,hp,havoid q.val hp hq]
  . simp [primeBlockMask,hp]

theorem block_mask_eq_zero (Q n p : Nat) (hp : Nat.Prime p) (hpQ : p<=Q)
    (hd : Dvd.dvd p (Nat.TwinCubic.block n)) :
    blockMask Q n=0 := by
  have hp2 := hp.two_le
  let q : BoundedModulus Q := Subtype.mk p (Finset.mem_Icc.mpr (And.intro (by omega) hpQ))
  unfold blockMask
  apply Finset.prod_eq_zero (Finset.mem_attach _ q)
  simp [primeBlockMask,q,hp,hd]

theorem actual_packet_eq_of_no_new_prime (Q n : Nat)
    (havoid : forall p : Nat, Nat.Prime p -> p<=Q ->
      Not (Dvd.dvd p (Nat.TwinCubic.block n))) :
    actualPacket 2 Q (Nat.TwinCubic.step n)=actualPacket 2 Q n := by
  rw [actual_packet_cubic_lift,block_mask_eq_one Q n havoid,mul_one]

theorem actual_packet_zero_of_new_prime (Q n p : Nat) (hp : Nat.Prime p) (hpQ : p<=Q)
    (hd : Dvd.dvd p (Nat.TwinCubic.block n)) :
    actualPacket 2 Q (Nat.TwinCubic.step n)=0 := by
  rw [actual_packet_cubic_lift,block_mask_eq_zero Q n p hp hpQ hd,mul_zero]

end PrimeFactorOscillations.FiniteFieldCubicLift
