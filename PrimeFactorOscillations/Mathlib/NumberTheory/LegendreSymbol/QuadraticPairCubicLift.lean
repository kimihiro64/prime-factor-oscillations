/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairTwistAverage
import PrimeFactorOscillations.Mathlib.NumberTheory.Primes.TwinCubic

/-!
# Exact masked cubic transport of the actual pair-count average

The canonical trace-free law is unchanged. Simultaneous square
multipliers preserve both character rows and both endpoint masks.
The cubic Chebyshev substitution supplies those multipliers and adds
exactly its affine-factor mask. All actual count classes are retained;
no invariance of an individual raw count is asserted.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FiniteField
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def cubicPairLift (c : F) : F := c*(2*c+3)^2

omit [Fintype F] [DecidableEq F] in
theorem cubicPairLift_add_two (c : F) :
    cubicPairLift c+2=(c+2)*(2*c+1)^2 := by unfold cubicPairLift; ring

omit [Fintype F] [DecidableEq F] in
theorem cast_twinCubic_step (n : Nat) :
    ((Nat.TwinCubic.step n : Nat) : F)=cubicPairLift (n : F) := by
  simp [Nat.TwinCubic.step,cubicPairLift]

theorem traceFreePairNumerator_square_transport (c d u v : F)
    (hu : Not (u=0)) (hv : Not (v=0))
    (hd : d=c*u^2) (hd2 : d+2=(c+2)*v^2) :
    traceFreePairNumerator d 2=traceFreePairNumerator c 2 := by
  have hchar : (quadraticChar F) d=(quadraticChar F) c := by
    rw [hd,map_mul,map_pow,quadraticChar_sq_one hu,mul_one]
  have hchar2 : (quadraticChar F) (d+2)=(quadraticChar F) (c+2) := by
    rw [hd2,map_mul,map_pow,quadraticChar_sq_one hv,mul_one]
  have hzero : (d=0) <-> c=0 := by rw [hd]; simp [hu]
  have hplus : (d+2=0) <-> c+2=0 := by rw [hd2]; simp [hv]
  have hneg : (d=-(2 : F)) <-> c=-(2 : F) := by
    constructor
    . intro he
      have hz : d+2=0 := by rw [he]; ring
      exact eq_neg_of_add_eq_zero_left (hplus.mp hz)
    . intro he
      apply eq_neg_of_add_eq_zero_left
      apply hplus.mpr
      rw [he]
      ring
  have htwist : twistPairNumerator d 2=twistPairNumerator c 2 := by
    unfold twistPairNumerator
    rw [hchar,hchar2]
  simp only [traceFreePairNumerator,hzero,hneg,htwist]

theorem traceFreePairWeight_square_transport (c d u v : F)
    (hu : Not (u=0)) (hv : Not (v=0))
    (hd : d=c*u^2) (hd2 : d+2=(c+2)*v^2) :
    traceFreePairWeight d 2=traceFreePairWeight c 2 := by
  unfold traceFreePairWeight
  rw [traceFreePairNumerator_square_transport c d u v hu hv hd hd2]

theorem traceFreePairNumerator_cubic_lift (c : F) :
    traceFreePairNumerator (cubicPairLift c) 2=
      if (2*c+1)*(2*c+3)=0 then 0 else traceFreePairNumerator c 2 := by
  by_cases hm : (2*c+1)*(2*c+3)=0
  . rw [ite_eq_left hm]
    rcases mul_eq_zero.mp hm with hv | hu
    . have he : cubicPairLift c=-(2 : F) := by
        apply eq_neg_of_add_eq_zero_left
        rw [cubicPairLift_add_two,hv]
        simp
      simp [traceFreePairNumerator,he]
    . simp [cubicPairLift,hu,traceFreePairNumerator]
  . rw [ite_eq_right hm]
    have hu : Not (2*c+3=0) := by intro he; apply hm; rw [he,mul_zero]
    have hv : Not (2*c+1=0) := by intro he; apply hm; rw [he,zero_mul]
    exact traceFreePairNumerator_square_transport c (cubicPairLift c)
      (2*c+3) (2*c+1) hu hv rfl (cubicPairLift_add_two c)

theorem traceFreePairWeight_cubic_lift (c : F) :
    traceFreePairWeight (cubicPairLift c) 2=
      if (2*c+1)*(2*c+3)=0 then 0 else traceFreePairWeight c 2 := by
  unfold traceFreePairWeight
  rw [traceFreePairNumerator_cubic_lift]
  by_cases hm : (2*c+1)*(2*c+3)=0 <;> simp only [hm,ite_true,ite_false,Int.cast_zero,zero_div]

theorem monicQuadraticPairCount_cubic_lift
    (hF : Not (ringChar F=2)) (c a : F) (ha : (quadraticChar F) a=-1) :
    monicQuadraticPairCount (cubicPairLift c) 2+
      monicQuadraticPairCount (a*cubicPairLift c) (a*2)=
      if (2*c+1)*(2*c+3)=0 then 0 else
        monicQuadraticPairCount c 2+monicQuadraticPairCount (a*c) (a*2) := by
  have ha0 : Not (a=0) := by intro he; subst a; norm_num at ha
  have h2 := two_ne_zero_of_odd hF
  have hnew := traceFreePairNumerator_eq_twist_counts hF (cubicPairLift c) 2 a h2 ha0 ha
  have hold := traceFreePairNumerator_eq_twist_counts hF c 2 a h2 ha0 ha
  have hi := traceFreePairNumerator_cubic_lift c
  rw [hnew,hold] at hi
  by_cases hm : (2*c+1)*(2*c+3)=0
  . rw [ite_eq_left hm] at hi
    rw [ite_eq_left hm]
    linarith only [hi]
  . rw [ite_eq_right hm] at hi
    rw [ite_eq_right hm]
    linarith only [hi]

theorem traceFreePairWeight_twinCubic_orbit (seed k : Nat)
    (hu : Not (((Nat.TwinCubic.leftScale seed k : Nat) : F)=0))
    (hv : Not (((Nat.TwinCubic.rightScale seed k : Nat) : F)=0)) :
    traceFreePairWeight ((Nat.TwinCubic.orbit seed k : Nat) : F) 2=
      traceFreePairWeight (seed : F) 2 := by
  have hd := congrArg (fun n : Nat => (n : F)) (Nat.TwinCubic.orbit_eq_left_square seed k)
  have hd2 := congrArg (fun n : Nat => (n : F))
    (Nat.TwinCubic.orbit_add_two_eq_right_square seed k)
  simp only [Nat.cast_mul,Nat.cast_pow] at hd
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at hd2
  exact traceFreePairWeight_square_transport (seed : F)
    ((Nat.TwinCubic.orbit seed k : Nat) : F)
    ((Nat.TwinCubic.leftScale seed k : Nat) : F)
    ((Nat.TwinCubic.rightScale seed k : Nat) : F) hu hv hd hd2

theorem quadraticChar_twinCubic_rows (seed k : Nat)
    (hu : Not (((Nat.TwinCubic.leftScale seed k : Nat) : F)=0))
    (hv : Not (((Nat.TwinCubic.rightScale seed k : Nat) : F)=0)) :
    (quadraticChar F) (-2*((Nat.TwinCubic.orbit seed k : Nat) : F))=
      (quadraticChar F) (-2*(seed : F)) /\
    (quadraticChar F) (2*(((Nat.TwinCubic.orbit seed k : Nat) : F)+2))=
      (quadraticChar F) (2*((seed : F)+2)) := by
  have hd := congrArg (fun n : Nat => (n : F)) (Nat.TwinCubic.orbit_eq_left_square seed k)
  have hd2 := congrArg (fun n : Nat => (n : F))
    (Nat.TwinCubic.orbit_add_two_eq_right_square seed k)
  simp only [Nat.cast_mul,Nat.cast_pow] at hd
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at hd2
  constructor
  . rw [hd,show (-2 : F)*((seed : F)*((Nat.TwinCubic.leftScale seed k : Nat) : F)^2)=
        (-2*(seed : F))*((Nat.TwinCubic.leftScale seed k : Nat) : F)^2 from by ring,
      map_mul,map_pow,quadraticChar_sq_one hu,mul_one]
  . rw [hd2,show (2 : F)*(((seed : F)+2)*((Nat.TwinCubic.rightScale seed k : Nat) : F)^2)=
        (2*((seed : F)+2))*((Nat.TwinCubic.rightScale seed k : Nat) : F)^2 from by ring,
      map_mul,map_pow,quadraticChar_sq_one hv,mul_one]

end FiniteField
