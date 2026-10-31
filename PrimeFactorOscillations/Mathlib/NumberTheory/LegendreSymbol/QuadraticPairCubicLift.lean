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


theorem traceFreePairNumerator_cubic_root (h3 : Not ((3 : F)=0)) (c : F)
    (hr : (2*c+1)*(2*c+3)=0) :
    traceFreePairNumerator c 2=(Fintype.card F : Int)+(quadraticChar F) (3 : F) := by
  have finish (a b : F) (ha : (-2 : F)*c=a) (hb : 2*(c+2)=b)
      (ha0 : Not (a=0)) (hb0 : Not (b=0))
      (hs : (quadraticChar F) a+(quadraticChar F) b=1+(quadraticChar F) (3 : F)) :
      traceFreePairNumerator c 2=(Fintype.card F : Int)+(quadraticChar F) (3 : F) := by
    have hc : Not (c=0) := by
      intro he
      apply ha0
      rw [<- ha,he,mul_zero]
    have hn : Not (c=-(2 : F)) := by
      intro he
      apply hb0
      rw [<- hb,he]
      ring
    simp only [traceFreePairNumerator,ite_eq_right hc,ite_eq_right hn,twistPairNumerator]
    rw [<- map_mul,<- map_mul,ha,hb]
    linarith only [hs]
  rcases mul_eq_zero.mp hr with h | h
  . have hc : 2*c=-(1 : F) := eq_neg_of_add_eq_zero_left h
    have ha : (-2 : F)*c=1 := by
      calc
        _ = -(2*c) := by ring
        _ = 1 := by rw [hc]; ring
    have hb : (2 : F)*(c+2)=3 := by
      calc
        _ = 2*c+4 := by ring
        _ = 3 := by rw [hc]; ring
    exact finish 1 3 ha hb one_ne_zero h3 (by simp)
  . have hc : 2*c=-(3 : F) := eq_neg_of_add_eq_zero_left h
    have ha : (-2 : F)*c=3 := by
      calc
        _ = -(2*c) := by ring
        _ = 3 := by rw [hc]; ring
    have hb : (2 : F)*(c+2)=1 := by
      calc
        _ = 2*c+4 := by ring
        _ = 1 := by rw [hc]; ring
    exact finish 3 1 ha hb h3 one_ne_zero (by simp [add_comm])

theorem traceFreePairWeight_cubic_root (h3 : Not ((3 : F)=0)) (c : F)
    (hr : (2*c+1)*(2*c+3)=0) :
    traceFreePairWeight c 2=
      ((Fintype.card F : Real)+((quadraticChar F) (3 : F) : Real))/
        ((Fintype.card F : Real)-3) := by
  unfold traceFreePairWeight
  rw [traceFreePairNumerator_cubic_root h3 c hr]
  norm_num only [Int.cast_add,Int.cast_natCast]

omit [Fintype F] [DecidableEq F] in
theorem cubic_pair_mask_zero_iff (h2 : Not ((2 : F)=0)) (c : F) :
    (2*c+1)*(2*c+3)=0 <-> c=-(1 : F)/2 \/ c=-(3 : F)/2 := by
  have linear_root (a : F) : (2*c+a=0) <-> c=-a/2 := by
    rw [eq_div_iff h2]
    constructor
    . intro he
      apply eq_neg_of_add_eq_zero_left
      calc
        c*2+a=2*c+a := by ring
        _ = 0 := he
    . intro he
      calc
        2*c+a=c*2+a := by ring
        _ = 0 := by rw [he]; ring
  rw [mul_eq_zero,linear_root,linear_root]

theorem sum_traceFreePairWeight_cubic_lift_deletion
    (hF : Not (ringChar F=2)) :
    (Finset.univ.sum fun c : F => traceFreePairWeight (cubicPairLift c) 2)=
      (Finset.univ.sum fun c : F => traceFreePairWeight c 2)-
        traceFreePairWeight (-(1 : F)/2) 2-traceFreePairWeight (-(3 : F)/2) 2 := by
  have h2 := two_ne_zero_of_odd hF
  have hab : Not ((-(1 : F)/2)=-(3 : F)/2) := by
    intro he
    have hd : (-(1 : F)/2)-(-(3 : F)/2)=1 := by field_simp [h2]; ring
    rw [he,sub_self] at hd
    exact zero_ne_one hd
  have he (c : F) :
      traceFreePairWeight (cubicPairLift c) 2=traceFreePairWeight c 2-
        (if c=-(1 : F)/2 then traceFreePairWeight (-(1 : F)/2) 2 else 0)-
        (if c=-(3 : F)/2 then traceFreePairWeight (-(3 : F)/2) 2 else 0) := by
    simp only [traceFreePairWeight_cubic_lift,cubic_pair_mask_zero_iff h2]
    by_cases ha : c=-(1 : F)/2
    . rw [ha]
      simp [hab]
    . by_cases hb : c=-(3 : F)/2
      . rw [hb]
        simp [Ne.symm hab]
      . simp [ha,hb]
  simp_rw [he]
  simp only [Finset.sum_sub_distrib]
  simp

theorem traceFreePairWeight_cubic_lift_mean (hF : Not (ringChar F=2))
    (h3 : Not ((3 : F)=0)) (hq : 5<=(Fintype.card F : Real)) :
    (1/(Fintype.card F : Real))*
      (Finset.univ.sum fun c : F => traceFreePairWeight (cubicPairLift c) 2)=
      1-2*((Fintype.card F : Real)+((quadraticChar F) (3 : F) : Real))/
        ((Fintype.card F : Real)*((Fintype.card F : Real)-3)) := by
  have h2 := two_ne_zero_of_odd hF
  have ha := (cubic_pair_mask_zero_iff h2 (-(1 : F)/2)).mpr (Or.inl rfl)
  have hb := (cubic_pair_mask_zero_iff h2 (-(3 : F)/2)).mpr (Or.inr rfl)
  have hm := traceFreePairWeight_mean_one hF (2 : F) h2 hq
  rw [sum_traceFreePairWeight_cubic_lift_deletion hF,
    traceFreePairWeight_cubic_root h3 _ ha,traceFreePairWeight_cubic_root h3 _ hb,
    mul_sub,mul_sub,hm]
  have hq0 : Not ((Fintype.card F : Real)=0) := ne_of_gt (by linarith only [hq])
  have hq3 : Not ((Fintype.card F : Real)-3=0) := ne_of_gt (by linarith only [hq])
  field_simp [hq0,hq3]
  ring

theorem traceFreePairNumerator_cubic_lift_char_three (hF : Not (ringChar F=2))
    (h3 : (3 : F)=0) (c : F) :
    traceFreePairNumerator (cubicPairLift c) 2=traceFreePairNumerator c 2 := by
  rw [traceFreePairNumerator_cubic_lift]
  by_cases hr : (2*c+1)*(2*c+3)=0
  . rw [ite_eq_left hr]
    have h2 := two_ne_zero_of_odd hF
    rcases mul_eq_zero.mp hr with hv | hu
    . have hz : (2 : F)*(c+2)=0 := by
        calc
          _ = (2*c+1)+3 := by ring
          _ = 0 := by rw [hv,h3]; ring
      have hc := (mul_eq_zero.mp hz).resolve_left h2
      have hn := eq_neg_of_add_eq_zero_left hc
      simp [traceFreePairNumerator,hn]
    . have hz : (2 : F)*c=0 := by simpa only [h3,add_zero] using hu
      have hc := (mul_eq_zero.mp hz).resolve_left h2
      simp [traceFreePairNumerator,hc]
  . rw [ite_eq_right hr]

theorem traceFreePairWeight_cubic_lift_char_three (hF : Not (ringChar F=2))
    (h3 : (3 : F)=0) (c : F) :
    traceFreePairWeight (cubicPairLift c) 2=traceFreePairWeight c 2 := by
  unfold traceFreePairWeight
  rw [traceFreePairNumerator_cubic_lift_char_three hF h3]

theorem traceFreePairWeight_cubic_iterate_char_three (hF : Not (ringChar F=2))
    (h3 : (3 : F)=0) (k : Nat) (c : F) :
    traceFreePairWeight ((cubicPairLift^[k]) c) 2=traceFreePairWeight c 2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',traceFreePairWeight_cubic_lift_char_three hF h3,ih]

theorem traceFreePairWeight_cubic_iterate_mean_char_three (hF : Not (ringChar F=2))
    (h3 : (3 : F)=0) (hq : 5<=(Fintype.card F : Real)) (k : Nat) :
    (1/(Fintype.card F : Real))*
      (Finset.univ.sum fun c : F =>
        traceFreePairWeight ((cubicPairLift^[k]) c) 2)=1 := by
  simp_rw [traceFreePairWeight_cubic_iterate_char_three hF h3]
  exact traceFreePairWeight_mean_one hF (2 : F) (two_ne_zero_of_odd hF) hq

end FiniteField
