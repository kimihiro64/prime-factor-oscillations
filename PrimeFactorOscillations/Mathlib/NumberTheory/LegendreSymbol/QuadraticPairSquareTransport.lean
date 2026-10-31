/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairTwistAverage

/-!
# All simultaneous-square transports of the actual pair law

Zero square multipliers are allowed. An admissible endpoint can be
absorbed exactly when its opposite scaled character is positive.
The double-negative core is forced to survive. Every other part of
the canonical two-class law can be erased, with an idempotent witness.
This concerns the actual trace-free twist average, not a raw count.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FiniteField
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def squarePairReach (c d h : F) : Prop :=
  Exists (fun u : F => Exists (fun v : F =>
    d=c*u^2 /\ d+h=(c+h)*v^2))

def squarePairCore (c h : F) : Prop :=
  (quadraticChar F) ((-h)*c)=-1 /\
    (quadraticChar F) (h*(c+h))=-1

def squarePairCollapse (c h : F) : F :=
  if (quadraticChar F) (h*(c+h))=1 then 0
  else if (quadraticChar F) ((-h)*c)=1 then -h else c

omit [Fintype F] [DecidableEq F] in
theorem squarePairReach_refl (c h : F) : squarePairReach c c h :=
  Exists.intro 1 (Exists.intro 1 (by constructor <;> simp))

theorem traceFreePairNumerator_square_transport_gap (c d h u v : F)
    (hu : Not (u=0)) (hv : Not (v=0))
    (hd : d=c*u^2) (hdh : d+h=(c+h)*v^2) :
    traceFreePairNumerator d h=traceFreePairNumerator c h := by
  have ha : (quadraticChar F) d=(quadraticChar F) c := by
    rw [hd,map_mul,map_pow,quadraticChar_sq_one hu,mul_one]
  have hb : (quadraticChar F) (d+h)=(quadraticChar F) (c+h) := by
    rw [hdh,map_mul,map_pow,quadraticChar_sq_one hv,mul_one]
  have hz : (d=0) <-> c=0 := by rw [hd]; simp [hu]
  have hp : (d+h=0) <-> c+h=0 := by rw [hdh]; simp [hv]
  have hn : (d=-h) <-> c=-h := by
    constructor
    . intro he
      apply eq_neg_of_add_eq_zero_left
      apply hp.mp
      rw [he]
      ring
    . intro he
      apply eq_neg_of_add_eq_zero_left
      apply hp.mpr
      rw [he]
      ring
  have ht : twistPairNumerator d h=twistPairNumerator c h := by
    unfold twistPairNumerator
    rw [ha,hb]
  simp only [traceFreePairNumerator,hz,hn,ht]

theorem traceFreePairWeight_square_transport_gap (c d h u v : F)
    (hu : Not (u=0)) (hv : Not (v=0))
    (hd : d=c*u^2) (hdh : d+h=(c+h)*v^2) :
    traceFreePairWeight d h=traceFreePairWeight c h := by
  unfold traceFreePairWeight
  rw [traceFreePairNumerator_square_transport_gap c d h u v hu hv hd hdh]

theorem squarePairReach_zero_iff (c h : F) (hh : Not (h=0)) :
    squarePairReach c 0 h <-> (quadraticChar F) (h*(c+h))=1 := by
  constructor
  . intro hr
    let u : F := Classical.choose hr
    let v : F := Classical.choose (Classical.choose_spec hr)
    have hv : 0=c*u^2 /\ 0+h=(c+h)*v^2 :=
      Classical.choose_spec (Classical.choose_spec hr)
    have hv0 : Not (v=0) := by
      intro he
      have hi := hv.2
      rw [he] at hi
      simp only [zero_add,zero_pow (by decide : Not (2=0)),mul_zero] at hi
      exact hh hi
    have hi := congrArg (fun x : F => (quadraticChar F) x) hv.2
    simp only [zero_add,map_mul,map_pow,quadraticChar_sq_one hv0,mul_one] at hi
    rw [map_mul,<- hi]
    nlinarith only [quadraticChar_sq_one hh]
  . intro hc
    have hch : Not (c+h=0) := by intro he; rw [he,mul_zero] at hc; norm_num at hc
    have hs := (quadraticChar_one_iff_isSquare (mul_ne_zero hh hch)).mp hc
    let z : F := Classical.choose hs
    have hz : h*(c+h)=z*z := Classical.choose_spec hs
    have hz2 : z^2=h*(c+h) := by rw [hz]; ring
    refine Exists.intro 0 (Exists.intro (z/(c+h)) (And.intro (by simp) ?_))
    simp only [zero_add]
    symm
    calc
      (c+h)*(z/(c+h))^2=z^2/(c+h) := by field_simp [hch]
      _=h := by rw [hz2]; field_simp

theorem squarePairReach_neg_shift_iff (c h : F) (hh : Not (h=0)) :
    squarePairReach c (-h) h <-> (quadraticChar F) ((-h)*c)=1 := by
  constructor
  . intro hr
    let u : F := Classical.choose hr
    let v : F := Classical.choose (Classical.choose_spec hr)
    have hv : -h=c*u^2 /\ -h+h=(c+h)*v^2 :=
      Classical.choose_spec (Classical.choose_spec hr)
    have hu0 : Not (u=0) := by
      intro he
      have hi := hv.1
      rw [he] at hi
      simp only [zero_pow (by decide : Not (2=0)),mul_zero,neg_eq_zero] at hi
      exact hh hi
    have hi := congrArg (fun x : F => (quadraticChar F) x) hv.1
    simp only [map_mul,map_pow,quadraticChar_sq_one hu0,mul_one] at hi
    rw [map_mul,<- hi]
    nlinarith only [quadraticChar_sq_one (neg_ne_zero.mpr hh)]
  . intro hc
    have hc0 : Not (c=0) := by intro he; rw [he,mul_zero] at hc; norm_num at hc
    have hs := (quadraticChar_one_iff_isSquare
      (mul_ne_zero (neg_ne_zero.mpr hh) hc0)).mp hc
    let z : F := Classical.choose hs
    have hz : (-h)*c=z*z := Classical.choose_spec hs
    have hz2 : z^2=(-h)*c := by rw [hz]; ring
    refine Exists.intro (z/c) (Exists.intro 0 (And.intro ?_ (by simp)))
    symm
    calc
      c*(z/c)^2=z^2/c := by field_simp [hc0]
      _= -h := by rw [hz2]; field_simp

theorem squarePairCore_good (c h : F) (hc : squarePairCore c h) :
    Not (c=0) /\ Not (c+h=0) := by
  constructor
  . intro he
    have hi := hc.1
    rw [he,mul_zero] at hi
    norm_num at hi
  . intro he
    have hi := hc.2
    rw [he,mul_zero] at hi
    norm_num at hi

theorem squarePairCore_of_no_positive (c h : F) (hh : Not (h=0))
    (ha : Not ((quadraticChar F) ((-h)*c)=1))
    (hb : Not ((quadraticChar F) (h*(c+h))=1)) : squarePairCore c h := by
  have hc0 : Not (c=0) := by
    intro he
    apply hb
    rw [he,zero_add,map_mul]
    nlinarith only [quadraticChar_sq_one hh]
  have hch : Not (c+h=0) := by
    intro he
    have hc : c=-h := eq_neg_of_add_eq_zero_left he
    apply ha
    rw [hc,map_mul]
    nlinarith only [quadraticChar_sq_one (neg_ne_zero.mpr hh)]
  constructor
  . rcases QuadraticPairEuler.quadraticChar_real_signs ((-h)*c)
      (mul_ne_zero (neg_ne_zero.mpr hh) hc0) with hs | hs
    . exact False.elim (ha (by exact_mod_cast hs))
    . exact_mod_cast hs
  . rcases QuadraticPairEuler.quadraticChar_real_signs (h*(c+h))
      (mul_ne_zero hh hch) with hs | hs
    . exact False.elim (hb (by exact_mod_cast hs))
    . exact_mod_cast hs

theorem traceFreePairWeight_core (c h : F) (hc : squarePairCore c h)
    (hq : 5<=(Fintype.card F : Real)) : traceFreePairWeight c h=1 := by
  have hg := squarePairCore_good c h hc
  have hn : Not (c=-h) := by intro he; apply hg.2; rw [he]; ring
  have ha : (quadraticChar F) (-h)*(quadraticChar F) c=-1 := by
    rw [<- map_mul]; exact hc.1
  have hb : (quadraticChar F) h*(quadraticChar F) (c+h)=-1 := by
    rw [<- map_mul]; exact hc.2
  have hi : traceFreePairNumerator c h=(Fintype.card F : Int)-3 := by
    simp only [traceFreePairNumerator,ite_eq_right hg.1,ite_eq_right hn,twistPairNumerator,ha,hb]
    ring
  have hd : Not ((Fintype.card F : Real)-3=0) := ne_of_gt (by linarith only [hq])
  unfold traceFreePairWeight
  rw [hi]
  push_cast
  exact div_self hd

theorem squarePairCollapse_reachable (c h : F) (hh : Not (h=0)) :
    squarePairReach c (squarePairCollapse c h) h := by
  unfold squarePairCollapse
  split_ifs with hb ha
  . exact (squarePairReach_zero_iff c h hh).mpr hb
  . exact (squarePairReach_neg_shift_iff c h hh).mpr ha
  . exact squarePairReach_refl c h

theorem squarePairCollapse_profile (c h : F) (hh : Not (h=0))
    (hq : 5<=(Fintype.card F : Real)) :
    traceFreePairWeight (squarePairCollapse c h) h=
      if squarePairCore c h then 1 else 0 := by
  by_cases hc : squarePairCore c h
  . have ha : Not ((quadraticChar F) ((-h)*c)=1) := by rw [hc.1]; norm_num
    have hb : Not ((quadraticChar F) (h*(c+h))=1) := by rw [hc.2]; norm_num
    simp only [squarePairCollapse,ite_eq_right ha,ite_eq_right hb,ite_eq_left hc]
    exact traceFreePairWeight_core c h hc hq
  . rw [ite_eq_right hc]
    unfold squarePairCollapse
    split_ifs with hb ha
    . exact traceFreePairWeight_zero h
    . exact traceFreePairWeight_neg_shift h
    . exact False.elim (hc (squarePairCore_of_no_positive c h hh ha hb))

theorem traceFreePairWeight_square_reach_cases (c d h : F)
    (hr : squarePairReach c d h) :
    traceFreePairWeight d h=0 \/ traceFreePairWeight d h=traceFreePairWeight c h := by
  let u : F := Classical.choose hr
  let v : F := Classical.choose (Classical.choose_spec hr)
  have hv : d=c*u^2 /\ d+h=(c+h)*v^2 :=
    Classical.choose_spec (Classical.choose_spec hr)
  by_cases hu0 : u=0
  . left
    have hd : d=0 := by simpa only [hu0,zero_pow (by decide : Not (2=0)),mul_zero] using hv.1
    rw [hd,traceFreePairWeight_zero]
  . by_cases hv0 : v=0
    . left
      have hd : d=-h := eq_neg_of_add_eq_zero_left
        (by simpa only [hv0,zero_pow (by decide : Not (2=0)),mul_zero] using hv.2)
      rw [hd,traceFreePairWeight_neg_shift]
    . right
      exact traceFreePairWeight_square_transport_gap c d h u v hu0 hv0 hv.1 hv.2

theorem traceFreePairWeight_square_core (c d h : F) (hh : Not (h=0))
    (hq : 5<=(Fintype.card F : Real)) (hc : squarePairCore c h)
    (hr : squarePairReach c d h) : traceFreePairWeight d h=1 := by
  have hd0 : Not (d=0) := by
    intro he
    have hr0 : squarePairReach c 0 h := by rw [<- he]; exact hr
    have hi := (squarePairReach_zero_iff c h hh).mp hr0
    rw [hc.2] at hi
    norm_num at hi
  have hdn : Not (d=-h) := by
    intro he
    have hrn : squarePairReach c (-h) h := by rw [<- he]; exact hr
    have hi := (squarePairReach_neg_shift_iff c h hh).mp hrn
    rw [hc.1] at hi
    norm_num at hi
  let u : F := Classical.choose hr
  let v : F := Classical.choose (Classical.choose_spec hr)
  have hv : d=c*u^2 /\ d+h=(c+h)*v^2 :=
    Classical.choose_spec (Classical.choose_spec hr)
  have hu0 : Not (u=0) := by intro he; apply hd0; rw [hv.1,he]; simp
  have hv0 : Not (v=0) := by
    intro he
    apply hdn
    apply eq_neg_of_add_eq_zero_left
    rw [hv.2,he]
    simp
  rw [traceFreePairWeight_square_transport_gap c d h u v hu0 hv0 hv.1 hv.2]
  exact traceFreePairWeight_core c h hc hq

theorem traceFreePairWeight_nonneg_all (c h : F) (hh : Not (h=0))
    (hq : 5<=(Fintype.card F : Real)) : 0<=traceFreePairWeight c h := by
  by_cases hc : c=0
  . rw [hc,traceFreePairWeight_zero]
  . by_cases hn : c=-h
    . rw [hn,traceFreePairWeight_neg_shift]
    . have hch : Not (c+h=0) := by intro he; exact hn (eq_neg_of_add_eq_zero_left he)
      exact le_trans (by norm_num) (traceFreePairWeight_good_bounds c h hc hch hh hq).1

end FiniteField
