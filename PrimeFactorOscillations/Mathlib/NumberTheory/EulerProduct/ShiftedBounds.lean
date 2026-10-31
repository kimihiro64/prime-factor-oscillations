/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Uniform finite comparisons of shifted Euler factors

The ratio of shifted and ordinary Euler factors telescopes over consecutive
integers. Every finite subset inherits the same positive lower constant.
No prime-distribution estimate is used.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Finset

def shiftedEulerFactor (c : Real) (n : Nat) : Real := 1-1/((n : Real)-c)

def eulerShiftRatio (c : Real) (n : Nat) : Real :=
  (n : Real)*((n : Real)-c-1)/(((n : Real)-c)*((n : Real)-1))

private theorem real_prod_le_one {I : Type*} (s : Finset I) (f : I -> Real)
    (h0 : forall i, Membership.mem s i -> 0<=f i)
    (h1 : forall i, Membership.mem s i -> f i<=1) : s.prod f<=1 := by
  classical
  revert h0 h1
  induction s using Finset.induction_on with
  | empty => intro _ _; simp
  | @insert i s hi ih =>
    intro h0 h1
    have hp : 0<=s.prod f := Finset.prod_nonneg
      (fun j hj => h0 j (Finset.mem_insert_of_mem hj))
    have ht := ih (fun j hj => h0 j (Finset.mem_insert_of_mem hj))
      (fun j hj => h1 j (Finset.mem_insert_of_mem hj))
    rw [Finset.prod_insert hi]
    calc
      _<=1*s.prod f := mul_le_mul_of_nonneg_right (h1 i (Finset.mem_insert_self i s)) hp
      _<=1 := by simpa only [one_mul] using ht

private theorem real_prod_reverse_subset {I : Type*} [DecidableEq I]
    (s t : Finset I) (hst : forall {i : I}, Membership.mem s i -> Membership.mem t i) (f : I -> Real)
    (h0 : forall i, Membership.mem t i -> 0<=f i)
    (h1 : forall i, Membership.mem t i -> f i<=1) : t.prod f<=s.prod f := by
  have hd : (t \ s).prod f<=1 := real_prod_le_one (t \ s) f
    (fun i hi => h0 i (Finset.mem_sdiff.mp hi).1)
    (fun i hi => h1 i (Finset.mem_sdiff.mp hi).1)
  have hs : 0<=s.prod f := Finset.prod_nonneg (fun i hi => h0 i (hst hi))
  have hsplit : (t \ s).prod f*s.prod f=t.prod f :=
    Finset.prod_sdiff (fun {i} hi => hst (i := i) hi)
  rw [<- hsplit]
  calc
    _<=1*s.prod f := mul_le_mul_of_nonneg_right hd hs
    _=s.prod f := one_mul _

theorem eulerShiftRatio_bounds (c : Real) (n : Nat) (hc : 0<=c)
    (hn : c+1<(n : Real)) :
    And (0<eulerShiftRatio c n) (eulerShiftRatio c n<=1) := by
  have h0 : 0<(n : Real) := by linarith only [hc,hn]
  have h1 : 0<(n : Real)-1 := by linarith only [hc,hn]
  have h2 : 0<(n : Real)-c := by linarith only [hn]
  have h3 : 0<(n : Real)-c-1 := by linarith only [hn]
  constructor
  . exact div_pos (mul_pos h0 h3) (mul_pos h2 h1)
  . have hp : 0<=c/(((n : Real)-c)*((n : Real)-1)) :=
      div_nonneg hc (mul_nonneg h2.le h1.le)
    have he : 1-eulerShiftRatio c n=c/(((n : Real)-c)*((n : Real)-1)) := by
      unfold eulerShiftRatio
      field_simp [ne_of_gt h2,ne_of_gt h1]
      ring
    rw [<- he] at hp
    linarith only [hp]

theorem eulerShiftRatio_Icc (c : Real) (m N : Nat) (hc : 0<=c)
    (hm : c+1<(m : Real)) (hmN : m<=N) :
    (Finset.Icc m N).prod (eulerShiftRatio c)=
      (N : Real)*((m : Real)-c-1)/(((m : Real)-1)*((N : Real)-c)) := by
  induction N, hmN using Nat.le_induction with
  | base =>
    rw [Finset.Icc_self,Finset.prod_singleton]
    unfold eulerShiftRatio
    have h1 : 0<(m : Real)-1 := by linarith only [hc,hm]
    have h2 : 0<(m : Real)-c := by linarith only [hm]
    field_simp [ne_of_gt h1,ne_of_gt h2]
  | succ N hN ih =>
    rw [Finset.prod_Icc_succ_top (by omega),ih]
    unfold eulerShiftRatio
    norm_num only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right]
    have hmn : (m : Real)<=(N : Real) := by exact_mod_cast hN
    have hm1 : 0<(m : Real)-1 := by linarith only [hc,hm]
    have hN0 : 0<(N : Real) := by linarith only [hc,hm,hmn]
    have hNc : 0<(N : Real)-c := by linarith only [hm,hmn]
    have hNc1 : 0<(N : Real)+1-c := by linarith only [hm,hmn]
    field_simp [ne_of_gt hm1,ne_of_gt hN0,ne_of_gt hNc,ne_of_gt hNc1]
    ring

theorem eulerShiftRatio_Icc_lower (c : Real) (m N : Nat) (hc : 0<=c)
    (hm : c+1<(m : Real)) (hmN : m<=N) :
    ((m : Real)-c-1)/((m : Real)-1)<=
      (Finset.Icc m N).prod (eulerShiftRatio c) := by
  rw [eulerShiftRatio_Icc c m N hc hm hmN]
  have hmn : (m : Real)<=(N : Real) := by exact_mod_cast hmN
  have hm1 : 0<(m : Real)-1 := by linarith only [hc,hm]
  have hNc : 0<(N : Real)-c := by linarith only [hm,hmn]
  have ha : 0<=((m : Real)-c-1)/((m : Real)-1) :=
    div_nonneg (by linarith only [hm]) hm1.le
  have hp : 0<=(((m : Real)-c-1)/((m : Real)-1))*c/((N : Real)-c) :=
    div_nonneg (mul_nonneg ha hc) hNc.le
  have he :
      (N : Real)*((m : Real)-c-1)/(((m : Real)-1)*((N : Real)-c))-
        ((m : Real)-c-1)/((m : Real)-1)=
      (((m : Real)-c-1)/((m : Real)-1))*c/((N : Real)-c) := by
    field_simp [ne_of_gt hm1,ne_of_gt hNc]
    ring
  rw [<- he] at hp
  linarith only [hp]

theorem eulerShiftRatio_subset_lower (s : Finset Nat) (c : Real) (m : Nat)
    (hc : 0<=c) (hm : c+1<(m : Real))
    (hs : forall n, Membership.mem s n -> m<=n) :
    ((m : Real)-c-1)/((m : Real)-1)<=s.prod (eulerShiftRatio c) := by
  let N : Nat := max m (s.sup id)
  have hmN : m<=N := le_max_left _ _
  have hsub : forall {n : Nat}, Membership.mem s n -> Membership.mem (Finset.Icc m N) n := by
    intro n hn
    apply Finset.mem_Icc.mpr
    refine And.intro (hs n hn) ?_
    exact le_trans (Finset.le_sup (f := id) hn) (le_max_right _ _)
  have hb (n : Nat) (hn : Membership.mem (Finset.Icc m N) n) :
      And (0<eulerShiftRatio c n) (eulerShiftRatio c n<=1) := by
    have hmn : (m : Real)<=(n : Real) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    exact eulerShiftRatio_bounds c n hc (lt_of_lt_of_le hm hmn)
  exact (eulerShiftRatio_Icc_lower c m N hc hm hmN).trans
    (real_prod_reverse_subset s (Finset.Icc m N) hsub (eulerShiftRatio c)
      (fun n hn => (hb n hn).1.le) (fun n hn => (hb n hn).2))

theorem shiftedEulerProduct_bounds (s : Finset Nat) (c : Real) (m : Nat)
    (hc : 0<=c) (hm : c+1<(m : Real))
    (hs : forall n, Membership.mem s n -> m<=n) :
    And
      ((((m : Real)-c-1)/((m : Real)-1))*
        s.prod (shiftedEulerFactor 0)<=s.prod (shiftedEulerFactor c))
      (s.prod (shiftedEulerFactor c)<=s.prod (shiftedEulerFactor 0)) := by
  have hn (n : Nat) (hn : Membership.mem s n) : c+1<(n : Real) := by
    have hmn : (m : Real)<=(n : Real) := by exact_mod_cast hs n hn
    exact lt_of_lt_of_le hm hmn
  have h0 : 0<=s.prod (shiftedEulerFactor 0) := by
    apply Finset.prod_nonneg
    intro n hns
    have hN : 0<(n : Real) := by have ht := hn n hns; linarith only [ht,hc]
    have hN1 : 0<=(n : Real)-1 := by have ht := hn n hns; linarith only [ht,hc]
    have he : shiftedEulerFactor 0 n=((n : Real)-1)/(n : Real) := by
      unfold shiftedEulerFactor
      field_simp [ne_of_gt hN]
      ring
    rw [he]
    exact div_nonneg hN1 hN.le
  have he : s.prod (eulerShiftRatio c)*s.prod (shiftedEulerFactor 0)=
      s.prod (shiftedEulerFactor c) := by
    rw [<- Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro n hns
    have hN : 0<(n : Real) := by have ht := hn n hns; linarith only [ht,hc]
    have hN1 : 0<(n : Real)-1 := by have ht := hn n hns; linarith only [ht,hc]
    have hNc : 0<(n : Real)-c := by have ht := hn n hns; linarith only [ht]
    unfold eulerShiftRatio shiftedEulerFactor
    field_simp [ne_of_gt hN,ne_of_gt hN1,ne_of_gt hNc]
    ring
  have hl := eulerShiftRatio_subset_lower s c m hc hm hs
  have hu := real_prod_le_one s (eulerShiftRatio c)
    (fun n hns => (eulerShiftRatio_bounds c n hc (hn n hns)).1.le)
    (fun n hns => (eulerShiftRatio_bounds c n hc (hn n hns)).2)
  constructor
  . calc
      _<=s.prod (eulerShiftRatio c)*s.prod (shiftedEulerFactor 0) :=
        mul_le_mul_of_nonneg_right hl h0
      _=_ := he
  . calc
      _=s.prod (eulerShiftRatio c)*s.prod (shiftedEulerFactor 0) := he.symm
      _<=1*s.prod (shiftedEulerFactor 0) := mul_le_mul_of_nonneg_right hu h0
      _=_ := one_mul _

end Finset
