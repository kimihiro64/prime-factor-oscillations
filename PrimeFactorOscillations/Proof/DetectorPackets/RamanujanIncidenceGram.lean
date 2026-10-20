/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import OAI.NumberTheory.DirichletL.MeanSquare.TransformedColumns
import OAI.NumberTheory.DirichletL.Mellin.InverseContour
import OAI.NumberTheory.DirichletL.QuadraticSieve.FiniteOperator

/-!
# RamanujanIncidenceGram

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
# The nonzero-row arithmetic estimate for the exceptional reflected sector

The complete normalized divisor kernel is bounded before its branches are
separated. The eventual application is the full j=4 reflected packet, with
both nonzero theta indices retained and product length charged. No global
zero-free exponent improvement is asserted here.
-/

set_option maxHeartbeats 1600000

noncomputable section
namespace OAI.SevenEighths.RamanujanIncidenceGram
open scoped Classical BigOperators
open IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem weighted_schur {A B : Type*} (R : Finset A) (C : Finset B)
    (k : A -> B -> Real) (w a : B -> Real) (H V : Real)
    (hk : forall r, Membership.mem R r -> forall c, Membership.mem C c -> 0<=k r c)
    (hw : forall c, Membership.mem C c -> 0<w c)
    (ha : forall c, Membership.mem C c -> 0<=a c)
    (hH : 0<=H)
    (hrow : forall r, Membership.mem R r -> (C.sum fun c=>k r c*w c)<=H)
    (hcol : forall c, Membership.mem C c -> (R.sum fun r=>k r c/w c)<=V) :
    (R.sum fun r=>(C.sum fun c=>a c*k r c)^2)<=
      H*V*(C.sum fun c=>(a c)^2) := by
  have hpoint (r : A) (hr : Membership.mem R r) :
      (C.sum fun c=>a c*k r c)^2<=H*(C.sum fun c=>k r c/w c*(a c)^2) := by
    let f := fun c=>Real.sqrt (k r c*w c)
    let g := fun c=>Real.sqrt (k r c/w c)*a c
    have hprod (c : B) (hc : Membership.mem C c) : f c*g c=a c*k r c := by
      have hk0 := hk r hr c hc
      have hw0 := hw c hc
      have hrad : k r c*w c*(k r c/w c)=(k r c)^2 := by
        field_simp
      dsimp [f,g]
      rw [<-mul_assoc,<-Real.sqrt_mul (mul_nonneg hk0 hw0.le),hrad,
        Real.sqrt_sq hk0]
      ring
    have hf (c : B) (hc : Membership.mem C c) : (f c)^2=k r c*w c :=
      Real.sq_sqrt (mul_nonneg (hk r hr c hc) (hw c hc).le)
    have hg (c : B) (hc : Membership.mem C c) : (g c)^2=k r c/w c*(a c)^2 := by
      dsimp [g]
      rw [mul_pow,Real.sq_sqrt (div_nonneg (hk r hr c hc) (hw c hc).le)]
    have hb := Finset.sum_mul_sq_le_sq_mul_sq C f g
    rw [Finset.sum_congr rfl hprod,Finset.sum_congr rfl hf,
      Finset.sum_congr rfl hg] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (hrow r hr)
      (Finset.sum_nonneg fun c hc=>mul_nonneg
        (div_nonneg (hk r hr c hc) (hw c hc).le) (sq_nonneg _)))
  calc
    _ <= R.sum (fun r=>H*(C.sum fun c=>k r c/w c*(a c)^2)) :=
      Finset.sum_le_sum hpoint
    _ = H*(C.sum fun c=>(R.sum fun r=>k r c/w c)*(a c)^2) := by
      rw [<-Finset.mul_sum,Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro c hc
      exact (Finset.sum_mul ..).symm
    _ <= H*(C.sum fun c=>V*(a c)^2) := by
      apply mul_le_mul_of_nonneg_left _ hH
      exact Finset.sum_le_sum fun c hc=>mul_le_mul_of_nonneg_right (hcol c hc) (sq_nonneg _)
    _ = _ := by rw [<-Finset.mul_sum];ring

theorem multiples_weighted_count (R : Finset Id) (M : Real) (hM : 1<=M)
    (hR0 : forall I, Membership.mem R I -> Not (I=0))
    (hR : forall I, Membership.mem R I -> (I.absNorm:Real)<=M)
    (D : Id) (hD : Not (D=0)) :
    ((R.filter fun I=>Dvd.dvd D I).card:Real)*(D.absNorm:Real)<=128*M := by
  let T := R.filter fun I=>Dvd.dvd D I
  by_cases hT : T.Nonempty
  . let q (I : T) : Id := Classical.choose (Finset.mem_filter.mp I.property).2
    have hq (I : T) : I.val=D*q I := Classical.choose_spec (Finset.mem_filter.mp I.property).2
    have hq0 (I : T) : Not (q I=0) := by
      intro he
      exact hR0 I.val (Finset.mem_filter.mp I.property).1
        (by rw [hq I,he,mul_zero])
    have hDn : 0<(D.absNorm:Real) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD)
    have hnorm (I : T) : (D.absNorm:Real)*((q I).absNorm:Real)<=M := by
      have hh := hR I.val (Finset.mem_filter.mp I.property).1
      rw [hq I,map_mul,Nat.cast_mul] at hh
      exact hh
    have hratio : 1<=M/(D.absNorm:Real) := by
      let I : T := {val:=Classical.choose hT, property:=Classical.choose_spec hT}
      have hn : (1:Real)<=((q I).absNorm:Real) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hq0 I))
      have hle : (D.absNorm:Real)<=M := by
        have hh := hnorm I
        nlinarith
      have hh := div_le_div_of_nonneg_right hle hDn.le
      simpa only [div_self (ne_of_gt hDn)] using hh
    let F : Finset Id := Finset.univ.image q
    have hf0 (J : Id) (hJ : Membership.mem F J) : Not (J=0) := by
      choose I hI he using Finset.mem_image.mp hJ
      simpa only [<-he] using hq0 I
    have hfN (J : Id) (hJ : Membership.mem F J) : (J.absNorm:Real)<=M/(D.absNorm:Real) := by
      choose I hI he using Finset.mem_image.mp hJ
      rw [<-he]
      have hh := div_le_div_of_nonneg_right (hnorm I) hDn.le
      have he : (D.absNorm:Real)*((q I).absNorm:Real)/(D.absNorm:Real)=((q I).absNorm:Real) := by
        field_simp
      rwa [he] at hh
    have hi : Function.Injective q := by
      intro I J he
      apply Subtype.ext
      exact (hq I).trans ((congrArg (fun x:Id=>D*x) he).trans (hq J).symm)
    have hc : F.card=T.card := by
      change (Finset.univ.image q).card=T.card
      rw [Finset.card_image_of_injective _ hi]
      simp
    have hh := DescentFiberCost.finite_ideal_count_real F (M/(D.absNorm:Real)) hratio hf0 hfN
    rw [hc] at hh
    change (T.card:Real)*(D.absNorm:Real)<=128*M
    have hp := mul_le_mul_of_nonneg_right hh hDn.le
    have he : (128*(M/(D.absNorm:Real)))*(D.absNorm:Real)=128*M := by
      field_simp
    exact hp.trans_eq he
  . have he : T=Finset.empty := Finset.not_nonempty_iff_eq_empty.mp hT
    change (T.card:Real)*(D.absNorm:Real)<=128*M
    rw [he]
    simp only [Finset.empty,Finset.card,Multiset.card_zero,Nat.cast_zero,zero_mul]
    positivity
end OAI.SevenEighths.RamanujanIncidenceGram
