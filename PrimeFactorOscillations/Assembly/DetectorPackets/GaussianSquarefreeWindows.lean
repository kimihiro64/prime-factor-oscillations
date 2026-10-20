/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Proof.DetectorPackets.GaussianSquarefreeEuler

/-!
# GaussianSquarefreeWindows

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
# Joint principal windows for the squarefree Gaussian kernel

Positive principal window weights are normalized to total mass one.
The proof retains the exact compensated ratio. It applies uniformly to
every finite set and target character satisfying the displayed local
norm hypotheses. It does not prove a low or high arithmetic moment.
-/


noncomputable section
namespace PrimeFactorOscillations.GaussianSquarefreeWindows
open GaussianSquarefreeEuler

def principalWindow {P : Type*} (S : Finset P) (w h : P -> Real)
    (a : P -> Complex) : Complex :=
  S.sum (fun p => (w p:Complex)*principalMarkedRatio (h p) (a p))

theorem principal_window_error {P : Type*} (S : Finset P) (w h : P -> Real)
    (a : P -> Complex) (r : Real) (hr : r <= 1/2)
    (hw : forall p, Membership.mem S p -> 0 <= w p)
    (hmass : S.sum w=1)
    (hh : forall p, Membership.mem S p -> 0 <= h p /\ h p <= 1)
    (ha : forall p, Membership.mem S p -> norm (a p) <= r) :
    norm (principalWindow S w h a+1) <= 2*r := by
  have hmassC : S.sum (fun p => (w p:Complex))=1 := by
    exact_mod_cast hmass
  have he : principalWindow S w h a+1=
      S.sum (fun p => (w p:Complex)*(principalMarkedRatio (h p) (a p)+1)) := by
    simp only [mul_add, mul_one, Finset.sum_add_distrib]
    rw [hmassC]
    rfl
  rw [he]
  calc
    norm (S.sum (fun p => (w p:Complex)*
        (principalMarkedRatio (h p) (a p)+1))) <=
        S.sum (fun p => norm ((w p:Complex)*
          (principalMarkedRatio (h p) (a p)+1))) := norm_sum_le _ _
    _ <= S.sum (fun p => w p*(2*r)) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw p hp)]
      have hl := marked_ratio_error_bound (h p) (hh p hp).1 (hh p hp).2
        (a p) ((ha p hp).trans hr)
      have hb : norm (principalMarkedRatio (h p) (a p)+1) <= 2*r := by
        linarith [ha p hp]
      exact mul_le_mul_of_nonneg_left hb (hw p hp)
    _ = 2*r := by rw [<-Finset.sum_mul, hmass, one_mul]

theorem product_error {I : Type*} (S : Finset I) (z : I -> Complex)
    (e : Real) (he : 0 <= e)
    (hz : forall i, Membership.mem S i -> norm (z i-1) <= e) :
    norm (S.prod z-1) <= (1+e)^S.card-1 := by
  classical
  have hb (T : Finset I) :
      (forall i, Membership.mem T i -> norm (z i-1) <= e) ->
      norm (T.prod z) <= (1+e)^T.card /\
        norm (T.prod z-1) <= (1+e)^T.card-1 := by
    induction T using Finset.induction_on with
    | empty =>
      intro ht
      constructor <;> simp
    | @insert i T hi ih =>
      intro ht
      have hzi : norm (z i-1) <= e := ht i (Finset.mem_insert_self _ _)
      have hT := ih (fun j hj => ht j (Finset.mem_insert_of_mem hj))
      have hzn : norm (z i) <= 1+e := by
        have hh := norm_add_le (z i-1) (1:Complex)
        have heq : z i-1+1=z i := by ring
        rw [heq, norm_one] at hh
        linarith
      have hcard : (insert i T).card=T.card+1 := by simp [hi]
      rw [Finset.prod_insert hi, hcard]
      constructor
      . rw [norm_mul, pow_succ]
        calc
          norm (z i)*norm (T.prod z) <= (1+e)*(1+e)^T.card :=
            mul_le_mul hzn hT.1 (norm_nonneg _) (by linarith)
          _ = (1+e)^T.card*(1+e) := by ring
      . have heq : z i*T.prod z-1=
            (z i-1)*T.prod z+(T.prod z-1) := by ring
        rw [heq]
        calc
          norm ((z i-1)*T.prod z+(T.prod z-1)) <=
              norm ((z i-1)*T.prod z)+norm (T.prod z-1) := norm_add_le _ _
          _ <= e*(1+e)^T.card+((1+e)^T.card-1) := by
            rw [norm_mul]
            exact add_le_add (mul_le_mul hzi hT.1 (norm_nonneg _) he) hT.2
          _ = (1+e)^(T.card+1)-1 := by rw [pow_succ]; ring
  exact (hb S hz).2

theorem product_nonzero {I : Type*} (S : Finset I) (z : I -> Complex)
    (e : Real) (he : 0 <= e)
    (hz : forall i, Membership.mem S i -> norm (z i-1) <= e)
    (hsmall : (1+e)^S.card < 2) :
    Not (S.prod z=0) := by
  have hb := product_error S z e he hz
  intro hzero
  rw [hzero, zero_sub, norm_neg, norm_one] at hb
  linarith

theorem joint_principal_window_signal {I P : Type*} (J : Finset I)
    (S : I -> Finset P) (w h : I -> P -> Real) (a : I -> P -> Complex)
    (r : Real) (hr0 : 0 <= r) (hr : r <= 1/2)
    (hw : forall i, Membership.mem J i -> forall p, Membership.mem (S i) p -> 0 <= w i p)
    (hmass : forall i, Membership.mem J i -> (S i).sum (w i)=1)
    (hh : forall i, Membership.mem J i -> forall p, Membership.mem (S i) p ->
      0 <= h i p /\ h i p <= 1)
    (ha : forall i, Membership.mem J i -> forall p, Membership.mem (S i) p ->
      norm (a i p) <= r)
    (hsmall : (1+2*r)^J.card < 2) :
    norm (J.prod (fun i => -principalWindow (S i) (w i) (h i) (a i))-1) <=
        (1+2*r)^J.card-1 /\
      Not (J.prod (fun i => -principalWindow (S i) (w i) (h i) (a i))=0) := by
  have hz (i : I) (hi : Membership.mem J i) :
      norm (-principalWindow (S i) (w i) (h i) (a i)-1) <= 2*r := by
    have heq : -principalWindow (S i) (w i) (h i) (a i)-1=
        -(principalWindow (S i) (w i) (h i) (a i)+1) := by ring
    rw [heq, norm_neg]
    exact principal_window_error (S i) (w i) (h i) (a i) r hr
      (hw i hi) (hmass i hi) (hh i hi) (ha i hi)
  exact And.intro
    (product_error J _ (2*r) (by linarith) hz)
    (product_nonzero J _ (2*r) (by linarith) hz hsmall)

end PrimeFactorOscillations.GaussianSquarefreeWindows
