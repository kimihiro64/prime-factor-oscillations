/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import OAI.NumberTheory.DirichletL.PrimeRows.TupleBound

/-!
# Ramified terms in the extended selected-prime bound

Retains every finite source sector and the multiplicity bound. The scalar
powers give the selected ramified bound on Re(x)>=3/4, Re(w)>=1/2 and
Re(z)>=17/50. Adapted from the pinned OAI selected-row proofs.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.SelectedTupleExtension
open scoped Classical
open OAI OAI.SevenEighths
open OAI.ActualEisensteinCubic OAI.CompletedGauss OAI.ConcretePrimeRowBridge
open OAI.SevenEighths.ProbePrimePower OAI.SevenEighths.HeckeFamily
open OAI.SevenEighths.HeckeInverseAmplification OAI.SevenEighths.ProbePhysical
open OAI.SevenEighths.ProbeEuler OAI.SevenEighths.ProbeRow
open OAI.SevenEighths.ProbeHighRowFamily
open OAI.CanonicalQuadraticSieve OAI.CanonicalRowCompletion
local notation "O" => OAI.ActualEisensteinCubic.O

variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : Not (Membership.mem (Ideal.span {p}) goodLambda))
  (hc : Not (ringChar (HasQuotient.Quotient O (Ideal.span {p} : Ideal O)) = 2))

include hc in
theorem sourceRowTerm_selected_base_extended (eta a rho x w z : Complex)
    (heta : norm (eta)<=1) (ha : norm (a)<=1) (hrho : rho^6=1)
    (hx : (3/4:Real)<=x.re) (_hw : (1/2:Real)<=w.re) (hz : (17/50:Real)<=z.re)
    (j e l k m : Nat) (hj : j<6) (hk : k<=1)
    (hf : Or (e=0 /\ l=2) (Or (e=1 /\ l=0) (Or (e=0 /\ l=1) (e=1 /\ l=1)))) :
    norm (sourceRowTerm p hp hg eta a rho x w z j e l k m)<=2*(Ideal.absNorm (Ideal.span {p}):Real)^(-x.re+max (1-w.re) 0) := by
  let Q : Real := Ideal.absNorm (Ideal.span {p})
  have hQ : 0<Q := by
    dsimp only [Q]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hm0 : (0:Real)<=m := Nat.cast_nonneg m
  have hb0 : (0:Real)<=max (1-w.re) 0 := le_max_right _ _
  have hb1 : 1-w.re<=max (1-w.re) 0 := le_max_left _ _
  have hzm : 0<=6*z.re*(m:Real) := by positivity
  have hzm1 (hm : Not (m=0)) : 6*z.re<=6*z.re*(m:Real) := by
    have hm1 : (1:Real)<=m := by exact_mod_cast (by omega : 1<=m)
    nlinarith
  have hrelax (v : Real) : Q^v<=2*Q^v := by nlinarith [Real.rpow_nonneg hQ.le v]
  have hz0 (t k : Nat) (ht : Not (t=0)) : sourceScalar p hp hg t k (j+6*m)=
      positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (t-1) k (j+6*m) := by
    rw [sourceScalar,ite_eq_right ht]
  rcases hf with hf | hf | hf | hf
  . have he := hf.1
    have hl := hf.2
    subst e
    subst l
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    . by_cases hm : m=0
      . apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hrho j 0 2 0 m 5 (-x.re+max (1-w.re) 0)
        . have hs := even_base_kzero_norm p hp hg hc m j hj
          rw [ite_eq_left hm] at hs
          simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 6 0 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
            hs.trans (show Q^5<=2*Q^5 by nlinarith [pow_nonneg hQ.le 5])
        . norm_num only [Nat.cast_zero,Nat.cast_ofNat,mul_zero,mul_one,sub_zero]
          linarith
      . apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hrho j 0 2 0 m 6 (-x.re+max (1-w.re) 0)
        . have hs := even_base_kzero_norm p hp hg hc m j hj
          rw [ite_eq_right hm] at hs
          simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 6 0 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
            hs.trans (show Q^6<=2*Q^6 by nlinarith [pow_nonneg hQ.le 6])
        . norm_num only [Nat.cast_zero,Nat.cast_ofNat,mul_zero,mul_one,sub_zero]
          nlinarith [hzm1 hm]
    . by_cases hm : m=0
      . subst m
        simp only [sourceRowTerm,sourceScalar,Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub,
          Nat.reduceEqDiff,ite_false,mul_zero,add_zero,even_base_kone_zero p hp hg hc j hj,
          sourceWeightedScalar,zero_mul,mul_zero,norm_zero]
        positivity
      . apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hrho j 0 2 1 m 6 (-x.re+max (1-w.re) 0)
        . have hs := nonprincipal_kone_norm p hp hg hc 5 (j+6*m) (by decide) (by decide)
          simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 6 1 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
            hs.trans (show Q^6<=2*Q^6 by nlinarith [pow_nonneg hQ.le 6])
        . norm_num only [Nat.cast_zero,Nat.cast_ofNat,mul_zero,mul_one,sub_zero]
          nlinarith [hzm1 hm]
  . have he := hf.1
    have hl := hf.2
    subst e
    subst l
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    . apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hrho j 1 0 0 m (1/2) (-x.re+max (1-w.re) 0)
      . have hs := nonprincipal_kzero_norm p hp hg hc 0 (j+6*m) (by decide)
        simp only [pow_zero,one_mul,Real.sqrt_eq_rpow] at hs
        simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 1 0 (by decide),Nat.reduceSub] using hs.trans (hrelax (1/2))
      . norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith
    . apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hrho j 1 0 1 m (3/2) (-x.re+max (1-w.re) 0)
      . have hs := positiveScalar_norm_le p hp hg hc 0 1 (j+6*m) (by decide)
        simp only [Nat.zero_add,pow_one] at hs
        have he : 2*Q*Real.sqrt Q=2*Q^(3/2:Real) := by
          have ht := pow_mul_sqrt Q hQ 1
          norm_num at ht
          rw [mul_assoc,ht]
        rw [he] at hs
        simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 1 1 (by decide),Nat.reduceSub] using hs
      . norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith
  . have he := hf.1
    have hl := hf.2
    subst e
    subst l
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    . apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hrho j 0 1 0 m (5/2) (-x.re+max (1-w.re) 0)
      . have hs := nonprincipal_kzero_norm p hp hg hc 2 (j+6*m) (by decide)
        rw [pow_mul_sqrt _ hQ] at hs
        norm_num only [Nat.cast_ofNat] at hs
        convert hs.trans (hrelax (5/2)) using 1 ;
          simp only [sourceScalar,Nat.reduceMul,Nat.reduceAdd,Nat.reduceEqDiff,ite_false,Nat.reduceSub]
      . norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith
    . apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hrho j 0 1 1 m 3 (-x.re+max (1-w.re) 0)
      . have hs := nonprincipal_kone_norm p hp hg hc 2 (j+6*m) (by decide) (by decide)
        simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 3 1 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
          hs.trans (show Q^3<=2*Q^3 by nlinarith [pow_nonneg hQ.le 3])
      . norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith
  . have he := hf.1
    have hl := hf.2
    subst e
    subst l
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    . apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hrho j 1 1 0 m (7/2) (-x.re+max (1-w.re) 0)
      . have hs := nonprincipal_kzero_norm p hp hg hc 3 (j+6*m) (by decide)
        rw [pow_mul_sqrt _ hQ] at hs
        norm_num only [Nat.cast_ofNat] at hs
        convert hs.trans (hrelax (7/2)) using 1 ;
          simp only [sourceScalar,Nat.reduceMul,Nat.reduceAdd,Nat.reduceEqDiff,ite_false,Nat.reduceSub]
      . norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith
    . apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hrho j 1 1 1 m 4 (-x.re+max (1-w.re) 0)
      . have hs := nonprincipal_kone_norm p hp hg hc 3 (j+6*m) (by decide) (by decide)
        simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 4 1 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
          hs.trans (show Q^4<=2*Q^4 by nlinarith [pow_nonneg hQ.le 4])
      . norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith

include hc in
lemma rowBaseFinite_selected_bound_extended (eta a rho x w z : Complex)
    (hQ : (4:Real)<=Ideal.absNorm (Ideal.span {p}))
    (heta : norm (eta)<=1) (ha : norm (a)<=1) (hrho : rho^6=1)
    (hx : (3/4:Real)<=x.re) (hw : (1/2:Real)<=w.re) (hz : (17/50:Real)<=z.re)
    (j e l : Nat) (hj : j<6)
    (hf : Or (e=0 /\ l=2) (Or (e=1 /\ l=0) (Or (e=0 /\ l=1) (e=1 /\ l=1)))) :
    norm (rowBaseFinite p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):Complex)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):Complex)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
      rho j e l)<=16*(Ideal.absNorm (Ideal.span {p}):Real)^(-x.re+max (1-w.re) 0) := by
  have hpow : 0<=(Ideal.absNorm (Ideal.span {p}):Real)^(-x.re+max (1-w.re) 0) := by positivity
  have hv := ProbeLocal.inv_one_sub_norm_le_two _ (first_region_V_half _ hQ z hz)
  have ht' (k : Fin 2) (m : Nat) :
      norm (rowMarkedTerm p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):Complex)^(-x))
        ((Ideal.absNorm (Ideal.span {p}):Complex)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
        rho j e l k.val m)<=2*(Ideal.absNorm (Ideal.span {p}):Real)^(-x.re+max (1-w.re) 0) := by
    have ht : Not (e+3*l=0) := by rcases hf with h|h|h|h <;> omega
    rw [<-sourceRowTerm_pos p hp hg eta a rho x w z j e l k.val m ht]
    exact sourceRowTerm_selected_base_extended p hp hg hc eta a rho x w z heta ha hrho hx hw hz
      j e l k.val m hj (by omega) hf
  unfold rowBaseFinite
  apply (norm_sum_le _ _).trans
  calc
    _ <= Finset.univ.sum (fun _k : Fin 2 => 8*(Ideal.absNorm (Ideal.span {p}):Real)^(-x.re+max (1-w.re) 0)) := by
      apply Finset.sum_le_sum
      intro k hk
      apply (norm_add_le _ _).trans
      have hab := (norm_add_le _ _).trans (add_le_add (ht' k 0) (ht' k 1))
      have hd : norm (rowMarkedTerm p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):Complex)^(-x))
          ((Ideal.absNorm (Ideal.span {p}):Complex)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
          rho j e l k.val 2/(1-coordV (Ideal.absNorm (Ideal.span {p})) z))<=4*(Ideal.absNorm (Ideal.span {p}):Real)^(-x.re+max (1-w.re) 0) := by
        rw [div_eq_mul_inv,norm_mul]
        exact (mul_le_mul (ht' k 2) hv (norm_nonneg _) (by positivity)).trans_eq (by ring)
      linarith
    _ = _ := by simp;ring

include hc in
theorem rowClosedMarked_selected_bound_extended (eta a rho x w z : Complex)
    (hQ : (4:Real)<=Ideal.absNorm (Ideal.span {p}))
    (heta : norm (eta)<=1) (ha : norm (a)<=1) (hrho : rho^6=1)
    (hx : (3/4:Real)<=x.re) (hw : (1/2:Real)<=w.re) (hz : (17/50:Real)<=z.re) (j : Nat) (hj : j<6) :
    norm (rowClosedMarked p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):Complex)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):Complex)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j)<=128*(Ideal.absNorm (Ideal.span {p}):Real)^(-x.re+max (1-w.re) 0) := by
  have hpow : 0<=(Ideal.absNorm (Ideal.span {p}):Real)^(-x.re+max (1-w.re) 0) := by positivity
  have h02 := rowBaseFinite_selected_bound_extended p hp hg hc eta a rho x w z hQ heta ha hrho hx hw hz j 0 2 hj (by omega)
  have h10 := rowBaseFinite_selected_bound_extended p hp hg hc eta a rho x w z hQ heta ha hrho hx hw hz j 1 0 hj (by omega)
  have h01 := rowBaseFinite_selected_bound_extended p hp hg hc eta a rho x w z hQ heta ha hrho hx hw hz j 0 1 hj (by omega)
  have h11 := rowBaseFinite_selected_bound_extended p hp hg hc eta a rho x w z hQ heta ha hrho hx hw hz j 1 1 hj (by omega)
  have hr := ProbeLocal.inv_one_sub_norm_le_two _ (first_region_R_half _ hQ a x z ha (by linarith) hz)
  simp only [Complex.ofReal_natCast] at hr
  unfold rowClosedMarked
  rw [div_eq_mul_inv,norm_mul]
  apply (mul_le_mul_of_nonneg_right
    ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add h02 h10)) h01)) h11)) (norm_nonneg _)).trans
  nlinarith

include hc in
theorem ramifiedSelected_bound_extended (eta a rho x w z : Complex)
    (hQ : (4:Real)<=Ideal.absNorm (Ideal.span {p}))
    (heta : norm (eta)<=1) (ha : norm (a)<=1) (hrho : rho^6=1)
    (hx : (3/4:Real)<=x.re) (hw : (1/2:Real)<=w.re) (hz : (17/50:Real)<=z.re) (j : Nat) (hj : j<6) :
    norm (ramifiedSelected p hp hg eta a rho x w z j)<=385*(Ideal.absNorm (Ideal.span {p}):Real)^(max (1-w.re) 0) := by
  let Q : Real := Ideal.absNorm (Ideal.span {p})
  let B : Real := max (1-w.re) 0
  have hQ0 : 0<Q := by dsimp [Q];linarith
  have hQ1 : 1<=Q := by dsimp [Q];linarith
  have hB0 : 0<=B := le_max_right _ _
  have hM := rowClosedMarked_selected_bound_extended p hp hg hc eta a rho x w z hQ heta ha hrho hx hw hz j hj
  have hH := ramifiedClosed_first_region_bound p hp hg hc eta a rho x w z hQ heta ha hrho
    (by linarith) (by linarith) hz (by linarith) j hj
  have hV := first_region_V_half _ hQ z hz
  have h1V : norm (1-coordV (Ideal.absNorm (Ideal.span {p})) z)<=3/2 := by
    have hh := norm_sub_le (1:Complex) (coordV (Ideal.absNorm (Ideal.span {p})) z)
    simp only [norm_one] at hh
    linarith
  have hphase : norm (star eta*(Ideal.absNorm (Ideal.span {p}):Complex)^x)<=Q^x.re := by
    change norm (star eta*(Q:Complex)^x)<=Q^x.re
    rw [norm_mul,norm_star,Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) heta
  have hq : norm ((Ideal.absNorm (Ideal.span {p}):Complex)^(-w))<=Q^B := by
    change norm ((Q:Complex)^(-w))<=Q^B
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0,Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by dsimp [B];linarith)
  have he : Q^x.re*Q^(-x.re+B)=Q^B := by rw [<-Real.rpow_add hQ0];congr 1;ring
  unfold ramifiedSelected
  apply (norm_sub_le _ _).trans
  simp only [norm_mul] at hphase
  simp only [norm_mul]
  calc
    _ <= (Q^x.re*(3/2))*(128*Q^(-x.re+B))+Q^B*193 := by
      gcongr
    _ = 385*Q^B := by nlinarith [he]

end PrimeFactorOscillations.SelectedTupleExtension
