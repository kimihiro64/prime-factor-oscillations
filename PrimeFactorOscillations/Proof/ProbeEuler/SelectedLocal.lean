/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.ProbeEuler.SelectedTerms

/-!
# Local selected-prime replacements on the three-quarter line

Bounds both ramified and unramified replacements, including vanishing
character coefficients. The resulting divisor weight is retained for the
weighted prime sums. Adapted from the pinned OAI selected-local proofs.
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

lemma unramifiedMarked_selected_error_extended (Q : Real) (A eta v x w z : Complex)
    (hQ : 4<=Q) (hA : norm (A)<=1) (heta : norm (eta)<=1) (hv : norm (v)<=1)
    (hx : (3/4:Real)<=x.re) (hw : (1/2:Real)<=w.re) (hz : (17/50:Real)<=z.re) :
    norm (unramifiedMarked Q A eta v x w z+coordD Q eta v x)<=28 /\
    norm (star eta*(Q:Complex)^x)*norm (unramifiedMarked Q A eta v x w z+coordD Q eta v x)<=28 := by
  have hQ0 : 0<Q := by linarith
  have hQ1 : 1<=Q := by linarith
  let R := coordR Q A x z
  let V := coordV Q z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  let B := star eta*(Q:Complex)^x
  have hR : norm (R)<=Q^(4-6*x.re-6*z.re) := coordR_norm_le Q hQ0 A x z hA
  have hV : norm (V)=Q^(-6*z.re) := coordV_norm Q hQ0 z
  have hD : norm (D)<=Q^(-x.re) := coordD_norm_le Q hQ0 eta v x heta hv
  have hW : norm (W)<=1 := (coordW_norm_le Q hQ0 v w hv).trans
    (Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith))
  have hK : norm (K)<=Q^(1-x.re-w.re) := coordK_norm_le Q hQ1 eta x w heta
  have hB : norm (B)<=Q^x.re := by
    dsimp only [B]
    rw [norm_mul,norm_star,Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) heta
  have hRh : norm (R)<=1/2 := hR.trans (rpow_le_half Q _ hQ (by linarith))
  have hVh : norm (V)<=1/2 := by rw [hV];exact rpow_le_half Q _ hQ (by linarith)
  have hDh : norm (D)<=1/2 := hD.trans (rpow_le_half Q _ hQ (by linarith))
  have hqi : norm ((Inv.inv (Q:Complex)))<=1 := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hQ0,<-one_div]
    exact (div_le_one hQ0).mpr hQ1
  have hprod (a b aa bb : Real) (ha : 0<=a) (hb : 0<=b)
      (haa : a<=Q^aa) (hbb : b<=Q^bb) (he : aa+bb<=0) : a*b<=1 := by
    calc
      a*b<=Q^aa*Q^bb := mul_le_mul haa hbb hb (Real.rpow_nonneg hQ0.le _)
      _=Q^(aa+bb) := (Real.rpow_add hQ0 _ _).symm
      _<=1 := Real.rpow_le_one_of_one_le_of_nonpos hQ1 he
  have hKV : norm (K)*norm (V)<=1 := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hK hV.le (by linarith)
  have hBR : norm (B)*norm (R)<=1 := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hB hR (by linarith)
  have hKV' : norm (K)*norm (V)<=Q^(1-x.re-w.re-6*z.re) := by
    calc
      _<=Q^(1-x.re-w.re)*Q^(-6*z.re) := mul_le_mul hK hV.le (norm_nonneg _) (Real.rpow_nonneg hQ0.le _)
      _=_ := by rw [<-Real.rpow_add hQ0];congr 1;ring
  have hBKV : norm (B)*(norm (K)*norm (V))<=1 := hprod _ _ _ _ (norm_nonneg _) (by positivity) hB hKV' (by linarith)
  have hE := OAI.SevenEighths.ProbeLocal.unramified_marked_error_bound R V (Inv.inv (Q:Complex)) K W D hRh hVh hqi hDh
  change norm (unramifiedMarked Q A eta v x w z+D)<=_ at hE
  have hE' : norm (unramifiedMarked Q A eta v x w z+D)<=24*norm (R)+4*(norm (K)*norm (V)) := by
    apply hE.trans
    nlinarith [mul_le_mul_of_nonneg_left hW (norm_nonneg R)]
  constructor
  . change norm (unramifiedMarked Q A eta v x w z+D)<=28
    linarith
  . have hh := mul_le_mul_of_nonneg_left hE' (norm_nonneg B)
    change norm (B)*norm (unramifiedMarked Q A eta v x w z+D)<=28
    nlinarith

lemma unramifiedSelected_error_bound_extended (Q : Real) (A eta v x w z : Complex)
    (hQ : 4<=Q) (hA : norm (A)<=1) (heta : norm (eta)=1) (hv : norm (v)=1)
    (hx : (3/4:Real)<=x.re) (hw : (1/2:Real)<=w.re) (hz : (17/50:Real)<=z.re) :
    norm (unramifiedSelected Q A eta v x w z+unramifiedClosed Q A eta v x w z*star v)<=720 := by
  have hQ0 : 0<Q := by linarith
  have hQ1 : 1<=Q := by linarith
  have hV : norm (coordV Q z)<=1/2 := by
    rw [coordV_norm Q hQ0]
    exact rpow_le_half Q _ hQ (by linarith)
  have hD : norm (coordD Q eta v x)<=1/2 :=
    (coordD_norm_le Q hQ0 eta v x heta.le hv.le).trans (rpow_le_half Q _ hQ (by linarith))
  have hW : norm (coordW Q v w)<=1 :=
    (coordW_norm_le Q hQ0 v w hv.le).trans (Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith))
  have hq : norm ((Q:Complex)^(-w))<=1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0,Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith)
  have he := unramifiedMarked_selected_error_extended Q A eta v x w z hQ hA heta.le hv.le hx hw hz
  have hi := selected_phase_identities Q eta v x w hQ0 heta hv
  have hh := OAI.SevenEighths.ProbeLocal.compensated_phase_error_bound (coordV Q z) (coordW Q v w) (coordD Q eta v x)
    (unramifiedMarked Q A eta v x w z) (star eta*(Q:Complex)^x) ((Q:Complex)^(-w)) (star v) 1
    (by norm_num) hV hW hD hq (by linarith) (by linarith)
    (by simpa using he.1) (by simpa using he.2) (by rw [norm_star,hv]) hi.1 hi.2
  simpa only [mul_one,unramifiedSelected,unramifiedClosed,unramifiedMarked] using hh

lemma unramifiedSelected_bound_extended (Q : Real) (A eta v x w z : Complex)
    (hQ : 4<=Q) (hA : norm (A)<=1) (heta : norm (eta)=1) (hv : norm (v)=1)
    (hx : (3/4:Real)<=x.re) (hw : (1/2:Real)<=w.re) (hz : (17/50:Real)<=z.re) :
    norm (unramifiedSelected Q A eta v x w z)<=961 := by
  have hd := unramifiedClosed_first_region_bound Q A eta v x w z (1/4) hQ hA heta.le hv.le
    (by norm_num) (by linarith) hz (by linarith) (by linarith)
  have hpow : Q^(-1-min (1/4:Real) (1/50))<=1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hH : norm (unramifiedClosed Q A eta v x w z)<=241 := by
    have hh := norm_add_le (unramifiedClosed Q A eta v x w z-1) (1:Complex)
    rw [sub_add_cancel,norm_one] at hh
    nlinarith
  have he := unramifiedSelected_error_bound_extended Q A eta v x w z hQ hA heta hv hx hw hz
  have hh := norm_sub_le
    (unramifiedSelected Q A eta v x w z+unramifiedClosed Q A eta v x w z*star v)
    (unramifiedClosed Q A eta v x w z*star v)
  rw [add_sub_cancel_right,norm_mul,norm_star,hv,mul_one] at hh
  linarith

theorem actualUnramifiedSelected_bound_extended (eta : HeckeFamily.Character) (p u : O)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : Not (Membership.mem (Ideal.span {p} : Ideal O) goodLambda))
    (hc : Not (ringChar (HasQuotient.Quotient O (Ideal.span {p} : Ideal O))=2)) (hu : IsCoprime u p)
    (hQ : (4:Real)<=Ideal.absNorm (Ideal.span {p})) (x w z : Complex)
    (hx : (3/4:Real)<=x.re) (hw : (1/2:Real)<=w.re) (hz : (17/50:Real)<=z.re) :
    norm (actualUnramifiedSelected eta p u hg x w z)<=961 := by
  have hv := Complex.norm_eq_one_of_pow_eq_one (ProbePhysical.actualSextic_unit_six p u hg hc hu) (by decide : Not ((6:Nat)=0))
  unfold actualUnramifiedSelected
  rcases elementCoeff_zero_or_norm_one eta p with heta|heta
  . have hA : actualAPhase eta p=0 := by simp [actualAPhase,heta]
    rw [heta,hA]
    exact (unramifiedSelected_zero_bound _ _ x w z hQ hv.le hw hz).trans (by norm_num)
  . exact unramifiedSelected_bound_extended _ _ _ _ x w z hQ (actualAPhase_norm_le_one eta p) heta hv hx hw hz

lemma continuedCompensatedLocal_ramified_bound_extended (eta : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hP : Dvd.dvd P.val (Ideal.span {u.val} : Ideal O)) (hQ : (4:Real)<=P.val.absNorm)
    (x w z : Complex) (hx : (3/4:Real)<=x.re) (hw : (1/2:Real)<=w.re) (hz : (17/50:Real)<=z.re) :
    norm (continuedCompensatedLocal eta u P hs x w z
      (star (idealCoeff eta P.val)*(P.val.absNorm:Complex)^x) ((P.val.absNorm:Complex)^(-w)))<=
        385*(P.val.absNorm:Real)^(max (1-w.re) 0) := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := (by simpa only [hspan] using hs)
  have hg := supported_prime_data p hp hsp
  have ha : norm (actualACube eta p)<=1 := by
    have h := actualAPhase_norm_le_one eta p
    rw [<-actualACube_sq,norm_pow] at h
    nlinarith [norm_nonneg (actualACube eta p)]
  rw [continuedCompensatedLocal_ramified eta u P hs hP x w z]
  have hb := ramifiedSelected_bound_extended p hp hg.1 hg.2 _ _ _ x w z
    ((by simpa only [hspan] using hQ)) (targetMonoid_norm_le_one eta p) ha
    (actualSextic_unit_six p (unitPart u p hp) hg.1 hg.2 (unitPart_coprime u p hp)) hx hw hz
    (multiplicity p u.val) (multiplicity_lt_six u p hp)
  simpa only [hspan] using hb

lemma continuedCompensatedLocal_unramified_bound_extended (eta : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hP : Not (Dvd.dvd P.val (Ideal.span {u.val} : Ideal O))) (hQ : (4:Real)<=P.val.absNorm)
    (x w z : Complex) (hx : (3/4:Real)<=x.re) (hw : (1/2:Real)<=w.re) (hz : (17/50:Real)<=z.re) :
    norm (continuedCompensatedLocal eta u P hs x w z
      (star (idealCoeff eta P.val)*(P.val.absNorm:Complex)^x) ((P.val.absNorm:Complex)^(-w)))<=961 := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := (by simpa only [hspan] using hs)
  have hg := supported_prime_data p hp hsp
  have hnot : Not (Dvd.dvd p u.val) := by
    intro hd
    apply hP
    rw [Ideal.dvd_iff_le,<-hspan,Ideal.span_singleton_le_span_singleton]
    exact hd
  have hu : IsCoprime u.val p := (hp.irreducible.coprime_iff_not_dvd.mpr hnot).symm
  have hQ0 : (0:Real)<P.val.absNorm := by linarith
  have hV : norm (coordV P.val.absNorm z)<1 := by
    exact (first_region_V_half _ hQ z hz).trans_lt (by norm_num)
  have hR : norm (coordR P.val.absNorm (actualAPhase eta p) x z)<1 := by
    apply (coordR_norm_le _ hQ0 _ x z (actualAPhase_norm_le_one eta p)).trans_lt
    exact (rpow_le_half _ _ hQ (by linarith)).trans_lt (by norm_num)
  rw [continuedCompensatedLocal_unramified eta u P hs hP x w z hV hR]
  have hb := actualUnramifiedSelected_bound_extended eta p u.val hg.1 hg.2 hu ((by simpa only [hspan] using hQ)) x w z hx hw hz
  have he : idealCoeff eta P.val=elementCoeff eta p := by rw [<-hspan,idealCoeff_span eta hp.ne_zero]
  have hv : idealRowHom u.val P.val=actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ u.val) := by
    rw [<-hspan,idealRowHom_prime u.val (Ideal.span {p}) hg.1]
  simpa only [actualUnramifiedSelected,hspan,he,hv] using hb

lemma continuedCompensatedLocal_bound_extended (eta : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hQ : (4:Real)<=P.val.absNorm)
    (x w z : Complex) (hx : (3/4:Real)<=x.re) (hw : (1/2:Real)<=w.re) (hz : (17/50:Real)<=z.re) :
    norm (continuedCompensatedLocal eta u P hs x w z
      (star (idealCoeff eta P.val)*(P.val.absNorm:Complex)^x) ((P.val.absNorm:Complex)^(-w)))<=
        961*(if Dvd.dvd P.val (Ideal.span {u.val} : Ideal O) then (P.val.absNorm:Real)^(max (1-w.re) 0) else 1) := by
  by_cases hp : Dvd.dvd P.val (Ideal.span {u.val} : Ideal O)
  . rw [ite_eq_left hp]
    apply (continuedCompensatedLocal_ramified_bound_extended eta u P hs hp hQ x w z hx hw hz).trans
    gcongr
    norm_num
  . simpa only [ite_eq_right hp,mul_one] using continuedCompensatedLocal_unramified_bound_extended eta u P hs hp hQ x w z hx hw hz

end PrimeFactorOscillations.SelectedTupleExtension
