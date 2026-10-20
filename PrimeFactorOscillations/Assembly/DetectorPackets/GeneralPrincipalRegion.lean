/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Detector.GlobalCorrection
import PrimeFactorOscillations.Proof.DetectorPackets.GeneralPrincipalExponents

/-!
# GeneralPrincipalRegion

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
# Principal correction on the enlarged source strip

The actual rational correction is controlled on Re(x)>=3/4 with the same
w,z ranges. The slower summable majorant is240*N(P)^(-7/5).
A finite enlargement of exclusions makes its complete Euler product small.
This repairs a coefficient-domain restriction,not a zero-free theorem.
-/


noncomputable section
namespace PrimeFactorOscillations.GeneralPrincipalRegion
open scoped Classical
open OAI OAI.SevenEighths
open ActualEisensteinCubic ProbeEuler CompletedGauss ProbePhysical
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem unramifiedClosed_principal_extended_bound (Q : Real) (A eta v x w z : Complex)
    (hQ : 4 <= Q) (hA : norm (A) <= 1) (heta : norm (eta) <= 1) (hv : norm (v) <= 1)
    (hx : (3/4:Real) <= x.re) (hw : (9/10:Real) <= w.re) (hz : (4/25:Real) <= z.re) :
    norm (unramifiedClosed Q A eta v x w z - 1) <= 240 * Q ^ (-(7/5:Real)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 <= Q := by linarith
  let V := coordV Q z
  let R := coordR Q A x z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  have hcaps := principal_coordinate_exponent_caps x.re w.re z.re hx hw hz
  have hV : norm (V) <= Q ^ (-(24/25:Real)) := by
    rw [show V = coordV Q z from rfl, coordV_norm Q hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 hcaps.1
  have hR : norm (R) <= Q ^ (-(73/50:Real)) :=
    (coordR_norm_le Q hQ0 A x z hA).trans (Real.rpow_le_rpow_of_exponent_le hQ1 hcaps.2.1)
  have hW : norm (W) <= Q ^ (-(9/10:Real)) :=
    (coordW_norm_le Q hQ0 v w hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 hcaps.2.2.1)
  have hD : norm (D) <= Q ^ (-(3/4:Real)) :=
    (coordD_norm_le Q hQ0 eta v x heta hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 hcaps.2.2.2.1)
  have hK : norm (K) <= Q ^ (-(13/20:Real)) :=
    (coordK_norm_le Q hQ1 eta x w heta).trans (Real.rpow_le_rpow_of_exponent_le hQ1 hcaps.2.2.2.2)
  have hVh : norm (V) <= 1/2 := hV.trans (rpow_le_half Q _ hQ (by norm_num))
  have hRh : norm (R) <= 1/2 := hR.trans (rpow_le_half Q _ hQ (by norm_num))
  have hDh : norm (D) <= 1/2 := hD.trans (rpow_le_half Q _ hQ (by norm_num))
  have hWh : norm (W) <= 1 := by
    exact hW.trans ((Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num : -(9/10:Real) <= 0)).trans_eq (Real.rpow_zero Q))
  have hqi : norm ((Inv.inv (Q:Complex))) <= 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0, <- one_div]
    exact (div_le_one hQ0).mpr hQ1
  let T := Q ^ (-(7/5:Real))
  have hT : 0 <= T := Real.rpow_nonneg hQ0.le _
  have hRT : norm (R) <= T := hR.trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num))
  have hprod (a b a' b' : Real) (ha : 0 <= a) (hb : 0 <= b)
      (haa : a <= Q^a') (hbb : b <= Q^b') (he : a'+b' <= -(7/5:Real)) : a*b <= T := by
    calc
      a*b <= Q^a' * Q^b' := mul_le_mul haa hbb hb (Real.rpow_nonneg hQ0.le _)
      _ = Q^(a'+b') := (Real.rpow_add hQ0 _ _).symm
      _ <= T := Real.rpow_le_rpow_of_exponent_le hQ1 he
  have hKV : norm (K)*norm (V) <= T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hK hV (by norm_num)
  have hDV : norm (D)*norm (V) <= T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hV (by norm_num)
  have hDW : norm (D)*norm (W) <= T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hW (by norm_num)
  have hVW : norm (V)*norm (W) <= T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hV hW (by norm_num)
  have hDVW : norm (D)*norm (V)*norm (W) <= T :=
    (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hWh).trans hDV
  let P := markedFactor R V (Inv.inv (Q:Complex)) K (-D+W*R) 1
  have hE : norm (P+D) <= 28*T := by
    have h := ProbeLocal.unramified_marked_error_bound R V (Inv.inv (Q:Complex)) K W D hRh hVh hqi hDh
    have hrw : norm (R)*(1+norm (W)) <= 2*T := by
      calc
        _ <= norm (R)*2 := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
        _ <= _ := by nlinarith
    dsimp only [P]
    nlinarith
  have h := ProbeLocal.continuedCorrection_defect_bound V W D P hVh hDh
  change norm (ProbeLocal.continuedCorrection V W D P-1) <= 240*T
  have hWE : (1+norm (W))*norm (P+D) <= 56*T := by
    calc
      _ <= 2*(28*T) := mul_le_mul (by linarith) hE (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  nlinarith


def principalPrimeDefectBound (P : PrimeIdeal) : Real :=
  240*(Ideal.absNorm P.val:Real)^(-(7/5:Real))

lemma principalPrimeDefectBound_nonneg (P : PrimeIdeal) :
    0<=principalPrimeDefectBound P := by
  unfold principalPrimeDefectBound
  positivity

lemma principalPrimeDefectBound_summable : Summable principalPrimeDefectBound := by
  have h := (CubicEisenstein.fullIdealWeight_summable_norm ((7/5:Real):Complex)
    (by norm_num)).comp_injective
    (Subtype.val_injective : Function.Injective (fun P : PrimeIdeal=>P.val))
  apply (h.mul_left 240).congr
  intro P
  change 240*norm (CubicEisenstein.fullIdealWeight ((7/5:Real):Complex) P.val)=
    principalPrimeDefectBound P
  unfold principalPrimeDefectBound CubicEisenstein.fullIdealWeight
  simp only [P.property.ne_zero,ite_false]
  rw [Complex.norm_natCast_cpow_of_pos
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero))]
  norm_num

structure PrincipalCorrectionTail (S : Finset Id) : Prop where
  norm_four : forall P : PrimeIdeal, Not (Membership.mem S P.val) -> 4<=Ideal.absNorm P.val
  small : (tsum fun P : {P : PrimeIdeal // Not (Membership.mem S P.val)}=>
    principalPrimeDefectBound P.val)<=1/6

lemma PrincipalCorrectionTail.summable {S : Finset Id} (_h : PrincipalCorrectionTail S) :
    Summable (fun P : {P : PrimeIdeal // Not (Membership.mem S P.val)}=>
      principalPrimeDefectBound P.val) :=
  principalPrimeDefectBound_summable.subtype _

lemma PrincipalCorrectionTail.half {S : Finset Id} (h : PrincipalCorrectionTail S)
    (P : {P : PrimeIdeal // Not (Membership.mem S P.val)}) :
    principalPrimeDefectBound P.val<=1/2 := by
  have hh := Summable.le_tsum h.summable P
    (fun Q _=>principalPrimeDefectBound_nonneg Q.val)
  linarith [h.small]

theorem idealClosedCorrection_principal_extended_bound (eta : HeckeFamily.Character)
    (P : PrimeIdeal) (hP : 4<=Ideal.absNorm P.val) (x w z : Complex)
    (hx : (3/4:Real)<=x.re) (hw : (9/10:Real)<=w.re) (hz : (4/25:Real)<=z.re) :
    norm (idealClosedCorrection eta P x w z-1)<=principalPrimeDefectBound P := by
  apply unramifiedClosed_principal_extended_bound
  . exact_mod_cast hP
  . exact actualAPhase_norm_le_one eta _
  . exact HeckeFamily.idealCoeff_norm_le_one eta P.val
  . simp
  . exact hx
  . exact hw
  . exact hz

theorem globalClosedCorrection_principal_extended_bound (eta : HeckeFamily.Character)
    (S : Finset Id) (hS : PrincipalCorrectionTail S) (x w z : Complex)
    (hx : (3/4:Real)<=x.re) (hw : (9/10:Real)<=w.re) (hz : (4/25:Real)<=z.re) :
    norm (globalClosedCorrection eta S x w z-1)<=1/2 :=
  product_defect_le _ _ hS.summable
    (fun P=>idealClosedCorrection_principal_extended_bound eta P.val
      (hS.norm_four P.val P.property) x w z hx hw hz)
    hS.half hS.small

lemma PrincipalCorrectionTail.toCorrectionTail {S : Finset Id} (hS : PrincipalCorrectionTail S) :
    CorrectionTail S := by
  refine { norm_four := hS.norm_four, small := ?_ }
  apply le_trans ?_ hS.small
  apply Summable.tsum_le_tsum_of_inj
    (fun P : {P : PrimeIdeal // Not (Membership.mem S P.val)}=>P)
    (fun _ _ h=>h)
    (fun P _=>principalPrimeDefectBound_nonneg P.val) ?_
    (globalPrimeDefectBound_summable.subtype _) hS.summable
  intro P
  unfold globalPrimeDefectBound principalPrimeDefectBound
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hn : 1<=(Ideal.absNorm P.val.val:Real) := by
    have h4 := hS.norm_four P.val P.property
    exact_mod_cast (Nat.le_trans (by decide : 1<=4) h4)
  exact Real.rpow_le_rpow_of_exponent_le hn (by norm_num)

theorem exists_uniform_principal_global_cutoff :
    Exists fun N : Nat=>4<=N /\ forall S : Finset Id,
      (forall P : PrimeIdeal,Ideal.absNorm P.val<=N -> Membership.mem S P.val) ->
      PrincipalCorrectionTail S := by
  have ht := (tendsto_order.1 (tendsto_tsum_compl_atTop_zero principalPrimeDefectBound)).2
    (1/6) (by norm_num)
  cases ht.exists with
  | intro F hF =>
    let N := max 4 (F.sup (fun P=>Ideal.absNorm P.val))
    refine Exists.intro N (And.intro (le_max_left _ _) ?_)
    intro S hS
    let T := {P : PrimeIdeal // Not (Membership.mem S P.val)}
    have hnot (P : T) : Not (Membership.mem F P.val) := by
      intro hm
      exact P.property (hS P.val
        ((Finset.le_sup (f:=fun P : PrimeIdeal=>Ideal.absNorm P.val) hm).trans
          (le_max_right _ _)))
    let inc : T->{P : PrimeIdeal // Not (Membership.mem F P)} :=
      fun P=>Subtype.mk P.val (hnot P)
    have hi : Function.Injective inc := by
      intro P Q h
      exact Subtype.ext
        (congrArg (fun P : {P : PrimeIdeal // Not (Membership.mem F P)}=>P.val) h)
    constructor
    . intro P hP
      have hn : Not (Ideal.absNorm P.val<=N) := fun hn=>hP (hS P hn)
      exact (le_max_left _ _).trans (Nat.le_of_lt (Nat.lt_of_not_ge hn))
    . apply le_trans ?_ hF.le
      exact Summable.tsum_le_tsum_of_inj inc hi
        (fun P _=>principalPrimeDefectBound_nonneg P.val) (fun _=>le_rfl)
        (principalPrimeDefectBound_summable.subtype _)
        (principalPrimeDefectBound_summable.subtype _)

theorem exists_principal_global_correction (S0 : Finset Id) :
    Exists fun S : Finset Id=>S0<=S /\ PrincipalCorrectionTail S /\ CorrectionTail S := by
  cases exists_uniform_principal_global_cutoff with
  | intro N hN =>
    cases hN with
    | intro hN0 hcut =>
      let S := Union.union S0 (smallPrimeSet N)
      have hS : PrincipalCorrectionTail S := by
        apply hcut
        intro P hP
        exact Finset.mem_union_right _ ((mem_smallPrimeSet N P).mpr hP)
      exact Exists.intro S (And.intro Finset.subset_union_left
        (And.intro hS hS.toCorrectionTail))

end PrimeFactorOscillations.GeneralPrincipalRegion

