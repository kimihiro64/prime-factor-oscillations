/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.ProbeEuler.PrincipalLocal

/-!
# Normal convergence and uniform principal Euler tails

The exact source factors have a summable uniform defect on Re(s) >= 3/4.
After one finite deletion their product is uniformly within 1/2 of one.
These statements concern the correction product and assert no improved
zero-free region for the accompanying L-functions.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.PrincipalEulerContinuation

theorem hasProdUniformlyOn_principalFactor {I : Type*}
    (Q : I -> Real) (eta a : I -> Complex)
    (hQ : forall i, Real.exp 2 <= Q i)
    (heta : forall i, norm (eta i) <= 1) (ha : forall i, norm (a i) <= 1)
    (hs : Summable (fun i => Real.exp (-(3 / 2) * Real.log (Q i))))
    (K : Set Complex) (hK : IsCompact K)
    (hRe : forall z, Membership.mem K z -> 3 / 4 <= z.re) :
    HasProdUniformlyOn (fun i z => principalFactor (Q i) (eta i) (a i) z)
      (fun z => tprod (fun i => principalFactor (Q i) (eta i) (a i) z)) K := by
  have hQ2 (i : I) : 2 <= Q i := by
    linarith [hQ i, Real.add_one_le_exp (2 : Real)]
  have hbound : forall i, forall z, Membership.mem K z ->
      norm (principalFactor (Q i) (eta i) (a i) z - 1) <=
        20 * Real.exp (-(3 / 2) * Real.log (Q i)) := by
    intro i z hz
    exact principal_factor_uniform_defect (Q i) (eta i) (a i) z
      (hQ i) (heta i) (ha i) (hRe z hz)
  have hcts : forall i, ContinuousOn
      (fun z => principalFactor (Q i) (eta i) (a i) z - 1) K := by
    intro i z hz
    have han := principal_factor_analyticAt (Q i) (eta i) (a i) z
      (hQ2 i) (heta i) (ha i) (by linarith [hRe z hz])
    exact (han.continuousAt.sub continuousAt_const).continuousWithinAt
  have hp := Summable.hasProdUniformlyOn_one_add
    (f := fun i z => principalFactor (Q i) (eta i) (a i) z - 1)
    hK (hs.mul_left 20) (Filter.Eventually.of_forall hbound) hcts
  simpa only [add_sub_cancel] using hp

theorem analyticOnNhd_principalProduct {I : Type*}
    (Q : I -> Real) (eta a : I -> Complex)
    (hQ : forall i, Real.exp 2 <= Q i)
    (heta : forall i, norm (eta i) <= 1) (ha : forall i, norm (a i) <= 1)
    (hs : Summable (fun i => Real.exp (-(3 / 2) * Real.log (Q i)))) :
    AnalyticOnNhd Complex
      (fun z => tprod (fun i => principalFactor (Q i) (eta i) (a i) z))
      {z : Complex | 3 / 4 < z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro z hz
  change 3 / 4 < z.re at hz
  let r : Real := (z.re - 3 / 4) / 2
  have hr : 0 < r := by dsimp [r]; linarith [hz]
  have hRe : forall w, Membership.mem (Metric.closedBall z r) w ->
      3 / 4 <= w.re := by
    intro w hw
    have hnorm : norm (w - z) <= r := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hw
    have habs := Complex.abs_re_le_norm (w - z)
    have hleft := (neg_le_abs ((w - z).re)).trans habs
    simp only [Complex.sub_re] at hleft
    dsimp [r] at hnorm
    linarith [hz]
  have hp := hasProdUniformlyOn_principalFactor Q eta a hQ heta ha hs
    (Metric.closedBall z r) (isCompact_closedBall z r) hRe
  have hlim : TendstoLocallyUniformlyOn
      (fun F : Finset I => fun w => F.prod
        (fun i => principalFactor (Q i) (eta i) (a i) w))
      (fun w => tprod (fun i => principalFactor (Q i) (eta i) (a i) w))
      Filter.atTop (Metric.ball z r) :=
    (hp.mono Metric.ball_subset_closedBall).hasProdLocallyUniformlyOn
  have hfin : forall F : Finset I, DifferentiableOn Complex
      (fun w => F.prod (fun i => principalFactor (Q i) (eta i) (a i) w))
      (Metric.ball z r) := by
    intro F w hw
    have hwr := hRe w (Metric.ball_subset_closedBall hw)
    have hfactor (i : I) : DifferentiableAt Complex
        (principalFactor (Q i) (eta i) (a i)) w := by
      have hQ2 : 2 <= Q i := by
        linarith [hQ i, Real.add_one_le_exp (2 : Real)]
      exact (principal_factor_analyticAt (Q i) (eta i) (a i) w
        hQ2 (heta i) (ha i) (by linarith)).differentiableAt
    have hprod : DifferentiableAt Complex
        (fun v => F.prod (fun i => principalFactor (Q i) (eta i) (a i) v)) w := by
      classical
      induction F using Finset.induction_on with
      | empty =>
        simp only [Finset.prod_empty]
        fun_prop
      | @insert i F hi ih =>
        simp only [Finset.prod_insert hi]
        apply DifferentiableAt.mul
        . exact hfactor i
        . exact ih
    exact hprod.differentiableWithinAt
  have hd := hlim.differentiableOn
    (Filter.Eventually.of_forall hfin) Metric.isOpen_ball
  have hcenter : Membership.mem (Metric.ball z r) z := by simpa using hr
  exact ((hd z hcenter).differentiableAt
    (Metric.isOpen_ball.mem_nhds hcenter)).differentiableWithinAt

abbrev SourcePrime := OAI.SmoothMobiusCorrection.PrimeIdeal
abbrev SourceCharacter := OAI.SevenEighths.HeckeFamily.Character

def sourceNorm (P : SourcePrime) : Real := (Ideal.absNorm P.val : Real)

def sourceEta (eta : SourceCharacter) (P : SourcePrime) : Complex :=
  OAI.SevenEighths.HeckeFamily.idealCoeff eta P.val

def sourceRoot (eta : SourceCharacter) (P : SourcePrime) : Complex :=
  OAI.SevenEighths.ProbeEuler.actualACube eta (OAI.CompletedGauss.primaryGenerator P.val)

def HighSourcePrime (S : Finset SourcePrime) : Type :=
  {P : SourcePrime // Real.exp 2 <= sourceNorm P /\ Not (Membership.mem S P)}

theorem source_norm_majorant_summable :
    Summable (fun P : SourcePrime => Real.exp (-(3 / 2) * Real.log (sourceNorm P))) := by
  have hfull := OAI.CubicEisenstein.fullIdealWeight_summable_norm
    (3 / 2 : Complex) (by norm_num)
  have hprime : Summable (fun P : SourcePrime =>
      norm (OAI.CubicEisenstein.fullIdealWeight (3 / 2 : Complex) P.val)) :=
    hfull.comp_injective Subtype.val_injective
  apply hprime.congr
  intro P
  have hPpos := OAI.SmoothMobiusCorrection.prime_norm_pos P
  rw [OAI.CubicEisenstein.fullIdealWeight, ite_eq_right P.property.ne_zero]
  rw [<- Complex.ofReal_natCast (Ideal.absNorm P.val),
    Complex.norm_cpow_eq_rpow_re_of_pos hPpos]
  have hre : (-(3 / 2 : Complex)).re = (-3 / 2 : Real) := by norm_num
  rw [hre, Real.rpow_def_of_pos hPpos]
  dsimp [sourceNorm]
  congr 1
  ring

theorem source_eta_norm_le (eta : SourceCharacter) (P : SourcePrime) :
    norm (sourceEta eta P) <= 1 :=
  OAI.SevenEighths.HeckeFamily.idealCoeff_norm_le_one eta P.val

theorem source_root_norm_le (eta : SourceCharacter) (P : SourcePrime) :
    norm (sourceRoot eta P) <= 1 := by
  have h := OAI.SevenEighths.ProbeEuler.actualAPhase_norm_le_one eta
    (OAI.CompletedGauss.primaryGenerator P.val)
  rw [<- OAI.SevenEighths.ProbeEuler.actualACube_sq, norm_pow] at h
  have hn := norm_nonneg (sourceRoot eta P)
  change norm (sourceRoot eta P) ^ 2 <= 1 at h
  nlinarith

theorem source_high_norm_majorant_summable (S : Finset SourcePrime) :
    Summable (fun P : HighSourcePrime S =>
      Real.exp (-(3 / 2) * Real.log (sourceNorm P.val))) :=
  source_norm_majorant_summable.comp_injective Subtype.val_injective

theorem analyticOnNhd_sourcePrincipalProduct (S : Finset SourcePrime)
    (eta : SourceCharacter) :
    AnalyticOnNhd Complex
      (fun z => tprod (fun P : HighSourcePrime S =>
        principalFactor (sourceNorm P.val) (sourceEta eta P.val) (sourceRoot eta P.val) z))
      {z : Complex | 3 / 4 < z.re} :=
  analyticOnNhd_principalProduct
    (fun P : HighSourcePrime S => sourceNorm P.val)
    (fun P => sourceEta eta P.val) (fun P => sourceRoot eta P.val)
    (fun P => P.property.1) (fun P => source_eta_norm_le eta P.val)
    (fun P => source_root_norm_le eta P.val) (source_high_norm_majorant_summable S)

theorem positive_cpow_eq_exp (Q : Real) (hQ : 0 < Q) (v : Complex) :
    (Q : Complex) ^ v = Complex.exp (v * (Real.log Q : Complex)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hQ)),
    <- Complex.ofReal_log hQ.le, mul_comm]

theorem unramifiedClosed_principal_eq (Q : Real) (eta a s : Complex)
    (hQ : 2 <= Q) (heta : norm eta <= 1) (ha : norm a <= 1)
    (hs : 1 / 2 < s.re) :
    OAI.SevenEighths.ProbeEuler.unramifiedClosed Q (a ^ 2) eta 1 s 1 (1 / 6) =
      principalFactor Q eta a s := by
  have hQpos : 0 < Q := by linarith
  have hQ0 : Not ((Q : Complex) = 0) := Complex.ofReal_ne_zero.mpr (ne_of_gt hQpos)
  have hQ1 : Not ((Q : Complex) - 1 = 0) := by
    intro h
    have h' : (Q : Complex) = 1 := sub_eq_zero.mp h
    have h'' : Q = 1 := by exact_mod_cast h'
    linarith
  have hn := moving_denominators Q eta a s hQ heta ha hs
  have hnegone : (Q : Complex) ^ (-(1 : Complex)) = 1 / (Q : Complex) := by
    rw [Complex.cpow_neg, Complex.cpow_one, one_div]
  have hV : OAI.SevenEighths.ProbeEuler.coordV Q (1 / 6) = 1 / (Q : Complex) := by
    change (Q : Complex) ^ ((-6 : Complex) * (1 / 6)) = 1 / (Q : Complex)
    rw [show (-6 : Complex) * (1 / 6) = -1 by ring]
    exact hnegone
  have hW : OAI.SevenEighths.ProbeEuler.coordW Q 1 1 = 1 / (Q : Complex) := by
    simpa only [OAI.SevenEighths.ProbeEuler.coordW, one_mul] using hnegone
  have hD : OAI.SevenEighths.ProbeEuler.coordD Q eta 1 s = localD Q eta s := by
    simp only [OAI.SevenEighths.ProbeEuler.coordD, star_one, mul_one, localD]
    rw [positive_cpow_eq_exp Q hQpos]
  have hR : OAI.SevenEighths.ProbeEuler.coordR Q (a ^ 2) s (1 / 6) = localR Q a s := by
    dsimp only [OAI.SevenEighths.ProbeEuler.coordR, localR]
    rw [show (4 : Complex) - 6 * s - 6 * (1 / 6) = 3 - 6 * s by ring,
      positive_cpow_eq_exp Q hQpos]
  have hK : OAI.SevenEighths.ProbeEuler.coordK Q eta s 1 =
      ((Q : Complex) - 1) * localD Q eta s * (1 / (Q : Complex)) := by
    rw [OAI.SevenEighths.ProbeEuler.coordK_eq_geometric Q hQpos,
      hnegone, positive_cpow_eq_exp Q hQpos]
    dsimp [localD]
    ring
  simp only [OAI.SevenEighths.ProbeEuler.unramifiedClosed, hV, hW, hD, hR, hK]
  dsimp only [OAI.SevenEighths.ProbeLocal.continuedCorrection,
    OAI.SevenEighths.ProbeEuler.markedFactor, principalFactor]
  field_simp [hn.1, hn.2, hQ0, hQ1]
  ring

theorem idealClosedCorrection_principal_eq (eta : SourceCharacter) (P : SourcePrime)
    (s : Complex) (hs : 1 / 2 < s.re) :
    OAI.SevenEighths.ProbePhysical.idealClosedCorrection eta P s 1 (1 / 6) =
      principalFactor (sourceNorm P) (sourceEta eta P) (sourceRoot eta P) s := by
  have hQ : 2 <= sourceNorm P := by
    dsimp [sourceNorm]
    exact_mod_cast OAI.SmoothMobiusCorrection.prime_norm_two_le P
  change OAI.SevenEighths.ProbeEuler.unramifiedClosed (sourceNorm P)
    (OAI.SevenEighths.ProbeEuler.actualAPhase eta (OAI.CompletedGauss.primaryGenerator P.val))
    (sourceEta eta P) 1 s 1 (1 / 6) = _
  rw [<- OAI.SevenEighths.ProbeEuler.actualACube_sq]
  exact unramifiedClosed_principal_eq (sourceNorm P) (sourceEta eta P)
    (sourceRoot eta P) s hQ (source_eta_norm_le eta P) (source_root_norm_le eta P) hs

theorem analyticOnNhd_actualSourceProduct (S : Finset SourcePrime)
    (eta : SourceCharacter) :
    AnalyticOnNhd Complex
      (fun z => tprod (fun P : HighSourcePrime S =>
        OAI.SevenEighths.ProbePhysical.idealClosedCorrection eta P.val z 1 (1 / 6)))
      {z : Complex | 3 / 4 < z.re} := by
  intro z hz
  change 3 / 4 < z.re at hz
  have hmem : Filter.Eventually (fun w : Complex => 3 / 4 < w.re) (nhds z) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
  have heq : Filter.EventuallyEq (nhds z)
      (fun w => tprod (fun P : HighSourcePrime S =>
        principalFactor (sourceNorm P.val) (sourceEta eta P.val) (sourceRoot eta P.val) w))
      (fun w => tprod (fun P : HighSourcePrime S =>
        OAI.SevenEighths.ProbePhysical.idealClosedCorrection eta P.val w 1 (1 / 6))) := by
    apply hmem.mono
    intro w hw
    apply tprod_congr
    intro P
    exact (idealClosedCorrection_principal_eq eta P.val w (by linarith)).symm
  exact (analyticOnNhd_sourcePrincipalProduct S eta z hz).congr heq


private theorem norm_tprod_defect_le_exp_tsum {I : Type*}
    (f : I -> Complex) (u : I -> Real) (hu0 : forall i, 0 <= u i)
    (hu : Summable u) (hbound : forall i, norm (f i - 1) <= u i) :
    norm (tprod f - 1) <= Real.exp (tsum u) - 1 := by
  have hdev : Summable (fun i => norm (f i - 1)) :=
    hu.of_nonneg_of_le (fun i => norm_nonneg _) hbound
  have hm : Multipliable f := by
    have h := multipliable_one_add_of_summable hdev
    simpa only [add_sub_cancel] using h
  have hfinite (F : Finset I) :
      norm (F.prod f - 1) <= Real.exp (tsum u) - 1 := by
    have hb := Finset.norm_prod_one_add_sub_one_le F (fun i => f i - 1)
    simp only [add_sub_cancel] at hb
    have hsum : F.sum (fun i => norm (f i - 1)) <= tsum u :=
      (Finset.sum_le_sum (fun i _ => hbound i)).trans
        (Summable.sum_le_tsum F (fun i _ => hu0 i) hu)
    exact hb.trans (sub_le_sub_right (Real.exp_le_exp.mpr hsum) 1)
  have hprod : Filter.Tendsto (fun F : Finset I => F.prod f) Filter.atTop
      (nhds (tprod f)) := hm.hasProd
  have hlim : Filter.Tendsto (fun F : Finset I => norm (F.prod f - 1)) Filter.atTop
      (nhds (norm (tprod f - 1))) :=
    (continuous_norm.tendsto _).comp (hprod.sub tendsto_const_nhds)
  exact le_of_tendsto hlim (Filter.Eventually.of_forall hfinite)

def sourceWeight (P : SourcePrime) : Real :=
  20 * Real.exp (-(3 / 2) * Real.log (sourceNorm P))

theorem source_weight_summable : Summable sourceWeight :=
  source_norm_majorant_summable.mul_left 20

theorem actual_source_factor_uniform_defect (S : Finset SourcePrime)
    (eta : SourceCharacter) (P : HighSourcePrime S) (s : Complex) (hs : 3 / 4 <= s.re) :
    norm (OAI.SevenEighths.ProbePhysical.idealClosedCorrection eta P.val s 1 (1 / 6) - 1) <=
      sourceWeight P.val := by
  rw [idealClosedCorrection_principal_eq eta P.val s (by linarith)]
  exact principal_factor_uniform_defect (sourceNorm P.val) (sourceEta eta P.val)
    (sourceRoot eta P.val) s P.property.1 (source_eta_norm_le eta P.val)
    (source_root_norm_le eta P.val) hs

theorem exists_uniform_principal_contraction (S0 : Finset SourcePrime) :
    Exists (fun S1 : Finset SourcePrime =>
      S0 <= S1 /\ forall S : Finset SourcePrime, S1 <= S ->
        forall eta : SourceCharacter, forall s : Complex, 3 / 4 <= s.re ->
          norm (tprod (fun P : HighSourcePrime S =>
            OAI.SevenEighths.ProbePhysical.idealClosedCorrection eta P.val s 1 (1 / 6)) - 1) <=
              1 / 2) := by
  classical
  have htail := tendsto_tsum_compl_atTop_zero sourceWeight
  have hevent : Filter.Eventually
      (fun S1 : Finset SourcePrime =>
        (tsum (fun P : {P : SourcePrime // Not (Membership.mem S1 P)} =>
          sourceWeight P.val)) < Real.log (3 / 2))
      Filter.atTop :=
    htail.eventually_lt_const (Real.log_pos (by norm_num))
  have hsup : Filter.Eventually (fun S1 : Finset SourcePrime => S0 <= S1) Filter.atTop :=
    Filter.eventually_ge_atTop S0
  have hex := (hevent.and hsup).exists
  let S1 : Finset SourcePrime := Classical.choose hex
  have hS1 := Classical.choose_spec hex
  refine Exists.intro S1 (And.intro hS1.2 ?_)
  intro S hsub eta s hs
  let e : HighSourcePrime S -> {P : SourcePrime // Not (Membership.mem S1 P)} :=
    fun P => Subtype.mk P.val (fun h => P.property.2 (hsub h))
  have he : Function.Injective e := by
    intro P R h
    apply Subtype.ext
    exact congrArg
      (fun T : {P : SourcePrime // Not (Membership.mem S1 P)} => T.val) h
  have hsmall : Summable (fun P : HighSourcePrime S => sourceWeight P.val) :=
    (source_high_norm_majorant_summable S).mul_left 20
  have hlarge : Summable
      (fun P : {P : SourcePrime // Not (Membership.mem S1 P)} => sourceWeight P.val) :=
    source_weight_summable.subtype _
  have htotal :
      (tsum (fun P : HighSourcePrime S => sourceWeight P.val)) <=
        tsum (fun P : {P : SourcePrime // Not (Membership.mem S1 P)} =>
          sourceWeight P.val) :=
    Summable.tsum_le_tsum_of_inj e he
      (fun P _ => by dsimp [sourceWeight]; positivity)
      (fun P => le_refl _) hsmall hlarge
  have hsum :
      (tsum (fun P : HighSourcePrime S => sourceWeight P.val)) < Real.log (3 / 2) :=
    lt_of_le_of_lt htotal hS1.1
  have hnorm := norm_tprod_defect_le_exp_tsum
    (fun P : HighSourcePrime S =>
      OAI.SevenEighths.ProbePhysical.idealClosedCorrection eta P.val s 1 (1 / 6))
    (fun P => sourceWeight P.val)
    (fun P => by dsimp [sourceWeight]; positivity)
    hsmall (fun P => actual_source_factor_uniform_defect S eta P s hs)
  calc
    _ <= Real.exp (tsum (fun P : HighSourcePrime S => sourceWeight P.val)) - 1 := hnorm
    _ <= Real.exp (Real.log (3 / 2)) - 1 :=
      sub_le_sub_right (Real.exp_le_exp.mpr hsum.le) 1
    _ = 1 / 2 := by rw [Real.exp_log (by norm_num : (0 : Real) < 3 / 2)]; norm_num


end PrimeFactorOscillations.PrincipalEulerContinuation
