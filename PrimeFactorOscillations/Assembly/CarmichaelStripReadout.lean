/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelStripCarrier
import PrimeFactorOscillations.Assembly.CarmichaelTraceSharpness

/-!
# Actual compensated readouts retain the strip-dependent carrier bound

The local residue identities identify the strict-sign carrier with the
multiplicity carrier. Both compensation terms remain present. No RH
hypothesis is used, and no claim of an upper multiplicity bound is made.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelStripCarrier

open DirichletCompensatedProbe CarmichaelWeightedSignal

theorem readout_projection_negative_iff (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {s : Complex | 0 < s.re /\ s.re < 1})
    (d : Real) (hd : 1 < d) (rho : Complex) (T : Real)
    (hRho : Membership.mem (upperZeroValues T) rho) (r : Complex)
    (hr : Filter.Tendsto
      (fun s => (s - rho) * affinePowerReadout (zetaMultiplicityReadout G) d s)
      (nhdsWithin rho (Set.compl {rho})) (nhds r)) :
    (r * (rho + (d : Complex) - 1)).im < 0 <->
      d * (analyticOrderNatAt riemannZeta (powerMap d rho) : Real) <
        (analyticOrderNatAt riemannZeta rho : Real) := by
  have hw := (mem_upperZeroValues T rho).mp hRho
  have heq := zeta_power_readout_residue_eq G hG d hd rho
    (And.intro hw.2.1 hw.2.2.1) (ne_of_gt hw.2.2.2.1) r hr
  rw [heq, zetaCanonicalPowerResidue_im d hd rho (ne_of_gt hw.2.2.2.1)]
  constructor
  . intro h
    by_contra hn
    have hp := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hn)) hw.2.2.2.1.le
    exact (not_le_of_gt h) hp
  . intro h
    exact mul_neg_of_neg_of_pos (sub_neg.mpr h) hw.2.2.2.1

theorem joint_readout_carrier_eq (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {s : Complex | 0 < s.re /\ s.re < 1})
    (d e T : Real) (hd : 1 < d) (he : 1 < e)
    (rd re : Complex -> Complex)
    (hD : forall rho, Membership.mem (upperZeroValues T) rho -> Filter.Tendsto
      (fun s => (s - rho) * affinePowerReadout (zetaMultiplicityReadout G) d s)
      (nhdsWithin rho (Set.compl {rho})) (nhds (rd rho)))
    (hE : forall rho, Membership.mem (upperZeroValues T) rho -> Filter.Tendsto
      (fun s => (s - rho) * affinePowerReadout (zetaMultiplicityReadout G) e s)
      (nhdsWithin rho (Set.compl {rho})) (nhds (re rho))) :
    jointCarrierSupport d e T = (upperZeroValues T).filter (fun rho =>
      (rd rho * (rho + (d : Complex) - 1)).im < 0 \/
        (re rho * (rho + (e : Complex) - 1)).im < 0) := by
  classical
  apply Finset.ext
  intro rho
  simp only [jointCarrierSupport, Finset.mem_filter]
  constructor
  . intro h
    apply And.intro h.1
    exact h.2.imp
      (readout_projection_negative_iff G hG d hd rho T h.1 (rd rho) (hD rho h.1)).mpr
      (readout_projection_negative_iff G hG e he rho T h.1 (re rho) (hE rho h.1)).mpr
  . intro h
    apply And.intro h.1
    exact h.2.imp
      (readout_projection_negative_iff G hG d hd rho T h.1 (rd rho) (hD rho h.1)).mp
      (readout_projection_negative_iff G hG e he rho T h.1 (re rho) (hE rho h.1)).mp

theorem zeta_joint_readout_strip_bound (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {s : Complex | 0 < s.re /\ s.re < 1})
    (d e T sigma : Real) (hd : 2 <= d) (he : 2 <= e)
    (L : Nat) (hL : 0 < L)
    (hStrip : forall z, Membership.mem (rightZeroSupport T) z -> z.re <= sigma)
    (hDepth : (1 / 2 : Real) <= (e / d) ^ L * (1 - sigma))
    (rd re : Complex -> Complex)
    (hD : forall rho, Membership.mem (upperZeroValues T) rho -> Filter.Tendsto
      (fun s => (s - rho) * affinePowerReadout (zetaMultiplicityReadout G) d s)
      (nhdsWithin rho (Set.compl {rho})) (nhds (rd rho)))
    (hE : forall rho, Membership.mem (upperZeroValues T) rho -> Filter.Tendsto
      (fun s => (s - rho) * affinePowerReadout (zetaMultiplicityReadout G) e s)
      (nhdsWithin rho (Set.compl {rho})) (nhds (re rho))) :
    (1 - (1 - 1 / (Finset.range L).sum (fun j => (e / d) ^ j)) / (2 * e)) *
        (upperZeroValues T).sum zetaSquareMass <=
      ((upperZeroValues T).filter (fun rho =>
        (rd rho * (rho + (d : Complex) - 1)).im < 0 \/
          (re rho * (rho + (e : Complex) - 1)).im < 0)).sum zetaSquareMass := by
  rw [<- joint_readout_carrier_eq G hG d e T (by linarith) (by linarith) rd re hD hE]
  exact zeta_joint_carrier_strip_bound d e T sigma hd he L hL hStrip hDepth

theorem zeta_two_three_readout_carrier_seven_eighths (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {s : Complex | 0 < s.re /\ s.re < 1})
    (T : Real) (rd re : Complex -> Complex)
    (hD : forall rho, Membership.mem (upperZeroValues T) rho -> Filter.Tendsto
      (fun s => (s - rho) * affinePowerReadout (zetaMultiplicityReadout G) 2 s)
      (nhdsWithin rho (Set.compl {rho})) (nhds (rd rho)))
    (hE : forall rho, Membership.mem (upperZeroValues T) rho -> Filter.Tendsto
      (fun s => (s - rho) * affinePowerReadout (zetaMultiplicityReadout G) 3 s)
      (nhdsWithin rho (Set.compl {rho})) (nhds (re rho))) :
    (111 / 130 : Real) * (upperZeroValues T).sum zetaSquareMass <=
      ((upperZeroValues T).filter (fun rho =>
        (rd rho * (rho + ((2 : Real) : Complex) - 1)).im < 0 \/
          (re rho * (rho + ((3 : Real) : Complex) - 1)).im < 0)).sum zetaSquareMass := by
  rw [<- joint_readout_carrier_eq G hG 2 3 T (by norm_num) (by norm_num) rd re hD hE]
  exact zeta_two_three_carrier_seven_eighths T

theorem zeta_two_four_readout_carrier_seven_eighths (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {s : Complex | 0 < s.re /\ s.re < 1})
    (T : Real) (rd re : Complex -> Complex)
    (hD : forall rho, Membership.mem (upperZeroValues T) rho -> Filter.Tendsto
      (fun s => (s - rho) * affinePowerReadout (zetaMultiplicityReadout G) 2 s)
      (nhdsWithin rho (Set.compl {rho})) (nhds (rd rho)))
    (hE : forall rho, Membership.mem (upperZeroValues T) rho -> Filter.Tendsto
      (fun s => (s - rho) * affinePowerReadout (zetaMultiplicityReadout G) 4 s)
      (nhdsWithin rho (Set.compl {rho})) (nhds (re rho))) :
    (11 / 12 : Real) * (upperZeroValues T).sum zetaSquareMass <=
      ((upperZeroValues T).filter (fun rho =>
        (rd rho * (rho + ((2 : Real) : Complex) - 1)).im < 0 \/
          (re rho * (rho + ((4 : Real) : Complex) - 1)).im < 0)).sum zetaSquareMass := by
  have h := zeta_joint_readout_strip_bound G hG 2 4 T (7 / 8)
    (by norm_num) (by norm_num) 2 (by norm_num)
    (rightZeroSupport_seven_eighths T) (by norm_num) rd re hD hE
  have hCoef : (1 - (1 - 1 /
      (Finset.range 2).sum (fun j => ((4 : Real) / 2) ^ j)) / (2 * 4)) =
        (11 / 12 : Real) := by
    norm_num [Finset.sum_range_succ]
  rw [hCoef] at h
  exact h

end PrimeFactorOscillations.CarmichaelStripCarrier
