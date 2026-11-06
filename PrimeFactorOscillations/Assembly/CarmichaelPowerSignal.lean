/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelPowerCompensation
import PrimeFactorOscillations.Assembly.CarmichaelWeightedSignal
import PrimeFactorOscillations.Helpers.DirichletPowerProbe

/-!
# Nonreal zero preservation for affine power compensation

Nonnegative real character weights preserve their target zero signal for every
real power d > 1, even when the affine reference point is also a zero.
The full reference multiplicity is retained in an exact signed residue wedge.
No RH, zero-free strip, simple-zero, or reference-nonvanishing hypothesis is used.
This is a signal theorem, not an estimate excluding zeros.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.CarmichaelWeightedSignal

private theorem power_residue_wedge (d A B : Real) (rho : Complex)
    (hden : Not (rho + (d : Complex) - 1 = 0)) :
    (((-(A : Complex) + (d : Complex) * rho /
      (rho + (d : Complex) - 1) * (B : Complex)) *
      (rho + (d : Complex) - 1)) * star rho).im =
        A * (d - 1) * rho.im := by
  have he :
      (-(A : Complex) + (d : Complex) * rho /
        (rho + (d : Complex) - 1) * (B : Complex)) *
        (rho + (d : Complex) - 1) =
      rho * ((d : Complex) * (B : Complex) - (A : Complex)) -
        (A : Complex) * ((d : Complex) - 1) := by
    field_simp [hden]
    ring
  rw [he]
  simp only [Complex.mul_im, Complex.mul_re, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re, Complex.one_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  ring

private theorem power_residue_wedge_bound (d A B : Real) (rho : Complex)
    (hden : Not (rho + (d : Complex) - 1 = 0)) :
    abs (A * (d - 1) * rho.im) <=
      norm (-(A : Complex) + (d : Complex) * rho /
        (rho + (d : Complex) - 1) * (B : Complex)) *
      norm (rho + (d : Complex) - 1) * norm rho := by
  have h := Complex.abs_im_le_norm
    (((-(A : Complex) + (d : Complex) * rho /
      (rho + (d : Complex) - 1) * (B : Complex)) *
      (rho + (d : Complex) - 1)) * star rho)
  rw [power_residue_wedge d A B rho hden] at h
  simpa only [norm_mul, norm_star] using h

private theorem power_residue_ne_zero (d A B : Real) (rho : Complex)
    (hd : 1 < d) (hA : 0 < A) (hIm : Not (rho.im = 0))
    (hden : Not (rho + (d : Complex) - 1 = 0)) :
    Not (-(A : Complex) + (d : Complex) * rho /
      (rho + (d : Complex) - 1) * (B : Complex) = 0) := by
  intro hz
  have hb := power_residue_wedge_bound d A B rho hden
  rw [hz, norm_zero, zero_mul, zero_mul] at hb
  have hp : 0 < abs (A * (d - 1) * rho.im) :=
    abs_pos.mpr (mul_ne_zero
      (mul_ne_zero (ne_of_gt hA) (ne_of_gt (sub_pos.mpr hd))) hIm)
  exact (not_lt_of_ge hb) hp

open DirichletCompensatedProbe

def affinePowerReadout (R : Complex -> Complex) (d : Real) (s : Complex) : Complex :=
  R s - s / (s + (d : Complex) - 1) * R (powerMap d s)

theorem affinePowerReadout_scaled_limit
    (R : Complex -> Complex) (d : Real) (hd : 0 < d)
    (rho : Complex) (hden : Not (rho + (d : Complex) - 1 = 0))
    (A B : Real)
    (hA : Filter.Tendsto (fun s => (s - rho) * R s)
      (nhdsWithin rho (Set.compl {rho})) (nhds (-(A : Complex))))
    (hB : Filter.Tendsto (fun s => (s - powerMap d rho) * R s)
      (nhdsWithin (powerMap d rho) (Set.compl {powerMap d rho}))
      (nhds (-(B : Complex)))) :
    Filter.Tendsto (fun s => (s - rho) * affinePowerReadout R d s)
      (nhdsWithin rho (Set.compl {rho}))
      (nhds (-(A : Complex) + (d : Complex) * rho /
        (rho + (d : Complex) - 1) * (B : Complex))) := by
  have hdC : Not ((d : Complex) = 0) := by exact_mod_cast hd.ne'
  have hi : Function.Injective (powerMap d) := by
    intro z v hv
    have he := congrArg (fun t : Complex => t * (d : Complex)) hv
    dsimp only [powerMap] at he
    field_simp [hdC] at he
    linear_combination he
  have hm : AnalyticAt Complex (powerMap d) rho := by
    change AnalyticAt Complex
      (fun s : Complex => (s + (d : Complex) - 1) / (d : Complex)) rho
    fun_prop
  have ht : Filter.Tendsto (powerMap d)
      (nhdsWithin rho (Set.compl {rho}))
      (nhdsWithin (powerMap d rho) (Set.compl {powerMap d rho})) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine And.intro (hm.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    change Not (s = rho) at hs
    change Not (powerMap d s = powerMap d rho)
    exact fun he => hs (hi he)
  have hdiff (s : Complex) :
      powerMap d s - powerMap d rho = (s - rho) / (d : Complex) := by
    dsimp only [powerMap]
    field_simp [hdC]
    ring
  have heq (s : Complex) : (s - rho) * R (powerMap d s) =
      (d : Complex) * ((powerMap d s - powerMap d rho) * R (powerMap d s)) := by
    rw [hdiff]
    field_simp [hdC]
  have href : Filter.Tendsto (fun s => (s - rho) * R (powerMap d s))
      (nhdsWithin rho (Set.compl {rho}))
      (nhds ((d : Complex) * (-(B : Complex)))) :=
    (Filter.tendsto_congr' (Filter.Eventually.of_forall heq)).mpr
      (tendsto_const_nhds.mul (hB.comp ht))
  have hscalar : AnalyticAt Complex
      (fun s : Complex => s / (s + (d : Complex) - 1)) rho :=
    analyticAt_id.div ((analyticAt_id.add analyticAt_const).sub analyticAt_const) hden
  have hsc : Filter.Tendsto
      (fun s : Complex => s / (s + (d : Complex) - 1))
      (nhdsWithin rho (Set.compl {rho}))
      (nhds (rho / (rho + (d : Complex) - 1))) :=
    hscalar.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hf : (fun s => (s - rho) * affinePowerReadout R d s) =
      (fun s => (s - rho) * R s -
        s / (s + (d : Complex) - 1) * ((s - rho) * R (powerMap d s))) := by
    funext s
    unfold affinePowerReadout
    ring
  rw [hf]
  (convert hA.sub (hsc.mul href) using 1; ring)

private theorem nonzero_scaled_limit_not_analytic (R : Complex -> Complex)
    (rho r : Complex) (hr : Not (r = 0))
    (ht : Filter.Tendsto (fun s => (s - rho) * R s)
      (nhdsWithin rho (Set.compl {rho})) (nhds r)) :
    Not (AnalyticAt Complex R rho) := by
  intro ha
  have hc : ContinuousAt (fun s : Complex => (s - rho) * R s) rho :=
    (continuousAt_id.sub continuousAt_const).mul ha.continuousAt
  have hz : Filter.Tendsto (fun s : Complex => (s - rho) * R s)
      (nhdsWithin rho (Set.compl {rho})) (nhds 0) := by
    simpa only [sub_self, zero_mul] using
      hc.tendsto.mono_left nhdsWithin_le_nhds
  have : Filter.NeBot (nhdsWithin rho (Set.compl {rho})) := by
    have h := PerfectSpace.univ_preperfect rho (Set.mem_univ rho)
    have he : Set.compl ({rho} : Set Complex) =
        Compl.compl ({rho} : Set Complex) := by rfl
    rw [he]
    simpa only [AccPt, Filter.principal_univ, inf_top_eq] using h
  exact hr (tendsto_nhds_unique ht hz)

theorem real_packet_scaled_residue {iota : Type*} [Fintype iota]
    {q : Nat} [NeZero q] (chi : iota -> DirichletCharacter Complex q)
    (w : iota -> Real) (G : Complex -> Complex)
    (rho : Complex) (hOne : Not (rho = 1)) (hG : AnalyticAt Complex G rho) :
    exists n : iota -> Nat,
      (forall i, DirichletCharacter.LFunction (chi i) rho = 0 -> 0 < n i) /\
      Filter.Tendsto
        (fun s => (s - rho) *
          readout (fun i => DirichletCharacter.LFunction (chi i))
            (fun i => (w i : Complex)) G s)
        (nhdsWithin rho (Set.compl {rho}))
        (nhds (-((Finset.univ.sum (fun i => w i * (n i : Real)) : Real) : Complex))) := by
  classical
  choose n g hg hgn hEq hPos using
    (fun i => L_factor_exists (chi i) rho hOne)
  refine Exists.intro n (And.intro hPos ?_)
  have h := weighted_limit (fun i => DirichletCharacter.LFunction (chi i))
    g (fun i => (w i : Complex)) n rho hg hgn hEq G hG
  have he : (Finset.univ.sum (fun i => (w i : Complex) * (n i : Complex))) =
      ((Finset.univ.sum (fun i => w i * (n i : Real)) : Real) : Complex) := by
    simp
  simpa only [he] using h

theorem real_packet_power_nonreal_zero_not_analytic
    {iota : Type*} [Fintype iota] {q : Nat} [NeZero q]
    (chi : iota -> DirichletCharacter Complex q) (w : iota -> Real)
    (hw : forall i, 0 <= w i) (i0 : iota) (hi0 : 0 < w i0)
    (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {s : Complex | 0 < s.re})
    (d : Real) (hd : 1 < d) (rho : Complex)
    (hRe : 0 < rho.re) (hIm : Not (rho.im = 0))
    (hZero : DirichletCharacter.LFunction (chi i0) rho = 0) :
    Not (AnalyticAt Complex
      (affinePowerReadout
        (readout (fun i => DirichletCharacter.LFunction (chi i))
          (fun i => (w i : Complex)) G) d) rho) := by
  classical
  have hd0 : 0 < d := zero_lt_one.trans hd
  have hdC : Not ((d : Complex) = 0) := by exact_mod_cast hd0.ne'
  have hOne : Not (rho = 1) := by
    intro he
    apply hIm
    rw [he, Complex.one_im]
  have hden : Not (rho + (d : Complex) - 1 = 0) := by
    intro he
    have hr := congrArg Complex.re he
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.one_re, Complex.zero_re] at hr
    linarith
  have hMapRe : 0 < (powerMap d rho).re := by
    have h := powerMap_real_identity d hd0 rho
    nlinarith
  have hMapOne : Not (powerMap d rho = 1) := by
    intro he
    have hm := congrArg (fun s : Complex => s * (d : Complex)) he
    dsimp only [powerMap] at hm
    field_simp [hdC] at hm
    apply hOne
    linear_combination hm
  choose n hn hFirst using real_packet_scaled_residue chi w G rho hOne (hG rho hRe)
  choose m hm hSecond using real_packet_scaled_residue chi w G (powerMap d rho)
    hMapOne (hG _ hMapRe)
  let A : Real := Finset.univ.sum (fun i => w i * (n i : Real))
  let B : Real := Finset.univ.sum (fun i => w i * (m i : Real))
  have hA : 0 < A := by
    have hp : 0 < w i0 * (n i0 : Real) :=
      mul_pos hi0 (by exact_mod_cast hn i0 hZero)
    exact lt_of_lt_of_le hp
      (Finset.single_le_sum (fun i _ => mul_nonneg (hw i) (Nat.cast_nonneg _))
        (Finset.mem_univ i0))
  have hLimit := affinePowerReadout_scaled_limit
    (readout (fun i => DirichletCharacter.LFunction (chi i))
      (fun i => (w i : Complex)) G) d hd0 rho hden A B hFirst hSecond
  exact nonzero_scaled_limit_not_analytic _ rho _
    (power_residue_ne_zero d A B rho hd hA hIm hden) hLimit

/-- The original one-character power probe retains every nonreal zero for d > 1. -/
theorem powerProbe_nonreal_zero_not_analytic
    {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    (G : Complex -> Complex)
    (hG : AnalyticOnNhd Complex G {s : Complex | 0 < s.re})
    (d : Real) (hd : 1 < d) (rho : Complex)
    (hRe : 0 < rho.re) (hIm : Not (rho.im = 0))
    (hZero : DirichletCharacter.LFunction chi rho = 0) :
    Not (AnalyticAt Complex
      (DirichletCompensatedProbe.powerProbe chi G d) rho) := by
  have h := real_packet_power_nonreal_zero_not_analytic
    (fun _ : Unit => chi) (fun _ : Unit => (1 : Real))
    (fun _ => zero_le_one) Unit.unit zero_lt_one G hG d hd rho hRe hIm hZero
  have he : readout (fun _ : Unit => DirichletCharacter.LFunction chi)
      (fun _ : Unit => ((1 : Real) : Complex)) G = DirichletZeroReadout.readout chi G := by
    funext s
    simp [readout, DirichletZeroReadout.readout]
  rw [he] at h
  exact h

end PrimeFactorOscillations.CarmichaelWeightedSignal
