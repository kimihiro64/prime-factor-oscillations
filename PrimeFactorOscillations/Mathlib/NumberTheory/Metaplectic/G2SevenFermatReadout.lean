/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.Metaplectic.G2SevenFermatCount

/-!
# The full sevenfold cubic source reads the Fermat septic

All 30 nondegenerate Jacobi terms and the full principal cross term
are retained. Both complete periods are compensated before cubing.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace Metaplectic.G2Seven.Fermat

open Curve Cubic

variable {F : Type*} [Field F] [Fintype F]

/-- Actual Gauss--Jacobi conversion for every nondegenerate character pair. -/
theorem normalized_jacobi_pair (chi : MulChar F Complex) (psi : AddChar F Complex)
    (rho : Complex) (horder : orderOf chi = 7) (hpsi : psi.IsPrimitive)
    (hrho : Not (rho = 0)) (r s : Fin 6)
    (hmod : Not ((r.val + 1 + (s.val + 1)) % 7 = 0)) :
    jacobi (chi ^ (r.val + 1)) (chi ^ (s.val + 1)) / rho =
      normalizedGauss chi psi rho (r.val + 1) *
        normalizedGauss chi psi rho (s.val + 1) /
          normalizedGauss chi psi rho (r.val + 1 + (s.val + 1)) := by
  have hn : Not (chi ^ (r.val + 1 + (s.val + 1)) = 1) := by
    intro he
    have hd := orderOf_dvd_of_pow_eq_one he
    rw [horder] at hd
    exact hmod (Nat.mod_eq_zero_of_dvd hd)
  have he : chi ^ (r.val + 1) * chi ^ (s.val + 1) =
      chi ^ (r.val + 1 + (s.val + 1)) := (pow_add _ _ _).symm
  have hp : Not (chi ^ (r.val + 1) * chi ^ (s.val + 1) = 1) := by
    rw [he]
    exact hn
  have hm := gauss_jacobi (chi ^ (r.val + 1)) (chi ^ (s.val + 1)) psi hp
  rw [he] at hm
  have hc : Not ((Fintype.card F : Complex) = 0) := by exact_mod_cast Fintype.card_ne_zero
  have hG := gaussSum_ne_zero_of_nontrivial hc hn hpsi
  apply (eq_div_iff (div_ne_zero hG hrho)).mpr
  unfold normalizedGauss
  field_simp [hrho]
  exact hm.symm

noncomputable def phaseTotal (g h j : Complex) : Complex :=
  Finset.univ.sum (fun i : Fin 8 =>
    (Jacobi.multiplicity i : Complex) * Jacobi.phase i g h j)

/-- All 30 actual Jacobi terms, including both formal sectors, match the source phases. -/
theorem nondegenerate_jacobi_phases (chi : MulChar F Complex) (psi : AddChar F Complex)
    (rho : Complex) (horder : orderOf chi = 7) (hpsi : psi.IsPrimitive)
    (hrho : Not (rho = 0)) (hrho2 : rho ^ 2 = (Fintype.card F : Complex)) :
    nondegenerateJacobi chi / rho =
      phaseTotal (normalizedGauss chi psi rho 1) (normalizedGauss chi psi rho 2)
        (normalizedGauss chi psi rho 3) := by
  let G : Nat -> Complex := normalizedGauss chi psi rho
  have hf (r s : Fin 6) :
      (if (r.val + 1 + (s.val + 1)) % 7 = 0 then 0
        else jacobi (chi ^ (r.val + 1)) (chi ^ (s.val + 1))) / rho =
      if (r.val + 1 + (s.val + 1)) % 7 = 0 then 0
        else G (r.val + 1) * G (s.val + 1) / G (r.val + 1 + (s.val + 1)) := by
    by_cases hm : (r.val + 1 + (s.val + 1)) % 7 = 0
    . simp [hm]
    . simp only [ite_eq_right hm]
      exact normalized_jacobi_pair chi psi rho horder hpsi hrho r s hm
  have h1 : Not (G 1 = 0) := normalized_gauss_ne_zero chi psi rho horder hpsi hrho 0
  have h2 : Not (G 2 = 0) := normalized_gauss_ne_zero chi psi rho horder hpsi hrho 1
  have h3 : Not (G 3 = 0) := normalized_gauss_ne_zero chi psi rho horder hpsi hrho 2
  have h4 : G 4 = 1 / G 3 := normalized_gauss_complement chi psi rho horder hpsi hrho hrho2 2
  have h5 : G 5 = 1 / G 2 := normalized_gauss_complement chi psi rho horder hpsi hrho hrho2 1
  have h6 : G 6 = 1 / G 1 := normalized_gauss_complement chi psi rho horder hpsi hrho hrho2 0
  have hper (n : Nat) : G n = G (n % 7) := by
    dsimp [G, normalizedGauss]
    rw [<- pow_mod_orderOf chi n, horder]
  have h8 : G 8 = G 1 := hper 8
  have h9 : G 9 = G 2 := hper 9
  have h10 : G 10 = G 3 := hper 10
  have h11 : G 11 = 1 / G 3 := (hper 11).trans h4
  have h12 : G 12 = 1 / G 2 := (hper 12).trans h5
  unfold nondegenerateJacobi
  simp_rw [Finset.sum_div, hf]
  change _ = phaseTotal (G 1) (G 2) (G 3)
  norm_num [phaseTotal, Jacobi.multiplicity, Jacobi.phase, Fin.sum_univ_succ]
  simp only [h4, h5, h6, h8, h9, h10, h11, h12]
  field_simp [h1, h2, h3]
  ring

/-- The exact eight-term weighted spectrum retains its native torus weights. -/
theorem phase_spectrum_total (t g h j X Y : Complex)
    (hg : Not (g = 0)) (hh : Not (h = 0)) (hj : Not (j = 0)) :
    Spectrum.phaseSpectrum t g h j X Y =
      Finset.univ.sum (fun i : Fin 8 =>
        (Jacobi.multiplicity i : Complex) * Jacobi.phase i g h j *
          Jacobi.weight i t X Y) := by
  norm_num [Spectrum.phaseSpectrum, Jacobi.multiplicity, Jacobi.phase,
    Jacobi.weight, Jacobi.powers, Fin.sum_univ_succ]
  field_simp [hg, hh, hj]
  ring

def principalCorrection (t X Y : Complex) : Complex :=
  (principal t X Y) ^ 3 + 6 * principal t X Y *
    (2 * t ^ 4 * X ^ 3 * Y ^ 6 + t ^ 6 * X ^ 10 * Y ^ 6)

noncomputable def fullFiniteProbe (t g h j X Y : Complex) (a : ZMod 7) : Complex :=
  1 + principalCorrection t X Y -
    (torusProjection (fun _ => true) t g h j X Y a) ^ 3

private theorem mean_const_sub (c : Complex) (f : ZMod 7 -> Complex) :
    mean (fun a => c - f a) = c - mean f := by
  unfold mean
  rw [Finset.sum_sub_distrib]
  norm_num
  ring

/-- The full cubic mean includes every principal-pair cross term before compensation. -/
theorem full_finite_probe_mean (t g h j X Y : Complex)
    (hg : Not (g = 0)) (hh : Not (h = 0)) (hj : Not (j = 0)) :
    mean (fullFiniteProbe t g h j X Y) = 1 - Spectrum.phaseSpectrum t g h j X Y := by
  unfold fullFiniteProbe
  rw [mean_const_sub, Spectrum.source_cubic_mean t g h j X Y hg hh hj]
  unfold principalCorrection
  ring

noncomputable def fullCoherentProbe (t g h j X Y : Complex) (a : ZMod 7) : Complex :=
  1 + principalCorrection t X Y -
    (periodDenominator t X Y * coherentProjection (fun _ => true) t g h j X Y a) ^ 3

theorem full_coherent_probe_eq (t g h j X Y : Complex)
    (hD : Not (periodDenominator t X Y = 0)) (a : ZMod 7) :
    fullCoherentProbe t g h j X Y a = fullFiniteProbe t g h j X Y a := by
  have he : periodDenominator t X Y *
      coherentProjection (fun _ => true) t g h j X Y a =
      torusProjection (fun _ => true) t g h j X Y a := by
    unfold coherentProjection
    field_simp [hD]
  unfold fullCoherentProbe fullFiniteProbe
  rw [he]

theorem full_coherent_probe_mean (t g h j X Y : Complex)
    (hg : Not (g = 0)) (hh : Not (h = 0)) (hj : Not (j = 0))
    (hD : Not (periodDenominator t X Y = 0)) :
    mean (fullCoherentProbe t g h j X Y) = 1 - Spectrum.phaseSpectrum t g h j X Y := by
  unfold mean
  simp_rw [full_coherent_probe_eq t g h j X Y hD]
  exact full_finite_probe_mean t g h j X Y hg hh hj

/-- The complete cubic observation equals the assembly of all eight masked means. -/
theorem full_coherent_assembly (t g h j X Y : Complex)
    (hg : Not (g = 0)) (hh : Not (h = 0)) (hj : Not (j = 0))
    (hD : Not (periodDenominator t X Y = 0)) :
    mean (fullCoherentProbe t g h j X Y) - 1 =
      Finset.univ.sum (fun i : Fin 8 => (Jacobi.multiplicity i : Complex) *
        (mean (Jacobi.coherentProbe i t g h j X Y) - 1)) := by
  calc
    _ = -(Finset.univ.sum (fun i : Fin 8 =>
        (Jacobi.multiplicity i : Complex) * Jacobi.phase i g h j *
          Jacobi.weight i t X Y)) := by
      rw [full_coherent_probe_mean t g h j X Y hg hh hj hD,
        phase_spectrum_total t g h j X Y hg hh hj]
      ring
    _ = _ := by
      rw [<- Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [Jacobi.coherent_probe_mean i t g h j X Y hg hh hj hD]
      ring


/-- The full eight-term spectrum has one common scale at the balanced corner. -/
theorem phase_spectrum_balanced (u g h j : Complex)
    (hu : Not (u = 0)) (hg : Not (g = 0)) (hh : Not (h = 0)) (hj : Not (j = 0)) :
    Spectrum.phaseSpectrum (u ^ 7) g h j (1 / u ^ 2) (1 / u ^ 2) =
      u ^ 15 * phaseTotal g h j := by
  rw [phase_spectrum_total _ _ _ _ _ _ hg hh hj]
  simp_rw [(Jacobi.balanced_corner u hu).2]
  rw [<- Finset.sum_mul]
  unfold phaseTotal
  ring

/-- Both full period series converge throughout the actual radial approach region. -/
theorem full_radial_series (u g h j : Complex) (hu : Not (u = 0))
    (r : Real) (hr0 : 0 <= r) (hr1 : r < 1) (a : ZMod 7) :
    HasSum (fun p : Period =>
      ((u ^ 7) ^ 2 * ((r : Complex) * (1 / u ^ 2)) ^ 7) ^ p.1 *
        ((u ^ 7) ^ 2 * ((r : Complex) * (1 / u ^ 2)) ^ 7) ^ p.2 *
        torusProjection (fun _ => true) (u ^ 7) g h j
          ((r : Complex) * (1 / u ^ 2)) ((r : Complex) * (1 / u ^ 2)) a)
      (coherentProjection (fun _ => true) (u ^ 7) g h j
        ((r : Complex) * (1 / u ^ 2)) ((r : Complex) * (1 / u ^ 2)) a) := by
  have hb := (Jacobi.balanced_corner u hu).1
  have hd := Jacobi.radial_domain (u ^ 7) (1 / u ^ 2) (1 / u ^ 2) hb hb r hr0 hr1
  exact coherentProjection_hasSum (fun _ => true) _ _ _ _ _ _ a hd.1 hd.2.1

/-- A nontrivial joint Abel limit of the complete cubic observation, not one masked phase. -/
theorem full_abel_readout (u g h j : Complex)
    (hu : Not (u = 0)) (hg : Not (g = 0)) (hh : Not (h = 0)) (hj : Not (j = 0)) :
    Filter.NeBot (nhdsWithin (1 : Real) (Set.Iio 1)) /\
    Filter.Tendsto (fun r : Real =>
      (mean (fullCoherentProbe (u ^ 7) g h j
        ((r : Complex) * (1 / u ^ 2)) ((r : Complex) * (1 / u ^ 2))) - 1) / u ^ 15)
      (nhdsWithin (1 : Real) (Set.Iio 1)) (nhds (-phaseTotal g h j)) := by
  constructor
  . infer_instance
  have hi (i : Fin 8) :
      Filter.Tendsto (fun r : Real => (Jacobi.multiplicity i : Complex) *
        ((mean (Jacobi.coherentProbe i (u ^ 7) g h j
          ((r : Complex) * (1 / u ^ 2)) ((r : Complex) * (1 / u ^ 2))) - 1) / u ^ 15))
        (nhdsWithin (1 : Real) (Set.Iio 1))
        (nhds ((Jacobi.multiplicity i : Complex) * (-Jacobi.phase i g h j))) :=
    tendsto_const_nhds.mul (Jacobi.normalized_abel_readout i u g h j hu hg hh hj).2
  have hsum := tendsto_finsetSum Finset.univ
    (fun i (_ : Membership.mem Finset.univ i) => hi i)
  have hv : Finset.univ.sum (fun i : Fin 8 =>
      (Jacobi.multiplicity i : Complex) * (-Jacobi.phase i g h j)) =
      -phaseTotal g h j := by
    simp only [phaseTotal, mul_neg, Finset.sum_neg_distrib]
  have hs : Filter.Tendsto (fun r : Real =>
      Finset.univ.sum (fun i : Fin 8 => (Jacobi.multiplicity i : Complex) *
        ((mean (Jacobi.coherentProbe i (u ^ 7) g h j
          ((r : Complex) * (1 / u ^ 2)) ((r : Complex) * (1 / u ^ 2))) - 1) / u ^ 15)))
      (nhdsWithin (1 : Real) (Set.Iio 1)) (nhds (-phaseTotal g h j)) := by
    simpa only [hv] using hsum
  have hr0 : Filter.Eventually (fun r : Real => 0 < r)
      (nhdsWithin (1 : Real) (Set.Iio 1)) :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_gt_nhds (by norm_num : (0 : Real) < 1))
  have hr1 : Filter.Eventually (fun r : Real => r < 1)
      (nhdsWithin (1 : Real) (Set.Iio 1)) := self_mem_nhdsWithin
  have heq : Filter.EventuallyEq (nhdsWithin (1 : Real) (Set.Iio 1))
      (fun r : Real => Finset.univ.sum (fun i : Fin 8 => (Jacobi.multiplicity i : Complex) *
        ((mean (Jacobi.coherentProbe i (u ^ 7) g h j
          ((r : Complex) * (1 / u ^ 2)) ((r : Complex) * (1 / u ^ 2))) - 1) / u ^ 15)))
      (fun r : Real => (mean (fullCoherentProbe (u ^ 7) g h j
        ((r : Complex) * (1 / u ^ 2)) ((r : Complex) * (1 / u ^ 2))) - 1) / u ^ 15) := by
    apply Filter.Eventually.mono (hr0.and hr1)
    intro r hr
    have hb := (Jacobi.balanced_corner u hu).1
    have hd := (Jacobi.radial_domain (u ^ 7) (1 / u ^ 2) (1 / u ^ 2)
      hb hb r (le_of_lt hr.1) hr.2).2.2
    dsimp only
    have ha := congrArg (fun z : Complex => z / u ^ 15)
      (full_coherent_assembly (u ^ 7) g h j _ _ hg hh hj hd)
    rw [ha, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    exact (mul_div_assoc _ _ _).symm
  exact Filter.Tendsto.congr' heq hs

/-- The complete Fermat discrepancy contains both the six-channel and two-phase sectors. -/
theorem fermat_trace_phases (chi : MulChar F Complex) (psi : AddChar F Complex)
    (rho : Complex) (horder : orderOf chi = 7) (hpsi : psi.IsPrimitive)
    (hrho : Not (rho = 0)) (hrho2 : rho ^ 2 = (Fintype.card F : Complex)) :
    ((Fintype.card F : Complex) + 1 - (chartCount F : Complex)) / rho =
      -phaseTotal (normalizedGauss chi psi rho 1) (normalizedGauss chi psi rho 2)
        (normalizedGauss chi psi rho 3) := by
  rw [chart_count_nondegenerate chi horder]
  calc
    _ = -(nondegenerateJacobi chi / rho) := by ring
    _ = _ := by rw [nondegenerate_jacobi_phases chi psi rho horder hpsi hrho hrho2]

/-- The actual full finite source observation is a Fermat-septic point-count readout. -/
theorem fermat_finite_readout (chi : MulChar F Complex) (psi : AddChar F Complex)
    (rho u : Complex) (horder : orderOf chi = 7) (hpsi : psi.IsPrimitive)
    (hrho : Not (rho = 0)) (hrho2 : rho ^ 2 = (Fintype.card F : Complex))
    (hu : Not (u = 0)) :
    mean (fullFiniteProbe (u ^ 7) (normalizedGauss chi psi rho 1)
      (normalizedGauss chi psi rho 2) (normalizedGauss chi psi rho 3)
      (1 / u ^ 2) (1 / u ^ 2)) =
      1 + u ^ 15 * (((Fintype.card F : Complex) + 1 - (chartCount F : Complex)) / rho) := by
  let G : Nat -> Complex := normalizedGauss chi psi rho
  have h1 : Not (G 1 = 0) := normalized_gauss_ne_zero chi psi rho horder hpsi hrho 0
  have h2 : Not (G 2 = 0) := normalized_gauss_ne_zero chi psi rho horder hpsi hrho 1
  have h3 : Not (G 3 = 0) := normalized_gauss_ne_zero chi psi rho horder hpsi hrho 2
  rw [full_finite_probe_mean _ _ _ _ _ _ h1 h2 h3,
    phase_spectrum_balanced u (G 1) (G 2) (G 3) hu h1 h2 h3,
    fermat_trace_phases chi psi rho horder hpsi hrho hrho2]
  ring

/-- The complete compensated double-period observation has the actual Fermat trace as its Abel limit. -/
theorem fermat_abel_readout (chi : MulChar F Complex) (psi : AddChar F Complex)
    (rho u : Complex) (horder : orderOf chi = 7) (hpsi : psi.IsPrimitive)
    (hrho : Not (rho = 0)) (hrho2 : rho ^ 2 = (Fintype.card F : Complex))
    (hu : Not (u = 0)) :
    Filter.NeBot (nhdsWithin (1 : Real) (Set.Iio 1)) /\
    Filter.Tendsto (fun r : Real =>
      (mean (fullCoherentProbe (u ^ 7) (normalizedGauss chi psi rho 1)
        (normalizedGauss chi psi rho 2) (normalizedGauss chi psi rho 3)
        ((r : Complex) * (1 / u ^ 2)) ((r : Complex) * (1 / u ^ 2))) - 1) / u ^ 15)
      (nhdsWithin (1 : Real) (Set.Iio 1))
      (nhds (((Fintype.card F : Complex) + 1 - (chartCount F : Complex)) / rho)) := by
  let G : Nat -> Complex := normalizedGauss chi psi rho
  have h1 : Not (G 1 = 0) := normalized_gauss_ne_zero chi psi rho horder hpsi hrho 0
  have h2 : Not (G 2 = 0) := normalized_gauss_ne_zero chi psi rho horder hpsi hrho 1
  have h3 : Not (G 3 = 0) := normalized_gauss_ne_zero chi psi rho horder hpsi hrho 2
  have ht := full_abel_readout u (G 1) (G 2) (G 3) hu h1 h2 h3
  constructor
  . exact ht.1
  rw [fermat_trace_phases chi psi rho horder hpsi hrho hrho2]
  exact ht.2

end Metaplectic.G2Seven.Fermat
