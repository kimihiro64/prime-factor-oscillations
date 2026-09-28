import PrimeFactorOscillations.Assembly.ReciprocalSmoothSpectrum
import PrimeFactorOscillations.Helpers.GapSpectrumPhase
import PrimeFactorOscillations.Proof.PrimeClusters.GapFrequency

/-! # Unconditional finite phase profile of reciprocal-smooth oscillations -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

/-- The least actual full-frequency gap class exists unconditionally. It cuts
the entire dimension profile to finitely many classes and dominates for every
sufficiently large fixed dimension. No numerical optimization is assumed. -/
theorem exists_least_full_gap_phase_profile :
    exists J : Nat, 2 <= J /\ primeGapFrequencyExponent J = 1 /\
      (forall H : Nat, 2 <= H -> H < J -> primeGapFrequencyExponent H < 1) /\
      (forall nu : Real, 0 < nu -> exists H : Nat, 2 <= H /\ H <= J /\
        primeGapSpectrum nu = primeGapFrequencyExponent H / ((H : Real) + nu)) /\
      exists V : Nat, forall nu : Real, 0 < nu -> (V : Real) <= nu ->
        primeGapSpectrum nu = 1 / ((J : Real) + nu) /\
        1 / primeGapSpectrum nu - nu = J := by
  classical
  let J := Nat.find exists_full_prime_gap_frequency_class
  have hJ : 2 <= J /\ primeGapFrequencyExponent J = 1 :=
    Nat.find_spec exists_full_prime_gap_frequency_class
  have hmin : forall H : Nat, 2 <= H -> H < J -> primeGapFrequencyExponent H < 1 := by
    intro H hH hHJ
    have hne : Not (primeGapFrequencyExponent H = 1) := by
      intro hfull
      have hle : J <= H := Nat.find_min' exists_full_prime_gap_frequency_class (And.intro hH hfull)
      omega
    exact lt_of_le_of_ne (primeGapFrequencyExponent_bounds H).2 hne
  choose V hV using primeGapSpectrum_eventually_full_class J hJ.1 hJ.2 hmin
  refine Exists.intro J (And.intro hJ.1 (And.intro hJ.2 (And.intro hmin (And.intro ?_ ?_))))
  next =>
    exact fun nu hnu => primeGapSpectrum_finite_maximum J hJ.1 hJ.2 nu hnu
  next =>
    refine Exists.intro V ?_
    intro nu hnu hVnu
    have heq := hV nu hnu hVnu
    refine And.intro heq ?_
    rw [heq]
    have hd : 0 < (J : Real) + nu := by positivity
    have hc : 1 / (1 / ((J : Real) + nu)) = (J : Real) + nu := by
      field_simp [ne_of_gt hd]
    rw [hc]
    ring

/-- The full-frequency input makes the exact spectrum strictly positive
for every fixed positive dimension. -/
theorem primeGapSpectrum_pos (nu : Real) (hnu : 0 < nu) :
    0 < primeGapSpectrum nu := by
  choose H hH using exists_full_prime_gap_frequency_class
  have hlo := primeGapFrequency_ratio_le_spectrum H nu hnu
  rw [hH.2] at hlo
  exact (div_pos (by norm_num) (by positivity : 0 < (H : Real) + nu)).trans_le hlo

/-- Across fixed reciprocal-smooth laws of sufficiently large dimension, the
exact reversal rate recovers the least actual full-frequency gap class.
The rank limit is taken separately for each fixed law. -/
theorem exists_reversal_rate_recovers_full_gap_class :
    exists J V : Nat, 2 <= J /\ primeGapFrequencyExponent J = 1 /\
      forall law : ReciprocalSmoothLaw, (V : Real) <= law.nu ->
      exists n : Nat -> Nat,
        (exists K : Nat, forall k : Nat, K <= k ->
          HasReversalNumber (law.rankDensity k) (n k)) /\
        1 / Filter.limsup (fun k : Nat =>
          Real.log (Real.log (3 + (n k : Real))) / k) Filter.atTop - law.nu = J := by
  choose J hJ using exists_least_full_gap_phase_profile
  choose V hV using hJ.2.2.2.2
  refine Exists.intro J (Exists.intro V (And.intro hJ.1 (And.intro hJ.2.1 ?_)))
  intro law hlarge
  choose n hn using law.exists_sharp_reversal_rate
  refine Exists.intro n (And.intro hn.1 ?_)
  rw [hn.2]
  exact (hV law.nu law.nu_pos hlarge).2

end PrimeFactorOscillations
