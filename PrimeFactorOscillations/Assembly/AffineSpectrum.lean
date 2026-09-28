import PrimeFactorOscillations.Assembly.GapSpectrumPhase
import PrimeFactorOscillations.Proof.AffinePairs.RankDensity

/-! # Sharp reversal spectrum of actual affine prime-pair factorization densities -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.AffineSumFamily

/-- Actual arithmetic densities, finite maximal reversal numbers on a rank tail,
and their exact positive double-logarithmic growth rate. The input cutoff limit
is taken separately before the rank limsup. -/
theorem exists_sharp_arithmetic_reversal_rate (F : AffineSumFamily) :
    exists d : Nat -> Nat -> Real, exists n : Nat -> Nat,
      (forall k i : Nat, Filter.Tendsto (fun N : Nat => primePairProbability N (fun ab =>
        PrimeFactorUnimodality.IsKthDistinctPrimeFactor (F.value ab.1 ab.2).natAbs k
          (PrimeFactorUnimodality.primeAt i))) Filter.atTop (nhds (d k i))) /\
      (exists K : Nat, forall k : Nat, K <= k -> HasReversalNumber (d k) (n k)) /\
      Filter.limsup (fun k : Nat =>
        Real.log (Real.log (3 + (n k : Real))) / k) Filter.atTop =
        primeGapSpectrum F.arity /\
      0 < primeGapSpectrum F.arity := by
  choose n hn using F.reciprocalSmoothLaw.exists_sharp_reversal_rate
  refine Exists.intro F.reciprocalSmoothLaw.rankDensity
    (Exists.intro n (And.intro ?_ (And.intro hn.1 (And.intro hn.2 ?_))))
  intro k i
  exact F.tendsto_kth_distinct_prime_factor k (PrimeFactorUnimodality.primeAt i)
    (PrimeFactorUnimodality.prime_primeAt i)
  exact primeGapSpectrum_pos F.arity (by exact_mod_cast F.arity_pos)

/-- Actual affine factorization densities with finite maximal reversal counts
at every rank and their exact positive sharp growth rate. -/
theorem exists_sharp_arithmetic_reversal_rate_all_ranks (F : AffineSumFamily) :
    exists d : Nat -> Nat -> Real, exists n : Nat -> Nat,
      (forall k i : Nat, Filter.Tendsto (fun N : Nat => primePairProbability N (fun ab =>
        PrimeFactorUnimodality.IsKthDistinctPrimeFactor (F.value ab.1 ab.2).natAbs k
          (PrimeFactorUnimodality.primeAt i))) Filter.atTop (nhds (d k i))) /\
      (forall k : Nat, HasReversalNumber (d k) (n k)) /\
      Filter.limsup (fun k : Nat =>
        Real.log (Real.log (3 + (n k : Real))) / k) Filter.atTop =
        primeGapSpectrum F.arity /\
      0 < primeGapSpectrum F.arity := by
  choose n hn using F.reciprocalSmoothLaw.exists_sharp_reversal_rate_all_ranks
  refine Exists.intro F.reciprocalSmoothLaw.rankDensity
    (Exists.intro n (And.intro ?_ (And.intro hn.1 (And.intro hn.2 ?_))))
  intro k i
  exact F.tendsto_kth_distinct_prime_factor k (PrimeFactorUnimodality.primeAt i)
    (PrimeFactorUnimodality.prime_primeAt i)
  exact primeGapSpectrum_pos F.arity (by exact_mod_cast F.arity_pos)


end PrimeFactorOscillations.AffineSumFamily

namespace PrimeFactorOscillations

/-- Across fixed affine families of sufficiently large degree, actual rank-density
oscillation rates recover the least full-frequency bounded-gap class. -/
theorem exists_affine_arithmetic_rate_recovers_full_gap_class :
    exists J V : Nat, 2 <= J /\ primeGapFrequencyExponent J = 1 /\
      forall F : AffineSumFamily, V <= F.arity ->
      exists d : Nat -> Nat -> Real, exists n : Nat -> Nat,
        (forall k i : Nat, Filter.Tendsto (fun N : Nat => primePairProbability N (fun ab =>
          PrimeFactorUnimodality.IsKthDistinctPrimeFactor (F.value ab.1 ab.2).natAbs k
            (PrimeFactorUnimodality.primeAt i))) Filter.atTop (nhds (d k i))) /\
        (exists K : Nat, forall k : Nat, K <= k -> HasReversalNumber (d k) (n k)) /\
        1 / Filter.limsup (fun k : Nat =>
          Real.log (Real.log (3 + (n k : Real))) / k) Filter.atTop - F.arity = J := by
  choose J V hJ using exists_reversal_rate_recovers_full_gap_class
  refine Exists.intro J (Exists.intro V (And.intro hJ.1 (And.intro hJ.2.1 ?_)))
  intro F hF
  have hlarge : (V : Real) <= F.reciprocalSmoothLaw.nu := by
    change (V : Real) <= F.arity
    exact_mod_cast hF
  choose n hn using hJ.2.2 F.reciprocalSmoothLaw hlarge
  refine Exists.intro F.reciprocalSmoothLaw.rankDensity
    (Exists.intro n (And.intro ?_ (And.intro hn.1 hn.2)))
  intro k i
  exact F.tendsto_kth_distinct_prime_factor k (PrimeFactorUnimodality.primeAt i)
    (PrimeFactorUnimodality.prime_primeAt i)

end PrimeFactorOscillations
