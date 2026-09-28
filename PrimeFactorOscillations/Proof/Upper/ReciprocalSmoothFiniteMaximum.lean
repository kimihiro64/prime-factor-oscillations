import PrimeFactorOscillations.Helpers.PrimeConsecutive
import PrimeFactorOscillations.Helpers.PrimeDensitySteps
import PrimeFactorOscillations.Helpers.ReciprocalSmoothBands
import PrimeFactorOscillations.Proof.Upper.FiniteMaximum

/-! # Attained finite reversal maxima for reciprocal-smooth real local densities -/

set_option autoImplicit false
set_option Elab.async false

open Filter

namespace PrimeFactorOscillations.ReciprocalSmoothLaw

/-- For every sufficiently large rank, the actual real density has an attained
finite maximal number of separated strict descent-then-ascent reversals. -/
theorem eventually_exists_reversal_number (law : ReciprocalSmoothLaw) :
    Filter.Eventually (fun k : Nat => exists N : Nat,
      HasReversalNumber (law.rankDensity k) N) Filter.atTop := by
  have hnu : Not (law.nu = 0) := ne_of_gt law.nu_pos
  have ha : 0 < 1 / law.nu := div_pos (by norm_num) law.nu_pos
  have hmargin : 1 < ((2 : Real) + law.nu) * (1 / law.nu) := by
    have hc : ((2 : Real) + law.nu) * (1 / law.nu) = 1 + 2 / law.nu := by
      field_simp
      ring
    rw [hc]
    have h := div_pos (by norm_num : (0 : Real) < 2) law.nu_pos
    linarith only [h]
  choose P hP using law.rank_density_descent_beyond_gap_scale 2 (1 / law.nu) ha hmargin
  filter_upwards [hP] with k hk
  choose T0 hT0 using exists_nat_gt (Real.exp (Real.exp ((1 / law.nu) * k)))
  let T := max (P + 3) (T0 + 3)
  have htail : forall i : Nat, T <= i -> law.rankDensity k (i + 1) < law.rankDensity k i := by
    intro i hi
    have hindex : i + 2 <= PrimeFactorUnimodality.primeAt i := Nat.add_two_le_nth_prime i
    have hiP : P + 3 <= i := (le_max_left _ _).trans hi
    have hiT : T0 + 3 <= i := (le_max_right _ _).trans hi
    have hp3 : 3 <= PrimeFactorUnimodality.primeAt i := by omega
    have hbound : Real.exp (Real.exp ((1 / law.nu) * k)) <=
        ((PrimeFactorUnimodality.primeAt i - 1 : Nat) : Real) := by
      exact hT0.le.trans (by exact_mod_cast (show T0 <= PrimeFactorUnimodality.primeAt i - 1 by omega))
    have hlog1 := Real.log_le_log (Real.exp_pos (Real.exp ((1 / law.nu) * k))) hbound
    rw [Real.log_exp] at hlog1
    have hlog2 := Real.log_le_log (Real.exp_pos ((1 / law.nu) * k)) hlog1
    rw [Real.log_exp] at hlog2
    apply hk (PrimeFactorUnimodality.primeAt i) (PrimeFactorUnimodality.primeAt (i + 1))
      hp3 (by omega) (PrimeFactorUnimodality.prime_primeAt i)
      (PrimeFactorUnimodality.prime_primeAt (i + 1))
      (PrimeFactorUnimodality.primeAt_strictMono (Nat.lt_succ_self i))
      (fun t htlo hthi => no_prime_between_consecutive_indexed i t htlo hthi)
      (primeAt_gap_ge_two i (by omega)) hlog2
  choose N hN using PrimeFactorOscillations.exists_reversalNumber_of_tail
    (law.rankDensity k) T (fun i hi => (htail i hi).le)
  exact Exists.intro N hN.1


end PrimeFactorOscillations.ReciprocalSmoothLaw
