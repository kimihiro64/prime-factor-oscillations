import Mathlib.Analysis.SpecialFunctions.Log.Basic
import PrimeFactorOscillations.Helpers.ReversalCount
import PrimeFactorOscillations.Proof.Upper.GapScaleCutoff
import PrimeFactorUnimodality.Helpers.PrimeSequence.Basic

set_option autoImplicit false

/-! # A reversal-count coefficient above one fifth forces twin-prime infinitude -/

namespace PrimeFactorOscillations

private theorem exists_late_ascent_of_reversal_count (f : Nat -> Rat) (T m : Nat)
    (hTm : T < m) (hm : HasAtLeastReversals f m) :
    exists i : Nat, T <= i /\ f i < f (i + 1) := by
  classical
  by_contra h
  have htail : forall i : Nat, T <= i -> f (i + 1) <= f i := by
    intro i hi
    exact le_of_not_gt (fun hgt => h (Exists.intro i (And.intro hi hgt)))
  exact (not_le_of_gt hTm) (reversal_count_le_of_nonincreasing_tail f T m htail hm)

/-- An independently proved double-exponential reversal supply with leading
coefficient strictly above 1/5, even only at arbitrarily large ranks and for
either of the two canonical families, implies infinitely many twin primes. -/
theorem infinitely_many_twins_of_double_exp_reversals (b : Real)
    (hb : (1 : Real) / 5 < b)
    (hsupply : forall K : Nat, exists k m : Nat, K <= k /\
      Real.exp (Real.exp (b * k)) <= (m : Real) /\
      (HasAtLeastReversals (ordinaryDensity k) m \/
        HasAtLeastReversals (genericOddDensity k) m)) :
    forall X : Nat, exists p : Nat, X <= p /\ Nat.Prime p /\ Nat.Prime (p + 2) := by
  apply infinitely_many_twins_of_late_ascent_supply b hb
  intro K Q
  have hb0 : 0 < b := by linarith
  choose N hN using exists_nat_gt ((Q : Real) / b)
  choose k m hkm using hsupply (max K N)
  have hkK := (le_max_left K N).trans hkm.1
  have hkN : (N : Real) <= k := by
    exact_mod_cast (le_max_right K N).trans hkm.1
  have hQdiv : (Q : Real) / b < k := hN.trans_le hkN
  have hQb : (Q : Real) < b * k := by
    have hmul := mul_lt_mul_of_pos_right hQdiv hb0
    have hc : ((Q : Real) / b) * b = Q := by field_simp [ne_of_gt hb0]
    rw [hc] at hmul
    simpa only [mul_comm] using hmul
  have hlinear : b * k + 2 <= Real.exp (Real.exp (b * k)) := by
    have hinner := Real.add_one_le_exp (b * k)
    have houter := Real.add_one_le_exp (Real.exp (b * k))
    linarith only [hinner, houter]
  have hmPos : 0 < m := by
    have hpositive := (Real.exp_pos (Real.exp (b * k))).trans_le hkm.2.1
    exact_mod_cast hpositive
  have hQm : Q < m := by
    exact_mod_cast (show (Q : Real) < m by linarith only [hQb, hlinear, hkm.2.1])
  have hloc : exists i : Nat, m - 1 <= i /\
      (ordinaryDensity k i < ordinaryDensity k (i + 1) \/
        genericOddDensity k i < genericOddDensity k (i + 1)) := by
    rcases hkm.2.2 with ho | hg
    next =>
      choose i hi using exists_late_ascent_of_reversal_count
        (ordinaryDensity k) (m - 1) m (by omega) ho
      exact Exists.intro i (And.intro hi.1 (Or.inl hi.2))
    next =>
      choose i hi using exists_late_ascent_of_reversal_count
        (genericOddDensity k) (m - 1) m (by omega) hg
      exact Exists.intro i (And.intro hi.1 (Or.inr hi.2))
  choose i hi using hloc
  have hbase : i + 2 <= PrimeFactorUnimodality.primeAt i := Nat.add_two_le_nth_prime i
  have hmp : m <= PrimeFactorUnimodality.primeAt i - 1 := by omega
  have hpQ : Q <= PrimeFactorUnimodality.primeAt i := by omega
  have hge : Real.exp (Real.exp (b * k)) <=
      ((PrimeFactorUnimodality.primeAt i - 1 : Nat) : Real) :=
    hkm.2.1.trans (by exact_mod_cast hmp)
  have hlog := Real.log_le_log (Real.exp_pos _) hge
  rw [Real.log_exp] at hlog
  have hscale := Real.log_le_log (Real.exp_pos _) hlog
  rw [Real.log_exp] at hscale
  exact Exists.intro k (Exists.intro i
    (And.intro hkK (And.intro hpQ (And.intro hscale hi.2))))

end PrimeFactorOscillations
