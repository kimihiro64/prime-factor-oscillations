import PrimeFactorOscillations.Helpers.ReversalGapCount
import PrimeFactorOscillations.Proof.Upper.GapScaleCutoff
import PrimeFactorOscillations.Proof.Upper.PrimeValueTail

/-! # Actual gap counts control canonical reversal counts -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open PrimeFactorUnimodality

/-- Every reversal beyond an arbitrary sharp gap scale is charged to an
actual gap smaller than H, up to the independently proved prime-value tail. -/
theorem both_reversal_count_le_gap_count_at_scale
    (H : Nat) (b epsilon : Real)
    (hb : 1 / ((H : Real) + 1) < b) (he : 0 < epsilon) :
    exists K Q : Nat, 2 <= K /\ 3 <= Q /\
      forall k : Nat, K <= k -> forall T U : Nat, Q <= T ->
      b * k <= Real.log (Real.log (T - 1 : Nat)) ->
      upperCutoffValue epsilon k + 1 <= (U : Real) + 1 ->
      forall m : Nat,
        (HasAtLeastReversals (ordinaryDensity k) m \/
          HasAtLeastReversals (genericOddDensity k) m) ->
        m <= T + ((Finset.range U).filter
          (fun i => primeAt i <= U /\ primeGap i <= H - 1)).card := by
  choose K1 Q hgap using both_densities_eventually_descend_above_gap_scale H b hb
  choose K2 htail using both_densities_eventually_strict_after_prime_value epsilon he
  refine Exists.intro (max K1 K2) (Exists.intro Q
    (And.intro (hgap.1.trans (le_max_left _ _)) (And.intro hgap.2.1 ?_)))
  intro k hk T U hQT hscale hU m hm
  have hk1 := (le_max_left K1 K2).trans hk
  have hk2 := (le_max_right K1 K2).trans hk
  have hT : 3 <= T := hgap.2.1.trans hQT
  have hcover : forall i : Nat,
      (ordinaryDensity k i < ordinaryDensity k (i + 1) \/
        genericOddDensity k i < genericOddDensity k (i + 1)) ->
      primeAt i <= T \/ (primeAt i <= U /\ primeGap i <= H - 1) := by
    intro i ha
    by_cases hpT : primeAt i <= T
    next => exact Or.inl hpT
    next =>
      have hTp : T <= primeAt i := by omega
      have hpU : primeAt i <= U := by
        by_contra hn
        have hnp : U + 1 <= primeAt i := by omega
        have hnpR : (U : Real) + 1 <= primeAt i := by exact_mod_cast hnp
        have hd := htail.2 k hk2 i (hU.trans hnpR)
        rcases ha with ho | hg
        next => exact (not_lt_of_ge hd.1.le) ho
        next => exact (not_lt_of_ge hd.2.le) hg
      have hTpos : (1 : Real) < ((T - 1 : Nat) : Real) := by
        exact_mod_cast (show 1 < T - 1 by omega)
      have hpref : ((T - 1 : Nat) : Real) <= ((primeAt i - 1 : Nat) : Real) := by
        exact_mod_cast Nat.sub_le_sub_right hTp 1
      have hlogs := Real.log_le_log (lt_trans (by norm_num) hTpos) hpref
      have hloglog := Real.log_le_log (Real.log_pos hTpos) hlogs
      have hscaleP := hscale.trans hloglog
      have hsmall : primeGap i <= H - 1 := by
        by_contra hn
        have hH : H <= primeGap i := by omega
        have hpq : primeAt i <= primeAt (i + 1) :=
          (primeAt_strictMono (Nat.lt_succ_self i)).le
        have hbig : primeAt i + H <= primeAt (i + 1) := by
          change H <= primeAt (i + 1) - primeAt i at hH
          omega
        have hd := hgap.2.2 k hk1 i (hQT.trans hTp) hbig hscaleP
        rcases ha with ho | hg
        next => exact (not_lt_of_ge hd.2.le) ho
        next => exact (not_lt_of_ge hd.1.le) hg
      exact Or.inr (And.intro hpU hsmall)
  rcases hm with ho | hg
  next =>
    exact reversal_count_le_short_gap_count (ordinaryDensity k) (H - 1) T U m
      (fun i hi => hcover i (Or.inl hi)) ho
  next =>
    exact reversal_count_le_short_gap_count (genericOddDensity k) (H - 1) T U m
      (fun i hi => hcover i (Or.inr hi)) hg

end PrimeFactorOscillations
