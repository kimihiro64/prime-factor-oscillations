import PrimeFactorOscillations.Definitions.PrimePairEnsemble
import PrimeFactorOscillations.Proof.AffinePairs.NormalizedProgressions

/-! # Finite-event errors for the ordered prime-pair ensemble -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations
open scoped Classical

theorem tendsto_prime_pair_finite_event (E : Prod Nat Nat -> Prop)
    (S : Finset (Prod Nat Nat)) (hS : forall ab, E ab -> Membership.mem S ab) :
    Filter.Tendsto (fun N : Nat => primePairProbability N E) Filter.atTop (nhds 0) := by
  have hpi : Filter.Tendsto (fun N : Nat => (Nat.primeCounting N : Real))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp Nat.tendsto_primeCounting
  have hinv := tendsto_inv_atTop_zero.comp hpi
  have hbound : Filter.Tendsto
      (fun N : Nat => (S.card : Real) / (Nat.primeCounting N : Real) ^ 2)
      Filter.atTop (nhds 0) := by
    simpa only [Function.comp_apply, div_eq_mul_inv, inv_pow,
      zero_pow (by decide : Not (2 = 0)), mul_zero] using
      (tendsto_const_nhds (x := (S.card : Real))).mul (hinv.pow 2)
  apply squeeze_zero _ _ hbound
  intro N
  exact div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  intro N
  have hc : ((primePairs N).filter E).card <= S.card := by
    apply Finset.card_le_card
    intro ab hab
    exact hS ab (Finset.mem_filter.mp hab).2
  exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (sq_nonneg _)

theorem prime_pair_probability_event_split (N : Nat) (E Z : Prod Nat Nat -> Prop) :
    primePairProbability N (fun ab => E ab /\ Z ab) +
      primePairProbability N (fun ab => E ab /\ Not (Z ab)) =
      primePairProbability N E := by
  have h := Finset.card_filter_add_card_filter_not (s := (primePairs N).filter E) Z
  have normalize (s : Finset (Prod Nat Nat)) (P : Prod Nat Nat -> Prop) (d : DecidablePred P) :
      @Finset.filter (Prod Nat Nat) P d s =
        @Finset.filter (Prod Nat Nat) P (fun ab => Classical.propDecidable (P ab)) s :=
    @Finset.filter_congr_decidable (Prod Nat Nat) s P d
      (fun ab => Classical.propDecidable (P ab))
  have hr := congrArg (fun n : Nat => (n : Real) / (Nat.primeCounting N : Real) ^ 2) h
  simpa only [primePairProbability, Nat.cast_add, add_div, Finset.filter_filter, normalize] using hr

theorem tendsto_prime_pair_remove_finite (E Z : Prod Nat Nat -> Prop)
    (S : Finset (Prod Nat Nat)) (hS : forall ab, Z ab -> Membership.mem S ab)
    (d : Real)
    (hlim : Filter.Tendsto (fun N : Nat => primePairProbability N E)
      Filter.atTop (nhds d)) :
    Filter.Tendsto (fun N : Nat =>
      primePairProbability N (fun ab => E ab /\ Not (Z ab))) Filter.atTop (nhds d) := by
  have hzero := tendsto_prime_pair_finite_event (fun ab => E ab /\ Z ab) S
    (fun ab h => hS ab h.2)
  have heq (N : Nat) :
      primePairProbability N E - primePairProbability N (fun ab => E ab /\ Z ab) =
      primePairProbability N (fun ab => E ab /\ Not (Z ab)) := by
    linarith only [prime_pair_probability_event_split N E Z]
  simpa only [sub_zero, heq] using hlim.sub hzero

end PrimeFactorOscillations
