import PrimeFactorOscillations.Definitions.PrimeEventProbability
import PrimeFactorOscillations.Proof.AffinePairs.FiniteEventLimits

/-! # Decision-procedure independent prime-frequency interfaces

These are exact observable transports, not new arithmetic estimates.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open scoped Classical
attribute [local instance] Classical.propDecidable

theorem prime_filter_ratio_eq_probability (N : Nat) (P : Nat -> Prop)
    (d : DecidablePred P) :
    ((@Finset.filter Nat P d (Nat.primesLE N)).card : Real) /
      (Nat.primeCounting N : Real) = primeEventProbability N P := by
  unfold primeEventProbability
  apply congrArg (fun z : Nat => (z : Real) / (Nat.primeCounting N : Real))
  apply congrArg Finset.card
  apply Finset.ext
  intro n
  simp only [Finset.mem_filter]

theorem tendsto_prime_probability_zero_of_imp (P Q : Nat -> Prop)
    (hPQ : forall n : Nat, P n -> Q n)
    (hQ : Filter.Tendsto (fun N : Nat => primeEventProbability N Q)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun N : Nat => primeEventProbability N P) Filter.atTop (nhds 0) := by
  have hQraw : Filter.Tendsto (fun N : Nat =>
      (((Nat.primesLE N).filter Q).card : Real) / (Nat.primeCounting N : Real))
        Filter.atTop (nhds 0) := by
    simpa only [prime_filter_ratio_eq_probability] using hQ
  simpa only [prime_filter_ratio_eq_probability] using
    tendsto_prime_event_zero_of_imp P Q hPQ hQraw

theorem tendsto_prime_probability_finite_union_zero {I : Type*} [Fintype I]
    (P : I -> Nat -> Prop)
    (hP : forall i : I, Filter.Tendsto (fun N : Nat => primeEventProbability N (P i))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun N : Nat => primeEventProbability N (fun n => exists i : I, P i n))
      Filter.atTop (nhds 0) := by
  have hPraw : forall i : I, Filter.Tendsto (fun N : Nat =>
      (((Nat.primesLE N).filter (P i)).card : Real) / (Nat.primeCounting N : Real))
        Filter.atTop (nhds 0) := by
    intro i
    simpa only [prime_filter_ratio_eq_probability] using hP i
  simpa only [prime_filter_ratio_eq_probability] using tendsto_prime_finite_union_zero P hPraw

theorem tendsto_prime_probability_bounded_zero (B : Nat) :
    Filter.Tendsto (fun N : Nat => primeEventProbability N (fun n => n <= B))
      Filter.atTop (nhds 0) := by
  simpa only [prime_filter_ratio_eq_probability] using tendsto_prime_bounded_event_zero B

theorem tendsto_prime_probability_one_of_complement_zero (P : Nat -> Prop)
    (hnot : Filter.Tendsto (fun N : Nat => primeEventProbability N (fun n => Not (P n)))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun N : Nat => primeEventProbability N P) Filter.atTop (nhds 1) := by
  have hraw : Filter.Tendsto (fun N : Nat =>
      (((Nat.primesLE N).filter (fun n => Not (P n))).card : Real) /
        (Nat.primeCounting N : Real)) Filter.atTop (nhds 0) := by
    simpa only [prime_filter_ratio_eq_probability] using hnot
  simpa only [prime_filter_ratio_eq_probability] using
    tendsto_prime_event_one_of_complement_zero P hraw

end PrimeFactorOscillations
