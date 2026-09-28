import PrimeFactorOscillations.Proof.AffinePairs.UnitEvents

/-! # Intrinsic event probabilities for the actual prime-pair ensemble -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open scoped Classical

theorem prime_pair_residue_event_eq_probability (N q : Nat) [NeZero q]
    (P : Prod (ZMod q) (ZMod q) -> Prop) :
    primePairResidueEventProbability N q P =
      primePairResidueProbability N q (Finset.univ.filter P) := by
  have heq : (primePairs N).filter (fun ab => P ((ab.1 : ZMod q), (ab.2 : ZMod q))) =
      (primePairs N).filter (fun ab =>
        Membership.mem (Finset.univ.filter P) ((ab.1 : ZMod q), (ab.2 : ZMod q))) := by
    apply Finset.ext
    intro ab
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold primePairResidueEventProbability primePairProbability
    primePairResidueProbability primePairResidueCount
  rw [heq]

theorem tendsto_prime_pair_predicate_probability (q : Nat) [NeZero q]
    (P : Prod (ZMod q) (ZMod q) -> Prop) :
    Filter.Tendsto (fun N : Nat => primePairResidueEventProbability N q P) Filter.atTop
      (nhds ((Nat.card {ab : Prod (Units (ZMod q)) (Units (ZMod q)) //
        P ((ab.1 : ZMod q), (ab.2 : ZMod q))} : Real) / (q.totient : Real) ^ 2)) := by
  simpa only [prime_pair_residue_event_eq_probability, Nat.card_eq_fintype_card] using
    tendsto_prime_pair_unit_event q P

end PrimeFactorOscillations
