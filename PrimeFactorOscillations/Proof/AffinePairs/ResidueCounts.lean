import PrimeFactorOscillations.Definitions.PrimePairEnsemble
import PrimeFactorOscillations.Proof.AffinePairs.ResidueProbabilities

/-! # Exact residue fibers of the ordered prime-pair ensemble -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open scoped Classical

theorem prime_progression_count_eq_filter (N q : Nat) (a : ZMod q) :
    Real.primeCountingZMod (N : Real) q a =
      ((Nat.primesLE N).filter (fun p : Nat => (p : ZMod q) = a)).card := by
  unfold Real.primeCountingZMod
  rw [<- Set.ncard_coe_finset]
  congr 1
  ext p
  simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_primesLE,
    Set.mem_ofPred_eq, Nat.cast_le, and_assoc, and_left_comm, and_comm]

theorem prime_pair_residue_fiber (N q : Nat) (a b : ZMod q) :
    ((primePairs N).filter (fun ab => ((ab.1 : ZMod q), (ab.2 : ZMod q)) = (a, b))).card =
      Real.primeCountingZMod (N : Real) q a * Real.primeCountingZMod (N : Real) q b := by
  have hf : (primePairs N).filter
      (fun ab => ((ab.1 : ZMod q), (ab.2 : ZMod q)) = (a, b)) =
      SProd.sprod ((Nat.primesLE N).filter (fun p : Nat => (p : ZMod q) = a))
        ((Nat.primesLE N).filter (fun p : Nat => (p : ZMod q) = b)) := by
    ext ab
    simp only [primePairs, Finset.mem_filter, Finset.mem_product, Prod.mk.injEq,
      and_assoc, and_left_comm]
  rw [hf]
  simp only [Finset.card_product, <- prime_progression_count_eq_filter]

theorem prime_pair_residue_count_eq_sum (N q : Nat) (R : Finset (Prod (ZMod q) (ZMod q))) :
    primePairResidueCount N q R = R.sum (fun ab =>
      Real.primeCountingZMod (N : Real) q ab.1 *
        Real.primeCountingZMod (N : Real) q ab.2) := by
  rw [primePairResidueCount, <- Finset.sum_card_fiberwise_eq_card_filter]
  apply Finset.sum_congr rfl
  intro ab hab
  exact prime_pair_residue_fiber N q ab.1 ab.2

end PrimeFactorOscillations
