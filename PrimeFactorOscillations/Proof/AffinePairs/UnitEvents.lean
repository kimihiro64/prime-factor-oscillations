import PrimeFactorOscillations.Mathlib.Data.ZMod.UnitPairCRT
import PrimeFactorOscillations.Proof.AffinePairs.ResidueLimits

/-! # Actual prime-pair event limits in unit-residue coordinates -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open scoped Classical

theorem tendsto_prime_pair_unit_event (q : Nat) [NeZero q]
    (P : Prod (ZMod q) (ZMod q) -> Prop) :
    Filter.Tendsto (fun N : Nat =>
      primePairResidueProbability N q (Finset.univ.filter P)) Filter.atTop
      (nhds ((Fintype.card {ab : Prod (Units (ZMod q)) (Units (ZMod q)) //
        P ((ab.1 : ZMod q), (ab.2 : ZMod q))} : Real) / (q.totient : Real) ^ 2)) := by
  have hq : 1 <= q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hcard := ZMod.card_unit_pair_event_eq_filter q P
  have hlimit := tendsto_prime_pair_residue_probability q hq (Finset.univ.filter P)
  have normalize (s : Finset (Prod (ZMod q) (ZMod q)))
      (d : DecidablePred (fun ab : Prod (ZMod q) (ZMod q) => IsUnit ab.1 /\ IsUnit ab.2)) :
      @Finset.filter (Prod (ZMod q) (ZMod q))
        (fun ab => IsUnit ab.1 /\ IsUnit ab.2) d s =
      @Finset.filter (Prod (ZMod q) (ZMod q))
        (fun ab => IsUnit ab.1 /\ IsUnit ab.2)
        (fun ab => Classical.propDecidable (IsUnit ab.1 /\ IsUnit ab.2)) s :=
    @Finset.filter_congr_decidable (Prod (ZMod q) (ZMod q)) s
      (fun ab => IsUnit ab.1 /\ IsUnit ab.2) d
      (fun ab => Classical.propDecidable (IsUnit ab.1 /\ IsUnit ab.2))
  simp only [normalize] at hcard hlimit
  rw [hcard] at hlimit
  exact hlimit

end PrimeFactorOscillations
