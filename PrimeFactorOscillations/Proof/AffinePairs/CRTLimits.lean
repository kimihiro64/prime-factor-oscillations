import Mathlib.Data.Nat.Totient
import PrimeFactorOscillations.Mathlib.Data.ZMod.UnitPairCRT
import PrimeFactorOscillations.Proof.AffinePairs.PredicateLimits

/-! # Exact CRT product limits for actual ordered prime pairs -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open scoped Classical

theorem tendsto_prime_pair_crt_pattern_probability {I : Type*} [Fintype I]
    (m : I -> Nat) [forall i : I, NeZero (m i)] [NeZero (Finset.univ.prod m)]
    (hc : Pairwise (fun i j : I => (m i).Coprime (m j)))
    (P : forall i : I, Prod (ZMod (m i)) (ZMod (m i)) -> Prop) :
    Filter.Tendsto (fun N : Nat => primePairResidueEventProbability N (Finset.univ.prod m)
      (fun ab => forall i : I,
        P i ((ZMod.prodEquivPi m hc ab.1) i, (ZMod.prodEquivPi m hc ab.2) i)))
      Filter.atTop (nhds (Finset.univ.prod (fun i : I =>
        (Nat.card {ab : Prod (Units (ZMod (m i))) (Units (ZMod (m i))) //
          P i ((ab.1 : ZMod (m i)), (ab.2 : ZMod (m i)))} : Real) /
          ((m i).totient : Real) ^ 2))) := by
  let e : Equiv (Units (ZMod (Finset.univ.prod m)))
      (forall i : I, Units (ZMod (m i))) :=
    (Units.mapEquiv (ZMod.prodEquivPi m hc).toMulEquiv).toEquiv.trans
      MulEquiv.piUnits.toEquiv
  have htot : (Finset.univ.prod m).totient = Finset.univ.prod (fun i => (m i).totient) := by
    calc
      _ = Fintype.card (Units (ZMod (Finset.univ.prod m))) :=
        (ZMod.card_units_eq_totient _).symm
      _ = Fintype.card (forall i : I, Units (ZMod (m i))) := Fintype.card_congr e
      _ = Finset.univ.prod (fun i : I => Fintype.card (Units (ZMod (m i)))) :=
        Fintype.card_pi
      _ = _ := by simp only [ZMod.card_units_eq_totient]
  have hnum := ZMod.natCard_unit_pair_crt_patterns m hc P
  have hscalar :
      (Nat.card {ab : Prod (Units (ZMod (Finset.univ.prod m)))
          (Units (ZMod (Finset.univ.prod m))) // forall i : I,
        P i ((ZMod.prodEquivPi m hc (ab.1 : ZMod (Finset.univ.prod m))) i,
          (ZMod.prodEquivPi m hc (ab.2 : ZMod (Finset.univ.prod m))) i)} : Real) /
        ((Finset.univ.prod m).totient : Real) ^ 2 =
      Finset.univ.prod (fun i : I =>
        (Nat.card {ab : Prod (Units (ZMod (m i))) (Units (ZMod (m i))) //
          P i ((ab.1 : ZMod (m i)), (ab.2 : ZMod (m i)))} : Real) /
          ((m i).totient : Real) ^ 2) := by
    rw [hnum, htot, Nat.cast_prod, Nat.cast_prod, Finset.prod_div_distrib, Finset.prod_pow]
  have hlimit := tendsto_prime_pair_predicate_probability (Finset.univ.prod m)
    (fun ab => forall i : I,
      P i ((ZMod.prodEquivPi m hc ab.1) i, (ZMod.prodEquivPi m hc ab.2) i))
  exact Eq.mp (congrArg (fun x : Real => Filter.Tendsto (fun N : Nat =>
    primePairResidueEventProbability N (Finset.univ.prod m)
      (fun ab => forall i : I,
        P i ((ZMod.prodEquivPi m hc ab.1) i, (ZMod.prodEquivPi m hc ab.2) i)))
        Filter.atTop (nhds x)) hscalar) hlimit

end PrimeFactorOscillations
