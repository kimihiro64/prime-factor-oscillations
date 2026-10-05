/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeProfileThetaClock
import PrimeFactorOscillations.Helpers.ReversalCount
import PrimeFactorUnimodality.Helpers.PrimeSequence.Basic

/-!
# Exact finite endpoint capacity and last ascents

Separated reversal witnesses inject into their actual lower prime endpoints.
The theta cutoff set is finite for every real threshold. An eventual
nonincreasing tail and a nonempty reversal family also give a last ascent.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

/-- Actual prime endpoints strictly below the theta reference threshold. -/
def primeThetaEndpoints (T : Real) : Set Nat :=
  fun p => Nat.Prime p /\ Chebyshev.theta ((p - 1 : Nat) : Real) < T

/-- Finiteness is proved separately, so the cardinal does not mask an infinite set. -/
noncomputable def primeThetaEndpointCount (T : Real) : Nat :=
  Nat.card (primeThetaEndpoints T)

theorem finite_primeThetaEndpoints (T : Real) : (primeThetaEndpoints T).Finite := by
  have he : Filter.Eventually (fun N : Nat => T <= Chebyshev.theta (N : Real))
      Filter.atTop :=
    tendsto_primeProfile_theta_atTop.eventually (Filter.eventually_ge_atTop T)
  choose N0 hN0 using he.exists_forall_of_atTop
  apply (Set.finite_Iic N0).subset
  intro p hp
  change p <= N0
  change Nat.Prime p /\ Chebyshev.theta ((p - 1 : Nat) : Real) < T at hp
  by_contra hnot
  have hge : N0 <= p - 1 := by omega
  exact (not_lt_of_ge (hN0 (p - 1) hge)) hp.2

variable {R : Type*} [Preorder R]

theorem reversal_count_le_prime_endpoint_card (f : Nat -> R) (m : Nat)
    (S : Set Nat) (hS : S.Finite)
    (hcover : forall i : Nat, f i < f (i + 1) ->
      S (PrimeFactorUnimodality.primeAt i))
    (hm : HasAtLeastReversals f m) : m <= Nat.card S := by
  classical
  let : Fintype S := hS.fintype
  choose descent ascent h using hm
  have hmono : StrictMono ascent := by
    intro i j hij
    exact lt_trans (Nat.lt_succ_self _) (lt_trans (h.2 i j hij) (h.1 j).1)
  let into : Fin m -> S := fun j =>
    Subtype.mk (PrimeFactorUnimodality.primeAt (ascent j))
      (hcover (ascent j) (h.1 j).2.2)
  have hinj : Function.Injective into := by
    intro i j heq
    exact hmono.injective
      (PrimeFactorUnimodality.primeAt_strictMono.injective (congrArg Subtype.val heq))
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective into hinj

theorem reversal_count_le_primeThetaEndpointCount (f : Nat -> R) (m : Nat)
    (T : Real)
    (hcover : forall i : Nat, f i < f (i + 1) ->
      Chebyshev.theta ((PrimeFactorUnimodality.primeAt i - 1 : Nat) : Real) < T)
    (hm : HasAtLeastReversals f m) : m <= primeThetaEndpointCount T := by
  apply reversal_count_le_prime_endpoint_card f m (primeThetaEndpoints T)
    (finite_primeThetaEndpoints T) _ hm
  intro i hi
  exact And.intro (PrimeFactorUnimodality.prime_primeAt i) (hcover i hi)

theorem reversal_count_le_primeCounting_of_ascent_bound (f : Nat -> R) (i m : Nat)
    (hbound : forall j : Nat, f j < f (j + 1) -> j <= i)
    (hm : HasAtLeastReversals f m) :
    m <= Nat.primeCounting (PrimeFactorUnimodality.primeAt i) := by
  classical
  let S := Nat.primesLE (PrimeFactorUnimodality.primeAt i)
  have hcover (j : Nat) (hj : f j < f (j + 1)) :
      Membership.mem S (PrimeFactorUnimodality.primeAt j) := by
    exact Nat.mem_primesLE.mpr (And.intro
      (PrimeFactorUnimodality.primeAt_strictMono.monotone (hbound j hj))
      (PrimeFactorUnimodality.prime_primeAt j))
  have hc := reversal_count_le_prime_endpoint_card f m (S : Set Nat)
    S.finite_toSet hcover hm
  change m <= Nat.card {p : Nat // Membership.mem S p} at hc
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, S,
    Nat.primesLE_card_eq_primeCounting] using hc

theorem primeCounting_le_primeThetaEndpointCount (P : Nat) (T : Real)
    (hP : Chebyshev.theta ((P - 1 : Nat) : Real) < T) :
    Nat.primeCounting P <= primeThetaEndpointCount T := by
  classical
  let : Fintype (primeThetaEndpoints T) := (finite_primeThetaEndpoints T).fintype
  let into : {p : Nat // Membership.mem (Nat.primesLE P) p} -> primeThetaEndpoints T :=
    fun p => Subtype.mk p.val (And.intro (Nat.mem_primesLE.mp p.property).2
      ((Chebyshev.theta_mono (by
        exact_mod_cast Nat.sub_le_sub_right (Nat.mem_primesLE.mp p.property).1 1)).trans_lt hP))
  have hinj : Function.Injective into := by
    intro p q heq
    apply Subtype.ext
    exact congrArg (fun z : primeThetaEndpoints T => z.val) heq
  have hc := Nat.card_le_card_of_injective into hinj
  change Nat.primeCounting P <= Nat.card (primeThetaEndpoints T)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe,
    Nat.primesLE_card_eq_primeCounting] using hc

theorem exists_last_ascent_of_nonincreasing_tail (f : Nat -> R) (T m : Nat)
    (hmpos : 0 < m)
    (htail : forall i : Nat, T <= i -> f (i + 1) <= f i)
    (hm : HasAtLeastReversals f m) :
    exists i : Nat, f i < f (i + 1) /\
      forall j : Nat, f j < f (j + 1) -> j <= i := by
  classical
  choose descent ascent h using hm
  have hlt (j : Nat) (hj : f j < f (j + 1)) : j < T := by
    exact lt_of_not_ge (fun hge => not_lt_of_ge (htail j hge) hj)
  let S : Finset Nat := (Finset.range T).filter (fun j => f j < f (j + 1))
  have hmemS (j : Nat) (hj : f j < f (j + 1)) : Membership.mem S j :=
    Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr (hlt j hj)) hj)
  have hne : S.Nonempty :=
    Exists.intro (ascent (Fin.mk 0 hmpos)) (hmemS _ (h.1 (Fin.mk 0 hmpos)).2.2)
  refine Exists.intro (S.max' hne) (And.intro ?_ ?_)
  . exact (Finset.mem_filter.mp (Finset.max'_mem S hne)).2
  . intro j hj
    exact Finset.le_max' S j (hmemS j hj)

end PrimeFactorOscillations
