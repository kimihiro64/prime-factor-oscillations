import PrimeFactorOscillations.Proof.AffinePairs.MarginalLimits

/-! # Finite-event prime-frequency limits

Finite unions retain every overlap. Frequencies are normalized by the actual
prime count, including its zero values at the smallest input cutoffs.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open scoped Classical
attribute [local instance] Classical.propDecidable

theorem tendsto_prime_event_zero_of_imp (P Q : Nat -> Prop)
    (hPQ : forall n : Nat, P n -> Q n)
    (hQ : Filter.Tendsto (fun N : Nat =>
      (((Nat.primesLE N).filter Q).card : Real) / (Nat.primeCounting N : Real))
        Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun N : Nat =>
      (((Nat.primesLE N).filter P).card : Real) / (Nat.primeCounting N : Real))
        Filter.atTop (nhds 0) := by
  refine squeeze_zero' (Filter.Eventually.of_forall (fun N =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))) ?_ hQ
  apply Filter.Eventually.of_forall
  intro N
  have hsub : (Nat.primesLE N).filter P <= (Nat.primesLE N).filter Q := by
    intro n hn
    have hh := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr (And.intro hh.1 (hPQ n hh.2))
  have hc : (((Nat.primesLE N).filter P).card : Real) <=
      (((Nat.primesLE N).filter Q).card : Real) := by
    exact_mod_cast Finset.card_le_card hsub
  exact div_le_div_of_nonneg_right hc (Nat.cast_nonneg _)

theorem tendsto_prime_finite_union_zero {I : Type*} [Fintype I]
    (P : I -> Nat -> Prop)
    (hP : forall i : I, Filter.Tendsto (fun N : Nat =>
      (((Nat.primesLE N).filter (P i)).card : Real) / (Nat.primeCounting N : Real))
        Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun N : Nat =>
      (((Nat.primesLE N).filter (fun n => exists i : I, P i n)).card : Real) /
        (Nat.primeCounting N : Real)) Filter.atTop (nhds 0) := by
  have hsum : Filter.Tendsto (fun N : Nat => Finset.univ.sum (fun i : I =>
      (((Nat.primesLE N).filter (P i)).card : Real) / (Nat.primeCounting N : Real)))
        Filter.atTop (nhds 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun i _ => hP i)
  refine squeeze_zero' (Filter.Eventually.of_forall (fun N =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))) ?_ hsum
  apply Filter.Eventually.of_forall
  intro N
  have heq : (Nat.primesLE N).filter (fun n => exists i : I, P i n) =
      Finset.univ.biUnion (fun i : I => (Nat.primesLE N).filter (P i)) := by
    apply Finset.ext
    intro n
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    . intro h
      choose i hi using h.2
      exact Exists.intro i (And.intro h.1 hi)
    . intro h
      choose i hi using h
      exact And.intro hi.1 (Exists.intro i hi.2)
  have hc : ((Nat.primesLE N).filter (fun n => exists i : I, P i n)).card <=
      Finset.univ.sum (fun i : I => ((Nat.primesLE N).filter (P i)).card) := by
    rw [heq]
    exact Finset.card_biUnion_le
  have hr : (((Nat.primesLE N).filter (fun n => exists i : I, P i n)).card : Real) <=
      Finset.univ.sum (fun i : I => (((Nat.primesLE N).filter (P i)).card : Real)) := by
    exact_mod_cast hc
  calc
    _ <= (Finset.univ.sum (fun i : I =>
        (((Nat.primesLE N).filter (P i)).card : Real))) / (Nat.primeCounting N : Real) :=
      div_le_div_of_nonneg_right hr (Nat.cast_nonneg _)
    _ = _ := by rw [Finset.sum_div]

theorem tendsto_prime_bounded_event_zero (B : Nat) :
    Filter.Tendsto (fun N : Nat =>
      (((Nat.primesLE N).filter (fun n => n <= B)).card : Real) /
        (Nat.primeCounting N : Real)) Filter.atTop (nhds 0) := by
  have hpi : Filter.Tendsto (fun N : Nat => (Nat.primeCounting N : Real))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp Nat.tendsto_primeCounting
  have hinv : Filter.Tendsto (fun N : Nat => Inv.inv (Nat.primeCounting N : Real))
      Filter.atTop (nhds 0) := tendsto_inv_atTop_zero.comp hpi
  have hconst : Filter.Tendsto (fun _ : Nat => ((B + 1 : Nat) : Real))
      Filter.atTop (nhds ((B + 1 : Nat) : Real)) := tendsto_const_nhds
  have hupper : Filter.Tendsto (fun N : Nat =>
      ((B + 1 : Nat) : Real) / (Nat.primeCounting N : Real))
        Filter.atTop (nhds 0) := by
    simpa only [mul_zero, div_eq_mul_inv] using hconst.mul hinv
  refine squeeze_zero' (Filter.Eventually.of_forall (fun N =>
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))) ?_ hupper
  apply Filter.Eventually.of_forall
  intro N
  have hsub : (Nat.primesLE N).filter (fun n => n <= B) <= Finset.range (B + 1) := by
    intro n hn
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hn).2)
  have hc : ((Nat.primesLE N).filter (fun n => n <= B)).card <= B + 1 := by
    simpa only [Finset.card_range] using Finset.card_le_card hsub
  have hr : (((Nat.primesLE N).filter (fun n => n <= B)).card : Real) <=
      ((B + 1 : Nat) : Real) := by exact_mod_cast hc
  exact div_le_div_of_nonneg_right hr (Nat.cast_nonneg _)

theorem tendsto_prime_event_one_of_complement_zero (P : Nat -> Prop)
    (hnot : Filter.Tendsto (fun N : Nat =>
      (((Nat.primesLE N).filter (fun n => Not (P n))).card : Real) /
        (Nat.primeCounting N : Real)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun N : Nat =>
      (((Nat.primesLE N).filter P).card : Real) / (Nat.primeCounting N : Real))
        Filter.atTop (nhds 1) := by
  have hconst : Filter.Tendsto (fun _ : Nat => (1 : Real))
      Filter.atTop (nhds 1) := tendsto_const_nhds
  have hlim := hconst.sub hnot
  simp only [sub_zero] at hlim
  choose K hK using eventually_primeCounting_lower
  refine Filter.Tendsto.congr' ?_ hlim
  apply Filter.eventually_atTop.mpr
  refine Exists.intro K ?_
  intro N hN
  have hp : (0 : Real) < Nat.primeCounting N := (hK N hN).2
  have hc : (((Nat.primesLE N).filter P).card : Real) +
      (((Nat.primesLE N).filter (fun n => Not (P n))).card : Real) =
        (Nat.primeCounting N : Real) := by
    have hh := Finset.card_filter_add_card_filter_not (s := Nat.primesLE N) P
    rw [Nat.primesLE_card_eq_primeCounting] at hh
    exact_mod_cast hh
  change 1 - (((Nat.primesLE N).filter (fun n => Not (P n))).card : Real) /
    (Nat.primeCounting N : Real) =
      (((Nat.primesLE N).filter P).card : Real) / (Nat.primeCounting N : Real)
  field_simp
  linarith only [hc]

end PrimeFactorOscillations
