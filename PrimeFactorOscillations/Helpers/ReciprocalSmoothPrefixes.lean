import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Count
import PrimeFactorOscillations.Helpers.ReciprocalSmoothMertens
import PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliAsymptotics
import PrimeFactorOscillations.Mathlib.RingTheory.MvPolynomial.Symmetric.LargestWeightHarmonic

/-! # Uniform moments and growing-rank ratios for actual prime prefixes -/

set_option autoImplicit false
set_option Elab.async false

open Filter

namespace PrimeFactorOscillations.ReciprocalSmoothLaw

/-- One fixed bound controls the exact number of forced coordinates in every
prime prefix. The cutoff and rank are otherwise unrestricted. -/
theorem prime_prefix_forced_count_bounded (law : ReciprocalSmoothLaw) :
    exists F : Nat, forall x : Nat,
      ((((Finset.range x).filter Nat.Prime).toList.map law.eta).count 1) <= F := by
  choose P hP using law.exceptional_primes_bounded
  refine Exists.intro P ?_
  intro x
  let xs := ((Finset.range x).filter Nat.Prime).toList
  let ys := xs.filter (fun p => law.eta p == 1)
  have hcount : (xs.map law.eta).count 1 = ys.length := by
    rw [List.count_eq_length_filter, List.filter_map, List.length_map]
    rfl
  have hnodup : ys.Nodup :=
    List.Nodup.filter (fun p => law.eta p == 1) (Finset.nodup_toList _)
  have hsubset : forall p, Membership.mem ys.toFinset p ->
      Membership.mem (Finset.range P) p := by
    intro p hp
    have hmem := List.mem_filter.mp (List.mem_toFinset.mp hp)
    have hprime := Finset.mem_toList.mp hmem.1
    change Membership.mem ((Finset.range x).filter Nat.Prime) p at hprime
    have heq : law.eta p = 1 := by simpa using hmem.2
    exact Finset.mem_range.mpr (hP p (Finset.mem_filter.mp hprime).2 (Or.inr heq))
  change (xs.map law.eta).count 1 <= P
  rw [hcount, <- List.toFinset_card_of_nodup hnodup]
  simpa only [Finset.card_range] using Finset.card_le_card hsubset

/-- Every probability in the actual finite prime prefix is admissible. -/
theorem prime_prefix_probability_bounds (law : ReciprocalSmoothLaw) (x : Nat) :
    forall a, List.Mem a (((Finset.range x).filter Nat.Prime).toList.map law.eta) ->
      0 <= a /\ a <= 1 := by
  intro a ha
  have h := Classical.choose_spec (List.mem_map.mp ha)
  rw [<- h.2]
  exact law.probability _ (Finset.mem_filter.mp (Finset.mem_toList.mp h.1)).2

/-- Erasing deterministic coordinates preserves the exact totalized odds sum. -/
theorem prime_prefix_interior_odds_sum_eq (law : ReciprocalSmoothLaw) (x : Nat) :
    ((List.bernoulliInterior
      (((Finset.range x).filter Nat.Prime).toList.map law.eta)).map
        (fun a => a / (1 - a))).sum =
      ((Finset.range x).filter Nat.Prime).sum (fun p => law.eta p / (1 - law.eta p)) := by
  have h := List.sum_map_bernoulliInterior
    (((Finset.range x).filter Nat.Prime).toList.map law.eta)
    (law.prime_prefix_probability_bounds x)
    (fun a : Real => a / (1 - a)) (by simp) (by simp)
  simpa [List.map_map] using h

/-- The actual interior probability list satisfies the required Mertens bound,
with one fixed constant and the exact n+1 cutoff. -/
theorem prime_prefix_interior_mertens_bound (law : ReciprocalSmoothLaw) :
    exists A : Real, 0 < A /\ forall n : Nat, 2 <= n ->
      abs (((List.bernoulliInterior
        (((Finset.range (n + 1)).filter Nat.Prime).toList.map law.eta)).map
          (fun a => a / (1 - a))).sum -
        law.nu * Real.log (Real.log n)) <= A := by
  choose A hA hM using law.odds_sum_mertens_bound
  refine Exists.intro A (And.intro hA ?_)
  intro n hn
  rw [law.prime_prefix_interior_odds_sum_eq (n + 1)]
  exact hM n hn

/-- The largest retained odds obey a logarithmic bound uniformly in every
prime prefix. Labels are distinct primes; probability values may coincide. -/
theorem prime_prefix_largest_weights_log_bound (law : ReciprocalSmoothLaw) :
    exists C : Real, 0 < C /\ forall x r : Nat, 1 <= r ->
      List.largestWeightSum
        ((List.bernoulliInterior
          (((Finset.range x).filter Nat.Prime).toList.map law.eta)).map
            (fun a => a / (1 - a))) r <= C * (2 + Real.log r) := by
  choose C hC hmajor using law.odds_global_majorant
  refine Exists.intro C (And.intro hC ?_)
  intro x r hr
  let E := (Finset.range x).filter Nat.Prime
  let s := E.toList.map law.eta
  let f := fun a : Real => max (a / (1 - a) - C / r) 0
  have hs : forall a, List.Mem a s -> 0 <= a /\ a <= 1 :=
    law.prime_prefix_probability_bounds x
  have hrR : 0 < (r : Real) := by exact_mod_cast (show 0 < r by omega)
  have ht : 0 <= C / (r : Real) := div_nonneg hC.le hrR.le
  have hzero : max (-(C / (r : Real))) 0 = 0 := max_eq_right (neg_nonpos.mpr ht)
  have hf0 : f 0 = 0 := by simpa [f] using hzero
  have hf1 : f 1 = 0 := by simpa [f] using hzero
  have hsum :
      (((List.bernoulliInterior s).map (fun a => a / (1 - a))).map
        (fun a => max (a - C / r) 0)).sum =
      E.sum (fun p => max (law.eta p / (1 - law.eta p) - C / r) 0) := by
    calc
      _ = ((List.bernoulliInterior s).map f).sum := by
        simp only [List.map_map, Function.comp_def, f]
      _ = (s.map f).sum := List.sum_map_bernoulliInterior s hs f hf0 hf1
      _ = _ := by simp [s, f]
  have hpos : forall p, Membership.mem E p -> 0 < p := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2.pos
  have hweight : forall p, Membership.mem E p ->
      law.eta p / (1 - law.eta p) <= C / p := by
    intro p hp
    have hprime := (Finset.mem_filter.mp hp).2
    by_cases hone : law.eta p = 1
    next =>
      rw [hone]
      simpa using div_nonneg hC.le (Nat.cast_nonneg p : (0 : Real) <= p)
    next =>
      have hlt : law.eta p < 1 := by
        by_contra hn
        exact hone (le_antisymm (law.probability p hprime).2 (le_of_not_gt hn))
      exact (hmajor p hprime hlt).2
  have he := Finset.sum_positive_excess_le_harmonic E
    (fun p => law.eta p / (1 - law.eta p)) C hC.le hpos hweight r hr
  have hcap := List.largestWeightSum_le_threshold_excess
    ((List.bernoulliInterior s).map (fun a => a / (1 - a))) r (C / r) ht
  have hcancel : (r : Real) * (C / r) = C := by field_simp
  rw [hsum, hcancel] at hcap
  have hh := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log r) hC.le
  change List.largestWeightSum
    ((List.bernoulliInterior s).map (fun a => a / (1 - a))) r <= C * (2 + Real.log r)
  nlinarith only [hcap, he, hh]


/-- Uniform growing-rank normalization, derived entirely from the original
reciprocal-smooth law. All finite forced and excluded coordinates are included.
The prime cutoff n may grow arbitrarily quickly relative to the rank k. -/
theorem prime_prefix_uniform_normalized_ratio
    (law : ReciprocalSmoothLaw) (u : Real) (hu : 0 < u)
    (epsilon : Real) (he : 0 < epsilon) :
    Filter.Eventually (fun k : Nat => forall n : Nat, 2 <= n ->
      u * k <= Real.log (Real.log n) ->
      0 < List.bernoulliMass
        (((Finset.range (n + 1)).filter Nat.Prime).toList.map law.eta) (k - 1) /\
      abs (law.nu * Real.log (Real.log n) *
        (List.bernoulliMass
            (((Finset.range (n + 1)).filter Nat.Prime).toList.map law.eta) (k - 2) /
          List.bernoulliMass
            (((Finset.range (n + 1)).filter Nat.Prime).toList.map law.eta) (k - 1)) /
        (k : Real) - 1) <= epsilon) Filter.atTop := by
  choose F hF using law.prime_prefix_forced_count_bounded
  choose A hA hsum using law.prime_prefix_interior_mertens_bound
  choose C hC hlarge using law.prime_prefix_largest_weights_log_bound
  have hratio := List.bernoulliMass_uniform_normalized_ratio law.nu u A C F
    law.nu_pos hu hC.le epsilon he
  filter_upwards [hratio, Filter.eventually_ge_atTop (F + 3)] with k hk hkg
  intro n hn hscale
  let s := (((Finset.range (n + 1)).filter Nat.Prime).toList.map law.eta)
  have hf : s.count 1 <= F := hF (n + 1)
  let j := k - 1 - s.count 1 - 1
  have hj : 1 <= j := by dsimp [j]; omega
  have hjk : j <= k := by dsimp [j]; omega
  have hjpos : (0 : Real) < j := by exact_mod_cast (show 0 < j by omega)
  have hlog : Real.log (j : Real) <= Real.log (k : Real) :=
    Real.log_le_log hjpos (by exact_mod_cast hjk)
  have hdeleted : List.largestWeightSum
      ((List.bernoulliInterior s).map (fun a => a / (1 - a))) j <=
      C * (2 + Real.log k) := by
    calc
      _ <= C * (2 + Real.log j) := hlarge (n + 1) j hj
      _ <= _ := mul_le_mul_of_nonneg_left (by linarith only [hlog]) hC.le
  exact hk s (law.prime_prefix_probability_bounds (n + 1)) hf
    (Real.log (Real.log n)) hscale (hsum n hn) hdeleted


end PrimeFactorOscillations.ReciprocalSmoothLaw
