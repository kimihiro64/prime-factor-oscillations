import PrimeFactorOscillations.Helpers.LocalSymmetricDensity
import PrimeFactorOscillations.Mathlib.RingTheory.MvPolynomial.Symmetric.RationalBounds

set_option autoImplicit false

/-! # Exact local-density ratio and its uniform finite bounds -/

namespace PrimeFactorOscillations

/-- The complementary product is positive when every local probability is below one. -/
theorem local_complement_prod_pos (eta : Nat -> Rat) (entries : List Nat)
    (hbelow : forall p, List.Mem p entries -> eta p < 1) :
    0 < (entries.map (fun p => 1 - eta p)).prod := by
  induction entries with
  | nil => simp
  | cons p entries ih =>
      simp only [List.map_cons, List.prod_cons]
      exact mul_pos (sub_pos.mpr (hbelow p (List.Mem.head _)))
        (ih (fun q hq => hbelow q (List.Mem.tail _ hq)))

/-- The common complementary product cancels exactly, in every degree. -/
theorem local_densityRatio_eq_esymm_ratio (eta : Nat -> Rat) (entries : List Nat)
    (hbelow : forall p, List.Mem p entries -> eta p < 1) (r : Nat) :
    finiteLocalMass eta entries (r - 1) / finiteLocalMass eta entries r =
      ((entries.map (fun p => eta p / (1 - eta p)) : List Rat) : Multiset Rat).esymm
          (r - 1) /
        ((entries.map (fun p => eta p / (1 - eta p)) : List Rat) : Multiset Rat).esymm r := by
  have hne : forall p, List.Mem p entries -> Not (eta p = 1) :=
    fun p hp => ne_of_lt (hbelow p hp)
  rw [finiteLocalMass_eq_base_mul_esymm eta entries hne (r - 1),
    finiteLocalMass_eq_base_mul_esymm eta entries hne r]
  exact mul_div_mul_left _ _ (ne_of_gt (local_complement_prod_pos eta entries hbelow))

/-- Every supported mass is positive when all local probabilities are in `(0,1)`. -/
theorem local_mass_pos (eta : Nat -> Rat) (entries : List Nat)
    (hprob : forall p, List.Mem p entries -> 0 < eta p /\ eta p < 1)
    (r : Nat) (hr : r <= entries.length) : 0 < finiteLocalMass eta entries r := by
  rw [finiteLocalMass_eq_base_mul_esymm eta entries
    (fun p hp => ne_of_lt (hprob p hp).2) r]
  apply mul_pos (local_complement_prod_pos eta entries (fun p hp => (hprob p hp).2))
  apply Multiset.esymm_pos_rat
  next =>
    intro a ha
    choose p hp using List.mem_map.mp ha
    rw [<- hp.2]
    exact div_pos (hprob p hp.1).1 (sub_pos.mpr (hprob p hp.1).2)
  next => simpa using hr

/-- Both ratio estimates on their complete positive-denominator domain. -/
theorem local_densityRatio_bounds (eta : Nat -> Rat) (entries : List Nat)
    (hprob : forall p, List.Mem p entries -> 0 < eta p /\ eta p < 1)
    (r : Nat) (hrPos : 1 <= r) (hr : r <= entries.length)
    (hdescending : (entries.map (fun p => eta p / (1 - eta p))).Pairwise
      (fun a b => b <= a))
    (hComplement : 0 < (entries.map (fun p => eta p / (1 - eta p))).sum -
      ((entries.map (fun p => eta p / (1 - eta p))).take (r - 1)).sum) :
    (r : Rat) / (entries.map (fun p => eta p / (1 - eta p))).sum <=
        finiteLocalMass eta entries (r - 1) / finiteLocalMass eta entries r /\
      finiteLocalMass eta entries (r - 1) / finiteLocalMass eta entries r <=
        (r : Rat) / ((entries.map (fun p => eta p / (1 - eta p))).sum -
          ((entries.map (fun p => eta p / (1 - eta p))).take (r - 1)).sum) := by
  let w : List Rat := entries.map (fun p => eta p / (1 - eta p))
  change 0 < w.sum - (w.take (r - 1)).sum at hComplement
  have hw : forall a, List.Mem a w -> 0 < a := by
    intro a ha
    choose p hp using List.mem_map.mp ha
    rw [<- hp.2]
    exact div_pos (hprob p hp.1).1 (sub_pos.mpr (hprob p hp.1).2)
  have hwm : forall a, Membership.mem (w : Multiset Rat) a -> 0 < a :=
    fun a ha => hw a ha
  have hE : 0 < (w : Multiset Rat).esymm r :=
    Multiset.esymm_pos_rat _ hwm r (by simpa [w] using hr)
  have hS : 0 < w.sum := by
    change 0 < (w : Multiset Rat).sum
    rw [<- Multiset.esymm_one_rat]
    exact Multiset.esymm_pos_rat _ hwm 1 (by simpa [w] using hrPos.trans hr)
  rw [local_densityRatio_eq_esymm_ratio eta entries (fun p hp => (hprob p hp).2) r]
  change (r : Rat) / w.sum <= (w : Multiset Rat).esymm (r - 1) /
      (w : Multiset Rat).esymm r /\
    (w : Multiset Rat).esymm (r - 1) / (w : Multiset Rat).esymm r <=
      (r : Rat) / (w.sum - (w.take (r - 1)).sum)
  constructor
  next =>
    have h := Multiset.degree_mul_esymm_le_sum_mul (w : Multiset Rat)
      (fun a ha => le_of_lt (hwm a ha)) r
    change (r : Rat) * (w : Multiset Rat).esymm r <=
      w.sum * (w : Multiset Rat).esymm (r - 1) at h
    have hdiv := div_le_div_of_nonneg_right h (le_of_lt (mul_pos hS hE))
    simpa only [mul_div_mul_right _ _ (ne_of_gt hE),
      mul_div_mul_left _ _ (ne_of_gt hS)] using hdiv
  next =>
    have h := List.sum_sub_take_sum_mul_esymm_le_rat w
      (fun a ha => le_of_lt (hw a ha)) hdescending r hrPos
    have hdiv := div_le_div_of_nonneg_right h (le_of_lt (mul_pos hComplement hE))
    simpa only [mul_div_mul_left _ _ (ne_of_gt hComplement),
      mul_div_mul_right _ _ (ne_of_gt hE)] using hdiv

end PrimeFactorOscillations
