/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.Erdos690
import PrimeFactorOscillations.Helpers.ReciprocalSmoothSteps
import PrimeFactorOscillations.Helpers.TiltedAscentGrid
import PrimeFactorOscillations.Mathlib.Analysis.Calculus.IteratedDeriv.LinearProduct
import PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliBounds

/-!
# Actual density signs for the odds-tilted prime-factor laws

The probabilities t / (p - 1 + t) scale each elementary symmetric
coefficient by t to its degree. The supported mass ratio is therefore
the ordinary prime-prefix ratio divided by t. At consecutive primes
this gives the exact strict ascent and descent thresholds g + t.

Both endpoints, finite degree support, and positivity of the tilt are
explicit. These finite identities supply the real-density interpretation
of the sampled counts; they do not assert an asymptotic count bound.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open PrimeFactorUnimodality

theorem oddsTiltLaw_eta_interior (t : Real) (ht : 0 < t) (p : Nat)
    (hp : 1 < p) :
    0 < (oddsTiltLaw t ht).eta p /\ (oddsTiltLaw t ht).eta p < 1 := by
  have hpReal : (1 : Real) < p := by exact_mod_cast hp
  have hDen : 0 < (p : Real) - 1 + t := by linarith
  change 0 < t / ((p : Real) - 1 + t) /\ t / ((p : Real) - 1 + t) < 1
  refine And.intro (div_pos ht hDen) ?_
  have h := div_lt_div_of_pos_right
    (show t < (p : Real) - 1 + t by linarith) hDen
  simpa only [div_self hDen.ne'] using h

theorem oddsTilt_esymm_eq (t : Real) (ht : 0 < t) (entries : List Nat)
    (hEntries : forall p, List.Mem p entries -> 1 < p) (r : Nat) :
    ((entries.map (fun p => (oddsTiltLaw t ht).eta p /
      (1 - (oddsTiltLaw t ht).eta p)) : List Real) : Multiset Real).esymm r =
      t ^ r * (weightEsymm entries r : Real) := by
  let w : Multiset Rat := (entries.map primeWeight : List Rat)
  let f : RingHom Rat Real := Rat.castHom Real
  have hMap :
      Multiset.map (fun a : Real => t * a) (Multiset.map f w) =
      ((entries.map (fun p => (oddsTiltLaw t ht).eta p /
        (1 - (oddsTiltLaw t ht).eta p)) : List Real) : Multiset Real) := by
    change ((((entries.map primeWeight).map (fun a : Rat => (a : Real))).map
      (fun a : Real => t * a) : List Real) : Multiset Real) = _
    apply congrArg (fun s : List Real => (s : Multiset Real))
    simp only [List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro p hp
    rw [oddsTiltLaw_odds t ht p (hEntries p hp)]
    unfold primeWeight
    rw [Rat.cast_div, Rat.cast_one, Rat.cast_natCast,
      Nat.cast_sub (Nat.le_of_lt (hEntries p hp)), Nat.cast_one]
    ring
  have hScale := Multiset.pow_smul_esymm t r (Multiset.map f w)
  simp only [smul_eq_mul] at hScale
  rw [hMap] at hScale
  have hCast := RingHom.map_multiset_esymm f w r
  rw [<- hScale, <- hCast]
  rfl

theorem oddsTilt_mass_ratio_eq (t : Real) (ht : 0 < t) (entries : List Nat)
    (hEntries : forall p, List.Mem p entries -> 1 < p) (r : Nat) (hr : 1 <= r) :
    List.bernoulliMass (entries.map (oddsTiltLaw t ht).eta) (r - 1) /
      List.bernoulliMass (entries.map (oddsTiltLaw t ht).eta) r =
        (densityRatio entries r : Real) / t := by
  have hInterior : forall a, List.Mem a (entries.map (oddsTiltLaw t ht).eta) ->
      0 < a /\ a < 1 := by
    intro a ha
    choose p hp using List.mem_map.mp ha
    rw [<- hp.2]
    exact oddsTiltLaw_eta_interior t ht p (hEntries p hp.1)
  rw [List.bernoulliMass_ratio_eq_esymm _ hInterior,
    List.map_map]
  change ((entries.map (fun p => (oddsTiltLaw t ht).eta p /
      (1 - (oddsTiltLaw t ht).eta p)) : List Real) : Multiset Real).esymm (r - 1) /
    ((entries.map (fun p => (oddsTiltLaw t ht).eta p /
      (1 - (oddsTiltLaw t ht).eta p)) : List Real) : Multiset Real).esymm r = _
  rw [oddsTilt_esymm_eq t ht entries hEntries (r - 1),
    oddsTilt_esymm_eq t ht entries hEntries r,
    densityRatio_eq_weightEsymm_ratio entries hEntries r, Rat.cast_div]
  have hPow : t ^ r = t ^ (r - 1) * t := by
    rw [<- pow_succ, Nat.sub_add_cancel hr]
  rw [hPow, mul_assoc, mul_div_mul_left _ _ (pow_ne_zero (r - 1) ht.ne'), div_div]
  congr 1
  ring

theorem oddsTilt_prefixMass_eq_sorted (t : Real) (ht : 0 < t) (p r : Nat) :
    (oddsTiltLaw t ht).prefixMass p r =
      List.bernoulliMass ((primesBelow p).map (oddsTiltLaw t ht).eta) r := by
  have hPerm := (((Finset.range p).filter Nat.Prime).sort_perm_toList
    (fun a b : Nat => a <= b)).map (oddsTiltLaw t ht).eta
  exact (List.bernoulliMass_perm hPerm r).symm

theorem oddsTilt_prefixMass_ratio_eq (t : Real) (ht : 0 < t)
    (p r : Nat) (hr : 1 <= r) :
    (oddsTiltLaw t ht).prefixMass p (r - 1) /
      (oddsTiltLaw t ht).prefixMass p r =
        (densityRatio (primesBelow p) r : Real) / t := by
  rw [oddsTilt_prefixMass_eq_sorted, oddsTilt_prefixMass_eq_sorted]
  apply oddsTilt_mass_ratio_eq t ht (primesBelow p) ?_ r hr
  intro q hq
  have hqSet : Membership.mem ((Finset.range p).filter Nat.Prime) q := by
    apply (Finset.mem_sort (s := (Finset.range p).filter Nat.Prime)
      (r := fun a b : Nat => a <= b)).mp
    exact hq
  exact (Finset.mem_filter.mp hqSet).2.one_lt


theorem oddsTilt_prefixMass_pos (t : Real) (ht : 0 < t) (p r : Nat)
    (hr : r <= (primesBelow p).length) :
    0 < (oddsTiltLaw t ht).prefixMass p r := by
  rw [oddsTilt_prefixMass_eq_sorted]
  apply List.bernoulliMass_pos_of_interior
  next =>
    intro a ha
    choose q hq using List.mem_map.mp ha
    rw [<- hq.2]
    have hqSet : Membership.mem ((Finset.range p).filter Nat.Prime) q :=
      (Finset.mem_sort (s := (Finset.range p).filter Nat.Prime)
        (r := fun a b : Nat => a <= b)).mp hq.1
    exact oddsTiltLaw_eta_interior t ht q (Finset.mem_filter.mp hqSet).2.one_lt
  next => simpa only [List.length_map] using hr

theorem oddsTilt_reciprocal_gap (t : Real) (ht : 0 < t) (p q : Nat) :
    1 / (oddsTiltLaw t ht).eta q - 1 / (oddsTiltLaw t ht).eta p + 1 =
      ((q : Real) - p) / t + 1 := by
  change 1 / (t / ((q : Real) - 1 + t)) -
    1 / (t / ((p : Real) - 1 + t)) + 1 = _
  simp only [one_div_div]
  ring

theorem oddsTilt_rank_ascent_iff (t : Real) (ht : 0 < t) (p q r : Nat)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p < q)
    (hgap : forall n : Nat, p < n -> n < q -> Not (Nat.Prime n))
    (hr : 1 <= r) (hsupport : r <= (primesBelow p).length) :
    (oddsTiltLaw t ht).rankDensityAt (r + 1) p <
      (oddsTiltLaw t ht).rankDensityAt (r + 1) q <->
      (q : Real) - p + t < (densityRatio (primesBelow p) r : Real) := by
  have hindex : r + 1 - 2 = r - 1 := by omega
  rw [(oddsTiltLaw t ht).rank_density_ascent_iff (r + 1) p q (by omega)
    hp hpq hgap (oddsTiltLaw_eta_interior t ht p hp.one_lt).1
    (oddsTiltLaw_eta_interior t ht q hq.one_lt).1
    (by simpa only [Nat.add_sub_cancel] using oddsTilt_prefixMass_pos t ht p r hsupport)]
  rw [hindex, Nat.add_sub_cancel, oddsTilt_prefixMass_ratio_eq t ht p r hr,
    oddsTilt_reciprocal_gap]
  exact tilted_gap_threshold_iff _ _ _ ht

theorem oddsTilt_rank_descent_iff (t : Real) (ht : 0 < t) (p q r : Nat)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p < q)
    (hgap : forall n : Nat, p < n -> n < q -> Not (Nat.Prime n))
    (hr : 1 <= r) (hsupport : r <= (primesBelow p).length) :
    (oddsTiltLaw t ht).rankDensityAt (r + 1) q <
      (oddsTiltLaw t ht).rankDensityAt (r + 1) p <->
      (densityRatio (primesBelow p) r : Real) < (q : Real) - p + t := by
  have hindex : r + 1 - 2 = r - 1 := by omega
  rw [(oddsTiltLaw t ht).rank_density_descent_iff (r + 1) p q (by omega)
    hp hpq hgap (oddsTiltLaw_eta_interior t ht p hp.one_lt).1
    (oddsTiltLaw_eta_interior t ht q hq.one_lt).1
    (by simpa only [Nat.add_sub_cancel] using oddsTilt_prefixMass_pos t ht p r hsupport)]
  rw [hindex, Nat.add_sub_cancel, oddsTilt_prefixMass_ratio_eq t ht p r hr,
    oddsTilt_reciprocal_gap]
  have heq : ((q : Real) - p) / t + 1 = ((q : Real) - p + t) / t := by
    field_simp [ht.ne']
  rw [heq]
  exact div_lt_div_iff_of_pos_right ht

end PrimeFactorOscillations
