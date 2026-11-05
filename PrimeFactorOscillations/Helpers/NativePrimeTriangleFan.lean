/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NativePrimeEulerianGeometry
import PrimeFactorOscillations.Helpers.NativePrimeEvenCycleMasks

/-! # Triangle-with-spokes graphs have no nonempty even Eulerian mask -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

def nativePrimeTriangleFan (P : Finset Nat) (p q r : Nat) : Finset (Prod Nat Nat) :=
  insert (q, r) ((P.erase p).image (fun x => (p, x)))

theorem native_triangle_fan_mem_iff (P : Finset Nat) (p q r : Nat) (e : Prod Nat Nat) :
    Membership.mem (nativePrimeTriangleFan P p q r) e <->
      Or (e = (q, r)) (And (e.1 = p) (And (Membership.mem P e.2) (Not (e.2 = p)))) := by
  rw [nativePrimeTriangleFan, Finset.mem_insert]
  constructor
  . intro h
    rcases h with h | h
    . exact Or.inl h
    . choose x hx using Finset.mem_image.mp h
      rw [<- hx.2]
      exact Or.inr (And.intro rfl
        (And.intro (Finset.mem_erase.mp hx.1).2 (Finset.mem_erase.mp hx.1).1))
  . intro h
    rcases h with h | h
    . exact Or.inl h
    . exact Or.inr (Finset.mem_image.mpr
        (Exists.intro e.2 (And.intro
          (Finset.mem_erase.mpr (And.intro h.2.2 h.2.1)) (Prod.ext h.1.symm rfl))))

theorem native_triangle_fan_card (P : Finset Nat) (p q r : Nat)
    (hp : Membership.mem P p) (hpq : p < q) :
    (nativePrimeTriangleFan P p q r).card = P.card := by
  have hn : Not (Membership.mem ((P.erase p).image (fun x => (p, x))) (q, r)) := by
    intro h
    choose x hx using Finset.mem_image.mp h
    exact hpq.ne (congrArg Prod.fst hx.2)
  have hi : Function.Injective (fun x : Nat => (p, x)) := by
    intro x y h
    exact congrArg Prod.snd h
  rw [nativePrimeTriangleFan, Finset.card_insert_of_notMem hn,
    Finset.card_image_of_injective _ hi]
  exact Finset.card_erase_add_one hp

theorem native_triangle_fan_support (P : Finset Nat) (p q r : Nat)
    (hp : Membership.mem P p) (hq : Membership.mem P q) (hr : Membership.mem P r)
    (hmin : forall x : Nat, Membership.mem P x -> p <= x) (hqr : q < r) :
    nativePrimeTriangleFan P p q r <= nativePrimeVertexEdges P := by
  intro e he
  rcases (native_triangle_fan_mem_iff P p q r e).mp he with h | h
  . rw [h]
    exact (native_gap_edges_mem_iff P (q, r)).mpr (And.intro hq (And.intro hr hqr))
  . apply (native_gap_edges_mem_iff P e).mpr
    have hm := hmin e.2 h.2.1
    have hp1 : Membership.mem P e.1 := by
      rw [h.1]
      exact hp
    exact And.intro hp1 (And.intro h.2.1 (by rw [h.1]; omega))

theorem native_triangle_fan_leaf_degree_one (P : Finset Nat) (p q r : Nat)
    (hpq : p < q) (C : Finset (Prod Nat Nat)) (hC : C <= nativePrimeTriangleFan P p q r)
    (x : Nat) (hxp : Not (x = p)) (hxq : Not (x = q)) (hxr : Not (x = r))
    (hxC : Membership.mem C (p, x)) : nativePrimeVertexCycleDegree C x = 1 := by
  rw [native_cycle_degree_eq_sum]
  calc
    _ = C.sum (fun e => if e = (p, x) then (1 : Nat) else 0) := by
      apply Finset.sum_congr rfl
      intro e he
      rcases (native_triangle_fan_mem_iff P p q r e).mp (hC he) with h | h
      . rw [h]
        simp [Ne.symm hxq, Ne.symm hxr, hpq.ne']
      . have heq : e = (p, e.2) := Prod.ext h.1 rfl
        rw [heq]
        simp [Ne.symm hxp]
    _ = 1 := by
      rw [Finset.sum_eq_single (p, x)]
      . simp
      . intro e he hne
        simp [hne]
      . intro hn
        exact False.elim (hn hxC)

theorem native_triangle_fan_eulerian_subset_triangle (P : Finset Nat) (p q r : Nat)
    (hpq : p < q) (C : Finset (Prod Nat Nat)) (hC : C <= nativePrimeTriangleFan P p q r)
    (hdeg : forall x : Nat, Membership.mem P x -> nativePrimeVertexCycleDegree C x % 2 = 0) :
    C <= {(p, q), (q, r), (p, r)} := by
  intro e he
  rcases (native_triangle_fan_mem_iff P p q r e).mp (hC he) with h | h
  . rw [h]
    simp
  . by_cases hq : e.2 = q
    . have heq : e = (p, q) := Prod.ext h.1 hq
      rw [heq]
      simp
    . by_cases hr : e.2 = r
      . have heq : e = (p, r) := Prod.ext h.1 hr
        rw [heq]
        simp
      . have hleaf : Membership.mem C (p, e.2) := by
          have heq : e = (p, e.2) := Prod.ext h.1 rfl
          rw [<- heq]
          exact he
        have hd := native_triangle_fan_leaf_degree_one P p q r hpq C hC e.2 h.2.2 hq hr hleaf
        have hv := hdeg e.2 h.2.1
        rw [hd] at hv
        norm_num at hv

theorem native_triangle_fan_even_mask_empty (P : Finset Nat) (p q r : Nat)
    (hp : Membership.mem P p) (hq : Membership.mem P q) (hr : Membership.mem P r)
    (hmin : forall x : Nat, Membership.mem P x -> p <= x) (hpq : p < q) (hqr : q < r)
    (C : Finset (Prod Nat Nat)) (hC : C <= nativePrimeTriangleFan P p q r)
    (hdeg : forall x : Nat, Membership.mem P x -> nativePrimeVertexCycleDegree C x % 2 = 0)
    (hc : C.card % 2 = 0) : C = {} := by
  have hs := native_triangle_fan_support P p q r hp hq hr hmin hqr
  have htri := native_triangle_fan_eulerian_subset_triangle P p q r hpq C hC hdeg
  have hcard : C.card <= 3 := by
    have hle := Finset.card_le_card htri
    rw [native_phase_triangle_card p q r hpq hqr] at hle
    exact hle
  exact native_small_even_cycle_empty P C (hC.trans hs) hdeg hcard hc

theorem native_triangle_fan_even_cycle_masks (P : Finset Nat) (p q r : Nat)
    (hp : Membership.mem P p) (hq : Membership.mem P q) (hr : Membership.mem P r)
    (hmin : forall x : Nat, Membership.mem P x -> p <= x) (hpq : p < q) (hqr : q < r) :
    nativeEvenCycleMasks P (nativePrimeTriangleFan P p q r) =
      {({} : Finset (Prod Nat Nat))} := by
  ext C
  rw [native_even_cycle_masks_mem_iff, Finset.mem_singleton]
  constructor
  . intro h
    exact native_triangle_fan_even_mask_empty P p q r hp hq hr hmin hpq hqr C h.1 h.2.1 h.2.2
  . intro h
    rw [h]
    exact And.intro (Finset.empty_subset _)
      (And.intro (by simp [nativePrimeVertexCycleDegree]) (by simp))

theorem native_triangle_fan_even_cycle_count (P : Finset Nat) (p q r : Nat)
    (hp : Membership.mem P p) (hq : Membership.mem P q) (hr : Membership.mem P r)
    (hmin : forall x : Nat, Membership.mem P x -> p <= x) (hpq : p < q) (hqr : q < r) :
    nativeEvenCycleCount P (nativePrimeTriangleFan P p q r) = 1 := by
  unfold nativeEvenCycleCount
  rw [native_triangle_fan_even_cycle_masks P p q r hp hq hr hmin hpq hqr, Finset.card_singleton]

end PrimeFactorOscillations.FiniteFieldIntegerSignature
