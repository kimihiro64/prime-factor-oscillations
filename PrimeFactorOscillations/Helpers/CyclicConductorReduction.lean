/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import PrimeFactorOscillations.Helpers.PrimePowerSubgroupTrace

/-!
# Exact image masses and signed pushforward under conductor reduction

The Fourier consumer uses arbitrary complex weights. Uniform fibers are
retained as exact multiplicities of the original signed transform.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CyclicConductorReduction

open scoped BigOperators

theorem cyclic_intersection_card {G : Type*} [CommGroup G] [IsCyclic G]
    [Finite G] (H K : Subgroup G) :
    Nat.card (@Min.min (Subgroup G) inferInstance H K) = Nat.gcd (Nat.card H) (Nat.card K) := by
  let d := Nat.gcd (Nat.card H) (Nat.card K)
  let C : Subgroup G := (powMonoidHom d).ker
  have hdG : Dvd.dvd d (Nat.card G) :=
    dvd_trans (Nat.gcd_dvd_left _ _) H.card_subgroup_dvd_card
  have hC : Nat.card C = d := by
    rw [IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right hdG]
  have hCH : C <= H := IsCyclic.subgroup_le_iff_card_dvd.mpr
    (by rw [hC]; exact Nat.gcd_dvd_left _ _)
  have hCK : C <= K := IsCyclic.subgroup_le_iff_card_dvd.mpr
    (by rw [hC]; exact Nat.gcd_dvd_right _ _)
  apply Nat.dvd_antisymm
  { exact Nat.dvd_gcd (IsCyclic.subgroup_le_iff_card_dvd.mp inf_le_left)
      (IsCyclic.subgroup_le_iff_card_dvd.mp inf_le_right) }
  { change Dvd.dvd d (Nat.card (@Min.min (Subgroup G) inferInstance H K))
    rw [<- hC]
    exact IsCyclic.subgroup_le_iff_card_dvd.mp (le_inf hCH hCK) }

theorem cyclic_restricted_kernel_card {G Q : Type*} [CommGroup G]
    [IsCyclic G] [Finite G] [Group Q] (H : Subgroup G) (f : MonoidHom G Q) :
    Nat.card (f.ker.subgroupOf H) = Nat.gcd (Nat.card H) (Nat.card f.ker) := by
  calc
    _ = Nat.card ((@Min.min (Subgroup G) inferInstance f.ker H).subgroupOf H) := by
      rw [Subgroup.inf_subgroupOf_right]
    _ = Nat.card (@Min.min (Subgroup G) inferInstance f.ker H) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    _ = Nat.gcd (Nat.card f.ker) (Nat.card H) := cyclic_intersection_card f.ker H
    _ = Nat.gcd (Nat.card H) (Nat.card f.ker) := Nat.gcd_comm _ _

theorem cyclic_image_card {G Q : Type*} [CommGroup G] [IsCyclic G]
    [Finite G] [Group Q] (H : Subgroup G) (f : MonoidHom G Q) :
    Nat.card (H.map f) = Nat.card H / Nat.gcd (Nat.card H) (Nat.card f.ker) := by
  rw [<- Subgroup.relIndex_ker H f, Subgroup.relIndex, Subgroup.index_eq_card_div,
    cyclic_restricted_kernel_card H f]

theorem sum_comp_surjective_hom {G Q : Type*} [Group G] [Group Q]
    [Fintype G] [Fintype Q] (f : MonoidHom G Q)
    (hf : Function.Surjective f) (w : Q -> Complex) :
    Finset.univ.sum (fun x : G => w (f x)) =
      (Nat.card f.ker : Complex) * Finset.univ.sum w := by
  classical
  have hcard (y : Q) : Fintype.card {x : G // f x = y} = Nat.card f.ker := by
    rw [<- Nat.card_eq_fintype_card]
    exact Nat.card_congr (MonoidHom.fiberEquivKerOfSurjective hf y)
  calc
    _ = Finset.univ.sum (fun y : Q => Finset.univ.sum
        (fun _x : {x : G // f x = y} => w y)) :=
      (Fintype.sum_fiberwise' f w).symm
    _ = Finset.univ.sum (fun y : Q => (Nat.card f.ker : Complex) * w y) := by
      apply Finset.sum_congr rfl
      intro y _
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem cyclic_subgroup_sum_pushforward {G Q : Type*} [CommGroup G]
    [IsCyclic G] [Finite G] [Group Q] [Finite Q] (H : Subgroup G)
    (f : MonoidHom G Q) (w : Q -> Complex) :
    letI : Fintype H := Fintype.ofFinite H
    letI : Fintype (H.map f) := Fintype.ofFinite (H.map f)
    Finset.univ.sum (fun u : H => w (f u.val)) =
      (Nat.gcd (Nat.card H) (Nat.card f.ker) : Complex) *
        Finset.univ.sum (fun v : H.map f => w v.val) := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  letI : Fintype (H.map f) := Fintype.ofFinite (H.map f)
  let g : MonoidHom H (H.map f) := f.subgroupMap H
  have hk : g.ker = f.ker.subgroupOf H := by
    apply Subgroup.ext
    intro u
    change (g u = 1) <-> (f u.val = 1)
    constructor
    { intro hu
      exact congrArg Subtype.val hu }
    { intro hu
      exact Subtype.ext hu }
  have hc : Nat.card g.ker = Nat.gcd (Nat.card H) (Nat.card f.ker) := by
    rw [hk, cyclic_restricted_kernel_card H f]
  have hs := sum_comp_surjective_hom g (f.subgroupMap_surjective H)
    (fun v : H.map f => w v.val)
  rw [hc] at hs
  exact hs

end PrimeFactorOscillations.CyclicConductorReduction
