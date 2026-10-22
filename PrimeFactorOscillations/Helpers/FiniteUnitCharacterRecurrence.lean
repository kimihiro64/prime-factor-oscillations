/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Relatively dense simultaneous returns of finite unitary characters

The finite phases may have arbitrary real frequencies. No common period,
rational independence assumption or finite numerical test is used.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem finite_unit_character_recurrence (m : Nat)
    (q : Fin m -> Real -> Complex)
    (hunit : forall j t, norm (q j t) = 1)
    (hadd : forall j s t, q j (s + t) = q j s * q j t)
    (e : Real) (he : 0 < e) :
    exists L : Real, And (0 < L) (forall b : Real,
      exists t : Real, And (b <= t) (And (t <= b + L)
        (forall j, norm (q j t - 1) < e))) := by
  classical
  let v : Real -> (Fin m -> Complex) := fun t j => q j t
  have hcontained : Set.range v <= Metric.closedBall (0 : Fin m -> Complex) 1 := by
    intro y hy
    choose t ht using hy
    rw [<- ht, Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : Real) <= 1)).mpr
    intro j
    exact le_of_eq (hunit j t)
  have hcompact : IsCompact (Metric.closedBall (0 : Fin m -> Complex) 1) :=
    isCompact_closedBall _ _
  have htb := TotallyBounded.subset hcontained hcompact.totallyBounded
  have hU : Membership.mem (uniformity (Fin m -> Complex))
      {p : Prod (Fin m -> Complex) (Fin m -> Complex) | dist p.1 p.2 < e} := by
    apply Metric.uniformity_basis_dist.mem_iff.mpr
    exact Exists.intro e (And.intro he (fun _ hp => hp))
  choose T hT using htb.exists_subset hU
  letI : Fintype T := hT.2.1.fintype
  have hpre : forall y : T, exists s : Real, v s = y.val := by
    intro y
    exact hT.1 y.property
  choose a ha using hpre
  let S : Finset Real := Finset.univ.image a
  have hget (t : Real) : exists s : Real, And (Membership.mem S s)
      (dist (v t) (v s) < e) := by
    have hmem := hT.2.2 (Set.mem_range_self t)
    choose y hy using Set.mem_iUnion.mp hmem
    choose hyT hdist using Set.mem_iUnion.mp hy
    let z : T := Subtype.mk y hyT
    refine Exists.intro (a z) (And.intro
      (Finset.mem_image.mpr (Exists.intro z (And.intro (Finset.mem_univ z) rfl))) ?_)
    rw [ha z]
    exact hdist
  have hS : S.Nonempty := by
    choose s hs using hget 0
    exact Exists.intro s hs.1
  let c := S.max' hS
  let d := S.min' hS
  let L : Real := max 1 (c - d)
  refine Exists.intro L (And.intro (lt_of_lt_of_le (by norm_num : (0 : Real) < 1)
    (le_max_left _ _)) ?_)
  intro b
  choose s hs using hget (b + c)
  let t := b + c - s
  have hsc : s <= c := Finset.le_max' S s hs.1
  have hds : d <= s := Finset.min'_le S s hs.1
  have hL : c - d <= L := le_max_right _ _
  refine Exists.intro t (And.intro (by dsimp [t]; linarith only [hsc])
    (And.intro (by dsimp [t]; linarith only [hds, hL]) ?_))
  intro j
  have hnear : norm (q j (b + c) - q j s) < e := by
    have hn := norm_le_pi_norm (v (b + c) - v s) j
    have hh : norm (v (b + c) - v s) < e := by
      simpa only [dist_eq_norm] using hs.2
    exact lt_of_le_of_lt hn hh
  have hqs : q j (b + c) = q j t * q j s := by
    rw [<- hadd]
    congr 1
    dsimp [t]
    ring
  have hid : (q j t - 1) * q j s = q j (b + c) - q j s := by
    rw [hqs]
    ring
  calc
    norm (q j t - 1) = norm ((q j t - 1) * q j s) := by
      rw [norm_mul, hunit, mul_one]
    _ = norm (q j (b + c) - q j s) := congrArg norm hid
    _ < e := hnear

end PrimeFactorOscillations.PrimeClassDeletion
