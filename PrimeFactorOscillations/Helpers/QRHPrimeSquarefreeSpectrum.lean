/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.QRHPrimeSquareTailLimit

/-! # Signed spectral transfer to actual squarefree differences

The physical graph is defined by Squarefree of the absolute integer gap.
Only its separated tail is estimated by rows; both signed principal modes
and the complete finite residual are retained.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
open Filter
open scoped Classical
namespace PrimeFactorOscillations.QRH

private theorem separated_tail_schur {I : Type*} (S : Finset I)
    (J : I -> I -> Real) (f : I -> Real) (B : Real)
    (hJ : forall i, Membership.mem S i -> forall j, Membership.mem S j -> 0 <= J i j)
    (hSym : forall i, Membership.mem S i -> forall j, Membership.mem S j -> J i j = J j i)
    (hRow : forall i, Membership.mem S i -> S.sum (fun j => J i j) <= B) :
    abs (Finset.kernelBilinear S J f f) <=
      B * S.sum (fun i => (f i) ^ 2) := by
  have hPair (i j : I) :
      abs (f i) * abs (f j) <= ((f i) ^ 2 + (f j) ^ 2) / 2 := by
    have h := sq_nonneg (abs (f i) - abs (f j))
    rw [sub_sq, sq_abs, sq_abs] at h
    nlinarith only [h]
  have hSymSum :
      S.sum (fun i => S.sum (fun j => J i j * (f j) ^ 2)) =
      S.sum (fun i => S.sum (fun j => J i j * (f i) ^ 2)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hSym j hj i hi]
  calc
    _ <= S.sum (fun i => S.sum (fun j => abs (J i j * f i * f j))) := by
      unfold Finset.kernelBilinear
      apply le_trans (Finset.abs_sum_le_sum_abs _ _)
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.abs_sum_le_sum_abs _ _
    _ <= S.sum (fun i => S.sum (fun j =>
        J i j * (((f i) ^ 2 + (f j) ^ 2) / 2))) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, abs_mul, abs_of_nonneg (hJ i hi j hj)]
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (hPair i j) (hJ i hi j hj)
    _ = (S.sum (fun i => S.sum (fun j => J i j * (f i) ^ 2)) +
        S.sum (fun i => S.sum (fun j => J i j * (f j) ^ 2))) / 2 := by
      simp_rw [<- mul_div_assoc, mul_add, add_div, Finset.sum_add_distrib,
        <- Finset.sum_div]
    _ = S.sum (fun i => S.sum (fun j => J i j * (f i) ^ 2)) := by
      rw [hSymSum]
      ring1
    _ = S.sum (fun i => (f i) ^ 2 * S.sum (fun j => J i j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [<- Finset.sum_mul]
      ring1
    _ <= S.sum (fun i => (f i) ^ 2 * B) :=
      Finset.sum_le_sum (fun i hi =>
        mul_le_mul_of_nonneg_left (hRow i hi) (sq_nonneg (f i)))
    _ = _ := by rw [<- Finset.sum_mul]; ring1

/-- The physical graph kernel uses squarefreeness of the absolute integer gap. -/
def primeSquarefreeDifferenceKernel (p q : Nat) : Real :=
  if Squarefree ((q : Int) - (p : Int)).natAbs then 1 else 0

private theorem square_congruence_iff_gap_dvd (p q ell : Nat) :
    (p : ZMod (ell ^ 2)) = (q : ZMod (ell ^ 2)) <->
      Dvd.dvd (ell ^ 2) ((q : Int) - (p : Int)).natAbs := by
  rw [ZMod.natCast_eq_natCast_iff, Nat.modEq_iff_dvd]
  have h := (Int.natAbs_dvd_natAbs
    (a := ((ell ^ 2 : Nat) : Int)) (b := (q : Int) - (p : Int))).symm
  have hAbs : (((ell ^ 2 : Nat) : Int)).natAbs = ell ^ 2 := rfl
  rw [hAbs] at h
  have hCast : ((ell ^ 2 : Nat) : Int) = (ell : Int) ^ 2 := Nat.cast_pow ell 2
  rw [hCast] at h
  exact h

theorem primeSquarefreeDifferenceKernel_eq_prime_avoidance (p q : Nat) :
    primeSquarefreeDifferenceKernel p q =
      if forall ell : Nat, Nat.Prime ell ->
          Not ((p : ZMod (ell ^ 2)) = (q : ZMod (ell ^ 2))) then 1 else 0 := by
  have hIff : Squarefree ((q : Int) - (p : Int)).natAbs <->
      forall ell : Nat, Nat.Prime ell ->
        Not ((p : ZMod (ell ^ 2)) = (q : ZMod (ell ^ 2))) := by
    constructor
    { intro h ell hell heq
      apply (Nat.squarefree_iff_prime_squarefree.mp h) ell hell
      have hd := (square_congruence_iff_gap_dvd p q ell).mp heq
      simpa only [pow_two] using hd }
    { intro h
      apply Nat.squarefree_iff_prime_squarefree.mpr
      intro ell hell hd
      apply h ell hell
      apply (square_congruence_iff_gap_dvd p q ell).mpr
      simpa only [pow_two] using hd }
  simp only [primeSquarefreeDifferenceKernel, hIff]

private theorem full_square_kernel_symm (p q : Nat) :
    primeSquarefreeDifferenceKernel p q = primeSquarefreeDifferenceKernel q p := by
  rw [primeSquarefreeDifferenceKernel_eq_prime_avoidance,
    primeSquarefreeDifferenceKernel_eq_prime_avoidance]
  have hIff :
      (forall ell : Nat, Nat.Prime ell ->
        Not ((p : ZMod (ell ^ 2)) = (q : ZMod (ell ^ 2)))) <->
      (forall ell : Nat, Nat.Prime ell ->
        Not ((q : ZMod (ell ^ 2)) = (p : ZMod (ell ^ 2)))) := by
    constructor
    { intro h ell hell heq
      exact h ell hell heq.symm }
    { intro h ell hell heq
      exact h ell hell heq.symm }
  rw [hIff]

private theorem cutoff_square_kernel_symm (S : Finset Nat) (p q : Nat) :
    primeSquareCutoffKernel S p q = primeSquareCutoffKernel S q p := by
  have hIff : (forall ell : S,
      Not ((p : ZMod (ell.val ^ 2)) = (q : ZMod (ell.val ^ 2)))) <->
      (forall ell : S,
      Not ((q : ZMod (ell.val ^ 2)) = (p : ZMod (ell.val ^ 2)))) := by
    constructor
    { intro h ell heq
      exact h ell heq.symm }
    { intro h ell heq
      exact h ell heq.symm }
  simp only [primeSquareCutoffKernel, hIff, eq_comm]

private theorem square_tail_entry_bound (R p q : Nat) :
    0 <= primeSquareCutoffKernel (oddPrimeVertices R) p q -
      primeSquarefreeDifferenceKernel p q /\
    primeSquareCutoffKernel (oddPrimeVertices R) p q -
      primeSquarefreeDifferenceKernel p q <=
      if Not (q = p) /\ exists ell : Nat, Nat.Prime ell /\ R < ell /\
          (q : ZMod (ell ^ 2)) = (p : ZMod (ell ^ 2)) then 1 else 0 := by
  classical
  rw [primeSquarefreeDifferenceKernel_eq_prime_avoidance]
  by_cases hAll : forall ell : Nat, Nat.Prime ell ->
      Not ((p : ZMod (ell ^ 2)) = (q : ZMod (ell ^ 2)))
  { have h4 : Not ((p : ZMod 4) = (q : ZMod 4)) := by
      simpa using hAll 2 Nat.prime_two
    have hSmall : forall ell : oddPrimeVertices R,
        Not ((p : ZMod (ell.val ^ 2)) = (q : ZMod (ell.val ^ 2))) := by
      intro ell
      have hp := (Nat.mem_primesBelow.mp (Finset.mem_erase.mp ell.property).2).2
      exact hAll ell.val hp
    simp only [ite_eq_left hAll, primeSquareCutoffKernel, ite_eq_right h4, ite_eq_left hSmall,
      sub_self, le_refl, true_and]
    split_ifs <;> norm_num }
  { rw [ite_eq_right hAll]
    by_cases h4 : (p : ZMod 4) = (q : ZMod 4)
    { simp only [primeSquareCutoffKernel, ite_eq_left h4, sub_zero]
      split_ifs <;> norm_num }
    by_cases hSmall : forall ell : oddPrimeVertices R,
        Not ((p : ZMod (ell.val ^ 2)) = (q : ZMod (ell.val ^ 2)))
    { have hExists : exists ell : Nat, Nat.Prime ell /\
          (p : ZMod (ell ^ 2)) = (q : ZMod (ell ^ 2)) := by
        by_contra hn
        apply hAll
        intro ell hell heq
        exact hn (Exists.intro ell (And.intro hell heq))
      choose ell hell heq using hExists
      have hLarge : R < ell := by
        by_contra hn
        have h2 : Not (ell = 2) := by
          intro he
          subst ell
          exact h4 (by simpa using heq)
        have hMem : Membership.mem (oddPrimeVertices R) ell := by
          apply Finset.mem_erase.mpr
          exact And.intro h2
            (Nat.mem_primesBelow.mpr (And.intro (by omega) hell))
        exact hSmall (Subtype.mk ell hMem) heq
      have hne : Not (q = p) := by
        intro he
        subst q
        exact h4 rfl
      have hTail : Not (q = p) /\ exists ell : Nat, Nat.Prime ell /\ R < ell /\
          (q : ZMod (ell ^ 2)) = (p : ZMod (ell ^ 2)) :=
        And.intro hne (Exists.intro ell (And.intro hell (And.intro hLarge heq.symm)))
      simp only [primeSquareCutoffKernel, ite_eq_right h4, ite_eq_left hSmall, sub_zero,
        ite_eq_left hTail]
      norm_num }
    { simp only [primeSquareCutoffKernel, ite_eq_right h4, ite_eq_right hSmall, sub_zero]
      split_ifs <;> norm_num } }

private theorem square_tail_row_le (R X p : Nat) :
    (oddPrimeVertices X).sum (fun q =>
      primeSquareCutoffKernel (oddPrimeVertices R) p q -
        primeSquarefreeDifferenceKernel p q) <= (primeSquareTailCount p X R : Real) := by
  classical
  let P : Nat -> Prop := fun q => Not (q = p) /\ exists ell : Nat,
    Nat.Prime ell /\ R < ell /\
      (q : ZMod (ell ^ 2)) = (p : ZMod (ell ^ 2))
  calc
    _ <= (oddPrimeVertices X).sum (fun q => if P q then (1 : Real) else 0) :=
      Finset.sum_le_sum (fun q _ => (square_tail_entry_bound R p q).2)
    _ = (((oddPrimeVertices X).filter P).card : Real) := by
      rw [<- Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ <= (primeSquareTailCount p X R : Real) := by
      have hSub : forall q : Nat,
          Membership.mem ((oddPrimeVertices X).filter P) q ->
          Membership.mem ((Nat.primesBelow (X + 1)).filter P) q := by
        intro q hq
        have hh := Finset.mem_filter.mp hq
        exact Finset.mem_filter.mpr (And.intro (Finset.mem_erase.mp hh.1).2 hh.2)
      have hCount := Finset.card_le_card hSub
      exact_mod_cast hCount

/-- Only the separated tail is estimated by a row bound; the signed finite kernel remains intact. -/
theorem eventually_prime_squarefree_tail_operator_le (R : Nat) (hR : 2 <= R)
    {eps : Real} (heps : 0 < eps) :
    Filter.Eventually (fun X : Nat => forall f : Nat -> Real,
      let n := ((oddPrimeVertices X).card : Real)
      abs (Finset.kernelBilinear (oddPrimeVertices X)
          primeSquarefreeDifferenceKernel f f / n ^ 2 -
        Finset.kernelBilinear (oddPrimeVertices X)
          (primeSquareCutoffKernel (oddPrimeVertices R)) f f / n ^ 2) <=
      (1 / (R : Real) + eps) *
        ((oddPrimeVertices X).sum (fun p => (f p) ^ 2) / n)) atTop := by
  classical
  have hTail := eventually_prime_square_tail_count_le R hR heps
  filter_upwards [eventually_ge_atTop (3 : Nat), hTail] with X hX hCount
  intro f
  let S := oddPrimeVertices X
  let n : Real := (S.card : Real)
  let B : Real := 1 / (R : Real) + eps
  let J : Nat -> Nat -> Real := fun p q =>
    primeSquareCutoffKernel (oddPrimeVertices R) p q -
      primeSquarefreeDifferenceKernel p q
  have hn : 0 < n := by
    apply Nat.cast_pos.mpr
    apply Finset.card_pos.mpr
    refine Exists.intro 3 ?_
    change Membership.mem ((Nat.primesBelow (X + 1)).erase 2) 3
    exact Finset.mem_erase.mpr (And.intro (by decide)
      (Nat.mem_primesBelow.mpr (And.intro (by omega) Nat.prime_three)))
  have hJ : forall p, Membership.mem S p -> forall q, Membership.mem S q ->
      0 <= J p q := fun p _ q _ => (square_tail_entry_bound R p q).1
  have hSym : forall p, Membership.mem S p -> forall q, Membership.mem S q ->
      J p q = J q p := by
    intro p hp q hq
    dsimp only [J]
    rw [cutoff_square_kernel_symm _ p q, full_square_kernel_symm p q]
  have hRow : forall p, Membership.mem S p -> S.sum (fun q => J p q) <= B * n := by
    intro p hp
    have hpFull := Nat.mem_primesBelow.mp (Finset.mem_erase.mp hp).2
    have h := mul_le_mul_of_nonneg_right (hCount p hpFull.2 (by omega)) hn.le
    change (primeSquareTailCount p X R : Real) / n * n <= B * n at h
    have hCancel : (primeSquareTailCount p X R : Real) / n * n =
        (primeSquareTailCount p X R : Real) := by field_simp [hn.ne']
    rw [hCancel] at h
    exact (square_tail_row_le R X p).trans h
  have hSchur := separated_tail_schur S J f (B * n) hJ hSym hRow
  have hDiff :
      Finset.kernelBilinear S (primeSquareCutoffKernel (oddPrimeVertices R)) f f -
        Finset.kernelBilinear S primeSquarefreeDifferenceKernel f f =
      Finset.kernelBilinear S J f f := by
    unfold Finset.kernelBilinear
    dsimp only [J]
    simp_rw [sub_mul, Finset.sum_sub_distrib]
  change abs (Finset.kernelBilinear S primeSquarefreeDifferenceKernel f f / n ^ 2 -
      Finset.kernelBilinear S (primeSquareCutoffKernel (oddPrimeVertices R)) f f /
        n ^ 2) <= B * (S.sum (fun p => (f p) ^ 2) / n)
  rw [abs_sub_comm, <- sub_div, hDiff, abs_div, abs_of_nonneg (sq_nonneg n)]
  calc
    _ <= (B * n * S.sum (fun p => (f p) ^ 2)) / n ^ 2 :=
      div_le_div_of_nonneg_right hSchur (sq_nonneg n)
    _ = _ := by field_simp [hn.ne']

/-- The full squarefree-gap graph inherits the signed finite gap, with an explicit 1/R tail. -/
theorem eventually_prime_squarefree_spectral_gap_at_cutoff
    (R : Nat) (hR : 2 <= R) {eps : Real} (heps : 0 < eps) :
    Filter.Eventually (fun X : Nat => forall f : Nat -> Real,
      let D := Nat.primeSquareUnitDensity (fun p : oddPrimeVertices R => p.val)
      let n := ((oddPrimeVertices X).card : Real)
      let a := (oddPrimeVertices X).sum f / n
      let b := (oddPrimeVertices X).sum (fun p => primeResidueSign p * f p) / n
      let e := (oddPrimeVertices X).sum (fun p => (f p) ^ 2) / n
      abs (Finset.kernelBilinear (oddPrimeVertices X)
        primeSquarefreeDifferenceKernel f f / n ^ 2 - D * (a ^ 2 - b ^ 2)) <=
        D / 5 * (e - a ^ 2 - b ^ 2) + (1 / (R : Real) + eps) * e) atTop := by
  classical
  let S := oddPrimeVertices R
  have hS : forall p, Membership.mem S p -> Nat.Prime p := by
    intro p hp
    exact (Nat.mem_primesBelow.mp (Finset.mem_erase.mp hp).2).2
  have h3 : forall p, Membership.mem S p -> 3 <= p := by
    intro p hp
    have hne := (Finset.mem_erase.mp hp).1
    have htwo := (hS p hp).two_le
    omega
  have hHalf : (0 : Real) < eps / 2 := by linarith
  have hFinite := eventually_prime_square_spectral_gap S hS h3 (eps := eps / 2) hHalf
  have hTail := eventually_prime_squarefree_tail_operator_le R hR (eps := eps / 2) hHalf
  filter_upwards [hFinite, hTail] with X hF hT
  intro f
  let D := Nat.primeSquareUnitDensity (fun p : S => p.val)
  let n := ((oddPrimeVertices X).card : Real)
  let a := (oddPrimeVertices X).sum f / n
  let b := (oddPrimeVertices X).sum (fun p => primeResidueSign p * f p) / n
  let e := (oddPrimeVertices X).sum (fun p => (f p) ^ 2) / n
  let qf := Finset.kernelBilinear (oddPrimeVertices X)
    primeSquarefreeDifferenceKernel f f / n ^ 2
  let qc := Finset.kernelBilinear (oddPrimeVertices X)
    (primeSquareCutoffKernel S) f f / n ^ 2
  have hf := hF f
  have ht := hT f
  change abs (qc - D * (a ^ 2 - b ^ 2)) <=
    D / 5 * (e - a ^ 2 - b ^ 2) + (eps / 2) * e at hf
  change abs (qf - qc) <= (1 / (R : Real) + eps / 2) * e at ht
  change abs (qf - D * (a ^ 2 - b ^ 2)) <=
    D / 5 * (e - a ^ 2 - b ^ 2) + (1 / (R : Real) + eps) * e
  have hTriangle : abs (qf - D * (a ^ 2 - b ^ 2)) <=
      abs (qf - qc) + abs (qc - D * (a ^ 2 - b ^ 2)) := by
    calc
      _ = abs ((qf - qc) + (qc - D * (a ^ 2 - b ^ 2))) := by congr 1; ring1
      _ <= _ := abs_add_le _ _
  linarith only [hTriangle, hf, ht]

end PrimeFactorOscillations.QRH
