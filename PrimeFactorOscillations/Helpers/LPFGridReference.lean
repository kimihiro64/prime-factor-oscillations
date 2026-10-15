/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFRationalGrid

/-!
# Exact rational-grid reference energy

Reduced rational centers and bounded signed offsets have disjoint support.
The common finite interval profile and the exact Mobius/totient weights
retain normalized reference energy at physical input scale M. The large
auxiliary grid N does not supply a saving or replace the small denominator
q in a prime-prefix estimate. The minor-arc and tail estimates remain open.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

namespace PrimeFactorOscillations.LPF

noncomputable def lpfGridReference {I : Type*} {N : Nat}
    (D : Finset I) (point : I -> ZMod N) (w : I -> Complex) (x : ZMod N) : Complex :=
  Finset.sum D (fun i => if point i = x then w i else 0)

theorem lpfGridReference_at {I : Type*} {N : Nat} (D : Finset I)
    (point : I -> ZMod N) (w : I -> Complex) (hinj : Set.InjOn point (D : Set I))
    (i : I) (hi : Membership.mem D i) : lpfGridReference D point w (point i) = w i := by
  unfold lpfGridReference
  rw [Finset.sum_eq_single i]
  next => simp
  next =>
    intro j hj hNe
    have hOther : Not (point j = point i) := fun h => hNe (hinj hj hi h)
    simp [hOther]
  next => intro hNot; exact False.elim (hNot hi)

theorem lpfGridReference_zero {I : Type*} {N : Nat} (D : Finset I)
    (point : I -> ZMod N) (w : I -> Complex) (x : ZMod N)
    (hx : Not (Membership.mem (D.image point) x)) : lpfGridReference D point w x = 0 := by
  unfold lpfGridReference
  apply Finset.sum_eq_zero
  intro i hi
  have hOther : Not (point i = x) := fun h => hx (Finset.mem_image.mpr (Exists.intro i (And.intro hi h)))
  simp [hOther]

theorem lpfGridReference_energy {I : Type*} {N : Nat} [NeZero N]
    (D : Finset I) (point : I -> ZMod N) (w : I -> Complex)
    (hinj : Set.InjOn point (D : Set I)) :
    Finset.sum Finset.univ (fun x : ZMod N => Complex.normSq (lpfGridReference D point w x)) =
      Finset.sum D (fun i => Complex.normSq (w i)) := by
  calc
    _ = Finset.sum (D.image point) (fun x => Complex.normSq (lpfGridReference D point w x)) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ (D.image point))
      intro x _ hx
      rw [lpfGridReference_zero D point w x hx, Complex.normSq_zero]
    _ = Finset.sum D (fun i => Complex.normSq (lpfGridReference D point w (point i))) :=
      Finset.sum_image hinj
    _ = _ := Finset.sum_congr rfl (fun i hi => by rw [lpfGridReference_at D point w hinj i hi])

noncomputable def lpfRationalPackets (P W : Nat) : Finset (Prod (lpfRationalCenters P) Int) :=
  SProd.sprod (Finset.univ : Finset (lpfRationalCenters P)) (Finset.Icc (-(W : Int)) (W : Int))

noncomputable def lpfRationalGrid (N P W : Nat) : Finset (ZMod N) :=
  (lpfRationalPackets P W).image (lpfRationalPacketPoint N)

noncomputable def lpfRationalGridReference (N P W : Nat) (V : Int -> Complex) : ZMod N -> Complex :=
  lpfGridReference (lpfRationalPackets P W) (lpfRationalPacketPoint N)
    (fun u => lpfRationalCoefficient (u.1.1.val + 1) * V u.2)

theorem lpfRationalGridReference_energy {N : Nat} [NeZero N] (P W : Nat) (V : Int -> Complex)
    (hDiv : forall q, 0 < q -> q <= P -> Dvd.dvd q N) (hWidth : 2 * W * P ^ 2 < N) :
    Finset.sum Finset.univ (fun x : ZMod N => Complex.normSq (lpfRationalGridReference N P W V x)) <=
      (P : Real) * Finset.sum (Finset.Icc (-(W : Int)) (W : Int)) (fun k => Complex.normSq (V k)) := by
  unfold lpfRationalGridReference lpfRationalPackets
  rw [lpfGridReference_energy _ _ _ (lpfRationalPacketPoint_injective P W hDiv hWidth)]
  simp only [Finset.sum_product, Complex.normSq_mul]
  simp_rw [<- Finset.mul_sum]
  rw [<- Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (lpfRationalCenters_coefficient_energy P)
    (Finset.sum_nonneg (fun k _ => Complex.normSq_nonneg _))

theorem lpfRationalGrid_card_le (N P W : Nat) :
    (lpfRationalGrid N P W).card <= P ^ 2 * (2 * W + 1) := by
  have hK : (Finset.Icc (-(W : Int)) (W : Int)).card = 2 * W + 1 := by
    rw [Int.card_Icc]
    omega
  calc
    _ <= (lpfRationalPackets P W).card := Finset.card_image_le
    _ = Fintype.card (lpfRationalCenters P) * (2 * W + 1) := by
      unfold lpfRationalPackets
      rw [Finset.card_product, Finset.card_univ, hK]
    _ <= _ := Nat.mul_le_mul_right _ (lpfRationalCenters_card_le P)

theorem lpfGridOffset_cast_injective {N : Nat} [NeZero N] (W : Nat) (hWidth : 2 * W < N) :
    Set.InjOn (fun k : Int => (k : ZMod N))
      ((Finset.Icc (-(W : Int)) (W : Int)) : Set Int) := by
  intro k hk ell hell hEq
  have hk' := Finset.mem_Icc.mp hk
  have hell' := Finset.mem_Icc.mp hell
  have hWidth' : 2 * W * (1 : Nat) ^ 2 < N := by simpa using hWidth
  have hEq' : lpfRationalGridPoint N 1 0 k = lpfRationalGridPoint N 1 0 ell := by
    simpa [lpfRationalGridPoint] using hEq
  exact (lpfRationalGridPoint_injective 1 W 1 1 0 0 k ell
    (by decide) (by decide) (by decide) (by decide) (one_dvd N) (one_dvd N)
    (by decide) (by decide) (by decide) (by decide)
    hk'.1 hk'.2 hell'.1 hell'.2 hWidth' hEq').2.2

theorem lpfGridOffset_interval_energy {N : Nat} [NeZero N]
    (W : Nat) (U : Finset Nat) (hWidth : 2 * W < N)
    (hU : forall n, Membership.mem U n -> n < N) :
    Finset.sum (Finset.Icc (-(W : Int)) (W : Int))
      (fun k => Complex.normSq (lpfFiniteTransform U (fun n => (n : ZMod N))
        (fun _ => (1 : Complex)) (k : ZMod N))) <= (N : Real) * (U.card : Real) := by
  let K := Finset.Icc (-(W : Int)) (W : Int)
  let V := lpfFiniteTransform U (fun n => (n : ZMod N)) (fun _ => (1 : Complex))
  have hInj : Set.InjOn (fun n : Nat => (n : ZMod N)) (U : Set Nat) := by
    intro n hn m hm hEq
    have h := congrArg (fun x : ZMod N => x.val) hEq
    simpa only [ZMod.val_natCast_of_lt (hU n hn), ZMod.val_natCast_of_lt (hU m hm)] using h
  change Finset.sum K (fun k => Complex.normSq (V (k : ZMod N))) <= _
  calc
    _ = Finset.sum (K.image (fun k : Int => (k : ZMod N))) (fun x => Complex.normSq (V x)) :=
      (Finset.sum_image (lpfGridOffset_cast_injective W hWidth)).symm
    _ <= Finset.sum Finset.univ (fun x : ZMod N => Complex.normSq (V x)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => Complex.normSq_nonneg _)
    _ = _ := by
      rw [lpfFiniteTransform_parseval U (fun n => (n : ZMod N)) (fun _ => (1 : Complex)) hInj]
      simp

theorem lpfRationalGridReference_interval_energy {N : Nat} [NeZero N]
    (P W : Nat) (U : Finset Nat) (hP : 0 < P)
    (hDiv : forall q, 0 < q -> q <= P -> Dvd.dvd q N) (hWidth : 2 * W * P ^ 2 < N)
    (hU : forall n, Membership.mem U n -> n < N) :
    Finset.sum Finset.univ (fun x : ZMod N => Complex.normSq (lpfRationalGridReference N P W
      (fun k => lpfFiniteTransform U (fun n => (n : ZMod N)) (fun _ => (1 : Complex)) (k : ZMod N)) x)) <=
      (P : Real) * (N : Real) * (U.card : Real) := by
  have hPOne : 1 <= P ^ 2 := by nlinarith
  have hWide : 2 * W < N := by nlinarith
  have h := lpfRationalGridReference_energy P W
    (fun k => lpfFiniteTransform U (fun n => (n : ZMod N)) (fun _ => (1 : Complex)) (k : ZMod N)) hDiv hWidth
  have hBound := mul_le_mul_of_nonneg_left (lpfGridOffset_interval_energy W U hWide hU)
    (Nat.cast_nonneg P : (0 : Real) <= P)
  exact h.trans (by simpa only [mul_assoc] using hBound)

end PrimeFactorOscillations.LPF
