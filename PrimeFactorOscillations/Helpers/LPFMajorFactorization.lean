/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFCyclicKernel
import PrimeFactorOscillations.Helpers.LPFGridPhase
import PrimeFactorOscillations.Helpers.LPFGridReference
import PrimeFactorOscillations.Helpers.LPFSingularSeries

/-!
# Exact major-reference factorization and the four signed source packets

Disjoint rational packets retain every Mobius/totient coefficient, composite
denominator and signed offset. The inverse reference square factors into
one common offset kernel and the exact partial Ramanujan series. Negative
inverse phases are matched by an explicit unit permutation. The complete
fixed-interval source identity preserves all four signs and normalizations;
positivity of the full singular series and actual-state entry remain open.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem lpf_gridReference_inverse_square {I : Type*} {N : Nat} [NeZero N]
    (D : Finset I) (point : I -> ZMod N) (w : I -> Complex)
    (hinj : Set.InjOn point (D : Set I)) (t : ZMod N) :
    lpfCyclicInverse (fun x => lpfGridReference D point w x ^ 2) t =
      (N : Complex) ^ (-1 : Int) * Finset.sum D
        (fun i => w i ^ 2 * ZMod.stdAddChar (t * (-point i))) := by
  classical
  unfold lpfCyclicInverse
  congr 1
  calc
    _ = Finset.sum (D.image point)
        (fun x => lpfGridReference D point w x ^ 2 * ZMod.stdAddChar (t * (-x))) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro x _ hx
      rw [lpfGridReference_zero D point w x hx]
      simp
    _ = Finset.sum D (fun i => lpfGridReference D point w (point i) ^ 2 *
        ZMod.stdAddChar (t * (-point i))) := Finset.sum_image hinj
    _ = _ := Finset.sum_congr rfl (fun i hi => by rw [lpfGridReference_at D point w hinj i hi])

theorem lpf_rational_grid_center_character {N q : Nat} [NeZero N] [NeZero q]
    (a : Units (ZMod q)) (hDiv : Dvd.dvd q N) (t : Nat) :
    ZMod.stdAddChar (N := N) (lpfRationalGridPoint N q (a : ZMod q).val 0 * (t : ZMod N)) =
      ZMod.stdAddChar (N := q) ((a : ZMod q) * (t : ZMod q)) := by
  change _ = lpfResiduePhase a (t : ZMod q)
  rw [lpfRationalGridPoint_phase a hDiv 0 t]
  simp only [lpfGridRadians, Int.cast_zero, mul_zero, zero_div, add_zero]
  exact (lpfResiduePhase_natCast a t).symm

theorem lpf_rational_grid_inverse_phase {N q : Nat} [NeZero N] [NeZero q]
    (a : Units (ZMod q)) (hDiv : Dvd.dvd q N) (k : Int) (t : Nat) :
    ZMod.stdAddChar (N := N) ((t : ZMod N) * (-lpfRationalGridPoint N q (a : ZMod q).val k)) =
      ZMod.stdAddChar (N := q) (-((a : ZMod q) * (t : ZMod q))) *
        ZMod.stdAddChar (N := N) ((t : ZMod N) * (-(k : ZMod N))) := by
  have hPoint : lpfRationalGridPoint N q (a : ZMod q).val k =
      lpfRationalGridPoint N q (a : ZMod q).val 0 + (k : ZMod N) := by
    simp only [lpfRationalGridPoint, Int.cast_zero, add_zero]
  have hArg : (t : ZMod N) * (-lpfRationalGridPoint N q (a : ZMod q).val k) =
      -(lpfRationalGridPoint N q (a : ZMod q).val 0 * (t : ZMod N)) +
        (t : ZMod N) * (-(k : ZMod N)) := by rw [hPoint]; ring
  rw [hArg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv,
    lpf_rational_grid_center_character a hDiv t, <- AddChar.map_neg_eq_inv]

theorem lpf_ramanujan_negative_unit_sum {q : Nat} [NeZero q] (t : Nat) :
    Finset.sum Finset.univ (fun a : Units (ZMod q) =>
      ZMod.stdAddChar (N := q) (-((a : ZMod q) * (t : ZMod q)))) =
        lpfRamanujanSum (q := q) t := by
  unfold lpfRamanujanSum
  have h := (Equiv.neg (Units (ZMod q))).sum_comp Finset.univ
    (fun a : Units (ZMod q) => ZMod.stdAddChar (N := q) ((a : ZMod q) * (t : ZMod q)))
    (by intro a _; exact Finset.mem_univ a)
  simpa only [Equiv.neg_apply, Units.val_neg, neg_mul] using h

theorem lpf_rational_centers_ramanujan_sum (P t : Nat) :
    Finset.sum Finset.univ (fun i : lpfRationalCenters P =>
      lpfRationalCoefficient (i.1.val + 1) ^ 2 *
        ZMod.stdAddChar (N := i.1.val + 1) (-((i.2 : ZMod (i.1.val + 1)) *
          (t : ZMod (i.1.val + 1))))) = lpfSingularPartial P t := by
  have hStep (q : Nat) :
      Finset.sum Finset.univ (fun a : Units (ZMod (q + 1)) =>
        lpfRationalCoefficient (q + 1) ^ 2 *
          ZMod.stdAddChar (N := q + 1) (-((a : ZMod (q + 1)) * (t : ZMod (q + 1))))) =
      lpfRamanujanCoefficient (q + 1) t := by
    rw [<- Finset.mul_sum, lpf_ramanujan_negative_unit_sum, lpfRamanujanCoefficient_eq]
  rw [Fintype.sum_sigma]
  simp_rw [hStep]
  rw [Fin.sum_univ_eq_sum_range (fun q => lpfRamanujanCoefficient (q + 1) t) P]
  rw [lpfSingularPartial, Finset.sum_range_succ']
  simp only [lpfRamanujanCoefficient_zero, add_zero]

noncomputable def lpfOffsetSquareInverse (N : Nat) [NeZero N] (W : Nat)
    (V : Int -> Complex) (t : Nat) : Complex :=
  (N : Complex) ^ (-1 : Int) * Finset.sum (Finset.Icc (-(W : Int)) (W : Int))
    (fun k => V k ^ 2 * ZMod.stdAddChar (N := N) ((t : ZMod N) * (-(k : ZMod N))))

theorem lpf_rational_reference_square_factorization {N : Nat} [NeZero N]
    (P W : Nat) (V : Int -> Complex) (t : Nat)
    (hDiv : forall q, 0 < q -> q <= P -> Dvd.dvd q N) (hWidth : 2 * W * P ^ 2 < N) :
    lpfCyclicInverse (fun x => lpfRationalGridReference N P W V x ^ 2) (t : ZMod N) =
      lpfOffsetSquareInverse N W V t * lpfSingularPartial P t := by
  classical
  have hPhase (i : lpfRationalCenters P) (k : Int) :
      ZMod.stdAddChar (N := N) ((t : ZMod N) * (-lpfRationalPacketPoint N (i, k))) =
      ZMod.stdAddChar (N := i.1.val + 1) (-((i.2 : ZMod (i.1.val + 1)) *
        (t : ZMod (i.1.val + 1)))) *
      ZMod.stdAddChar (N := N) ((t : ZMod N) * (-(k : ZMod N))) := by
    have hqP : i.1.val + 1 <= P := by have h := i.1.isLt; omega
    exact lpf_rational_grid_inverse_phase i.2 (hDiv _ (Nat.succ_pos _) hqP) k t
  have hTerm (i : lpfRationalCenters P) (k : Int) :
      (lpfRationalCoefficient (i.1.val + 1) * V k) ^ 2 *
        ZMod.stdAddChar (N := N) ((t : ZMod N) * (-lpfRationalPacketPoint N (i, k))) =
      (lpfRationalCoefficient (i.1.val + 1) ^ 2 *
        ZMod.stdAddChar (N := i.1.val + 1) (-((i.2 : ZMod (i.1.val + 1)) *
          (t : ZMod (i.1.val + 1))))) *
      (V k ^ 2 * ZMod.stdAddChar (N := N) ((t : ZMod N) * (-(k : ZMod N)))) := by
    rw [hPhase]
    ring
  unfold lpfRationalGridReference lpfRationalPackets
  rw [lpf_gridReference_inverse_square _ _ _
    (lpfRationalPacketPoint_injective P W hDiv hWidth)]
  rw [Finset.sum_product]
  simp_rw [hTerm, <- Finset.mul_sum]
  rw [<- Finset.sum_mul, lpf_rational_centers_ramanujan_sum]
  dsimp [lpfOffsetSquareInverse]
  ring

theorem lpf_offset_square_inverse_eq_cyclic {N : Nat} [NeZero N]
    (W : Nat) (F : ZMod N -> Complex) (t : Nat) (hWidth : 2 * W < N) :
    lpfOffsetSquareInverse N W (fun k => F (k : ZMod N)) t =
      lpfCyclicInverse (fun x => if Membership.mem (lpfIntervalOffsetGrid N W) x then F x ^ 2 else 0)
        (t : ZMod N) := by
  classical
  unfold lpfOffsetSquareInverse lpfCyclicInverse
  congr 1
  calc
    _ = Finset.sum (lpfIntervalOffsetGrid N W)
        (fun x => F x ^ 2 * ZMod.stdAddChar (N := N) ((t : ZMod N) * (-x))) :=
      (Finset.sum_image (lpfGridOffset_cast_injective W hWidth)).symm
    _ = Finset.sum (lpfIntervalOffsetGrid N W)
        (fun x => (if Membership.mem (lpfIntervalOffsetGrid N W) x then F x ^ 2 else 0) *
          ZMod.stdAddChar (N := N) ((t : ZMod N) * (-x))) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [ite_eq_left hx]
    _ = _ := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro x _ hx
      rw [ite_eq_right hx]
      simp

theorem lpf_rational_interval_reference_factorization {N : Nat} [NeZero N]
    (P W s L t : Nat) (hP : 0 < P)
    (hDiv : forall q, 0 < q -> q <= P -> Dvd.dvd q N) (hWidth : 2 * W * P ^ 2 < N) :
    lpfCyclicInverse (fun x => lpfRationalGridReference N P W
      (fun k => lpfGridIntervalKernel N s L k) x ^ 2) (t : ZMod N) =
      lpfCyclicInverse (fun x => if Membership.mem (lpfIntervalOffsetGrid N W) x then
        lpfIntervalFrequencyKernel N s L x ^ 2 else 0) (t : ZMod N) * lpfSingularPartial P t := by
  have hPP : 1 <= P ^ 2 := by
    have hOne : 1 <= P := by omega
    nlinarith only [hOne]
  have hOffsetWidth : 2 * W < N := by
    have h := Nat.mul_le_mul_left (2 * W) hPP
    simp only [mul_one] at h
    exact h.trans_lt hWidth
  rw [lpf_rational_reference_square_factorization P W _ t hDiv hWidth]
  change lpfOffsetSquareInverse N W (fun k => lpfIntervalFrequencyKernel N s L (k : ZMod N)) t *
    lpfSingularPartial P t = _
  rw [lpf_offset_square_inverse_eq_cyclic W _ t hOffsetWidth]

theorem lpf_cyclicInverse_add {N : Nat} [NeZero N]
    (F H : ZMod N -> Complex) (t : ZMod N) :
    lpfCyclicInverse (fun x => F x + H x) t = lpfCyclicInverse F t + lpfCyclicInverse H t := by
  unfold lpfCyclicInverse
  simp only [add_mul, Finset.sum_add_distrib]
  ring

theorem lpf_fixed_interval_source_four_packets {N : Nat} [NeZero N]
    (P W s L t : Nat) (hP : 0 < P)
    (hDiv : forall q, 0 < q -> q <= P -> Dvd.dvd q N) (hWidth : 2 * W * P ^ 2 < N) :
    lpfCyclicInverse (fun x => lpfGridIntervalWeight N s L x ^ 2) (t : ZMod N) -
        lpfIntervalPairCount N s L (t : ZMod N) * lpfSingularSeries t =
      lpfCyclicInverse (fun x => if Membership.mem (lpfRationalGrid N P W) x then
          lpfGridIntervalWeight N s L x ^ 2 -
            lpfRationalGridReference N P W (fun k => lpfGridIntervalKernel N s L k) x ^ 2 else 0)
        (t : ZMod N) +
      lpfCyclicInverse (fun x => if Membership.mem (lpfRationalGrid N P W) x then 0
          else lpfGridIntervalWeight N s L x ^ 2) (t : ZMod N) +
      (lpfCyclicInverse (fun x => if Membership.mem (lpfIntervalOffsetGrid N W) x then
          lpfIntervalFrequencyKernel N s L x ^ 2 else 0) (t : ZMod N) -
        lpfIntervalPairCount N s L (t : ZMod N)) * lpfSingularPartial P t +
      lpfIntervalPairCount N s L (t : ZMod N) * (lpfSingularPartial P t - lpfSingularSeries t) := by
  classical
  let S : ZMod N -> Complex := fun x => lpfGridIntervalWeight N s L x
  let A : ZMod N -> Complex := lpfRationalGridReference N P W (fun k => lpfGridIntervalKernel N s L k)
  let G : Finset (ZMod N) := lpfRationalGrid N P W
  let F : ZMod N -> Complex := fun x => if Membership.mem G x then S x ^ 2 - A x ^ 2 else 0
  let H : ZMod N -> Complex := fun x => if Membership.mem G x then 0 else S x ^ 2
  have hZero (x : ZMod N) (hx : Not (Membership.mem G x)) : A x = 0 := by
    exact lpfGridReference_zero (lpfRationalPackets P W) (lpfRationalPacketPoint N)
      (fun u => lpfRationalCoefficient (u.1.1.val + 1) * lpfGridIntervalKernel N s L u.2) x hx
  have hPoint (x : ZMod N) : S x ^ 2 = F x + H x + A x ^ 2 := by
    dsimp [F, H]
    by_cases hx : Membership.mem G x
    case pos => simp only [ite_eq_left hx]; ring
    case neg => simp only [ite_eq_right hx, hZero x hx]; ring
  have hFourier : lpfCyclicInverse (fun x => S x ^ 2) (t : ZMod N) =
      lpfCyclicInverse F (t : ZMod N) + lpfCyclicInverse H (t : ZMod N) +
        lpfCyclicInverse (fun x => A x ^ 2) (t : ZMod N) := by
    calc
      _ = lpfCyclicInverse (fun x => F x + H x + A x ^ 2) (t : ZMod N) := by
        congr 1
        exact funext hPoint
      _ = _ := by rw [lpf_cyclicInverse_add, lpf_cyclicInverse_add]
  have hFactor := lpf_rational_interval_reference_factorization P W s L t hP hDiv hWidth
  change lpfCyclicInverse (fun x => A x ^ 2) (t : ZMod N) = _ at hFactor
  rw [hFactor] at hFourier
  change lpfCyclicInverse (fun x => S x ^ 2) (t : ZMod N) -
    lpfIntervalPairCount N s L (t : ZMod N) * lpfSingularSeries t =
    lpfCyclicInverse F (t : ZMod N) + lpfCyclicInverse H (t : ZMod N) +
    (lpfCyclicInverse (fun x => if Membership.mem (lpfIntervalOffsetGrid N W) x then
        lpfIntervalFrequencyKernel N s L x ^ 2 else 0) (t : ZMod N) -
      lpfIntervalPairCount N s L (t : ZMod N)) * lpfSingularPartial P t +
    lpfIntervalPairCount N s L (t : ZMod N) * (lpfSingularPartial P t - lpfSingularSeries t)
  rw [hFourier]
  ring

end PrimeFactorOscillations.LPF
