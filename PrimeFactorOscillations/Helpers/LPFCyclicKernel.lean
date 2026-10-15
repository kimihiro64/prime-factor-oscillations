/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFIntervalGeometric

/-!
# Complete cyclic interval-kernel truncation

Positive and negative representatives cover the entire retained complement,
including the even-grid midpoint. The full tail energy is <= N^2/(2*W).
After exact cyclic inverse normalization the pointwise truncation is
<= N/(2*W). With M|N and W=(N/M)*P this is the physical bound M/(2*P),
independent of the size of the auxiliary grid. All shifts, lengths and
output residues are quantified; W>=1 excludes division at a zero cutoff.
The full inverse is the exact ordered interval pair count, including diagonals.
Its norm is <= L when s+L<N. The integer adapter requires 2*(s+L)<N and
a target below N, so both input and pair-sum wraparound are explicit.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

namespace PrimeFactorOscillations.LPF

noncomputable def lpfIntervalOffsetGrid (N W : Nat) : Finset (ZMod N) :=
  (Finset.Icc (-(W : Int)) (W : Int)).image (fun k : Int => (k : ZMod N))

noncomputable def lpfIntervalFrequencyKernel (N : Nat) [NeZero N] (s L : Nat) (x : ZMod N) : Complex :=
  Finset.sum (Finset.range L) (fun i => ZMod.stdAddChar (N := N) (x * ((s + 1 + i : Nat) : ZMod N)))

theorem lpfIntervalFrequency_tail_cover {N : Nat} [NeZero N] (W : Nat) (x : ZMod N)
    (hx : Not (Membership.mem (lpfIntervalOffsetGrid N W) x)) :
    exists k : Nat, And (Membership.mem (Finset.Ioc W (N / 2)) k)
      (Or (x = (k : ZMod N)) (x = -(k : ZMod N))) := by
  have hVal : x.val < N := ZMod.val_lt x
  by_cases hHalf : 2 * x.val <= N
  . have hW : W < x.val := by
      by_contra hNot
      have hSmall : x.val <= W := not_lt.mp hNot
      apply hx
      apply Finset.mem_image.mpr
      refine Exists.intro (x.val : Int) (And.intro ?_ ?_)
      . apply Finset.mem_Icc.mpr
        constructor <;> omega
      . simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
    refine Exists.intro x.val (And.intro ?_ (Or.inl ?_))
    . apply Finset.mem_Ioc.mpr
      constructor <;> omega
    . exact (ZMod.natCast_zmod_val x).symm
  . let k := N - x.val
    have hK : k <= N / 2 := by dsimp [k]; omega
    have hSum : x.val + k = N := by dsimp [k]; omega
    have hCast : x + (k : ZMod N) = 0 := by
      rw [<- ZMod.natCast_zmod_val x, <- Nat.cast_add, hSum]
      simp
    have hEq : x = -(k : ZMod N) := by
      have h := congrArg (fun z : ZMod N => z - (k : ZMod N)) hCast
      simpa only [add_sub_cancel_right, zero_sub] using h
    have hW : W < k := by
      by_contra hNot
      have hSmall : k <= W := not_lt.mp hNot
      apply hx
      apply Finset.mem_image.mpr
      refine Exists.intro (-(k : Int)) (And.intro ?_ ?_)
      . apply Finset.mem_Icc.mpr
        constructor <;> omega
      . simpa only [Int.cast_neg, Int.cast_natCast] using hEq.symm
    exact Exists.intro k (And.intro (Finset.mem_Ioc.mpr (And.intro hW hK)) (Or.inr hEq))

theorem lpfIntervalFrequencyKernel_norm_neg {N : Nat} [NeZero N] (s L : Nat) (x : ZMod N) :
    norm (lpfIntervalFrequencyKernel N s L (-x)) = norm (lpfIntervalFrequencyKernel N s L x) := by
  have h := norm_lpfGridIntervalKernel_neg (N := N) s L (x.val : Int)
  simpa only [lpfGridIntervalKernel, lpfIntervalFrequencyKernel, Int.cast_neg,
    Int.cast_natCast, ZMod.natCast_zmod_val] using h

theorem lpfIntervalFrequencyKernel_cyclic_tail_energy {N : Nat} [NeZero N]
    (s L W : Nat) (hW : 1 <= W) :
    Finset.sum (Finset.univ \ lpfIntervalOffsetGrid N W)
      (fun x : ZMod N => norm (lpfIntervalFrequencyKernel N s L x) ^ 2) <=
        (N : Real) ^ 2 / (2 * (W : Real)) := by
  let S := Finset.Ioc W (N / 2)
  let A := S.image (fun k : Nat => (k : ZMod N))
  let B := S.image (fun k : Nat => -(k : ZMod N))
  let f := fun x : ZMod N => norm (lpfIntervalFrequencyKernel N s L x) ^ 2
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hSub : (Finset.univ \ lpfIntervalOffsetGrid N W) <= Union.union A B := by
    intro x hx
    choose k hk hEq using lpfIntervalFrequency_tail_cover W x (Finset.mem_sdiff.mp hx).2
    cases hEq with
    | inl hEq =>
      apply Finset.mem_union.mpr
      exact Or.inl (Finset.mem_image.mpr (Exists.intro k (And.intro hk hEq.symm)))
    | inr hEq =>
      apply Finset.mem_union.mpr
      exact Or.inr (Finset.mem_image.mpr (Exists.intro k (And.intro hk hEq.symm)))
  have hCastInj : Set.InjOn (fun k : Nat => (k : ZMod N)) (S : Set Nat) := by
    intro a ha b hb hEq
    have hA : a < N := by have h := Finset.mem_Ioc.mp ha; omega
    have hB : b < N := by have h := Finset.mem_Ioc.mp hb; omega
    have h := congrArg (fun x : ZMod N => x.val) hEq
    simpa only [ZMod.val_natCast_of_lt hA, ZMod.val_natCast_of_lt hB] using h
  have hNegInj : Set.InjOn (fun k : Nat => -(k : ZMod N)) (S : Set Nat) := by
    intro a ha b hb hEq
    exact hCastInj ha hb (neg_injective hEq)
  have hPos : Finset.sum A f = Finset.sum S (fun k => norm (lpfGridIntervalKernel N s L (k : Int)) ^ 2) := by
    rw [Finset.sum_image hCastInj]
    simp only [f, lpfGridIntervalKernel, lpfIntervalFrequencyKernel, Int.cast_natCast]
  have hNeg : Finset.sum B f = Finset.sum A f := by
    rw [Finset.sum_image hNegInj, Finset.sum_image hCastInj]
    apply Finset.sum_congr rfl
    intro k hk
    rw [lpfIntervalFrequencyKernel_norm_neg]
  have hUnion : Finset.sum (Union.union A B) f <= Finset.sum A f + Finset.sum B f := by
    have h : Finset.sum (Union.union A B) f + Finset.sum (Inter.inter A B) f =
        Finset.sum A f + Finset.sum B f := Finset.sum_union_inter
    have hNonneg : 0 <= Finset.sum (Inter.inter A B) f := Finset.sum_nonneg (fun x hx => sq_nonneg _)
    linarith
  have hPosBound : Finset.sum A f <= (N : Real) ^ 2 / (4 * (W : Real)) := by
    rw [hPos]
    exact lpfGridIntervalKernel_positive_tail_energy s L W hW
  calc
    _ <= Finset.sum (Union.union A B) f := Finset.sum_le_sum_of_subset_of_nonneg hSub (fun x hx hxNot => sq_nonneg _)
    _ <= Finset.sum A f + Finset.sum B f := hUnion
    _ = 2 * Finset.sum A f := by rw [hNeg]; ring
    _ <= 2 * ((N : Real) ^ 2 / (4 * (W : Real))) := mul_le_mul_of_nonneg_left hPosBound (by norm_num)
    _ = _ := by ring

theorem norm_lpfIntervalKernel_truncation {N : Nat} [NeZero N]
    (s L W : Nat) (t : ZMod N) (hW : 1 <= W) :
    norm (lpfCyclicInverse (fun x => if Membership.mem (lpfIntervalOffsetGrid N W) x then
        (lpfIntervalFrequencyKernel N s L x) ^ 2 else 0) t -
      lpfCyclicInverse (fun x => (lpfIntervalFrequencyKernel N s L x) ^ 2) t) <=
        (N : Real) / (2 * (W : Real)) := by
  let K := lpfIntervalOffsetGrid N W
  let F := lpfIntervalFrequencyKernel N s L
  have hN : (0 : Real) < (N : Real) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hWR : (0 : Real) < (W : Real) := Nat.cast_pos.mpr (by omega)
  have hInner : Finset.sum Finset.univ (fun x : ZMod N =>
      (if Membership.mem K x then (F x) ^ 2 else 0) * ZMod.stdAddChar (t * (-x)) -
        (F x) ^ 2 * ZMod.stdAddChar (t * (-x))) =
      Finset.sum (Finset.univ \ K) (fun x : ZMod N => -(F x) ^ 2 * ZMod.stdAddChar (t * (-x))) := by
    have hSet : (Finset.univ \ K) = Finset.univ.filter (fun x : ZMod N => Not (Membership.mem K x)) := by
      apply Finset.ext
      intro x
      simp
    rw [hSet, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h : Membership.mem K x <;> simp [h] <;> ring
  have hDiff : lpfCyclicInverse (fun x => if Membership.mem K x then (F x) ^ 2 else 0) t -
      lpfCyclicInverse (fun x => (F x) ^ 2) t =
        (N : Complex) ^ (-1 : Int) *
          Finset.sum (Finset.univ \ K) (fun x : ZMod N => -(F x) ^ 2 * ZMod.stdAddChar (t * (-x))) := by
    unfold lpfCyclicInverse
    rw [<- mul_sub, <- Finset.sum_sub_distrib, hInner]
  have hPrefNorm : norm ((N : Complex) ^ (-1 : Int)) = 1 / (N : Real) := by
    have hNormN : norm (N : Complex) = (N : Real) := by simp
    rw [norm_zpow, hNormN, zpow_neg_one, one_div]
  have hSum : norm (Finset.sum (Finset.univ \ K)
      (fun x : ZMod N => -(F x) ^ 2 * ZMod.stdAddChar (t * (-x)))) <=
        Finset.sum (Finset.univ \ K) (fun x : ZMod N => norm (F x) ^ 2) := by
    calc
      _ <= Finset.sum (Finset.univ \ K) (fun x : ZMod N => norm (-(F x) ^ 2 * ZMod.stdAddChar (t * (-x)))) :=
        norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x hx
        have hPsi : norm (ZMod.stdAddChar (N := N) (t * (-x))) = 1 := by
          rw [ZMod.stdAddChar_apply]
          exact Circle.norm_coe _
        rw [norm_mul, norm_neg, norm_pow, hPsi, mul_one]
  change norm (lpfCyclicInverse (fun x => if Membership.mem K x then (F x) ^ 2 else 0) t -
    lpfCyclicInverse (fun x => (F x) ^ 2) t) <= _
  rw [hDiff, norm_mul, hPrefNorm]
  calc
    _ <= (1 / (N : Real)) * Finset.sum (Finset.univ \ K) (fun x : ZMod N => norm (F x) ^ 2) :=
      mul_le_mul_of_nonneg_left hSum (by positivity)
    _ <= (1 / (N : Real)) * ((N : Real) ^ 2 / (2 * (W : Real))) :=
      mul_le_mul_of_nonneg_left (lpfIntervalFrequencyKernel_cyclic_tail_energy s L W hW) (by positivity)
    _ = _ := by field_simp

theorem norm_lpfIntervalKernel_scaled_truncation {N : Nat} [NeZero N]
    (M P s L : Nat) (t : ZMod N) (hM : 0 < M) (hP : 0 < P) (hDiv : Dvd.dvd M N) :
    norm (lpfCyclicInverse (fun x => if Membership.mem (lpfIntervalOffsetGrid N ((N / M) * P)) x then
        (lpfIntervalFrequencyKernel N s L x) ^ 2 else 0) t -
      lpfCyclicInverse (fun x => (lpfIntervalFrequencyKernel N s L x) ^ 2) t) <=
        (M : Real) / (2 * (P : Real)) := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hQ : 0 < N / M := Nat.div_pos (Nat.le_of_dvd hN hDiv) hM
  have hW : 1 <= (N / M) * P := Nat.mul_pos hQ hP
  have hFactor : (N : Real) = ((N / M : Nat) : Real) * (M : Real) := by
    exact_mod_cast (Nat.div_mul_cancel hDiv).symm
  have hQr : (0 : Real) < ((N / M : Nat) : Real) := Nat.cast_pos.mpr hQ
  have hPr : (0 : Real) < (P : Real) := Nat.cast_pos.mpr hP
  have hEq : (N : Real) / (2 * (((N / M) * P : Nat) : Real)) = (M : Real) / (2 * (P : Real)) := by
    rw [hFactor, Nat.cast_mul]
    field_simp
  exact (norm_lpfIntervalKernel_truncation s L ((N / M) * P) t hW).trans_eq hEq

noncomputable def lpfIntervalPairCount (N : Nat) [NeZero N] (s L : Nat) (t : ZMod N) : Complex :=
  Finset.sum (Finset.range L) (fun i => Finset.sum (Finset.range L) (fun j =>
    if (((s + 1 + i : Nat) : ZMod N) + ((s + 1 + j : Nat) : ZMod N)) = t then 1 else 0))

theorem lpfIntervalFrequencyKernel_inverse_square {N : Nat} [NeZero N] (s L : Nat) (t : ZMod N) :
    lpfCyclicInverse (fun x => (lpfIntervalFrequencyKernel N s L x) ^ 2) t =
      lpfIntervalPairCount N s L t := by
  have h := lpfCyclicInverse_finite_product (Finset.range L) (Finset.range L)
    (fun i => ((s + 1 + i : Nat) : ZMod N)) (fun i => ((s + 1 + i : Nat) : ZMod N))
    (fun _ => (1 : Complex)) (fun _ => (1 : Complex)) t
  simpa only [pow_two, lpfIntervalFrequencyKernel, lpfFiniteTransform,
    lpfIntervalPairCount, one_mul, mul_one] using h

theorem norm_lpfIntervalPairCount_le {N : Nat} [NeZero N] (s L : Nat) (t : ZMod N)
    (hNoWrap : s + L < N) : norm (lpfIntervalPairCount N s L t) <= (L : Real) := by
  have hInner : forall i, Membership.mem (Finset.range L) i ->
      norm (Finset.sum (Finset.range L) (fun j =>
        if (((s + 1 + i : Nat) : ZMod N) + ((s + 1 + j : Nat) : ZMod N)) = t then (1 : Complex) else 0)) <= 1 := by
    intro i hi
    let B := (Finset.range L).filter (fun j =>
      (((s + 1 + i : Nat) : ZMod N) + ((s + 1 + j : Nat) : ZMod N)) = t)
    have hCard : B.card <= 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      have hA := Finset.mem_filter.mp ha
      have hB := Finset.mem_filter.mp hb
      have hAR := Finset.mem_range.mp hA.1
      have hBR := Finset.mem_range.mp hB.1
      have hAN : s + 1 + a < N := by omega
      have hBN : s + 1 + b < N := by omega
      have hEq := add_left_cancel (hA.2.trans hB.2.symm)
      have h := congrArg (fun x : ZMod N => x.val) hEq
      simp only [ZMod.val_natCast_of_lt hAN, ZMod.val_natCast_of_lt hBN] at h
      exact Nat.add_left_cancel h
    have hFilter : Finset.sum B (fun _ : Nat => (1 : Complex)) =
        Finset.sum (Finset.range L) (fun j =>
          if (((s + 1 + i : Nat) : ZMod N) + ((s + 1 + j : Nat) : ZMod N)) = t then (1 : Complex) else 0) :=
      Finset.sum_filter
        (fun j : Nat => (((s + 1 + i : Nat) : ZMod N) + ((s + 1 + j : Nat) : ZMod N)) = t)
        (fun _ : Nat => (1 : Complex))
    rw [<- hFilter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hR : (B.card : Real) <= 1 := by exact_mod_cast hCard
    simpa using hR
  unfold lpfIntervalPairCount
  calc
    _ <= Finset.sum (Finset.range L) (fun i => norm (Finset.sum (Finset.range L) (fun j =>
        if (((s + 1 + i : Nat) : ZMod N) + ((s + 1 + j : Nat) : ZMod N)) = t then (1 : Complex) else 0))) :=
      norm_sum_le _ _
    _ <= Finset.sum (Finset.range L) (fun _ => (1 : Real)) := Finset.sum_le_sum hInner
    _ = _ := by simp

theorem lpfIntervalPairCount_integer {N : Nat} [NeZero N] (s L n : Nat)
    (hNoWrap : 2 * (s + L) < N) (hn : n < N) :
    lpfIntervalPairCount N s L (n : ZMod N) =
      Finset.sum (Finset.range L) (fun i => Finset.sum (Finset.range L) (fun j =>
        if (s + 1 + i) + (s + 1 + j) = n then (1 : Complex) else 0)) := by
  unfold lpfIntervalPairCount
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hI := Finset.mem_range.mp hi
  have hJ := Finset.mem_range.mp hj
  have hSum : (s + 1 + i) + (s + 1 + j) < N := by omega
  have hEq : (((s + 1 + i : Nat) : ZMod N) + ((s + 1 + j : Nat) : ZMod N)) = (n : ZMod N) <->
      (s + 1 + i) + (s + 1 + j) = n := by
    rw [<- Nat.cast_add]
    constructor
    . intro h
      have hVal := congrArg (fun x : ZMod N => x.val) h
      simpa only [ZMod.val_natCast_of_lt hSum, ZMod.val_natCast_of_lt hn] using hVal
    . intro h
      rw [h]
  simp only [hEq]

end PrimeFactorOscillations.LPF
