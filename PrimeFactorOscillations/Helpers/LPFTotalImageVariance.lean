/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import PrimeFactorOscillations.Helpers.LPFCyclicFourier
import PrimeFactorOscillations.Helpers.LPFJointTransfer

/-!
# Signed variance on canonical owners of the inclusive LPF step

This is a finite, unconditional inequality for the actual all-diagonal
operator. It does not bound the variance or assert growth. Counting total
current outputs permits signed old-state controls without an old-sumset mask.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

def canonicalPairSet (S : Finset Nat) (r : Nat) : Finset (Prod Nat Nat) :=
  (((S.erase 2).product (S.erase 2)).filter (fun z =>
    affineValue z.1 z.2 = primeTargetCofactor r * r))

def canonicalPairCard (S : Finset Nat) (r : Nat) : Nat :=
  (canonicalPairSet S r).card

theorem canonicalPairCard_mono {A S : Finset Nat} (hAS : A <= S) (r : Nat) :
    canonicalPairCard A r <= canonicalPairCard S r := by
  classical
  apply Finset.card_le_card
  intro z hz
  have hf := Finset.mem_filter.mp hz
  have hpq := Finset.mem_product.mp hf.1
  apply Finset.mem_filter.mpr
  apply And.intro ?_ hf.2
  apply Finset.mem_product.mpr
  exact And.intro
    (Finset.mem_erase.mpr (And.intro (Finset.mem_erase.mp hpq.1).1
      (hAS (Finset.mem_erase.mp hpq.1).2)))
    (Finset.mem_erase.mpr (And.intro (Finset.mem_erase.mp hpq.2).1
      (hAS (Finset.mem_erase.mp hpq.2).2)))

theorem mem_fullStep_of_canonicalPairCard_pos (S : Finset Nat) (r : Nat)
    (hr : Nat.Prime r) (hr3 : 3 <= r) (hCount : 0 < canonicalPairCard S r) :
    Membership.mem (fullStep S) r := by
  classical
  have hNonempty : (canonicalPairSet S r).Nonempty := Finset.card_pos.mp hCount
  let z := Classical.choose hNonempty
  have hz := Classical.choose_spec hNonempty
  have hf := Finset.mem_filter.mp hz
  have hpq := Finset.mem_product.mp hf.1
  have hStep := mem_fullStep_of_pair S
    (Finset.mem_erase.mp hpq.1).2 (Finset.mem_erase.mp hpq.2).2
  have hOwner := primeTarget_owner r hr hr3
  rw [hf.2, Nat.largestPrimeFactor_mul_prime (Nat.ne_of_gt hOwner.1) hr hOwner.2]
    at hStep
  exact hStep

/--
The reference may be any real function. A positive reference is used in the
analytic interpretation; a zero reference gives the trivial zero score.
No positivity assumption on the signed controlled count is required.
-/
theorem fullStep_card_ge_canonical_variance
    (A S G : Finset Nat) (hAS : A <= S) (hTwo : Membership.mem S 2)
    (hG : forall r, Membership.mem G r -> And (Nat.Prime r) (3 <= r))
    (beta : Real) (reference : Nat -> Real) :
    1 + (G.card : Real) -
      Finset.sum G (fun r =>
        ((((canonicalPairCard S r : Real) - beta * (canonicalPairCard A r : Real)) /
          reference r) - 1) ^ 2) <= ((fullStep S).card : Real) := by
  classical
  let hits := G.filter (fun r => Membership.mem (fullStep S) r)
  let score := fun r =>
    1 - ((((canonicalPairCard S r : Real) - beta * (canonicalPairCard A r : Real)) /
      reference r) - 1) ^ 2
  have hPoint : forall r, Membership.mem G r ->
      score r <= if Membership.mem (fullStep S) r then (1 : Real) else 0 := by
    intro r hr
    by_cases hHit : Membership.mem (fullStep S) r
    next =>
      rw [if_pos hHit]
      exact sub_le_self _ (sq_nonneg _)
    next =>
      have hCurrent : canonicalPairCard S r = 0 := by
        by_contra hNonzero
        exact hHit (mem_fullStep_of_canonicalPairCard_pos S r (hG r hr).1
          (hG r hr).2 (Nat.pos_of_ne_zero hNonzero))
      have hOld : canonicalPairCard A r = 0 := by
        have hMono := canonicalPairCard_mono hAS r
        omega
      simp [score, hHit, hCurrent, hOld]
  have hScore : Finset.sum G score <= (hits.card : Real) := by
    calc
      _ <= Finset.sum G (fun r =>
          if Membership.mem (fullStep S) r then (1 : Real) else 0) :=
        Finset.sum_le_sum hPoint
      _ = _ := by
        rw [<- Finset.sum_filter]
        simp [hits]
  have hHits : hits <= (fullStep S).erase 2 := by
    intro r hr
    have hf := Finset.mem_filter.mp hr
    apply Finset.mem_erase.mpr
    exact And.intro (by have hLower := (hG r hf.1).2; omega) hf.2
  have hHitsCard : (hits.card : Real) <= (((fullStep S).erase 2).card : Real) := by
    exact_mod_cast Finset.card_le_card hHits
  have hTwoStep := subset_fullStep S hTwo
  have hCardErase := Finset.card_erase_of_mem hTwoStep
  have hCardPos := Finset.card_pos.mpr (Exists.intro 2 hTwoStep)
  have hCardNat : ((fullStep S).erase 2).card + 1 = (fullStep S).card := by omega
  have hCardReal :
      (((fullStep S).erase 2).card : Real) + 1 = ((fullStep S).card : Real) := by
    exact_mod_cast hCardNat
  have hExpand : Finset.sum G score = (G.card : Real) -
      Finset.sum G (fun r =>
        ((((canonicalPairCard S r : Real) - beta * (canonicalPairCard A r : Real)) /
          reference r) - 1) ^ 2) := by
    dsimp [score]
    rw [Finset.sum_sub_distrib]
    simp
  linarith only [hScore, hHitsCard, hCardReal, hExpand]

theorem high_fullStep_owner_has_prime_value
    (S : Finset Nat) (X T r : Nat)
    (hS : forall p, Membership.mem S p -> Nat.Prime p)
    (hBound : forall p, Membership.mem S p -> p <= X)
    (hXT : X <= T) (hCut : 4 * X - 1 <= 3 * T)
    (hr : Membership.mem (fullStep S) r) (hTr : T < r) :
    And (Nat.Prime r) (exists p, And (Membership.mem S p)
      (exists q, And (Membership.mem S q) (affineValue p q = r))) := by
  classical
  have hrPrime := fullStep_preserves_primes S hS r hr
  have hUnion := Finset.mem_union.mp hr
  cases hUnion with
  | inl hOld =>
      have hUpper := hBound r hOld
      omega
  | inr hNew =>
      let z := Classical.choose (Finset.mem_image.mp hNew)
      have hz := Classical.choose_spec (Finset.mem_image.mp hNew)
      have hpq := Finset.mem_product.mp hz.1
      have hp2 := (hS z.1 hpq.1).two_le
      have hq2 := (hS z.2 hpq.2).two_le
      have hN : 1 < affineValue z.1 z.2 := by unfold affineValue; omega
      have hNUpper : affineValue z.1 z.2 <= 4 * X - 1 := by
        have hpX := hBound z.1 hpq.1
        have hqX := hBound z.2 hpq.2
        unfold affineValue
        omega
      have hNOdd : affineValue z.1 z.2 % 2 = 1 := by unfold affineValue; omega
      have hDvd : Dvd.dvd r (affineValue z.1 z.2) := by
        rw [<- hz.2]
        exact Nat.largestPrimeFactor_dvd hN
      let c := Classical.choose hDvd
      have hFactor : affineValue z.1 z.2 = r * c := Classical.choose_spec hDvd
      have hcPos : 0 < c := by
        by_contra h
        have hcZero : c = 0 := by omega
        rw [hcZero, Nat.mul_zero] at hFactor
        omega
      have hcOdd : c % 2 = 1 := by
        have hcMod := Nat.mod_lt c (by decide : 0 < 2)
        by_contra h
        have hcEven : c % 2 = 0 := by omega
        have hMod := congrArg (fun v : Nat => v % 2) hFactor
        rw [Nat.mul_mod, hcEven] at hMod
        simp only [Nat.mul_zero, Nat.zero_mod] at hMod
        omega
      have hcOne : c = 1 := by
        by_contra h
        have hcThree : 3 <= c := by omega
        have hLower : 3 * r <= affineValue z.1 z.2 := by
          calc
            3 * r = r * 3 := Nat.mul_comm _ _
            _ <= r * c := Nat.mul_le_mul_left r hcThree
            _ = _ := hFactor.symm
        omega
      exact And.intro hrPrime (Exists.intro z.1 (And.intro hpq.1
        (Exists.intro z.2 (And.intro hpq.2 (by simpa only [hcOne, Nat.mul_one] using hFactor)))))

theorem high_fullStep_owner_cases
    (S : Finset Nat) (X T r : Nat)
    (hS : forall p, Membership.mem S p -> Nat.Prime p)
    (hBound : forall p, Membership.mem S p -> p <= X)
    (hXT : X <= T) (hCut : 4 * X - 1 <= 3 * T)
    (hr : Membership.mem (fullStep S) r) (hTr : T < r) :
    Or (r % 4 = 3) (exists q, And (Membership.mem S q)
      (And (Not (q = 2)) (And (Nat.Prime (2 * q + 3)) (r = 2 * q + 3)))) := by
  have h := high_fullStep_owner_has_prime_value S X T r hS hBound hXT hCut hr hTr
  let p := Classical.choose h.2
  have hp := Classical.choose_spec h.2
  let q := Classical.choose hp.2
  have hq := Classical.choose_spec hp.2
  have hpPrime := hS p hp.1
  have hqPrime := hS q hq.1
  have hp2 := hpPrime.two_le
  have hq2 := hqPrime.two_le
  by_cases hpTwo : p = 2
  next =>
    by_cases hqTwo : q = 2
    next =>
      left
      have hv : affineValue p q = r := hq.2
      unfold affineValue at hv
      omega
    next =>
      right
      have heq : r = 2 * q + 3 := by
        have hv : affineValue p q = r := hq.2
        unfold affineValue at hv
        omega
      exact Exists.intro q (And.intro hq.1 (And.intro hqTwo
        (And.intro (by rw [<- heq]; exact h.1) heq)))
  next =>
    by_cases hqTwo : q = 2
    next =>
      right
      have heq : r = 2 * p + 3 := by
        have hv : affineValue p q = r := hq.2
        unfold affineValue at hv
        omega
      exact Exists.intro p (And.intro hp.1 (And.intro hpTwo
        (And.intro (by rw [<- heq]; exact h.1) heq)))
    next =>
      left
      have hpOdd := hpPrime.eq_two_or_odd.resolve_left hpTwo
      have hqOdd := hqPrime.eq_two_or_odd.resolve_left hqTwo
      have hv : affineValue p q = r := hq.2
      unfold affineValue at hv
      omega

theorem fullStep_high_owner_card_le
    (S : Finset Nat) (X T : Nat)
    (hS : forall p, Membership.mem S p -> Nat.Prime p)
    (hBound : forall p, Membership.mem S p -> p <= X)
    (hXT : X <= T) (hCut : 4 * X - 1 <= 3 * T) :
    ((fullStep S).filter (fun r => T < r)).card <=
      ((Finset.Icc (T + 1) (4 * X - 1)).filter
        (fun r => And (Nat.Prime r) (r % 4 = 3))).card +
      ((S.erase 2).filter
        (fun q => And (Nat.Prime (2 * q + 3)) (T < 2 * q + 3))).card := by
  classical
  let P := (Finset.Icc (T + 1) (4 * X - 1)).filter
    (fun r => And (Nat.Prime r) (r % 4 = 3))
  let M := (S.erase 2).filter
    (fun q => And (Nat.Prime (2 * q + 3)) (T < 2 * q + 3))
  have hCover : (fullStep S).filter (fun r => T < r) <=
      Union.union P (M.image (fun q => 2 * q + 3)) := by
    intro r hr
    have hf := Finset.mem_filter.mp hr
    have hCase := high_fullStep_owner_cases S X T r hS hBound hXT hCut hf.1 hf.2
    cases hCase with
    | inl hMod =>
        apply Finset.mem_union_left
        apply Finset.mem_filter.mpr
        have hPrime := fullStep_preserves_primes S hS r hf.1
        have hValue := high_fullStep_owner_has_prime_value S X T r
          hS hBound hXT hCut hf.1 hf.2
        let p := Classical.choose hValue.2
        have hp := Classical.choose_spec hValue.2
        let q := Classical.choose hp.2
        have hq := Classical.choose_spec hp.2
        have hpX := hBound p hp.1
        have hqX := hBound q hq.1
        have hUpper : r <= 4 * X - 1 := by
          have hv : affineValue p q = r := hq.2
          unfold affineValue at hv
          omega
        exact And.intro (Finset.mem_Icc.mpr (And.intro (by omega) hUpper))
          (And.intro hPrime hMod)
    | inr hMixed =>
        let q := Classical.choose hMixed
        have hq := Classical.choose_spec hMixed
        apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        apply Exists.intro q
        apply And.intro ?_ hq.2.2.2.symm
        apply Finset.mem_filter.mpr
        exact And.intro (Finset.mem_erase.mpr (And.intro hq.2.1 hq.1))
          (And.intro hq.2.2.1 (by rw [<- hq.2.2.2]; exact hf.2))
  have hCard := Finset.card_le_card hCover
  have hUnion := Finset.card_union_le P (M.image (fun q => 2 * q + 3))
  have hImage : (M.image (fun q => 2 * q + 3)).card <= M.card := Finset.card_image_le
  change _ <= P.card + M.card
  omega

/-!
## Birth-layer Fourier remainder

The square difference is factored before taking norms. The bound retains
all current/old cross terms, and gives b*(4*a+b) for nested unit indicators.
It bounds a Fourier remainder, not the complete prime-coordinate variance.
-/

theorem square_difference_fourier_l1_sq
    {I : Type*} (U : Finset I) (F G : I -> Complex) :
    (Finset.sum U (fun x => norm (F x ^ 2 - G x ^ 2))) ^ 2 <=
      (Finset.sum U (fun x => Complex.normSq (F x - G x))) *
      Finset.sum U (fun x => Complex.normSq (F x + G x)) := by
  have hFactor (x : I) : F x ^ 2 - G x ^ 2 = (F x - G x) * (F x + G x) := by ring
  simp_rw [hFactor, norm_mul]
  have h := Finset.sum_mul_sq_le_sq_mul_sq U
    (fun x => norm (F x - G x)) (fun x => norm (F x + G x))
  simpa only [Complex.sq_norm] using h

theorem nested_indicator_fourier_l1_sq
    {I : Type*} [DecidableEq I] {N : Nat} [NeZero N]
    (A S : Finset I) (freq : I -> ZMod N) (hAS : A <= S)
    (hInj : Set.InjOn freq (S : Set I)) :
    (Finset.sum Finset.univ (fun x : ZMod N =>
      norm ((lpfFiniteTransform S freq (fun _ => 1) x) ^ 2 -
        (lpfFiniteTransform A freq (fun _ => 1) x) ^ 2))) ^ 2 <=
      (N : Real) ^ 2 * (((S \ A).card : Real) *
        (4 * (A.card : Real) + ((S \ A).card : Real))) := by
  classical
  let B := S \ A
  let F := lpfFiniteTransform S freq (fun _ => 1)
  let G := lpfFiniteTransform A freq (fun _ => 1)
  let H := lpfFiniteTransform B freq (fun _ => 1)
  have hAInj : Set.InjOn freq (A : Set I) := by
    intro i hi j hj h
    exact hInj (hAS hi) (hAS hj) h
  have hBInj : Set.InjOn freq (B : Set I) := by
    intro i hi j hj h
    exact hInj (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).1 h
  have hDifference (x : ZMod N) : F x - G x = H x := by
    have h := Finset.sum_sdiff hAS
      (f := fun i => (1 : Complex) * ZMod.stdAddChar (x * freq i))
    exact sub_eq_iff_eq_add.mpr h.symm
  have hS : Finset.sum Finset.univ (fun x : ZMod N => Complex.normSq (F x)) =
      (N : Real) * (S.card : Real) := by
    simpa only [Complex.normSq_one, Finset.sum_const, nsmul_eq_mul, mul_one]
      using lpfFiniteTransform_parseval S freq (fun _ => 1) hInj
  have hA : Finset.sum Finset.univ (fun x : ZMod N => Complex.normSq (G x)) =
      (N : Real) * (A.card : Real) := by
    simpa only [Complex.normSq_one, Finset.sum_const, nsmul_eq_mul, mul_one]
      using lpfFiniteTransform_parseval A freq (fun _ => 1) hAInj
  have hB : Finset.sum Finset.univ (fun x : ZMod N => Complex.normSq (F x - G x)) =
      (N : Real) * (B.card : Real) := by
    simp_rw [hDifference]
    simpa only [Complex.normSq_one, Finset.sum_const, nsmul_eq_mul, mul_one]
      using lpfFiniteTransform_parseval B freq (fun _ => 1) hBInj
  have hCard : (S.card : Real) = (A.card : Real) + (B.card : Real) := by
    have h := Finset.card_sdiff_add_card_eq_card hAS
    dsimp [B]
    exact_mod_cast h.symm.trans (Nat.add_comm _ _)
  have hPoint (x : ZMod N) :
      Complex.normSq (F x + G x) + Complex.normSq (F x - G x) =
        2 * Complex.normSq (F x) + 2 * Complex.normSq (G x) := by
    rw [Complex.normSq_add, Complex.normSq_sub]
    ring
  have hSum : Finset.sum Finset.univ (fun x : ZMod N => Complex.normSq (F x + G x)) +
      Finset.sum Finset.univ (fun x : ZMod N => Complex.normSq (F x - G x)) =
        2 * Finset.sum Finset.univ (fun x : ZMod N => Complex.normSq (F x)) +
        2 * Finset.sum Finset.univ (fun x : ZMod N => Complex.normSq (G x)) := by
    rw [<- Finset.sum_add_distrib]
    simp_rw [hPoint]
    rw [Finset.sum_add_distrib, <- Finset.mul_sum, <- Finset.mul_sum]
  have hPlus : Finset.sum Finset.univ (fun x : ZMod N => Complex.normSq (F x + G x)) =
      (N : Real) * (4 * (A.card : Real) + (B.card : Real)) := by
    rw [hB, hS, hA, hCard] at hSum
    nlinarith only [hSum]
  have h := square_difference_fourier_l1_sq Finset.univ F G
  rw [hB, hPlus] at h
  change _ <= (N : Real) ^ 2 * ((B.card : Real) *
    (4 * (A.card : Real) + (B.card : Real)))
  nlinarith only [h]

/-- The complete off-zero Fourier remainder keeps the birth cancellation. -/
theorem nested_indicator_quadratic_remainder
    {I : Type*} [DecidableEq I] {N : Nat} [NeZero N]
    (A S : Finset I) (freq : I -> ZMod N) (hAS : A <= S)
    (hInj : Set.InjOn freq (S : Set I))
    (K : ZMod N -> ZMod N -> Complex) (T : Real) (hT : 0 <= T)
    (hK : forall x y, norm (K x y) <= T) :
    let F := fun x : ZMod N => if x = 0 then (0 : Complex) else
      (lpfFiniteTransform S freq (fun _ => 1) x) ^ 2 -
        (lpfFiniteTransform A freq (fun _ => 1) x) ^ 2
    norm (Finset.sum Finset.univ (fun x : ZMod N =>
      Finset.sum Finset.univ (fun y : ZMod N =>
        F x * (starRingEnd Complex) (F y) * K x y))) / (N : Real) ^ 2 <=
      T * (((S \ A).card : Real) * (4 * (A.card : Real) + ((S \ A).card : Real))) := by
  classical
  let F := fun x : ZMod N => if x = 0 then (0 : Complex) else
    (lpfFiniteTransform S freq (fun _ => 1) x) ^ 2 -
      (lpfFiniteTransform A freq (fun _ => 1) x) ^ 2
  change norm (Finset.sum Finset.univ (fun x : ZMod N =>
    Finset.sum Finset.univ (fun y : ZMod N =>
      F x * (starRingEnd Complex) (F y) * K x y))) / (N : Real) ^ 2 <= _
  have hClip : Finset.sum Finset.univ (fun x : ZMod N => norm (F x)) <=
      Finset.sum Finset.univ (fun x : ZMod N =>
        norm ((lpfFiniteTransform S freq (fun _ => 1) x) ^ 2 -
          (lpfFiniteTransform A freq (fun _ => 1) x) ^ 2)) := by
    apply Finset.sum_le_sum
    intro x _
    by_cases hx : x = 0
    next =>
      dsimp only [F]
      rw [if_pos hx, norm_zero]
      exact norm_nonneg _
    next => simp only [F, if_neg hx, le_refl]
  have hClipSq := mul_self_le_mul_self
    (Finset.sum_nonneg (fun x _ => norm_nonneg (F x))) hClip
  have hFull := nested_indicator_fourier_l1_sq A S freq hAS hInj
  have hEnergy : (Finset.sum Finset.univ (fun x : ZMod N => norm (F x))) ^ 2 <=
      (N : Real) ^ 2 * (((S \ A).card : Real) *
        (4 * (A.card : Real) + ((S \ A).card : Real))) := by
    nlinarith only [hClipSq, hFull]
  have hPoint (x y : ZMod N) :
      norm (F x * (starRingEnd Complex) (F y) * K x y) <=
        T * (norm (F x) * norm (F y)) := by
    simp only [norm_mul, Complex.norm_conj]
    calc
      _ <= norm (F x) * norm (F y) * T :=
        mul_le_mul_of_nonneg_left (hK x y) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = _ := by ring
  have hNorm :
      norm (Finset.sum Finset.univ (fun x : ZMod N =>
        Finset.sum Finset.univ (fun y : ZMod N =>
          F x * (starRingEnd Complex) (F y) * K x y))) <=
        T * (Finset.sum Finset.univ (fun x : ZMod N => norm (F x))) ^ 2 := by
    calc
      _ <= Finset.sum Finset.univ (fun x : ZMod N =>
          norm (Finset.sum Finset.univ (fun y : ZMod N =>
            F x * (starRingEnd Complex) (F y) * K x y))) := norm_sum_le _ _
      _ <= Finset.sum Finset.univ (fun x : ZMod N =>
          Finset.sum Finset.univ (fun y : ZMod N =>
            norm (F x * (starRingEnd Complex) (F y) * K x y))) :=
        Finset.sum_le_sum (fun x _ => norm_sum_le _ _)
      _ <= Finset.sum Finset.univ (fun x : ZMod N =>
          Finset.sum Finset.univ (fun y : ZMod N => T * (norm (F x) * norm (F y)))) :=
        Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => hPoint x y))
      _ = _ := by
        rw [pow_two, Finset.sum_mul_sum]
        simp only [Finset.mul_sum]
  have hBound := hNorm.trans (mul_le_mul_of_nonneg_left hEnergy hT)
  have hN : (0 : Real) < (N : Real) := by exact_mod_cast NeZero.pos N
  let R := norm (Finset.sum Finset.univ (fun x : ZMod N =>
    Finset.sum Finset.univ (fun y : ZMod N =>
      F x * (starRingEnd Complex) (F y) * K x y)))
  change R / (N : Real) ^ 2 <= _
  have hNN : Not ((N : Real) = 0) := ne_of_gt hN
  have hCancel : R / (N : Real) ^ 2 * (N : Real) ^ 2 = R := by
    field_simp [hNN]
  by_contra hFailure
  have hStrict := mul_lt_mul_of_pos_right (lt_of_not_ge hFailure) (sq_pos_of_pos hN)
  rw [hCancel] at hStrict
  nlinarith only [hBound, hStrict]

theorem cyclic_weighted_normSq_eq_quadratic
    {N : Nat} [NeZero N] (F delta : ZMod N -> Complex) :
    Finset.sum Finset.univ (fun t : ZMod N =>
      delta t * (Complex.normSq (lpfCyclicInverse F t) : Complex)) =
      ((N : Complex) ^ (-1 : Int)) ^ 2 *
        Finset.sum Finset.univ (fun x : ZMod N =>
          Finset.sum Finset.univ (fun y : ZMod N =>
            F x * (starRingEnd Complex) (F y) * lpfCyclicTransform delta (y - x))) := by
  have hCast (z : Complex) : (Complex.normSq z : Complex) = z * (starRingEnd Complex) z := by
    apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring
  have hConj (t : ZMod N) :
      (starRingEnd Complex) (lpfCyclicInverse F t) =
        (N : Complex) ^ (-1 : Int) *
          Finset.sum Finset.univ (fun y : ZMod N =>
            (starRingEnd Complex) (F y) * ZMod.stdAddChar (t * y)) := by
    simp [lpfCyclicInverse, mul_neg, AddChar.map_neg_eq_conj]
  have hPoint (t : ZMod N) :
      (Complex.normSq (lpfCyclicInverse F t) : Complex) =
        ((N : Complex) ^ (-1 : Int)) ^ 2 *
          Finset.sum Finset.univ (fun x : ZMod N =>
            Finset.sum Finset.univ (fun y : ZMod N =>
              F x * (starRingEnd Complex) (F y) * ZMod.stdAddChar (t * (y - x)))) := by
    rw [hCast, hConj]
    change ((N : Complex) ^ (-1 : Int) *
      Finset.sum Finset.univ (fun x : ZMod N => F x * ZMod.stdAddChar (t * (-x)))) *
      ((N : Complex) ^ (-1 : Int) *
        Finset.sum Finset.univ (fun y : ZMod N =>
          (starRingEnd Complex) (F y) * ZMod.stdAddChar (t * y))) = _
    calc
      _ = ((N : Complex) ^ (-1 : Int)) ^ 2 *
          ((Finset.sum Finset.univ (fun x : ZMod N => F x * ZMod.stdAddChar (t * (-x)))) *
            Finset.sum Finset.univ (fun y : ZMod N =>
              (starRingEnd Complex) (F y) * ZMod.stdAddChar (t * y))) := by ring
      _ = _ := by
        rw [Finset.sum_mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        rw [show t * (y - x) = t * (-x) + t * y by ring, AddChar.map_add_eq_mul]
        ring
  have hInner (x : ZMod N) :
      Finset.sum Finset.univ (fun t : ZMod N =>
        Finset.sum Finset.univ (fun y : ZMod N =>
          delta t * (F x * (starRingEnd Complex) (F y) *
            ZMod.stdAddChar (t * (y - x))))) =
        Finset.sum Finset.univ (fun y : ZMod N =>
          F x * (starRingEnd Complex) (F y) * lpfCyclicTransform delta (y - x)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    unfold lpfCyclicTransform
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [mul_comm (y - x) t]
    ring
  calc
    _ = ((N : Complex) ^ (-1 : Int)) ^ 2 *
        Finset.sum Finset.univ (fun t : ZMod N =>
          Finset.sum Finset.univ (fun x : ZMod N =>
            Finset.sum Finset.univ (fun y : ZMod N =>
              delta t * (F x * (starRingEnd Complex) (F y) *
                ZMod.stdAddChar (t * (y - x)))))) := by
      simp_rw [hPoint]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.mul_sum]
      simp only [Finset.mul_sum]
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      simp_rw [hInner]

theorem nested_indicator_weighted_variance_discrepancy
    {I : Type*} [DecidableEq I] {N : Nat} [NeZero N]
    (A S : Finset I) (freq : I -> ZMod N) (hAS : A <= S)
    (hInj : Set.InjOn freq (S : Set I))
    (delta : ZMod N -> Complex) (T : Real) (hT : 0 <= T)
    (hDelta : forall x, norm (lpfCyclicTransform delta x) <= T) :
    let F := fun x : ZMod N => if x = 0 then (0 : Complex) else
      (lpfFiniteTransform S freq (fun _ => 1) x) ^ 2 -
        (lpfFiniteTransform A freq (fun _ => 1) x) ^ 2
    norm (Finset.sum Finset.univ (fun t : ZMod N =>
      delta t * (Complex.normSq (lpfCyclicInverse F t) : Complex))) <=
        T * (((S \ A).card : Real) * (4 * (A.card : Real) + ((S \ A).card : Real))) := by
  classical
  let F := fun x : ZMod N => if x = 0 then (0 : Complex) else
    (lpfFiniteTransform S freq (fun _ => 1) x) ^ 2 -
      (lpfFiniteTransform A freq (fun _ => 1) x) ^ 2
  change norm (Finset.sum Finset.univ (fun t : ZMod N =>
    delta t * (Complex.normSq (lpfCyclicInverse F t) : Complex))) <= _
  have h := nested_indicator_quadratic_remainder A S freq hAS hInj
    (fun x y => lpfCyclicTransform delta (y - x)) T hT (fun x y => hDelta (y - x))
  rw [cyclic_weighted_normSq_eq_quadratic]
  have hN : (0 : Real) < (N : Real) := by exact_mod_cast NeZero.pos N
  have hNorm : norm (((N : Complex) ^ (-1 : Int)) ^ 2) = ((N : Real) ^ 2) ^ (-1 : Int) := by
    simp [norm_pow, norm_zpow, Complex.norm_natCast, zpow_neg_one, inv_pow]
  rw [norm_mul, hNorm]
  simpa only [F, zpow_neg_one, div_eq_mul_inv, mul_comm] using h

end PrimeFactorOscillations.LPF
