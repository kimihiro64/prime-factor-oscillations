/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Mathlib.NumberTheory.GaussSum.FiniteRingEnergy

/-!
# Normalized cyclic inversion for the coupled Goldbach error

The exact source keeps four packets: the major-arc transform of S^2-A^2,
the minor-arc transform of S^2, the truncated-kernel correction, and the
singular-series tail. Here S^2-A^2 stays as 2*A*(S-A)+(S-A)^2 inside Bessel.
The 1/N normalization cancels a grid's N-point counting cost; it does not
change the physical interval parameter M. The eventual complete target is
O(M^(3-1/80)), uniformly over fixed eligible source windows. With
alpha=15/16 and P=M^(1/40), the proposed complete budget is logarithmic
factors times M^3/P + M^(13/5) + M^(2*alpha+1)*P^4 +
M^(4*alpha-1)*P^9 + M^2*P^2. Major-main, minor-arc and tail estimates
remain unproved here; these finite identities alone give no exception bound.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

namespace PrimeFactorOscillations.LPF

noncomputable def lpfCyclicTransform {N : Nat} [NeZero N]
    (f : ZMod N -> Complex) (x : ZMod N) : Complex :=
  Finset.sum Finset.univ (fun n : ZMod N => f n * ZMod.stdAddChar (x * n))

noncomputable def lpfCyclicInverse {N : Nat} [NeZero N]
    (F : ZMod N -> Complex) (t : ZMod N) : Complex :=
  (N : Complex) ^ (-1 : Int) *
    Finset.sum Finset.univ (fun x : ZMod N => F x * ZMod.stdAddChar (t * (-x)))

theorem lpfCyclicInverse_parseval {N : Nat} [NeZero N]
    (F : ZMod N -> Complex) :
    Finset.sum Finset.univ (fun t : ZMod N => Complex.normSq (lpfCyclicInverse F t)) =
      (N : Real) ^ (-1 : Int) *
        Finset.sum Finset.univ (fun x : ZMod N => Complex.normSq (F x)) := by
  have hN : Not ((N : Real) = 0) := by exact_mod_cast (NeZero.ne N)
  have hP := AddChar.sum_normSq_fourier_injective
    (ZMod.stdAddChar (N := N)) (ZMod.isPrimitive_stdAddChar N)
    (fun x : ZMod N => -x) neg_injective F
  simp only [ZMod.card] at hP
  simp only [lpfCyclicInverse, Complex.normSq_mul, zpow_neg_one,
    Complex.normSq_inv, Complex.normSq_natCast, <- Finset.mul_sum]
  rw [hP]
  field_simp

theorem lpfCyclicInverse_bessel {N : Nat} [NeZero N]
    (F : ZMod N -> Complex) (T : Finset (ZMod N)) :
    Finset.sum T (fun t => Complex.normSq (lpfCyclicInverse F t)) <=
      (N : Real) ^ (-1 : Int) *
        Finset.sum Finset.univ (fun x : ZMod N => Complex.normSq (F x)) := by
  rw [<- lpfCyclicInverse_parseval F]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
    (fun t _ _ => Complex.normSq_nonneg _)

theorem lpfCyclicInverse_square_difference_bessel {N : Nat} [NeZero N]
    (S A : ZMod N -> Complex) (G T : Finset (ZMod N)) :
    Finset.sum T (fun t => Complex.normSq (lpfCyclicInverse
      (fun x => if Membership.mem G x then S x ^ 2 - A x ^ 2 else 0) t)) <=
      (N : Real) ^ (-1 : Int) * Finset.sum G
        (fun x => Complex.normSq (2 * A x * (S x - A x) + (S x - A x) ^ 2)) := by
  have h := lpfCyclicInverse_bessel
    (fun x => if Membership.mem G x then S x ^ 2 - A x ^ 2 else 0) T
  have hId (x : ZMod N) : S x ^ 2 - A x ^ 2 =
      2 * A x * (S x - A x) + (S x - A x) ^ 2 := by ring
  simpa only [hId, apply_ite, Finset.sum_ite_mem, Complex.normSq_zero, Finset.sum_const_zero,
    add_zero, Finset.inter_univ, Finset.univ_inter] using h

theorem lpfCyclicInverse_product {N : Nat} [NeZero N]
    (f g : ZMod N -> Complex) (t : ZMod N) :
    lpfCyclicInverse (fun x => lpfCyclicTransform f x * lpfCyclicTransform g x) t =
      Finset.sum Finset.univ (fun u : ZMod N => f u * g (t - u)) := by
  have hNc : Not ((N : Complex) = 0) := by exact_mod_cast (NeZero.ne N)
  have hExpand (x : ZMod N) :
      lpfCyclicTransform f x * lpfCyclicTransform g x * ZMod.stdAddChar (t * (-x)) =
      Finset.sum Finset.univ (fun u : ZMod N => Finset.sum Finset.univ
        (fun v : ZMod N => (f u * g v) *
          (ZMod.stdAddChar (x * (u + v)) *
            (starRingEnd Complex) (ZMod.stdAddChar (x * t))))) := by
    simp only [lpfCyclicTransform]
    rw [Finset.sum_mul_sum]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    rw [show x * (u + v) = x * u + x * v by ring,
      AddChar.map_add_eq_mul, show t * (-x) = -(x * t) by ring,
      AddChar.map_neg_eq_conj]
    ring
  have hSum : Finset.sum Finset.univ (fun x : ZMod N =>
      lpfCyclicTransform f x * lpfCyclicTransform g x * ZMod.stdAddChar (t * (-x))) =
      (N : Complex) * Finset.sum Finset.univ (fun u : ZMod N => f u * g (t - u)) := by
    simp_rw [hExpand]
    rw [Finset.sum_comm]
    have hInner (u : ZMod N) :
        Finset.sum Finset.univ (fun x : ZMod N => Finset.sum Finset.univ
          (fun v : ZMod N => (f u * g v) *
            (ZMod.stdAddChar (x * (u + v)) *
              (starRingEnd Complex) (ZMod.stdAddChar (x * t))))) =
        (N : Complex) * (f u * g (t - u)) := by
      rw [Finset.sum_comm]
      simp_rw [<- Finset.mul_sum,
        AddChar.sum_crossPhase (ZMod.stdAddChar (N := N)) (ZMod.isPrimitive_stdAddChar N)]
      have hEq (v : ZMod N) : u + v = t <-> v = t - u := by
        rw [eq_sub_iff_add_eq, add_comm]
      simp_rw [hEq]
      simp [ZMod.card, mul_ite, mul_comm, mul_assoc]
    simp_rw [hInner]
    rw [Finset.mul_sum]
  simp only [lpfCyclicInverse, zpow_neg_one]
  rw [hSum]
  simp [hNc]

noncomputable def lpfFiniteTransform {I : Type*} {N : Nat} [NeZero N]
    (U : Finset I) (freq : I -> ZMod N) (w : I -> Complex) (x : ZMod N) : Complex :=
  Finset.sum U (fun i => w i * ZMod.stdAddChar (x * freq i))

/-- All ordered representations and repeated inputs retain their weights. -/
theorem lpfCyclicInverse_finite_product {I J : Type*} {N : Nat} [NeZero N]
    (U : Finset I) (V : Finset J) (freq : I -> ZMod N) (freq' : J -> ZMod N)
    (w : I -> Complex) (w' : J -> Complex) (t : ZMod N) :
    lpfCyclicInverse (fun x => lpfFiniteTransform U freq w x *
      lpfFiniteTransform V freq' w' x) t =
      Finset.sum U (fun i => Finset.sum V (fun j =>
        if freq i + freq' j = t then w i * w' j else 0)) := by
  have hNc : Not ((N : Complex) = 0) := by exact_mod_cast (NeZero.ne N)
  have hExpand (x : ZMod N) :
      lpfFiniteTransform U freq w x * lpfFiniteTransform V freq' w' x *
          ZMod.stdAddChar (t * (-x)) =
      Finset.sum U (fun i => Finset.sum V (fun j => (w i * w' j) *
        (ZMod.stdAddChar (x * (freq i + freq' j)) *
          (starRingEnd Complex) (ZMod.stdAddChar (x * t))))) := by
    simp only [lpfFiniteTransform]
    rw [Finset.sum_mul_sum]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [show x * (freq i + freq' j) = x * freq i + x * freq' j by ring,
      AddChar.map_add_eq_mul, show t * (-x) = -(x * t) by ring,
      AddChar.map_neg_eq_conj]
    ring
  have hSum : Finset.sum Finset.univ (fun x : ZMod N =>
      lpfFiniteTransform U freq w x * lpfFiniteTransform V freq' w' x *
        ZMod.stdAddChar (t * (-x))) =
      (N : Complex) * Finset.sum U (fun i => Finset.sum V (fun j =>
        if freq i + freq' j = t then w i * w' j else 0)) := by
    simp_rw [hExpand]
    rw [Finset.sum_comm]
    have hInner (i : I) :
        Finset.sum Finset.univ (fun x : ZMod N => Finset.sum V (fun j => (w i * w' j) *
          (ZMod.stdAddChar (x * (freq i + freq' j)) *
            (starRingEnd Complex) (ZMod.stdAddChar (x * t))))) =
        (N : Complex) * Finset.sum V (fun j =>
          if freq i + freq' j = t then w i * w' j else 0) := by
      rw [Finset.sum_comm]
      simp_rw [<- Finset.mul_sum,
        AddChar.sum_crossPhase (ZMod.stdAddChar (N := N)) (ZMod.isPrimitive_stdAddChar N),
        ZMod.card]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> ring
    simp_rw [hInner]
    rw [Finset.mul_sum]
  simp only [lpfCyclicInverse, zpow_neg_one]
  rw [hSum]
  simp [hNc]

/-- A checked no-wrap domain converts the cyclic identity into an integer pair sum. -/
theorem lpfCyclicInverse_integer_product {N : Nat} [NeZero N]
    (U V : Finset Nat) (w w' : Nat -> Complex) (t : Nat) (ht : t < N)
    (hSum : forall i, Membership.mem U i -> forall j, Membership.mem V j -> i + j < N) :
    lpfCyclicInverse (fun x => lpfFiniteTransform U (fun i => (i : ZMod N)) w x *
      lpfFiniteTransform V (fun j => (j : ZMod N)) w' x) (t : ZMod N) =
      Finset.sum U (fun i => Finset.sum V (fun j =>
        if i + j = t then w i * w' j else 0)) := by
  rw [lpfCyclicInverse_finite_product]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hEq : (i : ZMod N) + (j : ZMod N) = (t : ZMod N) <-> i + j = t := by
    constructor
    next =>
      intro h
      rw [<- Nat.cast_add] at h
      have hVal := congrArg (fun z : ZMod N => z.val) h
      simpa only [ZMod.val_natCast_of_lt (hSum i hi j hj),
        ZMod.val_natCast_of_lt ht] using hVal
    next =>
      intro h
      rw [<- Nat.cast_add, h]
  simp only [hEq]

/-- Restricted-frequency Parseval keeps the input squared weights exactly. -/
theorem lpfFiniteTransform_parseval {I : Type*} {N : Nat} [NeZero N]
    (U : Finset I) (freq : I -> ZMod N) (w : I -> Complex)
    (hinj : Set.InjOn freq (U : Set I)) :
    Finset.sum Finset.univ (fun x : ZMod N => Complex.normSq (lpfFiniteTransform U freq w x)) =
      (N : Real) * Finset.sum U (fun i => Complex.normSq (w i)) := by
  have hInj : Function.Injective (fun i : {i // Membership.mem U i} => freq i.val) := by
    intro i j h
    exact Subtype.ext (hinj i.property j.property h)
  have hP := AddChar.sum_normSq_fourier_injective
    (ZMod.stdAddChar (N := N)) (ZMod.isPrimitive_stdAddChar N)
    (fun i : {i // Membership.mem U i} => freq i.val) hInj (fun i => w i.val)
  have hAttach {K : Type} [AddCommMonoid K] (a : I -> K) :
      Finset.sum Finset.univ (fun i : {i // Membership.mem U i} => a i.val) =
        Finset.sum U a := by
    apply Finset.sum_bij (fun i _ => i.val)
    next => intro i _; exact i.property
    next => intro i _ j _ h; exact Subtype.ext h
    next =>
      intro i hi
      let j : {i // Membership.mem U i} := Subtype.mk i hi
      exact Exists.intro j (Exists.intro (Finset.mem_univ j) rfl)
    next => intro i _; rfl
  have hC (x : ZMod N) : Finset.sum Finset.univ
      (fun i : {i // Membership.mem U i} => w i.val * ZMod.stdAddChar (x * freq i.val)) =
      lpfFiniteTransform U freq w x := hAttach (fun i => w i * ZMod.stdAddChar (x * freq i))
  have hR : Finset.sum Finset.univ
      (fun i : {i // Membership.mem U i} => Complex.normSq (w i.val)) =
      Finset.sum U (fun i => Complex.normSq (w i)) := hAttach (fun i => Complex.normSq (w i))
  simp_rw [hC] at hP
  rw [hR] at hP
  simpa only [ZMod.card] using hP

/-- A uniform error acts on the coupled square difference, with both costs retained. -/
theorem lpfCyclicInverse_major_error_bound {N : Nat} [NeZero N]
    (S A : ZMod N -> Complex) (G T : Finset (ZMod N)) (E : Real) (hE : 0 <= E)
    (hError : forall x, Membership.mem G x -> norm (S x - A x) <= E) :
    Finset.sum T (fun t => Complex.normSq (lpfCyclicInverse
      (fun x => if Membership.mem G x then S x ^ 2 - A x ^ 2 else 0) t)) <=
      (N : Real) ^ (-1 : Int) * (8 * E ^ 2 * Finset.sum G
        (fun x => Complex.normSq (A x)) + 2 * E ^ 4 * (G.card : Real)) := by
  have hTerm (x : ZMod N) (hx : Membership.mem G x) :
      Complex.normSq (2 * A x * (S x - A x) + (S x - A x) ^ 2) <=
      8 * E ^ 2 * Complex.normSq (A x) + 2 * E ^ 4 := by
    have hd := hError x hx
    have hAn := norm_nonneg (A x)
    have hdn := norm_nonneg (S x - A x)
    have hds : norm (S x - A x) ^ 2 <= E ^ 2 := by nlinarith
    have hMul := mul_le_mul_of_nonneg_left hd (by positivity : 0 <= 2 * norm (A x))
    have hAdd := norm_add_le (2 * A x * (S x - A x)) ((S x - A x) ^ 2)
    simp only [norm_mul, norm_pow, Complex.norm_ofNat] at hAdd
    have hNorm : norm (2 * A x * (S x - A x) + (S x - A x) ^ 2) <=
        2 * norm (A x) * E + E ^ 2 := by nlinarith only [hAdd, hMul, hds]
    have hSq := mul_le_mul hNorm hNorm (norm_nonneg _) (by positivity)
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    nlinarith only [hSq, sq_nonneg (2 * norm (A x) * E - E ^ 2)]
  have hSum := Finset.sum_le_sum hTerm
  have hNorm : Finset.sum G
      (fun x => 8 * E ^ 2 * Complex.normSq (A x) + 2 * E ^ 4) =
      8 * E ^ 2 * Finset.sum G (fun x => Complex.normSq (A x)) +
        2 * E ^ 4 * (G.card : Real) := by
    simp only [Finset.sum_add_distrib, <- Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hNorm] at hSum
  exact (lpfCyclicInverse_square_difference_bessel S A G T).trans
    (mul_le_mul_of_nonneg_left hSum (by positivity))

end PrimeFactorOscillations.LPF
