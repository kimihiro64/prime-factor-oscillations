/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.FibonacciProbability
import PrimeFactorOscillations.Mathlib.NumberTheory.Primes.FermatCarrierProbability

/-!
# A common-index Fibonacci and Fermat probability law

The scalar index is uniform modulo 2^k times a product of odd index primes.
The full nested Fermat block is independent of every Fibonacci bit pattern.
Internal Fermat events remain nested. Both event families are evaluated at
the same integer representative; the CRT factorization is proved explicitly.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.FermatFibonacciProbability

local instance (S : Finset Nat.Primes) :
    NeZero (CyclotomicProbability.sampleModulus S) :=
  NeZero.mk (by
    unfold CyclotomicProbability.sampleModulus
    apply Finset.prod_ne_zero_iff.mpr
    intro p _
    exact p.val.property.ne_zero)

local instance (k : Nat) : NeZero (2 ^ k) :=
  NeZero.mk (pow_ne_zero k (by decide : Not ((2 : Nat) = 0)))

local instance (k : Nat) (S : Finset Nat.Primes) :
    NeZero (2 ^ k * CyclotomicProbability.sampleModulus S) :=
  NeZero.mk (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _))

private theorem dyadicCount_mod (k n : Nat) :
    Nat.truncatedDyadicCount k (n % 2 ^ k) = Nat.truncatedDyadicCount k n := by
  unfold Nat.truncatedDyadicCount
  apply Finset.sum_congr rfl
  intro j hj
  have hd : Dvd.dvd (2 ^ (j + 1)) (2 ^ k) :=
    pow_dvd_pow 2 (Nat.succ_le_iff.mpr (Finset.mem_range.mp hj))
  simp only [Nat.dvd_mod_iff hd]

private theorem sum_zmod_val {K : Type*} [AddCommMonoid K]
    (m : Nat) [NeZero m] (f : Nat -> K) :
    Finset.sum Finset.univ (fun u : ZMod m => f u.val) =
      (Finset.range m).sum f := by
  cases m with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ m => exact Fin.sum_univ_eq_sum_range f (m + 1)

/-- The actual two sampling periods are coprime, including empty odd support. -/
theorem jointPeriod_coprime (k : Nat) (S : Finset Nat.Primes)
    (hodd : forall p, Membership.mem S p -> 3 <= (p : Nat)) :
    Nat.Coprime (2 ^ k) (CyclotomicProbability.sampleModulus S) := by
  apply Nat.Coprime.pow_left k
  unfold CyclotomicProbability.sampleModulus
  apply Nat.Coprime.prod_right
  intro p _
  apply Nat.coprime_two_left.mpr
  apply p.val.property.odd_of_ne_two
  exact Nat.ne_of_gt (lt_of_lt_of_le (by decide : 2 < 3) (hodd p.val p.property))

/-- A weighted count of actual paired events at a single sampled index. -/
def actualJointSum {K : Type*} [CommSemiring K] (k : Nat)
    (S : Finset Nat.Primes) (bits : S -> Bool) (z : K) : K := by
  classical
  exact Finset.sum Finset.univ
    (fun u : ZMod (2 ^ k * CyclotomicProbability.sampleModulus S) =>
      if (forall p : S, if bits p then
        Dvd.dvd (Nat.fibonacciPrimeCarrier (p.val : Nat)) (Nat.fib u.val)
      else Not (Dvd.dvd (Nat.fibonacciPrimeCarrier (p.val : Nat)) (Nat.fib u.val)))
      then z ^ Nat.fermatCarrierCount k u.val else 0)

/-- Pointwise compatibility of the actual scalar events with the CRT coordinates. -/
theorem actual_summand_eq {K : Type*} [CommSemiring K] (k : Nat)
    (S : Finset Nat.Primes)
    (hodd : forall p, Membership.mem S p -> 3 <= (p : Nat))
    (bits : S -> Bool) (z : K)
    (u : ZMod (2 ^ k * CyclotomicProbability.sampleModulus S)) :
    (if (forall p : S, if bits p then
      Dvd.dvd (Nat.fibonacciPrimeCarrier (p.val : Nat)) (Nat.fib u.val)
    else Not (Dvd.dvd (Nat.fibonacciPrimeCarrier (p.val : Nat)) (Nat.fib u.val)))
    then z ^ Nat.fermatCarrierCount k u.val else 0) =
      if Membership.mem (FibonacciProbability.jointSet S bits)
        ((ZMod.chineseRemainder (jointPeriod_coprime k S hodd)) u).2
      then z ^ Nat.truncatedDyadicCount k
        (((ZMod.chineseRemainder (jointPeriod_coprime k S hodd)) u).1.val) else 0 := by
  classical
  let e := ZMod.chineseRemainder (jointPeriod_coprime k S hodd)
  have he : e (u.val : ZMod (2 ^ k * CyclotomicProbability.sampleModulus S)) =
      ((u.val : ZMod (2 ^ k)), (u.val : ZMod (CyclotomicProbability.sampleModulus S))) :=
    map_natCast e u.val
  rw [ZMod.natCast_zmod_val] at he
  have hf : (e u).1 = (u.val : ZMod (2 ^ k)) := congrArg Prod.fst he
  have hs : (e u).2 =
      (u.val : ZMod (CyclotomicProbability.sampleModulus S)) := congrArg Prod.snd he
  have hc : Nat.fermatCarrierCount k u.val =
      Nat.truncatedDyadicCount k (e u).1.val := by
    rw [Nat.fermatCarrierCount_eq_dyadic, hf, ZMod.val_natCast, dyadicCount_mod]
  change _ = if Membership.mem (FibonacciProbability.jointSet S bits) (e u).2
    then z ^ Nat.truncatedDyadicCount k (e u).1.val else 0
  have hp : Membership.mem (FibonacciProbability.jointSet S bits) (e u).2 <->
      (forall p : S, if bits p then
        Dvd.dvd (Nat.fibonacciPrimeCarrier (p.val : Nat)) (Nat.fib u.val)
      else Not (Dvd.dvd (Nat.fibonacciPrimeCarrier (p.val : Nat)) (Nat.fib u.val))) := by
    rw [hs]
    exact FibonacciProbability.jointSet_natCast_mem S hodd bits u.val
  by_cases hB : Membership.mem (FibonacciProbability.jointSet S bits) (e u).2
  { have hA := hp.mp hB
    rw [ite_eq_left hA, ite_eq_left hB, hc] }
  { have hA := mt hp.mpr hB
    rw [ite_eq_right hA, ite_eq_right hB] }

/-- The complete signed-pattern generating sum factors under scalar sampling. -/
theorem actualJointSum_factor {K : Type*} [CommSemiring K] (k : Nat)
    (S : Finset Nat.Primes)
    (hodd : forall p, Membership.mem S p -> 3 <= (p : Nat))
    (bits : S -> Bool) (z : K) :
    actualJointSum k S bits z =
      FermatProbability.sampleSum k z * ((FibonacciProbability.jointSet S bits).card : K) := by
  classical
  let e := ZMod.chineseRemainder (jointPeriod_coprime k S hodd)
  let B := FibonacciProbability.jointSet S bits
  have hb (a : ZMod (2 ^ k)) :
      Finset.sum Finset.univ (fun b : ZMod (CyclotomicProbability.sampleModulus S) =>
        if Membership.mem B b then z ^ Nat.truncatedDyadicCount k a.val else 0) =
      (B.card : K) * z ^ Nat.truncatedDyadicCount k a.val := by
    have hB : Finset.univ.filter (fun b => Membership.mem B b) = B := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [<- Finset.sum_filter, hB, Finset.sum_const, nsmul_eq_mul]
  let g : Prod (ZMod (2 ^ k)) (ZMod (CyclotomicProbability.sampleModulus S)) -> K :=
    fun v => if Membership.mem B v.2 then
      z ^ Nat.truncatedDyadicCount k v.1.val else 0
  have he : actualJointSum k S bits z = Finset.sum Finset.univ g := by
    calc
      actualJointSum k S bits z =
          Finset.sum Finset.univ (fun u => g (e.toEquiv u)) := by
            unfold actualJointSum
            exact Finset.sum_congr rfl (fun u _ => actual_summand_eq k S hodd bits z u)
      _ = Finset.sum Finset.univ g := e.toEquiv.sum_comp g
  have hprod : Finset.sum Finset.univ g =
      Finset.sum Finset.univ (fun a : ZMod (2 ^ k) =>
        (B.card : K) * z ^ Nat.truncatedDyadicCount k a.val) := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl (fun a _ => hb a)
  calc
    actualJointSum k S bits z = Finset.sum Finset.univ g := he
    _ = Finset.sum Finset.univ (fun a : ZMod (2 ^ k) =>
        (B.card : K) * z ^ Nat.truncatedDyadicCount k a.val) := hprod
    _ = (B.card : K) * FermatProbability.sampleSum k z := by
      rw [<- Finset.mul_sum]
      exact congrArg (fun t : K => (B.card : K) * t)
        (sum_zmod_val (2 ^ k) (fun n => z ^ Nat.truncatedDyadicCount k n))
    _ = FermatProbability.sampleSum k z * (B.card : K) := mul_comm _ _

/-- The actual probability-weighted PGF of a prescribed Fibonacci pattern. -/
def actualJointPGF (k : Nat) (S : Finset Nat.Primes)
    (bits : S -> Bool) (z : Real) : Real :=
  actualJointSum k S bits z /
    ((2 ^ k * CyclotomicProbability.sampleModulus S : Nat) : Real)

/-- Exact independence of the dyadic block and the entire odd-prime pattern. -/
theorem actualJointPGF_eq_product (k : Nat) (S : Finset Nat.Primes)
    (hodd : forall p, Membership.mem S p -> 3 <= (p : Nat))
    (bits : S -> Bool) (z : Real) :
    actualJointPGF k S bits z = FermatProbability.samplePGF k z *
      Finset.prod Finset.univ (fun p : S =>
        if bits p then 1 / ((p.val : Nat) : Real)
        else 1 - 1 / ((p.val : Nat) : Real)) := by
  rw [<- FibonacciProbability.jointProbability_eq_product]
  unfold actualJointPGF FermatProbability.samplePGF FibonacciProbability.jointProbability
  rw [actualJointSum_factor k S hodd bits z, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  exact (div_mul_div_comm _ _ _ _).symm

end PrimeFactorOscillations.FermatFibonacciProbability
