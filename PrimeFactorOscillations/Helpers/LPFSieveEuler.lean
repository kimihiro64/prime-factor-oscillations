/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFSieveCollisions

/-!
# A logarithmic lower bound for the upper-sieve Euler product

The primes 2 and 3 are removed explicitly. The positive constant is independent
of the prime cutoff and of the natural power of the Euler product.
-/

namespace PrimeFactorOscillations.LPF

def sievePrimeCutoff (z : Nat) : Finset Nat :=
  (Nat.primesBelow (z + 1)).filter (fun p => 5 <= p)

theorem mem_sievePrimeCutoff {z p : Nat} :
    Membership.mem (sievePrimeCutoff z) p <->
      And (Nat.Prime p) (And (5 <= p) (p <= z)) := by
  simp only [sievePrimeCutoff, Finset.mem_filter, Nat.mem_primesBelow]
  constructor
  next =>
    intro h
    exact And.intro h.1.2 (And.intro h.2 (by omega))
  next =>
    intro h
    exact And.intro (And.intro (by omega) h.1) h.2.1

noncomputable def sieveMertensConstant : Real :=
  Real.exp (Mertens.M - PrimeFactorUnimodality.mertensErrorConstant / Real.log 2 - 1)

theorem sieveMertensConstant_pos : 0 < sieveMertensConstant := Real.exp_pos _

/-- Removing the two excluded small primes costs at most one in the reciprocal sum. -/
theorem sieve_prime_reciprocal_lower_bound (z : Nat) (hz : 5 <= z) :
    Real.log (Real.log (z : Real)) + Mertens.M -
      PrimeFactorUnimodality.mertensErrorConstant / Real.log 2 - 1 <=
      Finset.sum (sievePrimeCutoff z) (fun p => 1 / (p : Real)) := by
  classical
  let R := Nat.primesBelow (z + 1)
  let B := R.filter (fun p => Not (5 <= p))
  have hSub : B <= Nat.primesBelow 5 := by
    intro p hp
    have h := Finset.mem_filter.mp hp
    have hPrime := (Nat.mem_primesBelow.mp h.1).2
    exact Nat.mem_primesBelow.mpr (And.intro (by omega) hPrime)
  have hSmall : Finset.sum B (fun p => 1 / (p : Real)) <= 1 := by
    calc
      _ <= Finset.sum (Nat.primesBelow 5) (fun p => 1 / (p : Real)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hSub
          (fun p _ _ => div_nonneg zero_le_one (Nat.cast_nonneg p))
      _ <= 1 := by
        have hSet : Nat.primesBelow 5 = {2, 3} := by decide
        rw [hSet]
        norm_num
  have hPartition : Finset.sum (sievePrimeCutoff z) (fun p => 1 / (p : Real)) +
      Finset.sum B (fun p => 1 / (p : Real)) = Finset.sum R (fun p => 1 / (p : Real)) :=
    Finset.sum_filter_add_sum_filter_not R (fun p => 5 <= p) _
  have hMertens := PrimeFactorUnimodality.reciprocalPrimeSumBelow_lower_of_estimate
    PrimeFactorUnimodality.hasMertensReciprocalPrimeEstimate (show 2 <= z by omega)
  change Real.log (Real.log (z : Real)) + Mertens.M -
    PrimeFactorUnimodality.mertensErrorConstant / Real.log (z : Real) <=
      Finset.sum R (fun p => 1 / (p : Real)) at hMertens
  have hLog2 : (0 : Real) < Real.log 2 := Real.log_pos (by norm_num)
  have hLog : Real.log 2 <= Real.log (z : Real) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 <= z by omega))
  have hError := div_le_div_of_nonneg_left
    PrimeFactorUnimodality.mertensErrorConstant_nonneg hLog2 hLog
  linarith

private theorem reciprocal_le_log_euler (x : Real) (hx : 5 <= x) :
    1 / x <= Real.log (x / (x - 1)) := by
  have hxPos : 0 < x := by linarith
  have hx1 : 0 < x - 1 := by linarith
  have hMul : x * (1 - 1 / x) = x - 1 := by field_simp
  have hY : 0 < 1 - 1 / x := by nlinarith
  have hLog := Real.log_le_sub_one_of_pos hY
  have hInv : x / (x - 1) = Inv.inv (1 - 1 / x) := by field_simp <;> ring
  rw [hInv, Real.log_inv]
  linarith

/-- A uniform positive multiple of log z is retained after excluding primes 2 and 3. -/
theorem sieve_euler_log_lower_bound (z : Nat) (hz : 5 <= z) :
    sieveMertensConstant * Real.log (z : Real) <=
      Finset.prod (sievePrimeCutoff z) (fun p => (p : Real) / ((p : Real) - 1)) := by
  classical
  let f := fun p : Nat => (p : Real) / ((p : Real) - 1)
  have hPos : forall p, Membership.mem (sievePrimeCutoff z) p -> 0 < f p := by
    intro p hp
    have h5 : (5 : Real) <= (p : Real) := by exact_mod_cast (mem_sievePrimeCutoff.mp hp).2.1
    exact div_pos (by linarith) (by linarith)
  have hLog : Finset.sum (sievePrimeCutoff z) (fun p => 1 / (p : Real)) <=
      Real.log (Finset.prod (sievePrimeCutoff z) f) := by
    rw [Real.log_prod (fun p hp => ne_of_gt (hPos p hp))]
    exact Finset.sum_le_sum (fun p hp => reciprocal_le_log_euler (p : Real)
      (by exact_mod_cast (mem_sievePrimeCutoff.mp hp).2.1))
  have hLower := (sieve_prime_reciprocal_lower_bound z hz).trans hLog
  have hLogZ : 0 < Real.log (z : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  calc
    _ = Real.exp (Real.log (Real.log (z : Real)) + Mertens.M -
        PrimeFactorUnimodality.mertensErrorConstant / Real.log 2 - 1) := by
      rw [show Real.log (Real.log (z : Real)) + Mertens.M -
          PrimeFactorUnimodality.mertensErrorConstant / Real.log 2 - 1 =
        (Mertens.M - PrimeFactorUnimodality.mertensErrorConstant / Real.log 2 - 1) +
          Real.log (Real.log (z : Real)) by ring]
      rw [Real.exp_add, Real.exp_log hLogZ]
      rfl
    _ <= Real.exp (Real.log (Finset.prod (sievePrimeCutoff z) f)) :=
      Real.exp_le_exp.mpr hLower
    _ = _ := Real.exp_log (Finset.prod_pos hPos)

/-- The same cutoff constant works at every natural power, including zero. -/
theorem sieve_euler_log_power_lower_bound (z k : Nat) (hz : 5 <= z) :
    sieveMertensConstant ^ k * Real.log (z : Real) ^ k <=
      Finset.prod (sievePrimeCutoff z) (fun p => ((p : Real) / ((p : Real) - 1)) ^ k) := by
  have hBase := sieve_euler_log_lower_bound z hz
  have hLeft : 0 <= sieveMertensConstant * Real.log (z : Real) :=
    mul_nonneg (le_of_lt sieveMertensConstant_pos)
      (Real.log_nonneg (by exact_mod_cast (show 1 <= z by omega)))
  have hRight := hLeft.trans hBase
  have hPow : forall k : Nat,
      (sieveMertensConstant * Real.log (z : Real)) ^ k <=
        (Finset.prod (sievePrimeCutoff z) (fun p => (p : Real) / ((p : Real) - 1))) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_succ]
      exact mul_le_mul ih hBase hLeft (pow_nonneg hRight k)
  simpa only [mul_pow, Finset.prod_pow] using hPow k

theorem threeResidue_log_euler_lower_bound (z t s : Nat) (hz : 5 <= z)
    (ht : 0 < t) (hs : 0 < s) (hne : Not (t = s)) :
    sieveMertensConstant ^ 3 * Real.log (z : Real) ^ 3 <=
      sieveEulerProduct (sievePrimeCutoff z)
        (fun p => ({0, (t : ZMod p), (s : ZMod p)} : Finset (ZMod p))) *
      (singularDivisorProduct t * singularDivisorProduct s *
        singularDivisorProduct ((t - s) + (s - t))) :=
  (sieve_euler_log_power_lower_bound z 3 hz).trans
    (threeResidue_eulerProduct_lower_bound (sievePrimeCutoff z) t s ht hs hne
      (fun p hp => And.intro (mem_sievePrimeCutoff.mp hp).1 (mem_sievePrimeCutoff.mp hp).2.1))

theorem twoResidue_log_euler_lower_bound (z t : Nat) (hz : 5 <= z) (ht : 0 < t) :
    sieveMertensConstant ^ 2 * Real.log (z : Real) ^ 2 <=
      sieveEulerProduct (sievePrimeCutoff z)
        (fun p => ({0, (t : ZMod p)} : Finset (ZMod p))) * singularDivisorProduct t :=
  (sieve_euler_log_power_lower_bound z 2 hz).trans
    (twoResidue_eulerProduct_lower_bound (sievePrimeCutoff z) t ht
      (fun p hp => And.intro (mem_sievePrimeCutoff.mp hp).1 (mem_sievePrimeCutoff.mp hp).2.1))

private theorem quotient_bound_of_product (K T H G : Real)
    (hK : 0 <= K) (hT : 0 < T) (hH : 0 < H) (hProd : H <= T * G) :
    K / T <= K * G / H := by
  have hneT : Not (T = 0) := ne_of_gt hT
  have hneH : Not (H = 0) := ne_of_gt hH
  apply (mul_le_mul_iff_of_pos_right (mul_pos hT hH)).mp
  field_simp
  have h := mul_le_mul_of_nonneg_left hProd hK
  nlinarith only [h]

/-- Uniform three-form sifted bound with all full singular factors retained. -/
theorem sifted_threeResidue_card_le (z t s : Nat)
    (hz : 5 <= z) (ht : 0 < t) (hs : 0 < s) (hne : Not (t = s))
    (X : Finset Nat) {N Q : Nat} (hN : 0 < N) (hQ : 1 < Q)
    (hX : X <= Finset.range N)
    (hAvoid : forall k, Membership.mem X k -> forall p,
      Membership.mem (sievePrimeCutoff z) p ->
      Not (Membership.mem ({0, (t : ZMod p), (s : ZMod p)} : Finset (ZMod p)) (k : ZMod p)))
    (hPower : z ^ 4 <= Q) :
    (X.card : Real) <=
      144 * ((N : Real) + (Q : Real) ^ 2) *
        (singularDivisorProduct t * singularDivisorProduct s *
          singularDivisorProduct ((t - s) + (s - t))) /
      (sieveMertensConstant ^ 3 * Real.log (z : Real) ^ 3) := by
  classical
  let P := sievePrimeCutoff z
  let A := fun p => ({0, (t : ZMod p), (s : ZMod p)} : Finset (ZMod p))
  have hP : forall p, Membership.mem P p -> Nat.Prime p /\ 5 <= p /\ p <= z :=
    fun p hp => mem_sievePrimeCutoff.mp hp
  have hA : forall p, Membership.mem P p -> And (0 < (A p).card) ((A p).card < p) := by
    intro p hp
    have h := threeResidue_card_bounds p (t : ZMod p) (s : ZMod p)
    exact And.intro h.1 (by have hp5 := (mem_sievePrimeCutoff.mp hp).2.1; dsimp [A]; omega)
  have hCard : forall p, Membership.mem P p -> (A p).card <= 3 :=
    fun p _ => (threeResidue_card_bounds p (t : ZMod p) (s : ZMod p)).2
  have hSieve := sieve_card_le_euler_of_sharp_cutoff P A z 3 hz (by decide) hP hA hCard
    X hN hQ hX hAvoid hPower
  norm_num at hSieve
  have hLower := threeResidue_log_euler_lower_bound z t s hz ht hs hne
  have hC := sieveMertensConstant_pos
  have hLog : 0 < Real.log (z : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  exact hSieve.trans (quotient_bound_of_product _ _ _ _ (by positivity)
    (sieveEulerProduct_pos P A hA) (by positivity) hLower)

/-- Uniform two-form sifted bound with its full singular factor retained. -/
theorem sifted_twoResidue_card_le (z t : Nat) (hz : 5 <= z) (ht : 0 < t)
    (X : Finset Nat) {N Q : Nat} (hN : 0 < N) (hQ : 1 < Q)
    (hX : X <= Finset.range N)
    (hAvoid : forall k, Membership.mem X k -> forall p,
      Membership.mem (sievePrimeCutoff z) p ->
      Not (Membership.mem ({0, (t : ZMod p)} : Finset (ZMod p)) (k : ZMod p)))
    (hPower : z ^ 4 <= Q) :
    (X.card : Real) <=
      72 * ((N : Real) + (Q : Real) ^ 2) * singularDivisorProduct t /
        (sieveMertensConstant ^ 2 * Real.log (z : Real) ^ 2) := by
  classical
  let P := sievePrimeCutoff z
  let A := fun p => ({0, (t : ZMod p)} : Finset (ZMod p))
  have hP : forall p, Membership.mem P p -> Nat.Prime p /\ 5 <= p /\ p <= z :=
    fun p hp => mem_sievePrimeCutoff.mp hp
  have hA : forall p, Membership.mem P p -> And (0 < (A p).card) ((A p).card < p) := by
    intro p hp
    have h := twoResidue_card_bounds p (t : ZMod p)
    exact And.intro h.1 (by have hp5 := (mem_sievePrimeCutoff.mp hp).2.1; dsimp [A]; omega)
  have hCard : forall p, Membership.mem P p -> (A p).card <= 2 :=
    fun p _ => (twoResidue_card_bounds p (t : ZMod p)).2
  have hSieve := sieve_card_le_euler_of_sharp_cutoff P A z 2 hz (by decide) hP hA hCard
    X hN hQ hX hAvoid hPower
  norm_num at hSieve
  have hLower := twoResidue_log_euler_lower_bound z t hz ht
  have hC := sieveMertensConstant_pos
  have hLog : 0 < Real.log (z : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  exact hSieve.trans (quotient_bound_of_product _ _ _ _ (by positivity)
    (sieveEulerProduct_pos P A hA) (by positivity) hLower)

end PrimeFactorOscillations.LPF
