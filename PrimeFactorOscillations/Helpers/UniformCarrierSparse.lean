/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.UniformCarrierInverse

/-!
# Uniform Carrier Sparse

Sparse high-prime carrier perturbations with error controlled by the square-weight sum.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.UniformCarrier

theorem canonical_compensator_eq_weight (law : PrimeClockLaw) (he : law.error = 0)
    (p : Nat.Primes) : law.compensator p = law.weight p := by
  have h := law.quadratic_error p
  rw [he, zero_mul] at h
  exact (sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))).symm

theorem canonical_compensator_le (law : PrimeClockLaw)
    (hs : law.scale = 1) (he : law.error = 0) (p : Nat.Primes) :
    law.compensator p <= primeProfileWeight (p : Nat) := by
  simpa only [hs, one_mul] using law.compensator_le p

theorem clock_difference_eq (A B : PrimeClockLaw) (N : Nat)
    (T : Finset Nat.Primes) (hT : T <= primeProfilePrefixSet N)
    (hSame : forall p, Membership.mem (primeProfilePrefixSet N \ T) p ->
      A.compensator p = B.compensator p) :
    A.arithmeticClock N - B.arithmeticClock N =
      T.sum (fun p => A.compensator p - B.compensator p) := by
  classical
  unfold PrimeClockLaw.arithmeticClock
  rw [<- Finset.sum_sub_distrib]
  symm
  apply Finset.sum_subset hT
  intro p hp hpT
  exact sub_eq_zero.mpr (hSame p (Finset.mem_sdiff.mpr (And.intro hp hpT)))

theorem clock_difference_bound (A B : PrimeClockLaw)
    (hAs : A.scale = 1) (hAe : A.error = 0) (hBs : B.scale = 1) (hBe : B.error = 0)
    (N : Nat) (T : Finset Nat.Primes) (hT : T <= primeProfilePrefixSet N)
    (hSame : forall p, Membership.mem (primeProfilePrefixSet N \ T) p ->
      A.compensator p = B.compensator p) :
    abs (A.arithmeticClock N - B.arithmeticClock N) <=
      T.sum (fun p => primeProfileWeight (p : Nat)) := by
  rw [clock_difference_eq A B N T hT hSame]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  have hA := canonical_compensator_le A hAs hAe p
  have hB := canonical_compensator_le B hBs hBe p
  have hA0 := A.compensator_nonneg p
  have hB0 := B.compensator_nonneg p
  apply abs_le.mpr
  constructor <;> linarith only [hA, hB, hA0, hB0]

theorem prime_weight_le_inv (P : Nat) (hP : 1 <= P) (p : Nat.Primes) (hp : P < (p : Nat)) :
    primeProfileWeight (p : Nat) <= 1 / (P : Real) := by
  have hPpos : (0 : Real) < P := by exact_mod_cast Nat.zero_lt_one.trans_le hP
  have hpred : P <= (p : Nat) - 1 := by omega
  have hpredR : (P : Real) <= ((p : Nat) - 1 : Nat) := by exact_mod_cast hpred
  exact one_div_le_one_div_of_le hPpos hpredR

theorem sparse_weight_sums (P : Nat) (hP : 1 <= P) (T : Finset Nat.Primes)
    (hprime : forall p, Membership.mem T p -> P < (p : Nat)) :
    T.sum (fun p => primeProfileWeight (p : Nat)) <= (T.card : Real) / P /\
    T.sum (fun p => (primeProfileWeight (p : Nat)) ^ 2) <= (T.card : Real) / (P : Real) ^ 2 := by
  constructor
  . calc
      _ <= T.sum (fun _ => 1 / (P : Real)) :=
        Finset.sum_le_sum (fun p hp => prime_weight_le_inv P hP p (hprime p hp))
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  . calc
      _ <= T.sum (fun _ => (1 / (P : Real)) ^ 2) := by
        apply Finset.sum_le_sum
        intro p hp
        have hv := prime_weight_le_inv P hP p (hprime p hp)
        have hv0 := primeProfileWeight_nonneg (p : Nat)
        have hP0 : 0 <= 1 / (P : Real) := by positivity
        nlinarith
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

theorem exists_uniform_carrier_inverse (base : PrimeClockLaw)
    (hbs : base.scale = 1) (hbe : base.error = 0)
    (a : Real) (ha : 0 < a) (b : Real) (hb : 0 < b) :
    exists r0 N0 P0 : Nat, exists C : Real,
      0 < r0 /\ 1 <= N0 /\ 1 <= P0 /\ 0 < C /\
      forall r : Nat, r0 <= r -> forall N : Nat, N0 <= N ->
      3 <= base.arithmeticClock N ->
      a <= (r : Real) / (base.arithmeticClock N + 1) ->
      (r : Real) / (base.arithmeticClock N - 1) <= b ->
      forall P : Nat, P0 <= P ->
      forall A : PrimeClockLaw, A.scale = 1 -> A.error = 0 ->
      forall T : Finset Nat.Primes, T <= primeProfilePrefixSet N ->
      (forall p, Membership.mem T p -> P < (p : Nat)) ->
      T.card <= P / 100 ->
      (forall p, Membership.mem (primeProfilePrefixSet N \ T) p ->
        A.weight p = base.weight p /\ A.compensator p = base.compensator p) ->
      exists U : Real,
        abs (U - A.arithmeticClock N) <= C * (T.card : Real) / (P : Real) ^ 2 /\
        A.densityRatio N r = prefixRatio base N r U /\
        (forall V : Real, abs (V - base.arithmeticClock N) <= 1 ->
          A.densityRatio N r = prefixRatio base N r V -> V = U) /\
        abs (U - base.arithmeticClock N) <= 1 / 2 := by
  choose r0 N0 eps C hr0 hN0 heps hC hInv using
    exists_uniform_reference_inverse base hbs hbe a ha b hb
  choose PP hPP using exists_nat_gt (1 / eps)
  let P0 := max 1 PP
  refine Exists.intro r0 (Exists.intro N0 (Exists.intro P0
    (Exists.intro C (And.intro hr0 (And.intro hN0
      (And.intro (le_max_left _ _) (And.intro hC ?_)))))))
  intro r hr N hN hB hLower hUpper P hP A hAs hAe T hT hprime hcard hSame
  have hP1 : 1 <= P := (le_max_left _ _).trans hP
  have hPpos : (0 : Real) < P := by exact_mod_cast Nat.zero_lt_one.trans_le hP1
  have hPPR : (PP : Real) <= P := by
    exact_mod_cast (le_max_right _ _).trans hP
  have hlarge : 1 / eps < (P : Real) := hPP.trans_le hPPR
  have hinv : 1 / (P : Real) <= eps := by
    have hm := mul_lt_mul_of_pos_right hlarge heps
    have hc : 1 / eps * eps = 1 := by field_simp
    rw [hc] at hm
    calc
      _ <= (eps * P) / P := div_le_div_of_nonneg_right (by linarith : (1 : Real) <= eps * P) hPpos.le
      _ = eps := by field_simp
  have hsums := sparse_weight_sums P hP1 T hprime
  have hcNat : 100 * T.card <= P := by omega
  have hcR : (100 : Real) * (T.card : Real) <= P := by exact_mod_cast hcNat
  have hcardR : (T.card : Real) <= (P : Real) / 100 := by linarith only [hcR]
  have hfirst : (T.card : Real) / P <= (1 / 100 : Real) := by
    calc
      _ <= ((P : Real) / 100) / P := div_le_div_of_nonneg_right hcardR hPpos.le
      _ = _ := by field_simp
  have hsecond : (T.card : Real) / (P : Real) ^ 2 <= eps := by
    calc
      _ <= ((P : Real) / 100) / (P : Real) ^ 2 :=
        div_le_div_of_nonneg_right hcardR (sq_nonneg _)
      _ <= 1 / (P : Real) := by
        have hid : ((P : Real) / 100) / (P : Real) ^ 2 = (1 / 100 : Real) / P := by field_simp
        rw [hid]
        exact div_le_div_of_nonneg_right (by norm_num) hPpos.le
      _ <= eps := hinv
  have hNear : abs (A.arithmeticClock N - base.arithmeticClock N) <= 1 / 4 :=
    ((clock_difference_bound A base hAs hAe hbs hbe N T hT
      (fun p hp => (hSame p hp).2)).trans hsums.1).trans
        (hfirst.trans (by norm_num))
  choose U hU hBasePos hRoot hUnique using hInv r hr N hN hB hLower hUpper
    A hAs hAe T hT hSame (hsums.2.trans hsecond) hNear
  refine Exists.intro U (And.intro ?_ (And.intro hRoot (And.intro hUnique.1 hUnique.2)))
  calc
    _ <= C * T.sum (fun p => (primeProfileWeight (p : Nat)) ^ 2) := hU
    _ <= C * ((T.card : Real) / (P : Real) ^ 2) :=
      mul_le_mul_of_nonneg_left hsums.2 hC.le
    _ = _ := by ring

end PrimeFactorOscillations.UniformCarrier
