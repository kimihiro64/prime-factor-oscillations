/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LcmZetaTail
import PrimeFactorOscillations.Helpers.PrimeProfileThetaClock

/-!
# The actual modified LCM and its exponent ledger

Start with lcm(1,...,N), and multiply once more by every prime satisfying
N < p^2 <= 2*N. This is the same explicit family used in the written
critical-window argument.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations

def modifiedLcmRaisedPrimes (N : Nat) : Finset Nat :=
  (Nat.primesLE N).filter (fun p => N < p ^ 2 /\ p ^ 2 <= 2 * N)

def modifiedLcm (N : Nat) : Nat :=
  Nat.lcmUpto N * (modifiedLcmRaisedPrimes N).prod id

theorem mem_modifiedLcmRaisedPrimes (N p : Nat) :
    Membership.mem (modifiedLcmRaisedPrimes N) p <->
      Nat.Prime p /\ N < p ^ 2 /\ p ^ 2 <= 2 * N := by
  constructor
  . intro h
    have hF := Finset.mem_filter.mp h
    exact And.intro (Nat.prime_of_mem_primesLE hF.1) hF.2
  . intro h
    have hpLe : p <= N := by nlinarith [h.1.two_le, h.2.2]
    apply Finset.mem_filter.mpr
    refine And.intro ?_ h.2
    rw [Nat.mem_primesLE]
    exact And.intro hpLe h.1

theorem modifiedLcmRaisedProduct_pos (N : Nat) :
    0 < (modifiedLcmRaisedPrimes N).prod id := by
  apply Finset.prod_pos
  intro p hp
  exact (mem_modifiedLcmRaisedPrimes N p |>.mp hp).1.pos

theorem modifiedLcm_pos (N : Nat) : 0 < modifiedLcm N :=
  mul_pos (Nat.lcmUpto_pos N) (modifiedLcmRaisedProduct_pos N)

theorem modifiedLcmRaisedProduct_factorization (N : Nat) (p : Nat) :
    ((modifiedLcmRaisedPrimes N).prod id).factorization p =
      if Membership.mem (modifiedLcmRaisedPrimes N) p then 1 else 0 := by
  rw [Nat.factorization_prod_apply (g := id) (fun q hq =>
    (mem_modifiedLcmRaisedPrimes N q |>.mp hq).1.ne_zero)]
  simp only [id_eq]
  have hSum : (modifiedLcmRaisedPrimes N).sum (fun q => q.factorization p) =
      (modifiedLcmRaisedPrimes N).sum (fun q => if q = p then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [(mem_modifiedLcmRaisedPrimes N q |>.mp hq).1.factorization,
      Finsupp.single_apply]
  rw [hSum]
  simp

theorem modifiedLcm_factorization (N : Nat) {p : Nat} (hp : Nat.Prime p) :
    (modifiedLcm N).factorization p =
      Nat.log p N + if Membership.mem (modifiedLcmRaisedPrimes N) p then 1 else 0 := by
  unfold modifiedLcm
  rw [Nat.factorization_mul (Nat.lcmUpto_ne_zero N) (modifiedLcmRaisedProduct_pos N).ne',
    Finsupp.add_apply, Nat.factorization_lcmUpto N hp,
    modifiedLcmRaisedProduct_factorization]

theorem modifiedLcm_factorization_ge_log (N : Nat) {p : Nat} (hp : Nat.Prime p) :
    Nat.log p N <= (modifiedLcm N).factorization p := by
  rw [modifiedLcm_factorization N hp]
  exact Nat.le_add_right _ _

theorem modifiedLcm_factorization_pos (N : Nat) {p : Nat} (hp : Nat.Prime p)
    (hpN : p <= N) : 1 <= (modifiedLcm N).factorization p :=
  (Nat.log_pos hp.one_lt hpN).trans_le (modifiedLcm_factorization_ge_log N hp)

theorem modifiedLcm_primeFactors (N : Nat) :
    (modifiedLcm N).primeFactors = Nat.primesLE N := by
  ext p
  constructor
  . intro hp
    have hPrime : Nat.Prime p := (Nat.mem_primeFactors.mp hp).1
    have hF : Not ((modifiedLcm N).factorization p = 0) := by
      apply Finsupp.mem_support_iff.mp
      rwa [Nat.support_factorization]
    by_contra hNot
    have hpNot : Not (p <= N) := by
      intro hpLe
      apply hNot
      rw [Nat.mem_primesLE]
      exact And.intro hpLe hPrime
    have hRaised : Not (Membership.mem (modifiedLcmRaisedPrimes N) p) := by
      intro h
      exact hNot (Finset.mem_filter.mp h).1
    rw [modifiedLcm_factorization N hPrime, if_neg hRaised,
      Nat.log_of_lt (Nat.lt_of_not_ge hpNot), Nat.zero_add] at hF
    exact hF rfl
  . intro hp
    have hPrime := Nat.prime_of_mem_primesLE hp
    have hPositive := modifiedLcm_factorization_pos N hPrime (Nat.le_of_mem_primesLE hp)
    rw [<- Nat.support_factorization, Finsupp.mem_support_iff]
    omega

theorem modifiedLcm_log_identity (N : Nat) :
    Real.log (modifiedLcm N : Real) =
      Chebyshev.psi (N : Real) +
        (modifiedLcmRaisedPrimes N).sum (fun p => Real.log (p : Real)) := by
  unfold modifiedLcm
  rw [Nat.cast_mul,
    Real.log_mul (by exact_mod_cast (Nat.lcmUpto_pos N).ne')
      (by exact_mod_cast (modifiedLcmRaisedProduct_pos N).ne'),
    <- Chebyshev.psi_eq_log_lcmUpto, Nat.cast_prod,
    Real.log_prod (fun p hp => by
      exact_mod_cast (mem_modifiedLcmRaisedPrimes N p |>.mp hp).1.ne_zero)]
  rfl

theorem modifiedLcmRaisedPrimes_eq_sdiff (N : Nat) :
    modifiedLcmRaisedPrimes N =
      (Nat.primesLE (Nat.sqrt (2 * N))) \ (Nat.primesLE (Nat.sqrt N)) := by
  ext p
  have hsqrt (t : Nat) : p <= Nat.sqrt t <-> p ^ 2 <= t := by
    simpa only [pow_two] using (Nat.le_sqrt (m := p) (n := t))
  simp only [mem_modifiedLcmRaisedPrimes, Finset.mem_sdiff, Nat.mem_primesLE, hsqrt]
  constructor
  . intro h
    refine And.intro (And.intro h.2.2 h.1) ?_
    intro hOther
    exact (Nat.not_le_of_lt h.2.1) hOther.1
  . intro h
    refine And.intro h.1.2 (And.intro ?_ h.1.1)
    by_contra hNot
    exact h.2 (And.intro (Nat.le_of_not_gt hNot) h.1.2)

theorem modifiedLcmRaisedSum_eq_theta_difference (N : Nat) :
    (modifiedLcmRaisedPrimes N).sum (fun p => Real.log (p : Real)) =
      Chebyshev.theta (Nat.sqrt (2 * N) : Real) -
        Chebyshev.theta (Nat.sqrt N : Real) := by
  have hSub : Nat.primesLE (Nat.sqrt N) <= Nat.primesLE (Nat.sqrt (2 * N)) := by
    intro p hp
    rw [Nat.mem_primesLE] at hp
    rw [Nat.mem_primesLE]
    refine And.intro ?_ hp.2
    apply Nat.le_sqrt.mpr
    have h := Nat.le_sqrt.mp hp.1
    omega
  have hSum := Finset.sum_sdiff (f := fun p : Nat => Real.log (p : Real)) hSub
  rw [<- modifiedLcmRaisedPrimes_eq_sdiff] at hSum
  rw [<- Chebyshev.theta_eq_sum_primesLE_log, <- Chebyshev.theta_eq_sum_primesLE_log] at hSum
  linarith only [hSum]

theorem modifiedLcm_log_eq_psi_add_theta_difference (N : Nat) :
    Real.log (modifiedLcm N : Real) =
      Chebyshev.psi (N : Real) +
        Chebyshev.theta (Nat.sqrt (2 * N) : Real) -
          Chebyshev.theta (Nat.sqrt N : Real) := by
  rw [modifiedLcm_log_identity, modifiedLcmRaisedSum_eq_theta_difference]
  ring

theorem modifiedLcm_factorization_eq_two
    (N : Nat) {p : Nat} (hp : Nat.Prime p)
    (hCube : N < p ^ 3) (hSquare : p ^ 2 <= 2 * N) :
    (modifiedLcm N).factorization p = 2 := by
  have hpN : p <= N := by nlinarith [hp.two_le]
  rw [modifiedLcm_factorization N hp]
  by_cases hLow : p ^ 2 <= N
  . have hLog : Nat.log p N = 2 :=
      Nat.log_eq_of_pow_le_of_lt_pow hLow hCube
    have hNot : Not (Membership.mem (modifiedLcmRaisedPrimes N) p) := by
      intro h
      exact (Nat.not_le_of_lt (mem_modifiedLcmRaisedPrimes N p |>.mp h).2.1) hLow
    rw [hLog, ite_eq_right hNot]
  . have hRaised : Membership.mem (modifiedLcmRaisedPrimes N) p :=
      (mem_modifiedLcmRaisedPrimes N p).mpr
        (And.intro hp (And.intro (Nat.lt_of_not_ge hLow) hSquare))
    have hLog : Nat.log p N = 1 := Nat.log_eq_of_pow_le_of_lt_pow
      (by simpa only [pow_one] using hpN) (Nat.lt_of_not_ge hLow)
    rw [hLog, ite_eq_left hRaised]

theorem modifiedLcm_factorization_eq_one
    (N : Nat) {p : Nat} (hp : Nat.Prime p) (hpN : p <= N)
    (hSquare : 2 * N < p ^ 2) :
    (modifiedLcm N).factorization p = 1 := by
  have hLog : Nat.log p N = 1 := Nat.log_eq_of_pow_le_of_lt_pow
    (by simpa only [pow_one] using hpN) (by change N < p ^ 2; omega)
  have hNot : Not (Membership.mem (modifiedLcmRaisedPrimes N) p) := by
    intro h
    exact (Nat.not_le_of_lt hSquare) (mem_modifiedLcmRaisedPrimes N p |>.mp h).2.2
  rw [modifiedLcm_factorization N hp, hLog, ite_eq_right hNot]

theorem modifiedLcm_exponentDefect_lt
    (N : Nat) (hN : 0 < N) {p : Nat} (hp : Nat.Prime p) :
    lcmExponentDefect (modifiedLcm N) p < 1 / (N : Real) := by
  have hPow : N < p ^ ((modifiedLcm N).factorization p + 1) := by
    exact (Nat.lt_pow_succ_log_self hp.one_lt N).trans_le
      (Nat.pow_le_pow_right hp.pos (Nat.add_le_add_right
        (modifiedLcm_factorization_ge_log N hp) 1))
  have hCast : (N : Real) < (p : Real) ^ ((modifiedLcm N).factorization p + 1) := by
    exact_mod_cast hPow
  have hDef : lcmExponentDefect (modifiedLcm N) p =
      1 / (p : Real) ^ ((modifiedLcm N).factorization p + 1) := by
    unfold lcmExponentDefect
    rw [Real.rpow_neg (Nat.cast_nonneg p),
      show ((modifiedLcm N).factorization p : Real) + 1 =
        (((modifiedLcm N).factorization p + 1 : Nat) : Real) by simp,
      Real.rpow_natCast, one_div]
  rw [hDef]
  exact one_div_lt_one_div_of_lt (by exact_mod_cast hN) hCast

theorem modifiedLcm_exponentDefect_small
    (N : Nat) (hN : 8 <= N) {p : Nat} (hp : Nat.Prime p) :
    lcmExponentDefect (modifiedLcm N) p <= 1 / 8 := by
  have h := modifiedLcm_exponentDefect_lt N (by omega) hp
  have hCast : (8 : Real) <= N := by exact_mod_cast hN
  exact h.le.trans (one_div_le_one_div_of_le (by norm_num) hCast)

theorem modifiedLcm_divisor_log_lower
    (k : Real) (hk : 0 < k) (hkOne : 1 <= k) (hkTwo : k <= 2)
    (N : Nat) (hN : 8 <= N) :
    k * Real.log (modifiedLcm N : Real) -
      k * (Nat.primesLE N).sum (fun p => Real.log (1 - 1 / (p : Real))) +
      (Nat.primesLE N).sum (fun p => Real.log (1 - (p : Real) ^ (-k))) -
      k * lcmDefectSum (modifiedLcm N) - lcmDefectRemainder (modifiedLcm N) <=
        Real.log (lcmDivisorSum k hk (modifiedLcm N)) := by
  have h := lcmDivisorSum_log_lower k hk hkOne hkTwo
    (modifiedLcm N) (modifiedLcm_pos N).ne'
    (fun p hp => modifiedLcm_exponentDefect_small N hN (Nat.mem_primeFactors.mp hp).1)
  simpa only [modifiedLcm_primeFactors] using h

theorem theta_nat_sqrt_eq_real_sqrt (N : Nat) :
    Chebyshev.theta (Nat.sqrt N : Real) = Chebyshev.theta (Real.sqrt (N : Real)) := by
  simp only [Chebyshev.theta_eq_sum_primesLE, Nat.floor_natCast,
    Real.nat_floor_real_sqrt_eq_nat_sqrt]

theorem modifiedLcm_log_eq_psi_add_real_theta_difference (N : Nat) :
    Real.log (modifiedLcm N : Real) =
      Chebyshev.psi (N : Real) +
        Chebyshev.theta (Real.sqrt (2 * (N : Real))) -
          Chebyshev.theta (Real.sqrt (N : Real)) := by
  rw [modifiedLcm_log_eq_psi_add_theta_difference,
    theta_nat_sqrt_eq_real_sqrt, theta_nat_sqrt_eq_real_sqrt]
  simp only [Nat.cast_mul, Nat.cast_ofNat]

end PrimeFactorOscillations
