/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LcmExplicitMargin
import PrimeFactorOscillations.Helpers.Robin1984.NicolasLandau.NicolasOscillation

/-!
# The actual generalized divisor ratio and its complete signed lower bound

The numerator is the Mobius-defined divisor sum. Positivity of the real zeta
value comes from its Euler product, and all logarithm domains are explicit.
The finite prime sums cancel before any asymptotic estimate is used.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations



def lcmRobinRatio (k : Real) (hk : 0 < k) (n : Nat) : Real :=
  (riemannZeta (k : Complex)).re * lcmDivisorSum k hk n /
    (Real.exp Real.eulerMascheroniConstant * (n : Real) *
      Real.log (Real.log (n : Real))) ^ k

theorem lcmRobinRatio_pos (k : Real) (hk : 0 < k) (hkOne : 1 < k)
    (n : Nat) (hn : Not (n = 0)) (hLogLog : 0 < Real.log (Real.log (n : Real))) :
    0 < lcmRobinRatio k hk n := by
  have hZeta : 0 < (riemannZeta (k : Complex)).re := by
    have hComplex := riemannZeta_eulerProduct_exp_log (s := (k : Complex))
      (by simpa using hkOne)
    have hSum :
        tsum (fun p : Nat.Primes => -Complex.log (1 - (p : Complex) ^ (-(k : Complex)))) =
          ((tsum (fun p : Nat.Primes => -Real.log (1 - (p : Real) ^ (-k))) : Real) : Complex) := by
      rw [Complex.ofReal_tsum]
      exact tsum_congr (fun p => (lcmPrimeLog_complex_cast k hk p).symm)
    rw [<- hComplex, hSum, Complex.exp_ofReal_re]
    exact Real.exp_pos _
  have hnReal : (0 : Real) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  have hBase := mul_pos (mul_pos (Real.exp_pos Real.eulerMascheroniConstant) hnReal) hLogLog
  exact div_pos (mul_pos hZeta (lcmDivisorSum_pos k hk n hn))
    (Real.rpow_pos_of_pos hBase k)

theorem lcmRobinRatio_log_identity (k : Real) (hk : 0 < k) (hkOne : 1 < k)
    (n : Nat) (hn : Not (n = 0)) (hLogLog : 0 < Real.log (Real.log (n : Real))) :
    Real.log (lcmRobinRatio k hk n) =
      Real.log (riemannZeta (k : Complex)).re + Real.log (lcmDivisorSum k hk n) -
        k * (Real.eulerMascheroniConstant + Real.log (n : Real) +
          Real.log (Real.log (Real.log (n : Real)))) := by
  have hnReal : (0 : Real) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  have hZeta : Not ((riemannZeta (k : Complex)).re = 0) := by
    intro hZero
    have hRatioZero : lcmRobinRatio k hk n = 0 := by
      simp only [lcmRobinRatio, hZero, zero_mul, zero_div]
    exact (lcmRobinRatio_pos k hk hkOne n hn hLogLog).ne' hRatioZero
  have hSum := lcmDivisorSum_pos k hk n hn
  have hFirst := mul_pos (Real.exp_pos Real.eulerMascheroniConstant) hnReal
  have hBase := mul_pos hFirst hLogLog
  unfold lcmRobinRatio
  rw [Real.log_div (mul_ne_zero hZeta hSum.ne') (Real.rpow_pos_of_pos hBase k).ne',
    Real.log_mul hZeta hSum.ne', Real.log_rpow hBase,
    Real.log_mul hFirst.ne' hLogLog.ne',
    Real.log_mul (Real.exp_pos Real.eulerMascheroniConstant).ne' hnReal.ne', Real.log_exp]

theorem lcm_primeProfilePrefix_sum (N : Nat) (f : Nat -> Real) :
    (primeProfilePrefixSet N).sum (fun p : Nat.Primes => f p.val) =
      (Nat.primesLE N).sum f := by
  classical
  refine Finset.sum_bij (fun (p : Nat.Primes) _ => p.val) ?_ ?_ ?_ ?_
  . intro p hp
    have hpMem : p.val < N + 1 := by
      exact Finset.mem_range.mp (Finset.mem_subtype.mp hp)
    have hpLe : p.val <= N := Nat.le_of_lt_succ hpMem
    have hpPrime : Nat.Prime p.val := p.property
    apply Nat.mem_primesLE.mpr
    constructor
    . assumption
    . assumption
  . intro p hp q hq heq
    exact Subtype.ext heq
  . intro p hp
    have hpPrime := Nat.prime_of_mem_primesLE hp
    have hpLe := Nat.le_of_mem_primesLE hp
    let pp : Nat.Primes := Subtype.mk p hpPrime
    have hppMem : Membership.mem (primeProfilePrefixSet N) pp := by
      exact Finset.mem_subtype.mpr (Finset.mem_range.mpr (Nat.lt_succ_of_le hpLe))
    exact Exists.intro pp (Exists.intro hppMem rfl)
  . intro p hp
    rfl

theorem lcmNicolasLog_eq_prime_sum (N : Nat)
    (hTheta : 1 < Chebyshev.theta (N : Real)) :
    Robin1984.nicolasLogMertensOscillation (N : Real) =
      Real.eulerMascheroniConstant + Real.log (Real.log (Chebyshev.theta (N : Real))) +
        (Nat.primesLE N).sum (fun p => Real.log (1 - 1 / (p : Real))) := by
  have hLog := Real.log_pos hTheta
  have hProduct := Robin1984.nicolasMertensProduct_pos (N : Real)
  have hFactors : forall p, Membership.mem (Nat.primesLE N) p ->
      Not (1 - 1 / (p : Real) = 0) := by
    intro p hp
    have hPrime := Nat.prime_of_mem_primesLE hp
    have hpPos : (0 : Real) < p := by exact_mod_cast hPrime.pos
    have hpOne : (1 : Real) < p := by exact_mod_cast hPrime.one_lt
    exact (sub_pos.mpr ((div_lt_one hpPos).mpr hpOne)).ne'
  unfold Robin1984.nicolasLogMertensOscillation Robin1984.nicolasFunction
  rw [Real.log_mul (mul_pos (Real.exp_pos _) hLog).ne' hProduct.ne',
    Real.log_mul (Real.exp_pos _).ne' hLog.ne', Real.log_exp]
  unfold Robin1984.nicolasMertensProduct
  simp only [Nat.floor_natCast]
  rw [Real.log_prod hFactors]

theorem modifiedLcm_loglog_pos (N : Nat) (hN : 3 <= N) :
    0 < Real.log (Real.log (modifiedLcm N : Real)) := by
  have hTheta : 1 < Chebyshev.theta (N : Real) :=
    Robin1984.one_lt_chebyshevTheta_of_three_le (by exact_mod_cast hN)
  exact Real.log_pos (lt_of_lt_of_le hTheta (modifiedLcm_theta_le_log N))

theorem modifiedLcm_logRatio_lower
    (k : Real) (hk : 0 < k) (hkOne : 1 < k) (hkTwo : k <= 2)
    (N : Nat) (hN : 8 <= N) :
    lcmFiniteZetaTail k (primeProfilePrefixSet N) -
      k * (Robin1984.nicolasLogMertensOscillation (N : Real) +
        modifiedLcmHeightCorrection N + lcmDefectSum (modifiedLcm N)) -
          lcmDefectRemainder (modifiedLcm N) <=
      Real.log (lcmRobinRatio k hk (modifiedLcm N)) := by
  have hTheta : 1 < Chebyshev.theta (N : Real) :=
    Robin1984.one_lt_chebyshevTheta_of_three_le
      (by exact_mod_cast (show 3 <= N by omega))
  have hF := lcmNicolasLog_eq_prime_sum N hTheta
  have hZeta := lcm_logZeta_eq_prefix_add_tail k hkOne (primeProfilePrefixSet N)
  change Real.log (riemannZeta (k : Complex)).re =
    (primeProfilePrefixSet N).sum
      (fun p : Nat.Primes => -Real.log (1 - (p.val : Real) ^ (-k))) +
        lcmFiniteZetaTail k (primeProfilePrefixSet N) at hZeta
  rw [lcm_primeProfilePrefix_sum N (fun p => -Real.log (1 - (p : Real) ^ (-k))),
    Finset.sum_neg_distrib] at hZeta
  have hDiv := modifiedLcm_divisor_log_lower k hk hkOne.le hkTwo N hN
  have hRatio := lcmRobinRatio_log_identity k hk hkOne (modifiedLcm N)
    (modifiedLcm_pos N).ne' (modifiedLcm_loglog_pos N (by omega))
  calc
    _ = (k * Real.log (modifiedLcm N : Real) -
          k * (Nat.primesLE N).sum (fun p => Real.log (1 - 1 / (p : Real))) +
          (Nat.primesLE N).sum (fun p => Real.log (1 - (p : Real) ^ (-k))) -
          k * lcmDefectSum (modifiedLcm N) - lcmDefectRemainder (modifiedLcm N)) +
        Real.log (riemannZeta (k : Complex)).re -
          k * (Real.eulerMascheroniConstant + Real.log (modifiedLcm N : Real) +
            Real.log (Real.log (Real.log (modifiedLcm N : Real)))) := by
      rw [hF, hZeta]
      unfold modifiedLcmHeightCorrection
      ring
    _ <= Real.log (lcmDivisorSum k hk (modifiedLcm N)) +
        Real.log (riemannZeta (k : Complex)).re -
          k * (Real.eulerMascheroniConstant + Real.log (modifiedLcm N : Real) +
            Real.log (Real.log (Real.log (modifiedLcm N : Real)))) := by
      linarith only [hDiv]
    _ = _ := by rw [hRatio]; ring

theorem modifiedLcm_logRatio_window_lower
    (k K : Real) (hk : 0 < k) (hkOne : 1 < k) (hLe : k <= K) (hTwo : K <= 2)
    (N : Nat) (hN : 8 <= N) :
    lcmFiniteZetaTail K (primeProfilePrefixSet N) -
      K * max (Robin1984.nicolasLogMertensOscillation (N : Real) +
        modifiedLcmHeightCorrection N + lcmDefectSum (modifiedLcm N)) 0 -
          lcmDefectRemainder (modifiedLcm N) <=
      Real.log (lcmRobinRatio k hk (modifiedLcm N)) := by
  let A := Robin1984.nicolasLogMertensOscillation (N : Real) +
    modifiedLcmHeightCorrection N + lcmDefectSum (modifiedLcm N)
  have hBase := modifiedLcm_logRatio_lower k hk hkOne (hLe.trans hTwo) N hN
  have hTail := lcmFiniteZetaTail_antitone k K hkOne hLe (primeProfilePrefixSet N)
  have hCoeff : k * A <= K * max A 0 := by
    calc
      k * A <= k * max A 0 := mul_le_mul_of_nonneg_left (le_max_left A 0) hk.le
      _ <= K * max A 0 := mul_le_mul_of_nonneg_right hLe (le_max_right A 0)
  change lcmFiniteZetaTail k (primeProfilePrefixSet N) -
    k * A - lcmDefectRemainder (modifiedLcm N) <= _ at hBase
  change lcmFiniteZetaTail K (primeProfilePrefixSet N) -
    K * max A 0 - lcmDefectRemainder (modifiedLcm N) <= _
  linarith only [hBase, hTail, hCoeff]

theorem modifiedLcm_logRatio_finite_window_lower
    (k K q : Real) (hk : 0 < k) (hkOne : 1 < k) (hLe : k <= K)
    (hTwo : K <= 2) (hq : 1 <= q) (N m : Nat) (hN : 8 <= N) :
    lcmFiniteTailLowerSum N m q K -
      K * max (Robin1984.nicolasLogMertensOscillation (N : Real) +
        modifiedLcmHeightCorrection N + lcmDefectSum (modifiedLcm N)) 0 -
          lcmDefectRemainder (modifiedLcm N) <=
      Real.log (lcmRobinRatio k hk (modifiedLcm N)) := by
  have hFinite := lcmFiniteTailLowerSum_le N m q K (by omega) hq
    (lt_of_lt_of_le hkOne hLe) hTwo
  have hWindow := modifiedLcm_logRatio_window_lower k K hk hkOne hLe hTwo N hN
  linarith only [hFinite, hWindow]

end PrimeFactorOscillations
