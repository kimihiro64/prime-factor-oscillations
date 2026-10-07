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

theorem lcmPowerCorrection_unit_upper (k u t : Real)
    (hk : 1 <= k) (hu : 0 <= u) (huOne : u < 1)
    (ht : 0 <= t) (htOne : t <= 1) :
    lcmPowerCorrection k (u * t) (u ^ k) t <= 1 := by
  have hkPos : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have huLe : u <= 1 := huOne.le
  have hWeight : 0 <= 1 - u := by linarith
  have hV : u ^ k <= u := by
    have h := (convexOn_rpow hk).2
      (show (0 : Real) <= 0 by rfl) (show (0 : Real) <= 1 by norm_num)
      hWeight hu (show (1 - u) + u = 1 by ring)
    simpa only [smul_eq_mul, mul_zero, mul_one, zero_add,
      Real.zero_rpow hkPos.ne', Real.one_rpow] using h
  have hQ : (1 - t) ^ k <= 1 :=
    Real.rpow_le_one (by linarith) (by linarith) hkPos.le
  have hChord : (1 - u * t) ^ k <= 1 - u + u * (1 - t) ^ k := by
    have h := (convexOn_rpow hk).2
      (show (0 : Real) <= 1 by norm_num) (show (0 : Real) <= 1 - t by linarith)
      hWeight hu (show (1 - u) + u = 1 by ring)
    simp only [smul_eq_mul, mul_one, Real.one_rpow] at h
    rw [show (1 - u) + u * (1 - t) = 1 - u * t by ring] at h
    exact h
  have hSlack := mul_nonneg (sub_nonneg.mpr hV) (sub_nonneg.mpr hQ)
  have hDen : 0 < 1 - u ^ k := by linarith only [hV, huOne]
  unfold lcmPowerCorrection
  apply (div_le_one hDen).mpr
  nlinarith only [hChord, hSlack]

theorem lcmPowerLocalFactor_le_one (p : Real) (hp : 1 < p)
    (a : Nat) (k : Real) (hk : 1 <= k) :
    lcmPowerLocalFactor p a k <= 1 := by
  have hpPos : 0 < p := zero_lt_one.trans hp
  have hu : 0 <= 1 / p := by positivity
  have huOne : 1 / p < 1 := (div_lt_one hpPos).mpr hp
  have ht : 0 <= p ^ (-(a : Real)) := Real.rpow_nonneg hpPos.le _
  have htOne : p ^ (-(a : Real)) <= 1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hp.le
        (show -(a : Real) <= 0 from neg_nonpos.mpr (Nat.cast_nonneg a))
  have hU : 1 / p * p ^ (-(a : Real)) = p ^ (-((a : Real) + 1)) := by
    rw [one_div, <- Real.rpow_neg_one, <- Real.rpow_add hpPos]
    congr 1
    ring
  have hV : (1 / p) ^ k = p ^ (-k) := by
    rw [Real.div_rpow (by norm_num : (0 : Real) <= 1) hpPos.le,
      Real.one_rpow, one_div, Real.rpow_neg hpPos.le]
  have h := lcmPowerCorrection_unit_upper k (1 / p) (p ^ (-(a : Real)))
    hk hu huOne ht htOne
  rw [hU, hV] at h
  exact h


theorem lcmDivisorSum_log_upper (k : Real) (hk : 0 < k) (hkOne : 1 <= k)
    (n : Nat) (hn : Not (n = 0)) :
    Real.log (lcmDivisorSum k hk n) <=
      k * Real.log (n : Real) -
        k * n.primeFactors.sum (fun p => Real.log (1 - 1 / (p : Real))) +
        n.primeFactors.sum (fun p => Real.log (1 - (p : Real) ^ (-k))) := by
  have hCorrection : n.primeFactors.sum (fun p =>
      Real.log (lcmPowerLocalFactor (p : Real) (n.factorization p) k)) <= 0 := by
    apply Finset.sum_nonpos
    intro p hp
    have hPrime := (Nat.mem_primeFactors.mp hp).1
    have hSupport : Membership.mem n.factorization.support p := by
      rwa [Nat.support_factorization]
    have ha : 1 <= n.factorization p := by
      have h := Finsupp.mem_support_iff.mp hSupport
      omega
    have hPos := lcmPowerLocalFactor_prime_pos k hk hPrime _ ha
    have hUpper := lcmPowerLocalFactor_le_one (p : Real)
      (by exact_mod_cast hPrime.one_lt) (n.factorization p) k hkOne
    simpa only [Real.log_one] using Real.log_le_log hPos hUpper
  rw [lcmDivisorSum_log_identity k hk n hn]
  linarith only [hCorrection]

theorem modifiedLcm_logRatio_upper
    (k : Real) (hk : 0 < k) (hkOne : 1 < k) (N : Nat) (hN : 3 <= N) :
    Real.log (lcmRobinRatio k hk (modifiedLcm N)) <=
      lcmFiniteZetaTail k (primeProfilePrefixSet N) -
        k * (Robin1984.nicolasLogMertensOscillation (N : Real) +
          modifiedLcmHeightCorrection N) := by
  have hTheta : 1 < Chebyshev.theta (N : Real) :=
    Robin1984.one_lt_chebyshevTheta_of_three_le (by exact_mod_cast hN)
  have hF := lcmNicolasLog_eq_prime_sum N hTheta
  have hZeta := lcm_logZeta_eq_prefix_add_tail k hkOne (primeProfilePrefixSet N)
  change Real.log (riemannZeta (k : Complex)).re =
    (primeProfilePrefixSet N).sum
      (fun p : Nat.Primes => -Real.log (1 - (p.val : Real) ^ (-k))) +
        lcmFiniteZetaTail k (primeProfilePrefixSet N) at hZeta
  rw [lcm_primeProfilePrefix_sum N (fun p => -Real.log (1 - (p : Real) ^ (-k))),
    Finset.sum_neg_distrib] at hZeta
  have hDiv := lcmDivisorSum_log_upper k hk hkOne.le (modifiedLcm N)
    (modifiedLcm_pos N).ne'
  rw [modifiedLcm_primeFactors] at hDiv
  rw [lcmRobinRatio_log_identity k hk hkOne (modifiedLcm N)
    (modifiedLcm_pos N).ne' (modifiedLcm_loglog_pos N hN), hF]
  unfold modifiedLcmHeightCorrection
  linarith only [hDiv, hZeta]

theorem modifiedLcmHeightCorrection_nonneg (N : Nat) (hN : 3 <= N) :
    0 <= modifiedLcmHeightCorrection N := by
  have hTheta : 1 < Chebyshev.theta (N : Real) :=
    Robin1984.one_lt_chebyshevTheta_of_three_le (by exact_mod_cast hN)
  have h := Real.log_le_log (Real.log_pos hTheta)
    (Real.log_le_log (zero_lt_one.trans hTheta) (modifiedLcm_theta_le_log N))
  exact sub_nonneg.mpr h

theorem nicolasLog_le_of_modifiedLcm_ratio_ge_one
    (k : Real) (hk : 0 < k) (hkOne : 1 < k) (N : Nat) (hN : 3 <= N)
    (hRatio : 1 <= lcmRobinRatio k hk (modifiedLcm N)) :
    Robin1984.nicolasLogMertensOscillation (N : Real) <=
      lcmFiniteZetaTail k (primeProfilePrefixSet N) / k := by
  have hLower := Real.log_nonneg hRatio
  have hUpper := modifiedLcm_logRatio_upper k hk hkOne N hN
  have hHeight := mul_nonneg hk.le (modifiedLcmHeightCorrection_nonneg N hN)
  have hMul : Robin1984.nicolasLogMertensOscillation (N : Real) * k <=
      lcmFiniteZetaTail k (primeProfilePrefixSet N) := by
    nlinarith only [hLower, hUpper, hHeight]
  have hDiv := div_le_div_of_nonneg_right hMul hk.le
  have hCancel : (Robin1984.nicolasLogMertensOscillation (N : Real) * k) / k =
      Robin1984.nicolasLogMertensOscillation (N : Real) := by field_simp [hk.ne']
  rwa [hCancel] at hDiv

end PrimeFactorOscillations
