import Mathlib.NumberTheory.Bertrand
import PrimeFactorOscillations.Helpers.PeakPrimePrefixBounds
import PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliPeakScale

/-!
# Explicit prime-tail bounds and an interior benchmark

Explicit prime-tail bounds and an interior benchmark for the peak-height comparison of regular prime Bernoulli laws.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter Topology

namespace PrimeFactorOscillations

noncomputable def primeTailOddsMertensError (P : Nat) (nu K : Real) : Real :=
  2 * K / (P : Real) + nu *
    (abs (PrimeFactorUnimodality.reciprocalPrimeSumBelow (P + 1)) +
      (abs Mertens.M + abs PrimeFactorUnimodality.mertensErrorConstant / Real.log 2))

theorem primeTail_bernoulliMass_explicit_lower
    (n P H r : Nat) (hn : 2 <= n) (hP : 1 <= P) (hH : 2 <= H)
    (hPH : P <= H) (hHn : H <= n)
    (eta : Nat -> Real) (nu K : Real) (hnu : 0 <= nu) (hK : 0 <= K)
    (hunit : forall p, Nat.Prime p -> P < p -> p <= n -> 0 <= eta p /\ eta p < 1)
    (hupper : forall p, Nat.Prime p -> P < p -> p <= n ->
      eta p / (1 - eta p) <= 2 * nu / (p : Real))
    (herror : forall p, Nat.Prime p -> P < p -> p <= n ->
      abs (eta p / (1 - eta p) - nu / (p : Real)) <= K / (p : Real) ^ 2) :
    let E := primeTailOddsMertensError P nu K
    let G := nu * (Real.log (Real.log (n : Real)) - Real.log (Real.log (H : Real))) -
      2 * E - (r : Real) * (2 * nu / (H : Real))
    0 <= G ->
      Real.exp (-(nu * Real.log (Real.log (n : Real)) + E)) *
        (G ^ r / (r.factorial : Real)) <=
          List.bernoulliMass
            (((n + 1).primesBelow \ (P + 1).primesBelow).toList.map eta) r := by
  classical
  dsimp only
  let E := primeTailOddsMertensError P nu K
  let T := (n + 1).primesBelow \ (P + 1).primesBelow
  let s := T.toList.map eta
  let a := fun p => eta p / (1 - eta p)
  let w := s.map (fun q => q / (1 - q))
  let B := (r : Real) * (2 * nu / (H : Real)) +
    nu * Real.log (Real.log (H : Real)) + E
  let G := nu * (Real.log (Real.log (n : Real)) - Real.log (Real.log (H : Real))) -
    2 * E - (r : Real) * (2 * nu / (H : Real))
  change 0 <= G ->
    Real.exp (-(nu * Real.log (Real.log (n : Real)) + E)) *
      (G ^ r / (r.factorial : Real)) <= List.bernoulliMass s r
  intro hG0
  have hinside (p : Nat) (hp : Membership.mem T p) : Nat.Prime p /\ P < p /\ p <= n := by
    have hh := Finset.mem_sdiff.mp hp
    have hn := Nat.mem_primesBelow.mp hh.1
    have hc : P < p := by
      by_contra hnot
      exact hh.2 (Nat.mem_primesBelow.mpr (And.intro (by omega) hn.2))
    exact And.intro hn.2 (And.intro hc (by omega))
  have hs : forall q, List.Mem q s -> 0 <= q /\ q < 1 := by
    intro q hq
    have hh := List.mem_map.mp hq
    choose p hp using hh
    have hh := hinside p (Finset.mem_toList.mp hp.1)
    rw [<- hp.2]
    exact hunit p hh.1 hh.2.1 hh.2.2
  have hpos (p : Nat) (hp : Nat.Prime p) (hPc : P < p) (hpn : p <= n) : 0 <= a p :=
    div_nonneg (hunit p hp hPc hpn).1 (sub_pos.mpr (hunit p hp hPc hpn).2).le
  have hm := tailPrimeOdds_uniform_logLog_error n P hn hP (hPH.trans hHn)
    a nu K hnu hK herror
  have hm' : abs (w.sum - nu * Real.log (Real.log (n : Real))) <= E := by
    simpa [w, s, a, T, E, primeTailOddsMertensError, Function.comp_def] using hm
  have hB : forall j : Nat, j < r -> List.largestWeightSum w j <= B := by
    intro j hj
    have hh := largestPrimeOdds_le_lowPrefix n P H j hn hP hH hPH hHn
      a nu K hnu hK hpos hupper herror
    have hh' : List.largestWeightSum w j <=
        (j : Real) * (2 * nu / (H : Real)) +
          nu * Real.log (Real.log (H : Real)) + E := by
      simpa [w, s, a, T, E, primeTailOddsMertensError, Function.comp_def] using hh
    have hHR : 0 <= (H : Real) := Nat.cast_nonneg H
    have hcoef : 0 <= 2 * nu / (H : Real) :=
      div_nonneg (mul_nonneg (by norm_num) hnu) hHR
    have hjr : (j : Real) * (2 * nu / (H : Real)) <=
        (r : Real) * (2 * nu / (H : Real)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.le_of_lt hj)) hcoef
    dsimp [B]
    linarith only [hh', hjr]
  have hG : G <= w.sum - B := by
    dsimp [G, B]
    linarith only [(abs_le.mp hm').1]
  have hgap : 0 <= w.sum - B := hG0.trans hG
  have hpowers : forall j : Nat, G ^ j <= (w.sum - B) ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [pow_succ, pow_succ]
        exact mul_le_mul ih hG hG0 (pow_nonneg hgap j)
  have hf : 0 < (r.factorial : Real) := by exact_mod_cast Nat.factorial_pos r
  have hfrac := div_le_div_of_nonneg_right (hpowers r) hf.le
  have hexp : Real.exp (-(nu * Real.log (Real.log (n : Real)) + E)) <=
      Real.exp (-w.sum) := Real.exp_le_exp.mpr (by linarith only [(abs_le.mp hm').2])
  have hk := List.bernoulliMass_lower_largest s r B hs hB hgap
  have hprod := mul_le_mul hexp hfrac (div_nonneg (pow_nonneg hG0 r) hf.le)
    (Real.exp_pos (-w.sum)).le
  exact hprod.trans hk

end PrimeFactorOscillations

namespace PrimeFactorOscillations

theorem primeTail_bernoulliMass_explicit_upper
    (n P r : Nat) (hn : 2 <= n) (hP : 1 <= P) (hPn : P <= n)
    (eta : Nat -> Real) (nu K : Real) (hnu : 0 <= nu) (hK : 0 <= K)
    (hunit : forall p, Nat.Prime p -> P < p -> p <= n -> 0 <= eta p /\ eta p < 1)
    (herror : forall p, Nat.Prime p -> P < p -> p <= n ->
      abs (eta p / (1 - eta p) - nu / (p : Real)) <= K / (p : Real) ^ 2) :
    List.bernoulliMass
      (((n + 1).primesBelow \ (P + 1).primesBelow).toList.map eta) r <=
      (nu * Real.log (Real.log (n : Real)) + primeTailOddsMertensError P nu K) ^ r /
        (r.factorial : Real) := by
  classical
  let T := (n + 1).primesBelow \ (P + 1).primesBelow
  let s := T.toList.map eta
  let w := s.map (fun q => q / (1 - q))
  let U := nu * Real.log (Real.log (n : Real)) + primeTailOddsMertensError P nu K
  have hs : forall q, List.Mem q s -> 0 <= q /\ q < 1 := by
    intro q hq
    have hh := List.mem_map.mp hq
    choose p hp using hh
    have hc := Finset.mem_sdiff.mp (Finset.mem_toList.mp hp.1)
    have hn' := Nat.mem_primesBelow.mp hc.1
    have hPc : P < p := by
      by_contra hnot
      exact hc.2 (Nat.mem_primesBelow.mpr (And.intro (by omega) hn'.2))
    rw [<- hp.2]
    exact hunit p hn'.2 hPc (by omega)
  have hw : 0 <= w.sum := by
    apply List.sum_nonneg
    intro q hq
    have hh := List.mem_map.mp hq
    choose a ha using hh
    rw [<- ha.2]
    exact div_nonneg (hs a ha.1).1 (sub_pos.mpr (hs a ha.1).2).le
  have hm := tailPrimeOdds_uniform_logLog_error n P hn hP hPn
    (fun p => eta p / (1 - eta p)) nu K hnu hK herror
  have hS : w.sum <= U := by
    have hh : abs (w.sum - nu * Real.log (Real.log (n : Real))) <=
        primeTailOddsMertensError P nu K := by
      simpa [w, s, T, primeTailOddsMertensError, Function.comp_def] using hm
    dsimp [U]
    linarith only [(abs_le.mp hh).2]
  have hU : 0 <= U := hw.trans hS
  have hp : forall j : Nat, w.sum ^ j <= U ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [pow_succ, pow_succ]
        exact mul_le_mul ih hS hw (pow_nonneg hU j)
  have hf : 0 < (r.factorial : Real) := by exact_mod_cast Nat.factorial_pos r
  exact (List.bernoulliMass_upper_power s r hs).trans
    (div_le_div_of_nonneg_right (hp r) hf.le)

end PrimeFactorOscillations
namespace PrimeFactorOscillations

theorem exists_prime_logarithmic_benchmark (t : Real) (ht : 0 <= t) :
    exists r : Nat, Nat.Prime r /\
      t <= Real.log ((r - 1 : Nat) : Real) /\
        Real.log (r : Real) <= t + Real.log 4 := by
  let N := Nat.floor (Real.exp t) + 1
  have hNpos : 0 < N := by dsimp [N]; omega
  have hpExists := Nat.exists_prime_lt_and_le_two_mul N (Nat.ne_of_gt hNpos)
  choose r hr using hpExists
  have hNexp : Real.exp t <= (N : Real) := by
    simpa only [N, Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one (Real.exp t)).le
  have hNn : N <= r - 1 := by omega
  have hNnR : (N : Real) <= ((r - 1 : Nat) : Real) := by exact_mod_cast hNn
  have hlo : t <= Real.log ((r - 1 : Nat) : Real) := by
    calc
      _ = Real.log (Real.exp t) := (Real.log_exp t).symm
      _ <= _ := Real.log_le_log (Real.exp_pos t) (hNexp.trans hNnR)
  have hexp1 : 1 <= Real.exp t := by
    have hh := Real.exp_le_exp.mpr ht
    simpa only [Real.exp_zero] using hh
  have hfloor := Nat.floor_le (Real.exp_pos t).le
  have hNup : (N : Real) <= 2 * Real.exp t := by
    dsimp [N]
    rw [Nat.cast_add, Nat.cast_one]
    linarith only [hfloor, hexp1]
  have hrup : (r : Real) <= 2 * (N : Real) := by exact_mod_cast hr.2.2
  have hr4 : (r : Real) <= 4 * Real.exp t := by linarith only [hrup, hNup]
  have hrpos : 0 < (r : Real) := by exact_mod_cast hr.1.pos
  have hhi : Real.log (r : Real) <= t + Real.log 4 := by
    have hh := Real.log_le_log hrpos hr4
    rw [Real.log_mul (by norm_num : Not ((4 : Real) = 0)) (ne_of_gt (Real.exp_pos t)),
      Real.log_exp] at hh
    linarith only [hh]
  exact Exists.intro r (And.intro hr.1 (And.intro hlo hhi))

end PrimeFactorOscillations
namespace PrimeFactorOscillations

theorem regularPrimeLaw_interior_benchmark
    (P : Nat) (hP : 1 <= P) (eta : Nat -> Real)
    (nu K gamma rho : Real) (hnu : 0 < nu) (hK : 0 <= K)
    (hgamma : 0 < gamma) (hrho : 0 < rho) (hrg : rho < gamma) (hg1 : gamma < 1)
    (hunit : forall p, Nat.Prime p -> P < p -> 0 <= eta p /\ eta p < 1)
    (hupper : forall p, Nat.Prime p -> P < p ->
      eta p / (1 - eta p) <= 2 * nu / (p : Real))
    (herror : forall p, Nat.Prime p -> P < p ->
      abs (eta p / (1 - eta p) - nu / (p : Real)) <= K / (p : Real) ^ 2) :
    let E := primeTailOddsMertensError P nu K
    Filter.Eventually (fun k : Nat => 2 <= k /\
      exists q : Nat, Nat.Prime q /\ k ^ 2 <= q - 1 /\
        (k : Real) ^ gamma <= Real.log ((q - 1 : Nat) : Real) /\
        Real.log (q : Real) <= (k : Real) ^ gamma + Real.log 4 /\
        forall r : Nat, r <= 2 * k ->
          Real.exp (-(nu * (Real.log (k : Real) + Real.log 2) + E)) *
              ((nu * rho * Real.log (k : Real)) ^ r / (r.factorial : Real)) <=
            List.bernoulliMass
              ((q.primesBelow \ (P + 1).primesBelow).toList.map eta) r) atTop := by
  classical
  dsimp only
  let E := primeTailOddsMertensError P nu K
  have hb := Real.eventually_primePeak_benchmark_budgets P nu gamma rho E
    hnu hgamma hrho hrg hg1
  filter_upwards [hb] with k hk
  have hk2 := hk.1
  have hkp : 0 < (k : Real) := by exact_mod_cast (show 0 < k by omega)
  have hpow : 0 < (k : Real) ^ gamma := Real.rpow_pos_of_pos hkp gamma
  have hq0 := exists_prime_logarithmic_benchmark ((k : Real) ^ gamma) hpow.le
  choose q hq using hq0
  have hn2 : 2 <= q - 1 := by
    by_contra hn
    have hq2 : q = 2 := by have hp := hq.1.two_le; omega
    have hh := hq.2.1
    rw [hq2] at hh
    norm_num at hh
    exact (not_le_of_gt hpow) hh
  have hnp : 0 < ((q - 1 : Nat) : Real) := by
    exact_mod_cast (show 0 < q - 1 by omega)
  have hnq : ((q - 1 : Nat) : Real) <= (q : Real) := by
    exact_mod_cast (show q - 1 <= q by omega)
  have hlogup : Real.log ((q - 1 : Nat) : Real) <=
      (k : Real) ^ gamma + Real.log 4 :=
    (Real.log_le_log hnp hnq).trans hq.2.2
  have hkn := (hk.2.2 (q - 1) 0 hn2 (by omega) hq.2.1 hlogup).1
  refine And.intro hk2 (Exists.intro q
    (And.intro hq.1 (And.intro hkn (And.intro hq.2.1 (And.intro hq.2.2 ?_)))))
  intro r hr
  have hbud := hk.2.2 (q - 1) r hn2 hr hq.2.1 hlogup
  let G := nu * (Real.log (Real.log ((q - 1 : Nat) : Real)) -
      Real.log (Real.log (((k ^ 2 : Nat) : Real)))) -
    2 * E - (r : Real) * (2 * nu / (((k ^ 2 : Nat) : Real)))
  let B := nu * rho * Real.log (k : Real)
  have hB : 0 <= B := by
    dsimp [B]
    exact mul_nonneg (mul_pos hnu hrho).le
      (Real.log_nonneg (by exact_mod_cast (show 1 <= k by omega)))
  have hBG : B <= G := hbud.2.1
  have hG : 0 <= G := hB.trans hBG
  have hlow := primeTail_bernoulliMass_explicit_lower (q - 1) P (k ^ 2) r
    hn2 hP (by nlinarith only [hk2]) hk.2.1 hkn eta nu K hnu.le hK
    (fun p hp hPp _ => hunit p hp hPp)
    (fun p hp hPp _ => hupper p hp hPp)
    (fun p hp hPp _ => herror p hp hPp) hG
  have hpowers : forall j : Nat, B ^ j <= G ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [pow_succ, pow_succ]
        exact mul_le_mul ih hBG hB (pow_nonneg hG j)
  have hf : 0 < (r.factorial : Real) := by exact_mod_cast Nat.factorial_pos r
  have he : Real.exp (-(nu * (Real.log (k : Real) + Real.log 2) + E)) <=
      Real.exp (-(nu * Real.log (Real.log ((q - 1 : Nat) : Real)) + E)) :=
    Real.exp_le_exp.mpr (neg_le_neg hbud.2.2)
  have hh := mul_le_mul he (div_le_div_of_nonneg_right (hpowers r) hf.le)
    (div_nonneg (pow_nonneg hB r) hf.le) (Real.exp_pos _).le
  have hqpos : 0 < q := hq.1.pos
  have hqe : q - 1 + 1 = q := by omega
  rw [hqe] at hlow
  exact hh.trans hlow

end PrimeFactorOscillations

