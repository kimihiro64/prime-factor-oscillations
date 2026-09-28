import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Exp.CeilDoubleExp
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Pow.CeilDoubleExpCount
import PrimeFactorOscillations.Proof.Lower.WindowReversals

/-! # Double-exponential reversal supply from quantitative prime windows -/

set_option Elab.async false

namespace PrimeFactorOscillations

/-- The full lower-bound transfer, with the precise analytic supply input explicit. -/
theorem both_double_exp_reversal_supply_of_prime_windows (H : Nat)
    (hsupply : Filter.Eventually (fun N : Nat =>
      (N : Real) ^ ((1 : Real) / 3) <=
        (((Finset.Ioc N (2 * N)).filter (fun n =>
          2 <= ((Finset.Icc n (n + H)).filter Nat.Prime).card)).card : Real))
      Filter.atTop) :
    exists a : Real, 0 < a /\ exists K : Nat, 4 <= K /\ forall k : Nat, K <= k ->
      exists m : Nat, Real.exp (Real.exp (a * k)) <= (m : Real) /\
        HasAtLeastReversals (ordinaryDensity k) m /\
        HasAtLeastReversals (genericOddDensity k) m := by
  classical
  let beta : Real := 1 / (2 * ((H : Real) + 1))
  have hb : 0 < beta := by dsimp [beta]; positivity
  let F := Nat.factorial (4 * (H + 1))
  let B := F + H
  have hFnat : 0 < F := Nat.factorial_pos _
  have hBnat : 0 < B := by dsimp [B]; omega
  have hB : (0 : Real) < B := by exact_mod_cast hBnat
  choose N0 hN0 using Filter.eventually_atTop.mp hsupply
  choose K0 hK0 using both_reversal_counts_of_prime_windows H
  let C : Real := 8 + 48 * (B : Real) + N0 + F + 2 + H
  choose K1 hK1 using exists_nat_gt (C / beta)
  refine Exists.intro (beta / 2) (And.intro (by positivity)
    (Exists.intro (max K0 K1) (And.intro (hK0.1.trans (le_max_left _ _)) ?_)))
  intro k hk
  let t := beta * (k : Real)
  let N := Nat.ceil (Real.exp (Real.exp t))
  have hk1 : (K1 : Real) <= k := by exact_mod_cast (le_max_right K0 K1).trans hk
  have hscaled := mul_lt_mul_of_pos_left (hK1.trans_le hk1) hb
  have hcancel : beta * (C / beta) = C := by field_simp [ne_of_gt hb]
  rw [hcancel] at hscaled
  have hC : C <= t := hscaled.le
  have hNlarge : t <= (N : Real) := by
    have hceil := Nat.le_ceil (Real.exp (Real.exp t))
    change Real.exp (Real.exp t) <= (N : Real) at hceil
    linarith [Real.add_one_le_exp t, Real.add_one_le_exp (Real.exp t)]
  have hN00 : (0 : Real) <= N0 := Nat.cast_nonneg N0
  have hF0 : (0 : Real) <= F := Nat.cast_nonneg F
  have hH0 : (0 : Real) <= H := Nat.cast_nonneg H
  dsimp only [C] at hC
  have ht : 8 <= t := by linarith
  have htB : 48 * (B : Real) <= t := by linarith
  have hNN0 : N0 <= N := by
    exact_mod_cast (show (N0 : Real) <= N by linarith)
  have hNF : F + 2 <= N := by
    exact_mod_cast (show (F : Real) + 2 <= N by linarith)
  have hNH : H <= N := by
    exact_mod_cast (show (H : Real) <= N by linarith)
  have hNpos : 0 < N := Nat.ceil_pos.mpr (Real.exp_pos (Real.exp t))
  let S := (Finset.Ioc N (2 * N)).filter (fun n =>
    2 <= ((Finset.Icc n (n + H)).filter Nat.Prime).card)
  have hcluster : (N : Real) ^ ((1 : Real) / 3) <= (S.card : Real) := hN0 N hNN0
  have hSpos : 0 < S.card := by
    have hreal := (Real.rpow_pos_of_pos
      (show (0 : Real) < N by exact_mod_cast hNpos) ((1 : Real) / 3)).trans_le hcluster
    exact_mod_cast hreal
  have hrange : forall n, Membership.mem S n -> N <= n /\ n + H <= 2 * N + H := by
    intro n hn
    have hbounds := Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1
    exact And.intro hbounds.1.le (Nat.add_le_add_right hbounds.2 H)
  have hwindows : forall n, Membership.mem S n ->
      2 <= ((Finset.Icc n (n + H)).filter Nat.Prime).card := by
    intro n hn
    exact (Finset.mem_filter.mp hn).2
  have hband : forall p : Nat, N <= p -> p <= 2 * N + H ->
      ((3 : Real) / 4) * (1 / (2 * ((H : Real) + 1))) * k <=
          Real.log (Real.log (p - 1 : Nat)) /\
        Real.log (Real.log (p - 1 : Nat)) <=
          ((5 : Real) / 4) * (1 / (2 * ((H : Real) + 1))) * k := by
    intro p hp hpu
    have hp4 : p <= 4 * N := by omega
    have h := Real.ceil_double_exp_prime_prefix_band ht hp hp4
    simpa only [t, beta, mul_assoc] using h
  have hrev := hK0.2 k ((le_max_left K0 K1).trans hk) N (2 * N + H) S
    (Finset.card_pos.mp hSpos) hNF hrange hwindows hband
  choose m hcount hOrd hGen using hrev
  have hcountR : (S.card : Real) <= 2 * (B : Real) * ((m : Real) + 1) := by
    exact_mod_cast hcount
  have hgrowth := Real.double_exp_half_le_of_ceil_cuberoot_count ht hB htB
    (hcluster.trans hcountR)
  have harg : t / 2 = (beta / 2) * k := by dsimp [t]; ring
  rw [harg] at hgrowth
  exact Exists.intro m (And.intro hgrowth (And.intro hOrd hGen))

end PrimeFactorOscillations
