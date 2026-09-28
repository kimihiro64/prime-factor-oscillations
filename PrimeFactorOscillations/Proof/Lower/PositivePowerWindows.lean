import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Exp.CeilDoubleExpAdditive
import PrimeFactorOscillations.Mathlib.Analysis.SpecialFunctions.Pow.CeilDoubleExpPowerCount
import PrimeFactorOscillations.Proof.Lower.AdditiveWindowReversals

/-! # Every rate below the quantitative prime-window threshold -/

set_option autoImplicit false

namespace PrimeFactorOscillations

/-- Any fixed positive-power dyadic prime-window supply gives every lower rate
strictly below 1/(H+1), for both canonical families. -/
theorem both_reversal_supply_of_positive_power_windows (H : Nat)
    (delta a : Real) (hd : 0 < delta) (ha : 0 < a)
    (haH : a < 1 / ((H : Real) + 1))
    (hsupply : Filter.Eventually (fun N : Nat =>
      (N : Real) ^ delta <=
        (((Finset.Ioc N (2 * N)).filter (fun n =>
          2 <= ((Finset.Icc n (n + H)).filter Nat.Prime).card)).card : Real))
      Filter.atTop) :
    exists K : Nat, 4 <= K /\ forall k : Nat, K <= k ->
      exists m : Nat, Real.exp (Real.exp (a * k)) <= (m : Real) /\
        HasAtLeastReversals (ordinaryDensity k) m /\
        HasAtLeastReversals (genericOddDensity k) m := by
  classical
  have hH : (0 : Real) < (H : Real) + 1 := by positivity
  have hhalf : 1 / (2 * ((H : Real) + 1)) < 1 / ((H : Real) + 1) :=
    one_div_lt_one_div_of_lt hH (by linarith)
  choose b hb using exists_between (max_lt haH hhalf)
  have hab : a < b := (le_max_left _ _).trans_lt hb.1
  have hbLow : 1 / (2 * ((H : Real) + 1)) < b :=
    (le_max_right _ _).trans_lt hb.1
  have hb0 : 0 < b := ha.trans hab
  have hmargin : ((H : Real) + 1) * b < 1 := by
    have h := mul_lt_mul_of_pos_left hb.2 hH
    have hc : ((H : Real) + 1) * (1 / ((H : Real) + 1)) = 1 := by field_simp
    rwa [hc] at h
  let F := Nat.factorial (4 * (H + 1))
  let B := F + H
  have hFnat : 0 < F := Nat.factorial_pos _
  have hBnat : 0 < B := by dsimp [B]; omega
  have hB : (0 : Real) < B := by exact_mod_cast hBnat
  choose N0 hN0 using Filter.eventually_atTop.mp hsupply
  choose K0 hK0 using both_reversal_counts_of_prime_windows_additive H b hbLow hmargin
  let C : Real := 8 + 8 * (B : Real) / delta + N0 + F + 2 + H
  choose K1 hK1 using exists_nat_gt (max (C / b) (Real.log (2 / delta) / (b - a)))
  refine Exists.intro (max K0 K1) (And.intro (hK0.1.trans (le_max_left _ _)) ?_)
  intro k hk
  let t := b * (k : Real)
  let N := Nat.ceil (Real.exp (Real.exp t))
  have hk1 : (K1 : Real) <= k := by exact_mod_cast (le_max_right K0 K1).trans hk
  have hscaled := mul_lt_mul_of_pos_left
    (((le_max_left _ _).trans_lt hK1).trans_le hk1) hb0
  have hcancel : b * (C / b) = C := by field_simp [ne_of_gt hb0]
  rw [hcancel] at hscaled
  have hC : C <= t := hscaled.le
  have hdiff : 0 < b - a := sub_pos.mpr hab
  have hgapScaled := mul_lt_mul_of_pos_left
    (((le_max_right _ _).trans_lt hK1).trans_le hk1) hdiff
  have hgapCancel : (b - a) * (Real.log (2 / delta) / (b - a)) =
      Real.log (2 / delta) := by field_simp [ne_of_gt hdiff]
  rw [hgapCancel] at hgapScaled
  have hgap : a * k + Real.log (2 / delta) <= t := by
    dsimp [t]
    nlinarith only [hgapScaled]
  have hNlarge : t <= (N : Real) := by
    have hceil := Nat.le_ceil (Real.exp (Real.exp t))
    change Real.exp (Real.exp t) <= (N : Real) at hceil
    linarith [Real.add_one_le_exp t, Real.add_one_le_exp (Real.exp t)]
  have hN00 : (0 : Real) <= N0 := Nat.cast_nonneg N0
  have hF0 : (0 : Real) <= F := Nat.cast_nonneg F
  have hH0 : (0 : Real) <= H := Nat.cast_nonneg H
  have hBd0 : (0 : Real) <= 8 * (B : Real) / delta := by positivity
  dsimp only [C] at hC
  have ht : 8 <= t := by linarith
  have htB : 8 * (B : Real) <= delta * t := by
    have h := mul_le_mul_of_nonneg_left
      (show 8 * (B : Real) / delta <= t by linarith) hd.le
    have hc : delta * (8 * (B : Real) / delta) = 8 * (B : Real) := by
      field_simp [ne_of_gt hd]
    rwa [hc] at h
  have hNN0 : N0 <= N := by
    exact_mod_cast (show (N0 : Real) <= N by linarith)
  have hNF : F + 2 <= N := by
    exact_mod_cast (show (F : Real) + 2 <= N by linarith)
  have hNH : H <= N := by
    exact_mod_cast (show (H : Real) <= N by linarith)
  have hNpos : 0 < N := Nat.ceil_pos.mpr (Real.exp_pos (Real.exp t))
  let S := (Finset.Ioc N (2 * N)).filter (fun n =>
    2 <= ((Finset.Icc n (n + H)).filter Nat.Prime).card)
  have hcluster : (N : Real) ^ delta <= (S.card : Real) := hN0 N hNN0
  have hSpos : 0 < S.card := by
    have hreal := (Real.rpow_pos_of_pos
      (show (0 : Real) < N by exact_mod_cast hNpos) delta).trans_le hcluster
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
      b * k - Real.log 2 <= Real.log (Real.log (p - 1 : Nat)) /\
        Real.log (Real.log (p - 1 : Nat)) <= b * k + Real.log 2 := by
    intro p hp hpu
    have hp4 : p <= 4 * N := by omega
    exact Real.ceil_double_exp_prime_prefix_additive_band ht hp hp4
  have hrev := hK0.2 k ((le_max_left K0 K1).trans hk) N (2 * N + H) S
    (Finset.card_pos.mp hSpos) hNF hrange hwindows hband
  choose m hcount hOrd hGen using hrev
  have hcountR : (S.card : Real) <= 2 * (B : Real) * ((m : Real) + 1) := by
    exact_mod_cast hcount
  have hgrowth := Real.double_exp_le_of_ceil_positive_power_count hd hgap hB htB
    (hcluster.trans hcountR)
  exact Exists.intro m (And.intro hgrowth (And.intro hOrd hGen))

end PrimeFactorOscillations
