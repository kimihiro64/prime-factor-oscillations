/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PeakProductComparison

/-! # Complete uniform Euler-product comparison

Original reciprocal regularity gives the full growing-tilt product asymptotic,
uniform in every upper cutoff at least floor(z). Its positive constant is
identified with the convergent corrected Euler product and the exact Mertens
normalization, with no sign restriction on the comparison exponent.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter

namespace PrimeFactorOscillations

theorem regularPrimeLaws_uniform_growing_logProduct
    (P : Nat) (eta1 eta2 : Nat -> Real) (nu b1 b2 C1 C2 : Real)
    (hnu : 0 < nu) (hC1 : 0 <= C1) (hC2 : 0 <= C2)
    (h1 : forall p, Nat.Prime p -> P < p -> 0 < eta1 p)
    (h2 : forall p, Nat.Prime p -> P < p -> 0 < eta2 p)
    (herr1 : forall p, Nat.Prime p -> P < p ->
      abs (1 / eta1 p - (p : Real) / nu - b1) <= C1 / (p : Real))
    (herr2 : forall p, Nat.Prime p -> P < p ->
      abs (1 / eta2 p - (p : Real) / nu - b2) <= C2 / (p : Real))
    (hscale1 : forall p, Nat.Prime p -> P < p ->
      2 * (nu * (abs b1 + C1)) <= (p : Real))
    (hscale2 : forall p, Nat.Prime p -> P < p ->
      2 * (nu * (abs b2 + C2)) <= (p : Real)) :
    let theta := nu * (b2 - b1)
    let logC := (tsum (fun p : Nat => if Nat.Prime p /\ P < p then
      Real.log (eta1 p) - Real.log (eta2 p) +
        theta * Real.log (1 - 1 / (p : Real)) else 0)) +
          theta * (Real.eulerMascheroniConstant +
            (P + 1).primesBelow.sum (fun p => Real.log (1 - 1 / (p : Real))))
    forall epsilon : Real, 0 < epsilon -> exists Z : Real, 2 <= Z /\
      forall z : Real, Z <= z -> forall n : Nat, Nat.floor z <= n ->
        abs ((((n + 1).primesBelow \ (P + 1).primesBelow).sum
          (fun p => Real.log (1 + (z - 1) * eta1 p) -
            Real.log (1 + (z - 1) * eta2 p))) -
              theta * Real.log (Real.log z) - logC) <= epsilon := by
  classical
  dsimp only
  let theta := nu * (b2 - b1)
  let B1 := abs b1 + C1
  let B2 := abs b2 + C2
  let R := B1 + B2
  let D := 2 * nu ^ 2 * R
  let K := (2 * (nu * B1) ^ 2 + nu * C1) +
    (2 * (nu * B2) ^ 2 + nu * C2) + 2 * abs theta
  let f := fun z p => Real.log (1 + (z - 1) * eta1 p) -
    Real.log (1 + (z - 1) * eta2 p)
  let g := fun p => Real.log (eta1 p) - Real.log (eta2 p)
  let logC := (tsum (fun p : Nat => if Nat.Prime p /\ P < p then
    g p + theta * Real.log (1 - 1 / (p : Real)) else 0)) +
      theta * (Real.eulerMascheroniConstant +
        (P + 1).primesBelow.sum (fun p => Real.log (1 - 1 / (p : Real))))
  change forall epsilon : Real, 0 < epsilon -> exists Z : Real, 2 <= Z /\
    forall z : Real, Z <= z -> forall n : Nat, Nat.floor z <= n ->
      abs ((((n + 1).primesBelow \ (P + 1).primesBelow).sum (f z)) -
        theta * Real.log (Real.log z) - logC) <= epsilon
  have hB1 : 0 <= B1 := add_nonneg (abs_nonneg _) hC1
  have hB2 : 0 <= B2 := add_nonneg (abs_nonneg _) hC2
  have hR : 0 <= R := add_nonneg hB1 hB2
  have hD : 0 <= D := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg nu)) hR
  have hK : 0 <= K := add_nonneg
    (add_nonneg
      (add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (mul_nonneg hnu.le hC1))
      (add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (mul_nonneg hnu.le hC2)))
    (mul_nonneg (by norm_num) (abs_nonneg _))
  have hlocal (x eta b C : Real) (hx : 1 <= x) (heta : 0 < eta) (hC : 0 <= C)
      (herr : abs (1 / eta - x / nu - b) <= C / x)
      (hscale : 2 * (nu * (abs b + C)) <= x) :
      abs (1 / eta - x / nu) <= abs b + C /\
        nu / (2 * x) <= eta /\
          abs (eta - nu / x) <= 2 * nu ^ 2 * (abs b + C) / x ^ 2 := by
    have hx0 : 0 < x := zero_lt_one.trans_le hx
    have hcap : C / x <= C := by
      have hh := mul_le_mul_of_nonneg_left
        (one_div_le_one_div_of_le zero_lt_one hx) hC
      simpa only [div_one, mul_one, mul_one_div] using hh
    have hid : 1 / eta - x / nu = (1 / eta - x / nu - b) + b := by ring
    have hr : abs (1 / eta - x / nu) <= abs b + C := by
      rw [hid]
      calc
        _ <= abs (1 / eta - x / nu - b) + abs b := abs_add_le _ _
        _ <= C / x + abs b := add_le_add herr (le_refl _)
        _ <= C + abs b := add_le_add hcap (le_refl _)
        _ = _ := add_comm _ _
    have hh := Real.reciprocal_approximation_explicit x nu eta (abs b + C)
      hx0 hnu heta (add_nonneg (abs_nonneg _) hC) hr
      (by simpa only [mul_assoc] using hscale)
    exact And.intro hr (And.intro hh.1 hh.2.2)
  have hp1 (p : Nat) (hp : Nat.Prime p) (hP : P < p) :=
    hlocal (p : Real) (eta1 p) b1 C1 (by exact_mod_cast hp.one_le) (h1 p hp hP)
      hC1 (herr1 p hp hP) (hscale1 p hp hP)
  have hp2 (p : Nat) (hp : Nat.Prime p) (hP : P < p) :=
    hlocal (p : Real) (eta2 p) b2 C2 (by exact_mod_cast hp.one_le) (h2 p hp hP)
      hC2 (herr2 p hp hP) (hscale2 p hp hP)
  have hlower1 : forall p, Nat.Prime p -> P < p ->
      (nu / 2) / (p : Real) <= eta1 p := by
    intro p hp hP
    have hid : (nu / 2) / (p : Real) = nu / (2 * (p : Real)) := by ring
    rw [hid]
    exact (hp1 p hp hP).2.1
  have hlower2 : forall p, Nat.Prime p -> P < p ->
      (nu / 2) / (p : Real) <= eta2 p := by
    intro p hp hP
    have hid : (nu / 2) / (p : Real) = nu / (2 * (p : Real)) := by ring
    rw [hid]
    exact (hp2 p hp hP).2.1
  have hdiff : forall p, Nat.Prime p -> P < p ->
      abs (eta1 p - eta2 p) <= D / (p : Real) ^ 2 := by
    intro p hp hP
    calc
      _ <= abs (eta1 p - nu / (p : Real)) + abs (nu / (p : Real) - eta2 p) :=
        abs_sub_le _ _ _
      _ <= 2 * nu ^ 2 * B1 / (p : Real) ^ 2 +
          2 * nu ^ 2 * B2 / (p : Real) ^ 2 := by
        apply add_le_add (hp1 p hp hP).2.2
        rw [abs_sub_comm]
        exact (hp2 p hp hP).2.2
      _ = _ := by dsimp [D, R]; ring
  have hinv : forall p, Nat.Prime p -> P < p ->
      abs (1 / eta1 p - 1 / eta2 p) <= R := by
    intro p hp hP
    calc
      _ <= abs (1 / eta1 p - (p : Real) / nu) +
          abs ((p : Real) / nu - 1 / eta2 p) := abs_sub_le _ _ _
      _ <= B1 + B2 := by
        apply add_le_add (hp1 p hp hP).1
        rw [abs_sub_comm]
        exact (hp2 p hp hP).1
      _ = _ := rfl
  have hres : forall p, Nat.Prime p -> P < p ->
      abs (g p + theta * Real.log (1 - 1 / (p : Real))) <= K / (p : Real) ^ 2 := by
    intro p hp hP
    exact Real.reciprocalRegularity_renormalized_log_ratio_bound (p : Real) nu
      (eta1 p) (eta2 p) b1 b2 C1 C2 (by exact_mod_cast hp.two_le) hnu
      (h1 p hp hP) (h2 p hp hP) hC1 hC2 (herr1 p hp hP) (herr2 p hp hP)
      (hscale1 p hp hP) (hscale2 p hp hP)
  have ht : Tendsto (fun z : Real =>
      ((((Nat.floor z) + 1).primesBelow \ (P + 1).primesBelow).sum g) -
        theta * Real.log (Real.log z)) atTop (nhds logC) :=
    tendsto_renormalized_primeLogRatio P g theta K hK hres
  intro epsilon he
  have hsat := regularPrimeLaws_uniform_logProduct_saturation P eta1 eta2 (nu / 2) D R
    (div_pos hnu (by norm_num)) hD hR h1 h2 hlower1 hlower2 hdiff hinv
    (epsilon / 2) (half_pos he)
  choose Z1 hZ1 using hsat
  have hev := (Metric.tendsto_nhds.1 ht) (epsilon / 2) (half_pos he)
  have hev' : Filter.Eventually (fun z : Real =>
      abs (((((Nat.floor z) + 1).primesBelow \ (P + 1).primesBelow).sum g) -
        theta * Real.log (Real.log z) - logC) < epsilon / 2) atTop := by
    simpa only [Real.dist_eq] using hev
  have hex := eventually_atTop.1 hev'
  choose Z0 hZ0 using hex
  let Z := max (2 : Real) (max Z0 Z1)
  refine Exists.intro Z (And.intro (le_max_left _ _) ?_)
  intro z hz n hn
  have hz0 : Z0 <= z := (le_max_left _ _).trans ((le_max_right _ _).trans hz)
  have hz1 : Z1 <= z := (le_max_right _ _).trans ((le_max_right _ _).trans hz)
  have hs := hZ1 z hz1 n hn
  have he0 := hZ0 z hz0
  let U := ((n + 1).primesBelow \ (P + 1).primesBelow).sum (f z)
  let V := ((Nat.floor z + 1).primesBelow \ (P + 1).primesBelow).sum g
  have hs' : abs (U - V) <= epsilon / 2 := hs
  have he0' : abs (V - theta * Real.log (Real.log z) - logC) < epsilon / 2 := he0
  change abs (U - theta * Real.log (Real.log z) - logC) <= epsilon
  have hid : U - theta * Real.log (Real.log z) - logC =
      (U - V) + (V - theta * Real.log (Real.log z) - logC) := by ring
  rw [hid]
  have hh := abs_add_le (U - V) (V - theta * Real.log (Real.log z) - logC)
  linarith only [hh, hs', he0']

theorem regularPrimeLaws_uniform_growing_product_ratio
    (P : Nat) (eta1 eta2 : Nat -> Real) (nu b1 b2 C1 C2 : Real)
    (hnu : 0 < nu) (hC1 : 0 <= C1) (hC2 : 0 <= C2)
    (h1 : forall p, Nat.Prime p -> P < p -> 0 < eta1 p)
    (h2 : forall p, Nat.Prime p -> P < p -> 0 < eta2 p)
    (herr1 : forall p, Nat.Prime p -> P < p ->
      abs (1 / eta1 p - (p : Real) / nu - b1) <= C1 / (p : Real))
    (herr2 : forall p, Nat.Prime p -> P < p ->
      abs (1 / eta2 p - (p : Real) / nu - b2) <= C2 / (p : Real))
    (hscale1 : forall p, Nat.Prime p -> P < p ->
      2 * (nu * (abs b1 + C1)) <= (p : Real))
    (hscale2 : forall p, Nat.Prime p -> P < p ->
      2 * (nu * (abs b2 + C2)) <= (p : Real)) :
    let theta := nu * (b2 - b1)
    let logC := (tsum (fun p : Nat => if Nat.Prime p /\ P < p then
      Real.log (eta1 p) - Real.log (eta2 p) +
        theta * Real.log (1 - 1 / (p : Real)) else 0)) +
          theta * (Real.eulerMascheroniConstant +
            (P + 1).primesBelow.sum (fun p => Real.log (1 - 1 / (p : Real))))
    0 < Real.exp logC /\ forall epsilon : Real, 0 < epsilon ->
      exists Z : Real, 2 <= Z /\ forall z : Real, Z <= z ->
        forall n : Nat, Nat.floor z <= n ->
          abs (((((n + 1).primesBelow \ (P + 1).primesBelow).prod
            (fun p => (1 + (z - 1) * eta1 p) / (1 + (z - 1) * eta2 p))) /
              (Real.exp logC * Real.rpow (Real.log z) theta)) - 1) <= epsilon := by
  classical
  dsimp only
  let theta := nu * (b2 - b1)
  let logC := (tsum (fun p : Nat => if Nat.Prime p /\ P < p then
    Real.log (eta1 p) - Real.log (eta2 p) +
      theta * Real.log (1 - 1 / (p : Real)) else 0)) +
        theta * (Real.eulerMascheroniConstant +
          (P + 1).primesBelow.sum (fun p => Real.log (1 - 1 / (p : Real))))
  change 0 < Real.exp logC /\ forall epsilon : Real, 0 < epsilon ->
    exists Z : Real, 2 <= Z /\ forall z : Real, Z <= z ->
      forall n : Nat, Nat.floor z <= n ->
        abs (((((n + 1).primesBelow \ (P + 1).primesBelow).prod
          (fun p => (1 + (z - 1) * eta1 p) / (1 + (z - 1) * eta2 p))) /
            (Real.exp logC * Real.rpow (Real.log z) theta)) - 1) <= epsilon
  refine And.intro (Real.exp_pos logC) ?_
  intro epsilon he
  have hct : ContinuousAt Real.exp (0 : Real) := Real.continuous_exp.continuousAt
  have hd := (Metric.continuousAt_iff.1 hct) epsilon he
  choose delta hdelta using hd
  have hl := regularPrimeLaws_uniform_growing_logProduct P eta1 eta2 nu b1 b2 C1 C2
    hnu hC1 hC2 h1 h2 herr1 herr2 hscale1 hscale2 (delta / 2) (half_pos hdelta.1)
  choose Z hZ using hl
  refine Exists.intro Z (And.intro hZ.1 ?_)
  intro z hz n hn
  let S := (n + 1).primesBelow \ (P + 1).primesBelow
  let f := fun p => Real.log (1 + (z - 1) * eta1 p) -
    Real.log (1 + (z - 1) * eta2 p)
  let A := S.prod (fun p => (1 + (z - 1) * eta1 p) / (1 + (z - 1) * eta2 p))
  let t := S.sum f - theta * Real.log (Real.log z) - logC
  have hs : abs t <= delta / 2 := hZ.2 z hz n hn
  have hdist : dist t (0 : Real) < delta := by
    rw [Real.dist_eq, sub_zero]
    exact hs.trans_lt (half_lt_self hdelta.1)
  have hexp : dist (Real.exp t) (Real.exp 0) < epsilon := by
    apply hdelta.2
    exact hdist
  have hz2 : 2 <= z := hZ.1.trans hz
  have hu : 0 < z - 1 := by linarith only [hz2]
  have hS (p : Nat) (hp : Membership.mem S p) : Nat.Prime p /\ P < p := by
    have hh := Finset.mem_sdiff.mp hp
    have hprime := (Nat.mem_primesBelow.mp hh.1).2
    have hP : P < p := by
      by_contra hnot
      exact hh.2 (Nat.mem_primesBelow.mpr (And.intro (by omega) hprime))
    exact And.intro hprime hP
  have hfac1 (p : Nat) (hp : Membership.mem S p) : 0 < 1 + (z - 1) * eta1 p :=
    add_pos zero_lt_one (mul_pos hu (h1 p (hS p hp).1 (hS p hp).2))
  have hfac2 (p : Nat) (hp : Membership.mem S p) : 0 < 1 + (z - 1) * eta2 p :=
    add_pos zero_lt_one (mul_pos hu (h2 p (hS p hp).1 (hS p hp).2))
  have hA : 0 < A := Finset.prod_pos (fun p hp => div_pos (hfac1 p hp) (hfac2 p hp))
  have hlog : S.sum f = Real.log A := by
    rw [Real.log_prod (fun p hp => ne_of_gt (div_pos (hfac1 p hp) (hfac2 p hp)))]
    apply Finset.sum_congr rfl
    intro p hp
    exact (Real.log_div (ne_of_gt (hfac1 p hp)) (ne_of_gt (hfac2 p hp))).symm
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith only [hz2])
  have hrpow : Real.rpow (Real.log z) theta =
      Real.exp (Real.log (Real.log z) * theta) := Real.rpow_def_of_pos hlogz theta
  have hid : A / (Real.exp logC * Real.rpow (Real.log z) theta) = Real.exp t := by
    dsimp only [t]
    rw [hlog, hrpow,
      mul_comm (Real.log (Real.log z)) theta, Real.exp_sub, Real.exp_sub,
      Real.exp_log hA]
    field_simp [ne_of_gt (Real.exp_pos logC),
      ne_of_gt (Real.exp_pos (theta * Real.log (Real.log z)))]
  change abs (A / (Real.exp logC * Real.rpow (Real.log z) theta) - 1) <= epsilon
  rw [hid]
  exact le_of_lt (by simpa only [Real.dist_eq, Real.exp_zero] using hexp)


theorem regularPrimeLaws_hasProd_renormalized_ratio
    (P : Nat) (eta1 eta2 : Nat -> Real) (nu b1 b2 C1 C2 : Real)
    (hnu : 0 < nu) (hC1 : 0 <= C1) (hC2 : 0 <= C2)
    (h1 : forall p, Nat.Prime p -> P < p -> 0 < eta1 p)
    (h2 : forall p, Nat.Prime p -> P < p -> 0 < eta2 p)
    (herr1 : forall p, Nat.Prime p -> P < p ->
      abs (1 / eta1 p - (p : Real) / nu - b1) <= C1 / (p : Real))
    (herr2 : forall p, Nat.Prime p -> P < p ->
      abs (1 / eta2 p - (p : Real) / nu - b2) <= C2 / (p : Real))
    (hscale1 : forall p, Nat.Prime p -> P < p ->
      2 * (nu * (abs b1 + C1)) <= (p : Real))
    (hscale2 : forall p, Nat.Prime p -> P < p ->
      2 * (nu * (abs b2 + C2)) <= (p : Real)) :
    let theta := nu * (b2 - b1)
    HasProd (fun p : Nat => if Nat.Prime p /\ P < p then
      (eta1 p / eta2 p) * Real.rpow (1 - 1 / (p : Real)) theta else 1)
      (Real.exp (tsum (fun p : Nat => if Nat.Prime p /\ P < p then
        Real.log (eta1 p) - Real.log (eta2 p) +
          theta * Real.log (1 - 1 / (p : Real)) else 0))) := by
  classical
  dsimp only
  let theta := nu * (b2 - b1)
  let residual := fun p : Nat => if Nat.Prime p /\ P < p then
    Real.log (eta1 p) - Real.log (eta2 p) +
      theta * Real.log (1 - 1 / (p : Real)) else 0
  let factor := fun p : Nat => if Nat.Prime p /\ P < p then
    (eta1 p / eta2 p) * Real.rpow (1 - 1 / (p : Real)) theta else 1
  let K := (2 * (nu * (abs b1 + C1)) ^ 2 + nu * C1) +
    (2 * (nu * (abs b2 + C2)) ^ 2 + nu * C2) + 2 * abs theta
  have hK : 0 <= K := add_nonneg
    (add_nonneg
      (add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (mul_nonneg hnu.le hC1))
      (add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (mul_nonneg hnu.le hC2)))
    (mul_nonneg (by norm_num) (abs_nonneg _))
  have hb : Summable (fun p : Nat => K * (1 / (p : Real) ^ 2)) :=
    (Real.summable_one_div_nat_pow.mpr (by decide)).mul_left K
  have hr : Summable residual := by
    apply hb.of_norm_bounded
    intro p
    rw [Real.norm_eq_abs]
    dsimp only [residual]
    by_cases hp : Nat.Prime p /\ P < p
    next =>
      rw [ite_eq_left hp]
      have hh := Real.reciprocalRegularity_renormalized_log_ratio_bound (p : Real) nu
        (eta1 p) (eta2 p) b1 b2 C1 C2 (by exact_mod_cast hp.1.two_le) hnu
        (h1 p hp.1 hp.2) (h2 p hp.1 hp.2) hC1 hC2 (herr1 p hp.1 hp.2)
        (herr2 p hp.1 hp.2) (hscale1 p hp.1 hp.2) (hscale2 p hp.1 hp.2)
      calc
        _ <= K / (p : Real) ^ 2 := hh
        _ = _ := by ring
    next =>
      rw [ite_eq_right hp, abs_zero]
      exact mul_nonneg hK (div_nonneg (by norm_num) (sq_nonneg _))
  have ht : Tendsto (fun S : Finset Nat => Real.exp (S.sum residual))
      atTop (nhds (Real.exp (tsum residual))) :=
    Real.continuous_exp.continuousAt.tendsto.comp hr.hasSum
  change Tendsto (fun S : Finset Nat => S.prod factor)
    atTop (nhds (Real.exp (tsum residual)))
  apply ht.congr'
  apply Filter.Eventually.of_forall
  intro S
  dsimp only
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro p hpS
  by_cases hp : Nat.Prime p /\ P < p
  next =>
    dsimp only [residual, factor]
    rw [ite_eq_left hp, ite_eq_left hp]
    have hpR : 1 < (p : Real) := by exact_mod_cast hp.1.one_lt
    have hp0 : 0 < (p : Real) := by linarith only [hpR]
    have hbase : 0 < 1 - 1 / (p : Real) :=
      sub_pos.mpr ((div_lt_one hp0).mpr hpR)
    have hrpow : Real.rpow (1 - 1 / (p : Real)) theta =
        Real.exp (Real.log (1 - 1 / (p : Real)) * theta) :=
      Real.rpow_def_of_pos hbase theta
    rw [Real.exp_add, Real.exp_sub, Real.exp_log (h1 p hp.1 hp.2),
      Real.exp_log (h2 p hp.1 hp.2), hrpow,
      mul_comm (Real.log (1 - 1 / (p : Real))) theta]
  next =>
    dsimp only [residual, factor]
    rw [ite_eq_right hp, ite_eq_right hp, Real.exp_zero]

theorem regularPrimeLaws_euler_constant_eq
    (P : Nat) (eta1 eta2 : Nat -> Real) (nu b1 b2 C1 C2 : Real)
    (hnu : 0 < nu) (hC1 : 0 <= C1) (hC2 : 0 <= C2)
    (h1 : forall p, Nat.Prime p -> P < p -> 0 < eta1 p)
    (h2 : forall p, Nat.Prime p -> P < p -> 0 < eta2 p)
    (herr1 : forall p, Nat.Prime p -> P < p ->
      abs (1 / eta1 p - (p : Real) / nu - b1) <= C1 / (p : Real))
    (herr2 : forall p, Nat.Prime p -> P < p ->
      abs (1 / eta2 p - (p : Real) / nu - b2) <= C2 / (p : Real))
    (hscale1 : forall p, Nat.Prime p -> P < p ->
      2 * (nu * (abs b1 + C1)) <= (p : Real))
    (hscale2 : forall p, Nat.Prime p -> P < p ->
      2 * (nu * (abs b2 + C2)) <= (p : Real)) :
    let theta := nu * (b2 - b1)
    Real.exp ((tsum (fun p : Nat => if Nat.Prime p /\ P < p then
      Real.log (eta1 p) - Real.log (eta2 p) +
        theta * Real.log (1 - 1 / (p : Real)) else 0)) +
          theta * (Real.eulerMascheroniConstant +
            (P + 1).primesBelow.sum (fun p => Real.log (1 - 1 / (p : Real))))) =
      Real.rpow (Real.exp Real.eulerMascheroniConstant *
        (P + 1).primesBelow.prod (fun p => 1 - 1 / (p : Real))) theta *
          tprod (fun p : Nat => if Nat.Prime p /\ P < p then
            (eta1 p / eta2 p) * Real.rpow (1 - 1 / (p : Real)) theta else 1) := by
  classical
  dsimp only
  let theta := nu * (b2 - b1)
  let residual := fun p : Nat => if Nat.Prime p /\ P < p then
    Real.log (eta1 p) - Real.log (eta2 p) +
      theta * Real.log (1 - 1 / (p : Real)) else 0
  let factor := fun p : Nat => if Nat.Prime p /\ P < p then
    (eta1 p / eta2 p) * Real.rpow (1 - 1 / (p : Real)) theta else 1
  let S := (P + 1).primesBelow
  let cP := Real.exp Real.eulerMascheroniConstant * S.prod (fun p => 1 - 1 / (p : Real))
  have hprod : HasProd factor (Real.exp (tsum residual)) :=
    regularPrimeLaws_hasProd_renormalized_ratio P eta1 eta2 nu b1 b2 C1 C2
      hnu hC1 hC2 h1 h2 herr1 herr2 hscale1 hscale2
  have htp : tprod factor = Real.exp (tsum residual) := hprod.tprod_eq
  have hbase (p : Nat) (hp : Membership.mem S p) : 0 < 1 - 1 / (p : Real) := by
    have hprime := (Nat.mem_primesBelow.mp hp).2
    have hpR : 1 < (p : Real) := by exact_mod_cast hprime.one_lt
    have hp0 : 0 < (p : Real) := by linarith only [hpR]
    exact sub_pos.mpr ((div_lt_one hp0).mpr hpR)
  have hsmall : 0 < S.prod (fun p => 1 - 1 / (p : Real)) := Finset.prod_pos hbase
  have hcp : 0 < cP := mul_pos (Real.exp_pos _) hsmall
  have hlogcp : Real.log cP = Real.eulerMascheroniConstant +
      S.sum (fun p => Real.log (1 - 1 / (p : Real))) := by
    dsimp only [cP]
    rw [Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt hsmall), Real.log_exp,
      Real.log_prod (fun p hp => ne_of_gt (hbase p hp))]
  have hrpow : Real.rpow cP theta = Real.exp (Real.log cP * theta) :=
    Real.rpow_def_of_pos hcp theta
  change Real.exp ((tsum residual) + theta * (Real.eulerMascheroniConstant +
    S.sum (fun p => Real.log (1 - 1 / (p : Real))))) = Real.rpow cP theta * tprod factor
  rw [hrpow, hlogcp, htp, Real.exp_add,
    mul_comm (Real.eulerMascheroniConstant +
      S.sum (fun p => Real.log (1 - 1 / (p : Real)))) theta]
  exact mul_comm _ _


end PrimeFactorOscillations
