/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Helpers.PeakPrimePrefixBounds
import PrimeFactorOscillations.Helpers.PrimeProfileClockLimit
import PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliAsymptotics
import PrimeFactorOscillations.Mathlib.Probability.Distributions.FiniteBernoulliProductComparison

/-! # Uniform growing-product comparison for regular prime laws

The proved Mertens inputs and exact finite logarithmic bounds give cutoff-uniform
saturation of tilted products and the convergent Euler-Mascheroni normalization.
All prime sums retain their explicit finite supports.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter

namespace Real

theorem tendsto_logLog_mul_sub_logLog (c : Real) (hc : 0 < c) :
    Tendsto (fun x : Real => log (log (c * x)) - log (log x))
      atTop (nhds 0) := by
  have hr : Tendsto (fun x : Real => log c / log x + 1) atTop (nhds (1 : Real)) := by
    simpa only [zero_add] using (tendsto_log_atTop.const_div_atTop (log c)).add_const 1
  have hh := (continuousAt_log (by norm_num : Not ((1 : Real) = 0))).tendsto.comp hr
  have hl : Tendsto (fun x : Real => log (log c / log x + 1)) atTop (nhds 0) := by
    simpa only [Function.comp_def, log_one] using hh
  apply hl.congr'
  filter_upwards [eventually_ge_atTop (max (2 : Real) (2 / c))] with x hx
  have hx2 : 2 <= x := (le_max_left _ _).trans hx
  have hxc : 2 / c <= x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith only [hx2]
  have hcx2 : 2 <= c * x := by
    calc
      _ = c * (2 / c) := by field_simp [ne_of_gt hc]
      _ <= _ := mul_le_mul_of_nonneg_left hxc hc.le
  have hlogx : 0 < log x := log_pos (by linarith only [hx2])
  have hlogcx : 0 < log (c * x) := log_pos (by linarith only [hcx2])
  symm
  rw [<- log_div (ne_of_gt hlogcx) (ne_of_gt hlogx),
    log_mul (ne_of_gt hc) (ne_of_gt hx0)]
  congr 1
  field_simp [ne_of_gt hlogx]

end Real

namespace PrimeFactorOscillations

theorem tendsto_reciprocalPrimePrefix_error :
    Tendsto (fun n : Nat =>
      PrimeFactorUnimodality.reciprocalPrimeSumBelow (n + 1) -
        Real.log (Real.log (n : Real)) - Mertens.M) atTop (nhds 0) := by
  have hlog : Tendsto (fun n : Nat => Real.log (n : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := Real))
  apply squeeze_zero_norm'
    (a := fun n : Nat =>
      abs PrimeFactorUnimodality.mertensErrorConstant / Real.log (n : Real)) ?_
    (hlog.const_div_atTop (abs PrimeFactorUnimodality.mertensErrorConstant))
  filter_upwards [eventually_ge_atTop (2 : Nat)] with n hn
  rw [Real.norm_eq_abs]
  have hh := PrimeFactorUnimodality.hasMertensReciprocalPrimeEstimate n hn
  have hnlog : 0 <= Real.log (n : Real) :=
    Real.log_nonneg (by exact_mod_cast (show 1 <= n by omega))
  exact hh.trans
    (div_le_div_of_nonneg_right (le_abs_self _) hnlog)

theorem tendsto_reciprocalPrimePrefix_mul_difference (c : Nat) (hc : 1 <= c) :
    Tendsto (fun m : Nat =>
      PrimeFactorUnimodality.reciprocalPrimeSumBelow (m * c + 1) -
        PrimeFactorUnimodality.reciprocalPrimeSumBelow (m + 1))
      atTop (nhds 0) := by
  have hm : Tendsto (fun m : Nat => m * c) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with m hmb
    have hmc : m <= m * c := by nlinarith only [hc]
    exact hmb.trans hmc
  have hupper := tendsto_reciprocalPrimePrefix_error.comp hm
  have hlower := tendsto_reciprocalPrimePrefix_error
  have hc0 : 0 < (c : Real) := by exact_mod_cast (show 0 < c by omega)
  have hl := (Real.tendsto_logLog_mul_sub_logLog (c : Real) hc0).comp
    (tendsto_natCast_atTop_atTop (R := Real))
  have hln : Tendsto (fun m : Nat =>
      Real.log (Real.log ((m * c : Nat) : Real)) - Real.log (Real.log (m : Real)))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, Nat.cast_mul, mul_comm] using hl
  have ht := (hupper.sub hlower).add hln
  have ht0 : Tendsto (fun m : Nat =>
      (PrimeFactorUnimodality.reciprocalPrimeSumBelow (m * c + 1) -
        Real.log (Real.log ((m * c : Nat) : Real)) - Mertens.M -
          (PrimeFactorUnimodality.reciprocalPrimeSumBelow (m + 1) -
            Real.log (Real.log (m : Real)) - Mertens.M)) +
              (Real.log (Real.log ((m * c : Nat) : Real)) -
                Real.log (Real.log (m : Real)))) atTop (nhds 0) := by
    simpa only [Function.comp_def, sub_self, add_zero] using ht
  apply ht0.congr'
  apply Filter.Eventually.of_forall
  intro m
  ring

end PrimeFactorOscillations

namespace PrimeFactorOscillations

theorem primeLogSaturation_uniform_multiplicative_scale
    (P : Nat) (f : Real -> Nat -> Real) (g : Nat -> Real) (R M D : Real)
    (hR : 0 <= R) (hM : 0 <= M) (hD : 0 <= D)
    (hclose : forall z, 2 <= z -> forall p, Nat.Prime p -> P < p ->
      abs (f z p - g p) <= R / (z - 1))
    (hfm : forall z, 2 <= z -> forall p, Nat.Prime p -> P < p ->
      abs (f z p) <= M / (p : Real))
    (hgm : forall p, Nat.Prime p -> P < p -> abs (g p) <= M / (p : Real))
    (hfh : forall z, 2 <= z -> forall p, Nat.Prime p -> P < p ->
      abs (f z p) <= z * D / (p : Real) ^ 2)
    (epsilon : Real) (he : 0 < epsilon) :
    exists H : Nat, 2 <= H /\
      Filter.Eventually (fun m : Nat => forall (z : Real) (q n : Nat),
        (H : Real) * (m : Real) <= z ->
        z <= (H : Real) * ((m : Real) + 1) ->
        m <= q -> q <= m * H ^ 2 -> q <= n ->
          abs ((((n + 1).primesBelow \ (P + 1).primesBelow).sum (f z)) -
            (((q + 1).primesBelow \ (P + 1).primesBelow).sum g)) <= epsilon) atTop := by
  have hnat := tendsto_natCast_atTop_atTop (R := Real)
  have hcost : Tendsto (fun H : Nat => 2 * R / (H : Real) + 4 * D / (H : Real))
      atTop (nhds 0) := by
    simpa only [zero_add] using
      (hnat.const_div_atTop (2 * R)).add (hnat.const_div_atTop (4 * D))
  have heCost := (tendsto_order.1 hcost).2 (epsilon / 2) (half_pos he)
  have hex := (heCost.and (eventually_ge_atTop (2 : Nat))).exists
  choose H hH using hex
  have hHsq : 1 <= H ^ 2 := by nlinarith only [hH.2]
  have hw := (tendsto_reciprocalPrimePrefix_mul_difference (H ^ 2) hHsq).const_mul (2 * M)
  have heWindow := (tendsto_order.1 hw).2 (epsilon / 2)
    (by simpa only [mul_zero] using half_pos he)
  refine Exists.intro H (And.intro hH.2 ?_)
  filter_upwards [heWindow, eventually_ge_atTop (1 : Nat)] with m hmWin hm
  intro z q n hzlo hzhi hmq hqy hqn
  have hz2 : 2 <= z := by
    have hmR : 1 <= (m : Real) := by exact_mod_cast hm
    have hHR : 2 <= (H : Real) := by exact_mod_cast hH.2
    have hprod : 2 <= (H : Real) * (m : Real) := by
      calc
        _ <= (H : Real) * 1 := by simpa using hHR
        _ <= _ := mul_le_mul_of_nonneg_left hmR (by linarith only [hHR])
    exact hprod.trans hzlo
  have hb := Finset.primeLogSaturation_three_range_bound P n m q H hm hH.2 hmq hqy hqn
    (f z) g R M D z hR hM hD hzlo hzhi (hclose z hz2) (hfm z hz2) hgm (hfh z hz2)
  dsimp only [PrimeFactorUnimodality.reciprocalPrimeSumBelow] at hmWin
  linarith only [hb, hH.1, hmWin]

theorem primeLogSaturation_uniform_cutoff
    (P : Nat) (f : Real -> Nat -> Real) (g : Nat -> Real) (R M D : Real)
    (hR : 0 <= R) (hM : 0 <= M) (hD : 0 <= D)
    (hclose : forall z, 2 <= z -> forall p, Nat.Prime p -> P < p ->
      abs (f z p - g p) <= R / (z - 1))
    (hfm : forall z, 2 <= z -> forall p, Nat.Prime p -> P < p ->
      abs (f z p) <= M / (p : Real))
    (hgm : forall p, Nat.Prime p -> P < p -> abs (g p) <= M / (p : Real))
    (hfh : forall z, 2 <= z -> forall p, Nat.Prime p -> P < p ->
      abs (f z p) <= z * D / (p : Real) ^ 2)
    (epsilon : Real) (he : 0 < epsilon) :
    exists Z : Real, forall z : Real, Z <= z -> forall n : Nat, Nat.floor z <= n ->
      abs ((((n + 1).primesBelow \ (P + 1).primesBelow).sum (f z)) -
        ((((Nat.floor z) + 1).primesBelow \ (P + 1).primesBelow).sum g)) <= epsilon := by
  have hs := primeLogSaturation_uniform_multiplicative_scale P f g R M D
    hR hM hD hclose hfm hgm hfh epsilon he
  choose H hH using hs
  have ht := eventually_atTop.1 hH.2
  choose m0 hm0 using ht
  have hHR : 2 <= (H : Real) := by exact_mod_cast hH.1
  have hHp : 0 < (H : Real) := by linarith only [hHR]
  let Z := (H : Real) * (((m0 + 2 : Nat) : Real))
  refine Exists.intro Z ?_
  intro z hz n hn
  have hZ0 : 0 <= Z := mul_nonneg hHp.le (Nat.cast_nonneg _)
  have hz0 : 0 <= z := hZ0.trans hz
  let m := Nat.floor (z / (H : Real))
  let q := Nat.floor z
  have hbase : (((m0 + 2 : Nat) : Real)) <= z / (H : Real) := by
    calc
      _ = Z / (H : Real) := by
        dsimp [Z]
        field_simp [ne_of_gt hHp]
      _ <= _ := div_le_div_of_nonneg_right hz hHp.le
  have hmlow : m0 + 2 <= m := by
    have hh := Nat.floor_mono hbase
    simpa only [Nat.floor_natCast] using hh
  have hm1 : 1 <= m := by omega
  have hmR : 1 <= (m : Real) := by exact_mod_cast hm1
  have hfloor := Nat.floor_le (div_nonneg hz0 hHp.le)
  have hzlo : (H : Real) * (m : Real) <= z := by
    have hh := mul_le_mul_of_nonneg_left hfloor hHp.le
    have hid : (H : Real) * (z / (H : Real)) = z := by
      field_simp [ne_of_gt hHp]
    rw [hid] at hh
    exact hh
  have hzhi : z <= (H : Real) * ((m : Real) + 1) := by
    have hh := mul_lt_mul_of_pos_left (Nat.lt_floor_add_one (z / (H : Real))) hHp
    have hid : (H : Real) * (z / (H : Real)) = z := by
      field_simp [ne_of_gt hHp]
    rw [hid] at hh
    exact hh.le
  have hmz : (m : Real) <= z := by
    have hh : (m : Real) <= (H : Real) * (m : Real) := by
      have hh := mul_le_mul_of_nonneg_right (show (1 : Real) <= H by linarith only [hHR])
        (Nat.cast_nonneg m)
      simpa only [one_mul] using hh
    exact hh.trans hzlo
  have hmq : m <= q := by
    have hh := Nat.floor_mono hmz
    simpa only [Nat.floor_natCast] using hh
  have hyscale : (H : Real) * ((m : Real) + 1) <=
      (m : Real) * (H : Real) ^ 2 := by
    have ha := mul_le_mul_of_nonneg_left
      (show (m : Real) + 1 <= 2 * (m : Real) by linarith only [hmR]) hHp.le
    have hb := mul_le_mul_of_nonneg_right hHR
      (mul_nonneg hHp.le (Nat.cast_nonneg m))
    nlinarith only [ha, hb]
  have hqy : q <= m * H ^ 2 := by
    have hh := (Nat.floor_le hz0).trans (hzhi.trans hyscale)
    exact_mod_cast hh
  exact hm0 m (by omega) z q n hzlo hzhi hmq hqy hn


theorem regularPrimeLaws_uniform_logProduct_saturation
    (P : Nat) (eta1 eta2 : Nat -> Real) (c D R : Real)
    (hc : 0 < c) (hD : 0 <= D) (hR : 0 <= R)
    (h1 : forall p, Nat.Prime p -> P < p -> 0 < eta1 p)
    (h2 : forall p, Nat.Prime p -> P < p -> 0 < eta2 p)
    (hlower1 : forall p, Nat.Prime p -> P < p -> c / (p : Real) <= eta1 p)
    (hlower2 : forall p, Nat.Prime p -> P < p -> c / (p : Real) <= eta2 p)
    (hdiff : forall p, Nat.Prime p -> P < p ->
      abs (eta1 p - eta2 p) <= D / (p : Real) ^ 2)
    (hinv : forall p, Nat.Prime p -> P < p -> abs (1 / eta1 p - 1 / eta2 p) <= R)
    (epsilon : Real) (he : 0 < epsilon) :
    exists Z : Real, forall z : Real, Z <= z -> forall n : Nat, Nat.floor z <= n ->
      abs ((((n + 1).primesBelow \ (P + 1).primesBelow).sum
        (fun p => Real.log (1 + (z - 1) * eta1 p) -
          Real.log (1 + (z - 1) * eta2 p))) -
        ((((Nat.floor z) + 1).primesBelow \ (P + 1).primesBelow).sum
          (fun p => Real.log (eta1 p) - Real.log (eta2 p)))) <= epsilon := by
  let f := fun z p => Real.log (1 + (z - 1) * eta1 p) -
    Real.log (1 + (z - 1) * eta2 p)
  let g := fun p => Real.log (eta1 p) - Real.log (eta2 p)
  have hcp (p : Nat) (hp : Nat.Prime p) : 0 < c / (p : Real) :=
    div_pos hc (by exact_mod_cast hp.pos)
  have hscale (p : Nat) (hp : Nat.Prime p) :
      (D / (p : Real) ^ 2) / (c / (p : Real)) = (D / c) / (p : Real) := by
    have hp0 : Not ((p : Real) = 0) := ne_of_gt (by exact_mod_cast hp.pos)
    field_simp [hp0, ne_of_gt hc]
  have hboundg : forall p, Nat.Prime p -> P < p ->
      abs (g p) <= (D / c) / (p : Real) := by
    intro p hp hP
    have hh := Real.abs_log_sub_log_le_div_lower (eta1 p) (eta2 p) (c / (p : Real))
      (hcp p hp) (hlower1 p hp hP) (hlower2 p hp hP)
    exact hh.trans ((div_le_div_of_nonneg_right (hdiff p hp hP) (hcp p hp).le).trans_eq
      (hscale p hp))
  apply primeLogSaturation_uniform_cutoff P f g R (D / c) D hR (div_nonneg hD hc.le) hD
    ?_ ?_ hboundg ?_ epsilon he
  next =>
    intro z hz p hp hP
    have hh := Real.log_bernoulliFactor_saturation_bound (eta1 p) (eta2 p) z
      (h1 p hp hP) (h2 p hp hP) (by linarith only [hz])
    exact hh.trans (div_le_div_of_nonneg_right (hinv p hp hP)
      (by linarith only [hz] : 0 <= z - 1))
  next =>
    intro z hz p hp hP
    have hh := Real.log_bernoulliFactor_difference_bound_lower (eta1 p) (eta2 p)
      (z - 1) (c / (p : Real)) (hcp p hp) (hlower1 p hp hP) (hlower2 p hp hP)
      (by linarith only [hz])
    exact hh.trans ((div_le_div_of_nonneg_right (hdiff p hp hP) (hcp p hp).le).trans_eq
      (hscale p hp))
  next =>
    intro z hz p hp hP
    have hu : 0 <= z - 1 := by linarith only [hz]
    have hh := Real.log_bernoulliFactor_difference_bound (eta1 p) (eta2 p) (z - 1)
      (h1 p hp hP).le (h2 p hp hP).le hu
    calc
      abs (f z p) <= (z - 1) * abs (eta1 p - eta2 p) := hh
      _ <= (z - 1) * (D / (p : Real) ^ 2) :=
        mul_le_mul_of_nonneg_left (hdiff p hp hP) hu
      _ <= z * (D / (p : Real) ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith)
          (div_nonneg hD (sq_nonneg _))
      _ = _ := by ring

end PrimeFactorOscillations

namespace PrimeFactorOscillations

theorem tendsto_real_primeLogProduct_error :
    Tendsto (fun x : Real => ((Nat.floor x + 1).primesBelow).sum
      (fun p => Real.log (1 - 1 / (p : Real))) +
        Real.log (Real.log x) + Real.eulerMascheroniConstant) atTop (nhds 0) := by
  have hm : Asymptotics.IsLittleO Filter.atTop
      (fun x : Real => ((Finset.Ioc 0 (Nat.floor x)).filter Nat.Prime).sum
          (fun p => Real.log (1 - 1 / (p : Real))) +
        Real.log (Real.log x) + Real.eulerMascheroniConstant)
      (fun _ : Real => (1 : Real)) := by
    run_tac
      let subscriptThree := String.singleton (Char.ofNat 8323)
      let declaration := Lean.Name.str
        (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "Mertens")
          ("E" ++ subscriptThree)) "bound'"
      let proofSyntax <- `(tactic| exact $(Lean.mkIdent declaration))
      Lean.Elab.Tactic.evalTactic proofSyntax
  have ht := (Asymptotics.isLittleO_one_iff Real).mp hm
  apply ht.congr'
  apply Filter.Eventually.of_forall
  intro x
  have hs : ((Finset.Ioc 0 (Nat.floor x)).filter Nat.Prime) =
      (Nat.floor x + 1).primesBelow := by
    apply Finset.ext
    intro p
    constructor
    next =>
      intro hp
      have hh := Finset.mem_filter.mp hp
      have hn := Finset.mem_Ioc.mp hh.1
      exact Nat.mem_primesBelow.mpr (And.intro (by omega) hh.2)
    next =>
      intro hp
      have hh := Nat.mem_primesBelow.mp hp
      exact Finset.mem_filter.mpr
        (And.intro (Finset.mem_Ioc.mpr (And.intro hh.2.pos (by omega))) hh.2)
  dsimp only
  rw [hs]

theorem tendsto_renormalized_primeLogRatio (P : Nat) (g : Nat -> Real) (theta K : Real)
    (hK : 0 <= K)
    (hres : forall p, Nat.Prime p -> P < p ->
      abs (g p + theta * Real.log (1 - 1 / (p : Real))) <= K / (p : Real) ^ 2) :
    Tendsto (fun z : Real =>
      ((((Nat.floor z) + 1).primesBelow \ (P + 1).primesBelow).sum g) -
        theta * Real.log (Real.log z)) atTop
      (nhds ((tsum (fun p : Nat => if Nat.Prime p /\ P < p then
        g p + theta * Real.log (1 - 1 / (p : Real)) else 0)) +
          theta * (Real.eulerMascheroniConstant +
            (P + 1).primesBelow.sum (fun p => Real.log (1 - 1 / (p : Real)))))) := by
  classical
  let residual := fun p => g p + theta * Real.log (1 - 1 / (p : Real))
  let small := (P + 1).primesBelow.sum (fun p => Real.log (1 - 1 / (p : Real)))
  have hf : Tendsto (Nat.floor : Real -> Nat) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (b : Real)] with x hx
    have hh := Nat.floor_mono hx
    simpa only [Nat.floor_natCast] using hh
  have hr := (Finset.tendsto_primeTail_sum_of_abs_le_sq P residual K hK hres).comp hf
  have hm := tendsto_real_primeLogProduct_error
  have ht := (hr.sub (hm.const_mul theta)).add_const
    (theta * (Real.eulerMascheroniConstant + small))
  have ht' : Tendsto (fun z : Real =>
      ((((Nat.floor z) + 1).primesBelow \ (P + 1).primesBelow).sum residual -
        theta * ((((Nat.floor z) + 1).primesBelow).sum
          (fun p => Real.log (1 - 1 / (p : Real))) +
            Real.log (Real.log z) + Real.eulerMascheroniConstant)) +
              theta * (Real.eulerMascheroniConstant + small)) atTop
      (nhds ((tsum (fun p : Nat => if Nat.Prime p /\ P < p then residual p else 0)) +
        theta * (Real.eulerMascheroniConstant + small))) := by
    simpa only [Function.comp_def, mul_zero, sub_zero] using ht
  apply ht'.congr'
  filter_upwards [eventually_ge_atTop (P : Real)] with z hz
  have hPz : P <= Nat.floor z := by
    have hh := Nat.floor_mono hz
    simpa only [Nat.floor_natCast] using hh
  let A := (Nat.floor z + 1).primesBelow
  let B := (P + 1).primesBelow
  let S := A \ B
  have hBA : forall p, Membership.mem B p -> Membership.mem A p := by
    intro p hp
    have hh := Nat.mem_primesBelow.mp hp
    exact Nat.mem_primesBelow.mpr (And.intro (by omega) hh.2)
  have hs : S.sum (fun p => Real.log (1 - 1 / (p : Real))) + small =
      A.sum (fun p => Real.log (1 - 1 / (p : Real))) := Finset.sum_sdiff hBA
  have hresid : S.sum residual = S.sum g +
      theta * S.sum (fun p => Real.log (1 - 1 / (p : Real))) := by
    dsimp only [residual]
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  change (S.sum residual -
    theta * (A.sum (fun p => Real.log (1 - 1 / (p : Real))) +
      Real.log (Real.log z) + Real.eulerMascheroniConstant)) +
        theta * (Real.eulerMascheroniConstant + small) = _
  rw [hresid, <- hs]
  ring

end PrimeFactorOscillations
