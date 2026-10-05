/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeProfileClockSign

/-!
# Local reference crossing points

The exact normalized coefficient identity bounds the reference ratio uniformly.
Every fixed positive level has one crossing near rank divided by that level.
Uniqueness is asserted only on the displayed interval.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

theorem exists_primeProfile_reference_value_bound (b : Real) (hb : 0 <= b) :
    exists (r0 : Nat) (C : Real), 0 < r0 /\ 0 <= C /\
      forall r : Nat, r0 <= r -> forall u : Real, 0 < u ->
        (r : Real) / u <= b ->
        0 < Nat.factorialConvolution primeProfileRealCoefficient r u /\
        DifferentiableAt Real (fun v : Real =>
          Nat.factorialConvolution primeProfileRealCoefficient (r - 1) v /
            Nat.factorialConvolution primeProfileRealCoefficient r v) u /\
        abs ((Nat.factorialConvolution primeProfileRealCoefficient (r - 1) u /
          Nat.factorialConvolution primeProfileRealCoefficient r u) * u - r) <= C := by
  choose r0 hr0 hlower using exists_primeProfile_normalized_coefficient_lower_bound b hb
  choose M hM hderiv using exists_primeProfile_normalized_derivative_bounds b hb
  let d := Real.exp (-(b ^ 2 * tsum (fun p : Nat.Primes =>
    (primeProfileWeight (p : Nat)) ^ 2)) / 2) / 2
  have hd : 0 < d := by dsimp [d]; positivity
  refine Exists.intro r0 (Exists.intro (b * (M / d))
    (And.intro hr0 (And.intro (by positivity) ?_)))
  intro r hr u hu htb
  have hrpos : 0 < r := hr0.trans_le hr
  have hrR : (0 : Real) < r := by exact_mod_cast hrpos
  let t := (r : Real) / u
  let A := Nat.normalizedDescFactorialPolynomial primeProfileRealCoefficient r t
  let V := deriv (Nat.normalizedDescFactorialPolynomial primeProfileRealCoefficient r) t
  have ht : 0 <= t := (div_pos hrR hu).le
  have hA : d <= A := hlower r hr t ht htb
  have hApos : 0 < A := hd.trans_le hA
  have hV : abs V <= M := (hderiv r hrpos t ht htb).1
  have hpos : 0 < Nat.factorialConvolution primeProfileRealCoefficient r u := by
    rw [Nat.factorialConvolution_eq_normalizedDescFactorialPolynomial
      primeProfileRealCoefficient r hrpos u hu.ne']
    exact mul_pos (by positivity) hApos
  refine And.intro hpos (And.intro
    (Nat.hasDerivAt_factorialConvolution_ratio primeProfileRealCoefficient r
      hrpos u hu.ne' hApos.ne').differentiableAt ?_)
  rw [Nat.factorialConvolution_ratio_eq_normalized_logDeriv
    primeProfileRealCoefficient r hrpos u hu.ne' hApos.ne']
  change abs ((t - (t ^ 2 / r) * V / A) * u - r) <= b * (M / d)
  have hid : (t - (t ^ 2 / r) * V / A) * u - r = -t * (V / A) := by
    dsimp [t]
    field_simp [hu.ne', hrR.ne', hApos.ne']
    ring
  rw [hid, abs_mul, abs_neg, abs_of_nonneg ht, abs_div, abs_of_pos hApos]
  apply mul_le_mul htb _ (by positivity) hb
  exact (div_le_div_of_nonneg_right hV hApos.le).trans
    (div_le_div_of_nonneg_left hM hd hA)

theorem exists_primeProfile_reference_local_crossing (s : Real) (hs : 0 < s) :
    exists (A : Real) (r0 : Nat), 0 < A /\ 0 < r0 /\
      forall r : Nat, r0 <= r ->
        (forall u : Real, Set.Icc ((r : Real) / s - A) ((r : Real) / s + A) u ->
          0 < u /\ s / 2 <= (r : Real) / u /\ (r : Real) / u <= 2 * s /\
            0 < Nat.factorialConvolution primeProfileRealCoefficient r u) /\
        exists u : Real,
          Set.Ioo ((r : Real) / s - A) ((r : Real) / s + A) u /\
          Nat.factorialConvolution primeProfileRealCoefficient (r - 1) u /
            Nat.factorialConvolution primeProfileRealCoefficient r u = s /\
          forall v : Real,
            Set.Icc ((r : Real) / s - A) ((r : Real) / s + A) v ->
            Nat.factorialConvolution primeProfileRealCoefficient (r - 1) v /
              Nat.factorialConvolution primeProfileRealCoefficient r v = s -> v = u := by
  have hb : 0 <= 2 * s := by positivity
  choose rV C hrV hC hvalue using exists_primeProfile_reference_value_bound (2 * s) hb
  choose rS hrS hsecant using
    exists_primeProfile_reference_secant_bounds (s / 2) (2 * s) (by positivity) (by linarith)
  let A := (C + 1) / s
  have hA : 0 < A := by dsimp [A]; positivity
  have hAs : A * s = C + 1 := by dsimp [A]; field_simp
  choose n0 hn0 using exists_nat_gt (2 * s * A)
  refine Exists.intro A (Exists.intro (max rV (max rS (n0 + 1)))
    (And.intro hA (And.intro (hrV.trans_le (le_max_left _ _)) ?_)))
  intro r hr
  have hrV' : rV <= r := (le_max_left _ _).trans hr
  have hrS' : rS <= r := (le_max_left _ _).trans ((le_max_right _ _).trans hr)
  have hn' : n0 + 1 <= r := (le_max_right _ _).trans ((le_max_right _ _).trans hr)
  have hnR : (n0 : Real) < r := by exact_mod_cast (Nat.lt_succ_self n0).trans_le hn'
  have hrlarge : 2 * s * A < (r : Real) := hn0.trans hnR
  have hrR : (0 : Real) < r := by exact_mod_cast hrV.trans_le hrV'
  let c := (r : Real) / s
  let l := c - A
  let h := c + A
  let R : Real -> Real := fun u =>
    Nat.factorialConvolution primeProfileRealCoefficient (r - 1) u /
      Nat.factorialConvolution primeProfileRealCoefficient r u
  have hcs : c * s = (r : Real) := by dsimp [c]; field_simp
  have hcenter : 2 * A < c := by
    by_contra hnot
    have hc := mul_le_mul_of_nonneg_right (le_of_not_gt hnot) hs.le
    nlinarith
  have hl : 0 < l := by dsimp [l]; linarith
  have hlh : l < h := by dsimp [l, h]; linarith
  have hband (u : Real) (huI : Set.Icc l h u) :
      0 < u /\ s / 2 <= (r : Real) / u /\ (r : Real) / u <= 2 * s := by
    have hu : 0 < u := hl.trans_le huI.1
    have hul : c - A <= u := huI.1
    have huh : u <= c + A := huI.2
    refine And.intro hu (And.intro ?_ ?_)
    . have htu : (r : Real) / u * u = r := by field_simp
      by_contra hnot
      have ht := mul_lt_mul_of_pos_right (lt_of_not_ge hnot) hu
      nlinarith
    . have htu : (r : Real) / u * u = r := by field_simp
      by_contra hnot
      have ht := mul_lt_mul_of_pos_right (lt_of_not_ge hnot) hu
      nlinarith
  have hbounds (u : Real) (huI : Set.Icc l h u) :=
    hvalue r hrV' u (hband u huI).1 (hband u huI).2.2
  have hcont : ContinuousOn R (Set.Icc l h) := fun u hu =>
    (hbounds u hu).2.1.continuousAt.continuousWithinAt
  have hleft : s < R l := by
    have he := (abs_le.mp (hbounds l (And.intro le_rfl hlh.le)).2.2).1
    have hls : l * s = (r : Real) - (C + 1) := by dsimp [l]; nlinarith
    change -C <= R l * l - r at he
    nlinarith
  have hright : R h < s := by
    have he := (abs_le.mp (hbounds h (And.intro hlh.le le_rfl)).2.2).2
    have hhs : h * s = (r : Real) + (C + 1) := by dsimp [h]; nlinarith
    have hh : 0 < h := hl.trans hlh
    change R h * h - r <= C at he
    nlinarith
  obtain hv := intermediate_value_Icc' hlh.le hcont (And.intro hright.le hleft.le)
  choose u huI hueq using hv
  have hstrict : Set.Ioo l h u := by
    constructor
    . have hne : Not (l = u) := by intro he; subst u; exact hleft.ne' hueq
      exact lt_of_le_of_ne huI.1 hne
    . have hne : Not (u = h) := by intro he; subst u; exact hright.ne hueq
      exact lt_of_le_of_ne huI.2 hne
  refine And.intro (fun v hv => And.intro (hband v hv).1
    (And.intro (hband v hv).2.1 (And.intro (hband v hv).2.2 (hbounds v hv).1)))
    (Exists.intro u (And.intro hstrict (And.intro hueq ?_)))
  intro v hvI hveq
  have hsegment (w : Real) (hw : Set.Icc (min v u) (max v u) w) :
      0 < w /\ s / 2 <= (r : Real) / w /\ (r : Real) / w <= 2 * s := by
    apply hband
    exact And.intro ((le_min hvI.1 huI.1).trans hw.1)
      (hw.2.trans (max_le hvI.2 huI.2))
  choose q hqlo hqhi hqeq using hsecant r hrS' v u hsegment
  have hqpos : 0 < q := lt_of_lt_of_le (by positivity) hqlo
  change R v - R u = q * (u - v) at hqeq
  change R v = s at hveq
  rw [hveq, hueq, sub_self] at hqeq
  have huv : u - v = 0 := (mul_eq_zero.mp hqeq.symm).resolve_left hqpos.ne'
  linarith

end PrimeFactorOscillations
