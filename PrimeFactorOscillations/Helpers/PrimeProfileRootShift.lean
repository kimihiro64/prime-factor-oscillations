/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeProfileReferenceCrossing
import PrimeFactorOscillations.Helpers.PrimeProfileRootApproximation

/-!
# The constant displacement of a positive reference crossing

A uniform bound applies to every root in a fixed-width neighborhood. The
locally unique crossing therefore equals rank/level minus the logarithmic
derivative of the actual profile, with an explicit inverse-rank error.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

theorem exists_primeProfile_reference_root_shift_bound (s A : Real)
    (hs : 0 < s) (hA : 0 <= A) :
    exists (C : Real) (r0 : Nat), 0 <= C /\ 0 < r0 /\
      forall r : Nat, r0 <= r -> forall u : Real, 0 < u ->
        (r : Real) / u <= 2 * s -> abs ((r : Real) / s - u) <= A ->
        Nat.factorialConvolution primeProfileRealCoefficient (r - 1) u /
          Nat.factorialConvolution primeProfileRealCoefficient r u = s ->
        abs (u - (r : Real) / s +
          deriv (fun x : Real => (primeProfile (x : Complex)).re) s /
            (primeProfile (s : Complex)).re) <= C / (r : Real) := by
  have hb : 0 <= 2 * s := by positivity
  choose rD hrD hdenom using exists_primeProfile_normalized_coefficient_lower_bound (2 * s) hb
  choose U V hU hV happrox using exists_primeProfile_normalized_value_deriv_errors (2 * s) hb
  choose M hM hderivs using exists_primeProfile_normalized_derivative_bounds (2 * s) hb
  let d := Real.exp (-((2 * s) ^ 2 * tsum (fun p : Nat.Primes =>
    (primeProfileWeight (p : Nat)) ^ 2)) / 2) / 2
  let F := (primeProfile (s : Complex)).re
  let G := deriv (fun x : Real => (primeProfile (x : Complex)).re) s
  have hd : 0 < d := by dsimp [d]; positivity
  have hF : 0 < F := by
    have h := primeProfile_re_lower_bound (2 * s) s hb hs.le (by linarith)
    exact (Real.exp_pos _).trans_le h
  let L := 2 * s ^ 2 * A
  let U0 := M * L + U
  let V0 := M * L + V
  let E := V0 / d + abs G * U0 / (d * F)
  let C := L / s * abs (G / F) + 2 * E
  have hL : 0 <= L := by dsimp [L]; positivity
  have hU0 : 0 <= U0 := by dsimp [U0]; positivity
  have hV0 : 0 <= V0 := by dsimp [V0]; positivity
  have hE : 0 <= E := by dsimp [E]; positivity
  have hC : 0 <= C := by dsimp [C]; positivity
  refine Exists.intro C (Exists.intro rD (And.intro hC (And.intro hrD ?_)))
  intro r hrD' u hu0 htb hnear hroot
  have hrpos : 0 < r := hrD.trans_le hrD'
  have hrR : (0 : Real) < r := by exact_mod_cast hrpos
  let t := (r : Real) / u
  let f := Nat.normalizedDescFactorialPolynomial primeProfileRealCoefficient r
  have ht : 0 < t := div_pos hrR hu0
  have htI : Set.Icc (0 : Real) (2 * s) t := And.intro ht.le htb
  have hsI : Set.Icc (0 : Real) (2 * s) s := And.intro hs.le (by linarith)
  have hAt : d <= f t := hdenom r hrD' t ht.le htb
  have hAt0 : 0 < f t := hd.trans_le hAt
  have htShift : abs (t - s) <= L / (r : Real) := by
    have hid : t - s = (t * s / r) * ((r : Real) / s - u) := by
      dsimp [t]
      field_simp [hs.ne', hu0.ne', hrR.ne']
    rw [hid, abs_mul, abs_of_nonneg (by positivity : 0 <= t * s / r)]
    calc
      (t * s / r) * abs ((r : Real) / s - u) <= (t * s / r) * A :=
        mul_le_mul_of_nonneg_left hnear (by positivity)
      _ <= (2 * s * s / r) * A := by gcongr
      _ = L / (r : Real) := by dsimp [L]; ring
  have hvMove : abs (f t - f s) <= M * abs (t - s) := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := f)
      (s := Set.Icc (0 : Real) (2 * s))
      (fun x _ => (Nat.hasDerivAt_normalizedDescFactorialPolynomial
        primeProfileRealCoefficient r x).differentiableAt)
      (fun x hx => by
        simpa only [Real.norm_eq_abs] using (hderivs r hrpos x hx.1 hx.2).1)
      (convex_Icc (0 : Real) (2 * s)) hsI htI
    simpa only [Real.norm_eq_abs] using h
  have hdMove : abs (deriv f t - deriv f s) <= M * abs (t - s) := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv f)
      (s := Set.Icc (0 : Real) (2 * s))
      (fun x _ => (Nat.hasDerivAt_deriv_normalizedDescFactorialPolynomial
        primeProfileRealCoefficient r x).differentiableAt)
      (fun x hx => by
        simpa only [Real.norm_eq_abs] using (hderivs r hrpos x hx.1 hx.2).2)
      (convex_Icc (0 : Real) (2 * s)) hsI htI
    simpa only [Real.norm_eq_abs] using h
  have hap := happrox r hrpos s hs.le hsI.2
  have hvalue : abs (f t - F) <= U0 / (r : Real) := by
    calc
      abs (f t - F) <= abs (f t - f s) + abs (f s - F) := abs_sub_le _ _ _
      _ <= M * abs (t - s) + U / (r : Real) := add_le_add hvMove hap.1
      _ <= M * (L / (r : Real)) + U / (r : Real) :=
        add_le_add (mul_le_mul_of_nonneg_left htShift hM) le_rfl
      _ = U0 / (r : Real) := by dsimp [U0]; ring
  have hderiv : abs (deriv f t - G) <= V0 / (r : Real) := by
    calc
      abs (deriv f t - G) <=
          abs (deriv f t - deriv f s) + abs (deriv f s - G) := abs_sub_le _ _ _
      _ <= M * abs (t - s) + V / (r : Real) := add_le_add hdMove hap.2
      _ <= M * (L / (r : Real)) + V / (r : Real) :=
        add_le_add (mul_le_mul_of_nonneg_left htShift hM) le_rfl
      _ = V0 / (r : Real) := by dsimp [V0]; ring
  have hquot : abs (deriv f t / f t - G / F) <= E / (r : Real) := by
    have hid : deriv f t / f t - G / F =
        (deriv f t - G) / f t + G * (F - f t) / (f t * F) := by
      field_simp [hAt0.ne', hF.ne']
      ring
    rw [hid]
    calc
      abs ((deriv f t - G) / f t + G * (F - f t) / (f t * F)) <=
          abs ((deriv f t - G) / f t) + abs (G * (F - f t) / (f t * F)) :=
        abs_add_le _ _
      _ = abs (deriv f t - G) / f t + abs G * abs (f t - F) / (f t * F) := by
        rw [abs_div, abs_div, abs_mul, abs_mul, abs_of_pos hAt0,
          abs_of_pos hF, abs_sub_comm F (f t)]
      _ <= (V0 / (r : Real)) / d + abs G * (U0 / (r : Real)) / (d * F) := by
        gcongr
      _ = E / (r : Real) := by dsimp [E]; ring
  have hidentity : s * u - r = -t * (deriv f t / f t) := by
    have heq := Nat.factorialConvolution_ratio_eq_normalized_logDeriv
      primeProfileRealCoefficient r hrpos u hu0.ne' hAt0.ne'
    rw [hroot] at heq
    change s = t - (t ^ 2 / r) * deriv f t / f t at heq
    rw [heq]
    dsimp [t]
    field_simp [hu0.ne', hrR.ne', hAt0.ne']
    ring
  have hts : t / s <= 2 := by
    have h := div_le_div_of_nonneg_right htb hs.le
    have heq : (2 * s) / s = 2 := by field_simp
    rwa [heq] at h
  have herror : abs (u - (r : Real) / s + G / F) <= C / (r : Real) := by
    have hid : u - (r : Real) / s + G / F =
        ((s - t) / s) * (G / F) - (t / s) * (deriv f t / f t - G / F) := by
      calc
        u - (r : Real) / s + G / F = (s * u - r) / s + G / F := by
          field_simp [hs.ne', hF.ne']
        _ = (-t * (deriv f t / f t)) / s + G / F := by rw [hidentity]
        _ = ((s - t) / s) * (G / F) -
            (t / s) * (deriv f t / f t - G / F) := by
          field_simp [hs.ne', hF.ne', hAt0.ne']
          ring
    rw [hid]
    calc
      abs (((s - t) / s) * (G / F) - (t / s) * (deriv f t / f t - G / F)) <=
          abs (((s - t) / s) * (G / F)) +
            abs ((t / s) * (deriv f t / f t - G / F)) := abs_sub _ _
      _ = (abs (t - s) / s) * abs (G / F) +
          (t / s) * abs (deriv f t / f t - G / F) := by
        rw [abs_mul, abs_mul, abs_div, abs_of_pos hs,
          abs_sub_comm s t, abs_of_nonneg (by positivity : 0 <= t / s)]
      _ <= ((L / (r : Real)) / s) * abs (G / F) + 2 * (E / (r : Real)) := by
        gcongr
      _ = C / (r : Real) := by dsimp [C]; ring
  exact herror

theorem exists_primeProfile_reference_sharp_crossing (s : Real) (hs : 0 < s) :
    exists (A C : Real) (r0 : Nat), 0 < A /\ 0 <= C /\ 0 < r0 /\
      forall r : Nat, r0 <= r -> exists u : Real,
        Set.Ioo ((r : Real) / s - A) ((r : Real) / s + A) u /\
        Nat.factorialConvolution primeProfileRealCoefficient (r - 1) u /
          Nat.factorialConvolution primeProfileRealCoefficient r u = s /\
        abs (u - (r : Real) / s +
          deriv (fun x : Real => (primeProfile (x : Complex)).re) s /
            (primeProfile (s : Complex)).re) <= C / (r : Real) /\
        forall v : Real, Set.Icc ((r : Real) / s - A) ((r : Real) / s + A) v ->
          Nat.factorialConvolution primeProfileRealCoefficient (r - 1) v /
            Nat.factorialConvolution primeProfileRealCoefficient r v = s -> v = u := by
  choose A rC hA hrC hcross using exists_primeProfile_reference_local_crossing s hs
  choose C rD hC hrD hbound using
    exists_primeProfile_reference_root_shift_bound s A hs hA.le
  refine Exists.intro A (Exists.intro C (Exists.intro (max rC rD)
    (And.intro hA (And.intro hC (And.intro (hrC.trans_le (le_max_left _ _)) ?_)))))
  intro r hr
  have hrC' : rC <= r := (le_max_left _ _).trans hr
  have hrD' : rD <= r := (le_max_right _ _).trans hr
  have hbase := hcross r hrC'
  choose u hu hroot hunique using hbase.2
  have hband := hbase.1 u (And.intro hu.1.le hu.2.le)
  have hnear : abs ((r : Real) / s - u) <= A := by
    apply abs_le.mpr
    constructor <;> linarith [hu.1, hu.2]
  have herror := hbound r hrD' u hband.1 hband.2.2.1 hnear hroot
  exact Exists.intro u (And.intro hu (And.intro hroot (And.intro herror hunique)))

end PrimeFactorOscillations
