/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasDegreeMoment
import PrimeFactorOscillations.Helpers.NicolasXiCounting
/-!
# A squared-logarithmic bound for the complete zero coefficient

Under RH, the absolute sum of n / (rho (n-rho)) is bounded by one constant
times log(n+2)^2 for every integer n >= 2. The proof uses the maintained
unconditional count of canonical xi zero indices with multiplicity.

The exact dyadic partition retains all indices. The low part uses 2/|rho|,
the tail uses n/|rho|^2, and inverse-square summability justifies the
regrouping. An explicit geometric tail is added before the cutoff is
chosen as the ceiling of log base two of n. No epsilon-dependent
existential constant is specialized at a moving epsilon.

Canonical-index and dyadic APIs are reused from the pinned PNT source
f6147e7572ab3abe5428101bc0b13627bcb005df. This is a classical analytic
estimate for the sharper degree-localization consumer, not prime-gap supply.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open Robin1984

private def xiShellIndex (p : RiemannXiDivisorZeroIndex) : Nat :=
  Nat.floor (Real.logb 2 (norm (riemannXiDivisorZeroValue p) / (1 / 2 : Real)))

private def xiShell (j : Nat) : Set RiemannXiDivisorZeroIndex :=
  fun p => xiShellIndex p = j

private theorem xi_norm_half (hRH : RiemannHypothesis)
    (p : RiemannXiDivisorZeroIndex) :
    (1 / 2 : Real) <= norm (riemannXiDivisorZeroValue p) := by
  have h := Complex.re_le_norm (riemannXiDivisorZeroValue p)
  rw [riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH p] at h
  exact h

private theorem xi_shell_bounds (hRH : RiemannHypothesis) {j : Nat}
    (p : xiShell j) :
    And ((2 : Real) ^ j / 2 <= norm (riemannXiDivisorZeroValue p.val))
      (norm (riemannXiDivisorZeroValue p.val) <= (2 : Real) ^ j) := by
  have hIndex : Nat.floor (Real.logb 2
      (norm (riemannXiDivisorZeroValue p.val) / (1 / 2 : Real))) = j := p.property
  have hLow := Real.dyadicShell_lower_bound
    (by norm_num : (0 : Real) < 1 / 2) (xi_norm_half hRH p.val) hIndex
  have hUp := Real.dyadicShell_upper_bound
    (by norm_num : (0 : Real) < 1 / 2) (xi_norm_half hRH p.val) hIndex
  rw [Real.rpow_natCast] at hLow
  rw [Real.rpow_add (by norm_num : (0 : Real) < 2),
    Real.rpow_natCast, Real.rpow_one] at hUp
  exact And.intro (by nlinarith [hLow]) (by nlinarith [hUp])

private theorem coefficient_norm_two_bounds (hRH : RiemannHypothesis)
    {n : Nat} (hn : 2 <= n) (p : RiemannXiDivisorZeroIndex) :
    And (norm (((n : Complex) / ((n : Complex) - riemannXiDivisorZeroValue p)) /
      riemannXiDivisorZeroValue p) <= 2 / norm (riemannXiDivisorZeroValue p))
      (norm (((n : Complex) / ((n : Complex) - riemannXiDivisorZeroValue p)) /
        riemannXiDivisorZeroValue p) <=
          (n : Real) / norm (riemannXiDivisorZeroValue p) ^ (2 : Nat)) := by
  let rho := riemannXiDivisorZeroValue p
  let a := norm rho
  let b := norm ((n : Complex) - rho)
  have ha : 0 < a := norm_pos_iff.mpr (riemannXiDivisorZeroValue_ne_zero p)
  have hnReal : (2 : Real) <= n := by exact_mod_cast hn
  have hRe : rho.re = (1 / 2 : Real) :=
    riemannXiDivisorZeroValue_re_eq_half_of_riemannHypothesis hRH p
  have hab : a <= b := by
    have h := norm_le_norm_sub_nat_of_re_eq_half (n := n) (by omega) hRe
    exact h.trans_eq (norm_sub_rev _ _)
  have hbN : (n : Real) / 2 <= b := by
    have h := Complex.re_le_norm ((n : Complex) - rho)
    simp only [Complex.sub_re, Complex.natCast_re, hRe] at h
    dsimp [b]
    linarith
  have hb : 0 < b := ha.trans_le hab
  have hNorm : norm (((n : Complex) / ((n : Complex) - rho)) / rho) =
      (n : Real) / (a * b) := by
    rw [norm_div, norm_div, Complex.norm_natCast]
    dsimp [a, b]
    ring
  change And (norm (((n : Complex) / ((n : Complex) - rho)) / rho) <= 2 / a)
    (norm (((n : Complex) / ((n : Complex) - rho)) / rho) <= (n : Real) / a ^ 2)
  rw [hNorm]
  have hSmall := mul_le_mul_of_nonneg_right
    (show (n : Real) <= 2 * b by linarith)
    (show 0 <= Inv.inv (a * b) by positivity)
  have hSmall' : (n : Real) / (a * b) <= 2 / a := by
    convert hSmall using 1 <;> field_simp [ha.ne', hb.ne']
  have hProduct : a * a <= a * b := mul_le_mul_of_nonneg_left hab ha.le
  have hInv := one_div_le_one_div_of_le (mul_pos ha ha) hProduct
  have hTail := mul_le_mul_of_nonneg_left hInv (Nat.cast_nonneg n)
  have hTail' : (n : Real) / (a * b) <= (n : Real) / a ^ 2 := by
    convert hTail using 1 <;> ring
  exact And.intro hSmall' hTail'


private theorem xi_two_pow_one_le (j : Nat) : (1 : Real) <= (2 : Real) ^ j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    rw [pow_succ]
    linarith

private theorem xi_shell_finite (hRH : RiemannHypothesis) (j : Nat) :
    Finite (xiShell j) := by
  let Ball : Type := {p : RiemannXiDivisorZeroIndex //
    norm (riemannXiDivisorZeroValue p) <= (2 : Real) ^ j}
  let : Finite Ball := nicolasXi_finite_zero_ball _
  let embed : xiShell j -> Ball :=
    fun p => Subtype.mk p.val (xi_shell_bounds hRH p).2
  have hInjective : Function.Injective embed := by
    intro p q h
    apply Subtype.ext
    exact congrArg (fun x : Ball => x.val) h
  exact Finite.of_injective embed hInjective

private theorem xi_shell_count (hRH : RiemannHypothesis)
    {C : Real} (hC : 0 <= C)
    (hCount : forall R : Real, 1 <= R ->
      (Nat.card {p : RiemannXiDivisorZeroIndex //
        norm (riemannXiDivisorZeroValue p) <= R} : Real) <=
          C * R * Real.log (R + 2)) (j : Nat) :
    (Nat.card (xiShell j) : Real) <=
      C * ((j : Real) + 2) * Real.log 2 * (2 : Real) ^ j := by
  let Ball : Type := {p : RiemannXiDivisorZeroIndex //
    norm (riemannXiDivisorZeroValue p) <= (2 : Real) ^ j}
  let : Finite Ball := nicolasXi_finite_zero_ball _
  let embed : xiShell j -> Ball :=
    fun p => Subtype.mk p.val (xi_shell_bounds hRH p).2
  have hInjective : Function.Injective embed := by
    intro p q h
    apply Subtype.ext
    exact congrArg (fun x : Ball => x.val) h
  have hCardNat := Nat.card_le_card_of_injective embed hInjective
  have hCard : (Nat.card (xiShell j) : Real) <= (Nat.card Ball : Real) := by
    exact_mod_cast hCardNat
  have hR := xi_two_pow_one_le j
  have hRadius : (2 : Real) ^ j + 2 <= (2 : Real) ^ (j + 2) := by
    rw [pow_add]
    norm_num
    linarith
  have hLog := Real.log_le_log
    (show 0 < (2 : Real) ^ j + 2 by positivity) hRadius
  rw [Real.log_pow] at hLog
  norm_num only [Nat.cast_add, Nat.cast_ofNat] at hLog
  have hScale := mul_le_mul_of_nonneg_left hLog
    (show 0 <= C * (2 : Real) ^ j by positivity)
  have hBall := hCount ((2 : Real) ^ j) hR
  change (Nat.card Ball : Real) <= _ at hBall
  nlinarith only [hCard, hBall, hScale]

private theorem xi_coefficient_summable (hRH : RiemannHypothesis)
    {n : Nat} (hn : 2 <= n) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      norm (((n : Complex) / ((n : Complex) - riemannXiDivisorZeroValue p)) /
        riemannXiDivisorZeroValue p)) := by
  have hMajor := summable_robinXiZeroWeight.mul_left (n : Real)
  apply hMajor.of_nonneg_of_le (fun p => norm_nonneg _)
  intro p
  have h := (coefficient_norm_two_bounds hRH hn p).2
  simpa only [div_eq_mul_inv, inv_pow] using h


private theorem xi_shell_coefficient_bounds (hRH : RiemannHypothesis)
    {C : Real} (hC : 0 <= C)
    (hCount : forall R : Real, 1 <= R ->
      (Nat.card {p : RiemannXiDivisorZeroIndex //
        norm (riemannXiDivisorZeroValue p) <= R} : Real) <=
          C * R * Real.log (R + 2))
    {n : Nat} (hn : 2 <= n) (j : Nat) :
    let mass : Real := tsum (fun p : xiShell j =>
      norm (((n : Complex) / ((n : Complex) - riemannXiDivisorZeroValue p.val)) /
        riemannXiDivisorZeroValue p.val))
    And (mass <= 4 * C * Real.log 2 * ((j : Real) + 2))
      (mass <= 4 * C * Real.log 2 * ((j : Real) + 2) * n / (2 : Real) ^ j) := by
  intro mass
  let R : Real := (2 : Real) ^ j
  have hR : 0 < R := by dsimp [R]; positivity
  have hPoint (p : xiShell j) :
      And (norm (((n : Complex) / ((n : Complex) - riemannXiDivisorZeroValue p.val)) /
        riemannXiDivisorZeroValue p.val) <= 4 / R)
      (norm (((n : Complex) / ((n : Complex) - riemannXiDivisorZeroValue p.val)) /
        riemannXiDivisorZeroValue p.val) <= 4 * n / R ^ (2 : Nat)) := by
    let a := norm (riemannXiDivisorZeroValue p.val)
    have ha : 0 < a := norm_pos_iff.mpr (riemannXiDivisorZeroValue_ne_zero p.val)
    have hLow : R / 2 <= a := (xi_shell_bounds hRH p).1
    have hInvRaw := one_div_le_one_div_of_le
      (div_pos hR (by norm_num : (0 : Real) < 2)) hLow
    have hInv : 1 / a <= 2 / R := by
      convert hInvRaw using 1; field_simp [hR.ne']
    have hTwo := mul_le_mul_of_nonneg_left hInv (by norm_num : (0 : Real) <= 2)
    have hSmall : 2 / a <= 4 / R := by
      convert hTwo using 1 <;> ring
    have hSquare := mul_le_mul hInv hInv (by positivity) (by positivity)
    have hScaled := mul_le_mul_of_nonneg_left hSquare (Nat.cast_nonneg n)
    have hTail : (n : Real) / a ^ (2 : Nat) <= 4 * n / R ^ (2 : Nat) := by
      convert hScaled using 1
      all_goals field_simp [ha.ne', hR.ne']
      all_goals norm_num
    have hCoefficient := coefficient_norm_two_bounds hRH hn p.val
    exact And.intro (hCoefficient.1.trans hSmall) (hCoefficient.2.trans hTail)
  let : Finite (xiShell j) := xi_shell_finite hRH j
  let : Fintype (xiShell j) := Fintype.ofFinite _
  have hMassBound (B : Real)
      (hB : forall p : xiShell j,
        norm (((n : Complex) / ((n : Complex) - riemannXiDivisorZeroValue p.val)) /
          riemannXiDivisorZeroValue p.val) <= B) :
      mass <= (Nat.card (xiShell j) : Real) * B := by
    change tsum _ <= _
    rw [tsum_fintype]
    calc
      _ <= Finset.sum Finset.univ (fun _ : xiShell j => B) :=
        Finset.sum_le_sum (fun p _ => hB p)
      _ = _ := by simp [Nat.card_eq_fintype_card]
  have hCard := xi_shell_count hRH hC hCount j
  change (Nat.card (xiShell j) : Real) <=
    C * ((j : Real) + 2) * Real.log 2 * R at hCard
  constructor
  . have hSmall := hMassBound (4 / R) (fun p => (hPoint p).1)
    have hScale := mul_le_mul_of_nonneg_right hCard (show 0 <= 4 / R by positivity)
    calc
      mass <= (Nat.card (xiShell j) : Real) * (4 / R) := hSmall
      _ <= (C * ((j : Real) + 2) * Real.log 2 * R) * (4 / R) := hScale
      _ = _ := by field_simp [hR.ne']
  . have hTail := hMassBound (4 * n / R ^ (2 : Nat)) (fun p => (hPoint p).2)
    have hScale := mul_le_mul_of_nonneg_right hCard
      (show 0 <= 4 * (n : Real) / R ^ (2 : Nat) by positivity)
    change mass <= 4 * C * Real.log 2 * ((j : Real) + 2) * n / R
    calc
      mass <= (Nat.card (xiShell j) : Real) * (4 * n / R ^ (2 : Nat)) := hTail
      _ <= (C * ((j : Real) + 2) * Real.log 2 * R) *
        (4 * n / R ^ (2 : Nat)) := hScale
      _ = _ := by field_simp [hR.ne']


private theorem xi_tail_hasSum (A : Real) (m : Nat) :
    HasSum (fun i : Nat => A * ((i : Real) + m + 3) / (2 : Real) ^ (i + 1))
      (A * ((m : Real) + 4)) := by
  have h0 := hasSum_geometric_of_norm_lt_one
    (show norm (1 / 2 : Real) < 1 by norm_num)
  have h1 := hasSum_choose_mul_geometric_of_norm_lt_one
    (r := (1 / 2 : Real)) 1 (by norm_num)
  have hBoth := (h1.add (h0.mul_left ((m : Real) + 2))).mul_left (A / 2)
  convert hBoth using 1
  . funext i
    simp [pow_succ]
    ring
  . norm_num
    ring

private theorem xi_finite_linear_sum (m : Nat) :
    2 * Finset.sum (Finset.range (m + 1)) (fun j : Nat => (j : Real) + 2) =
      ((m : Real) + 1) * ((m : Real) + 4) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Finset.sum_range_succ]
    push_cast
    nlinarith only [ih]


private theorem xi_degree_dyadic_bound (hRH : RiemannHypothesis)
    {C : Real} (hC : 0 <= C)
    (hCount : forall R : Real, 1 <= R ->
      (Nat.card {p : RiemannXiDivisorZeroIndex //
        norm (riemannXiDivisorZeroValue p) <= R} : Real) <=
          C * R * Real.log (R + 2))
    {n : Nat} (hn : 2 <= n) {m : Nat} (hnm : (n : Real) <= (2 : Real) ^ m) :
    tsum (fun p : RiemannXiDivisorZeroIndex =>
      norm (((n : Complex) / ((n : Complex) - riemannXiDivisorZeroValue p)) /
        riemannXiDivisorZeroValue p)) <=
      2 * C * Real.log 2 * ((m : Real) + 3) * ((m : Real) + 4) := by
  let A : Real := 4 * C * Real.log 2
  have hA : 0 <= A := by
    dsimp [A]
    exact mul_nonneg (by positivity) (Real.log_nonneg (by norm_num))
  let F : Nat -> Real := fun j => tsum (fun p : xiShell j =>
    norm (((n : Complex) / ((n : Complex) - riemannXiDivisorZeroValue p.val)) /
      riemannXiDivisorZeroValue p.val))
  have hPartition := (xi_coefficient_summable hRH hn).hasSum.tsum_fiberwise xiShellIndex
  change HasSum F _ at hPartition
  have hBounds (j : Nat) : And (F j <= A * ((j : Real) + 2))
      (F j <= A * ((j : Real) + 2) * n / (2 : Real) ^ j) :=
    xi_shell_coefficient_bounds hRH hC hCount hn j
  have hLowCmp : Finset.sum (Finset.range (m + 1)) F <=
      Finset.sum (Finset.range (m + 1)) (fun j => A * ((j : Real) + 2)) :=
    Finset.sum_le_sum (fun j _ => (hBounds j).1)
  rw [<- Finset.mul_sum] at hLowCmp
  have hLow : Finset.sum (Finset.range (m + 1)) F <=
      A * (((m : Real) + 1) * ((m : Real) + 4) / 2) := by
    have hEq : Finset.sum (Finset.range (m + 1)) (fun j : Nat => (j : Real) + 2) =
        ((m : Real) + 1) * ((m : Real) + 4) / 2 := by
      linarith only [xi_finite_linear_sum m]
    rwa [hEq] at hLowCmp
  have hTailPoint (i : Nat) :
      F (i + (m + 1)) <= A * ((i : Real) + m + 3) / (2 : Real) ^ (i + 1) := by
    have h := (hBounds (i + (m + 1))).2
    have hScale := mul_le_mul_of_nonneg_right hnm
      (show 0 <= A * (((i + (m + 1) : Nat) : Real) + 2) /
        (2 : Real) ^ (i + (m + 1)) by positivity)
    have hMid :
        A * (((i + (m + 1) : Nat) : Real) + 2) * n / (2 : Real) ^ (i + (m + 1)) <=
          A * ((i : Real) + m + 3) / (2 : Real) ^ (i + 1) := by
      convert hScale using 1
      all_goals simp only [Nat.cast_add, Nat.cast_one, pow_add, pow_succ]
      all_goals field_simp
      all_goals ring
    exact h.trans hMid
  have hTailSummable : Summable (fun i : Nat => F (i + (m + 1))) :=
    (summable_nat_add_iff (m + 1)).2 hPartition.summable
  have hTail := hTailSummable.tsum_le_tsum hTailPoint (xi_tail_hasSum A m).summable
  rw [(xi_tail_hasSum A m).tsum_eq] at hTail
  have hSplit := Summable.sum_add_tsum_nat_add (m + 1) hPartition.summable
  calc
    _ = tsum F := hPartition.tsum_eq.symm
    _ = Finset.sum (Finset.range (m + 1)) F +
        tsum (fun i : Nat => F (i + (m + 1))) := hSplit.symm
    _ <= A * (((m : Real) + 1) * ((m : Real) + 4) / 2) +
        A * ((m : Real) + 4) := add_le_add hLow hTail
    _ = _ := by dsimp [A]; ring


/-- The actual complete zero coefficient has one squared-logarithmic degree bound. -/
theorem exists_nicolasZeroCoefficient_log_bound (hRH : RiemannHypothesis) :
    Exists fun D : Real => And (0 < D) (forall n : Nat, 2 <= n ->
      tsum (fun p : RiemannXiDivisorZeroIndex =>
        norm (((n : Complex) / ((n : Complex) - riemannXiDivisorZeroValue p)) /
          riemannXiDivisorZeroValue p)) <= D * (Real.log ((n : Real) + 2)) ^ (2 : Nat)) := by
  choose C hC hCount using nicolasXi_zero_count_logarithmic
  have hLog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let D : Real := 60 * C / Real.log 2
  have hD : 0 < D := by dsimp [D]; positivity
  refine Exists.intro D (And.intro hD ?_)
  intro n hn
  have hnReal : (2 : Real) <= n := by exact_mod_cast hn
  have hnPos : (0 : Real) < n := by linarith
  let t : Real := Real.logb 2 (n : Real)
  let m : Nat := Nat.ceil t
  have hLogN : Real.log 2 <= Real.log (n : Real) :=
    Real.log_le_log (by norm_num) hnReal
  have ht : 1 <= t := by
    have h := mul_le_mul_of_nonneg_right hLogN (inv_nonneg.mpr hLog2.le)
    dsimp [t, Real.logb]
    simpa [div_eq_mul_inv, hLog2.ne'] using h
  have hceil : t <= (m : Real) := Nat.le_ceil t
  have hceilHi : (m : Real) <= t + 1 :=
    (Nat.ceil_lt_add_one (by linarith : 0 <= t)).le
  have hnPow : (n : Real) <= (2 : Real) ^ m := by
    calc
      _ = (2 : Real) ^ t := (Real.rpow_logb (by norm_num)
        (by norm_num : Not ((2 : Real) = 1)) hnPos).symm
      _ <= (2 : Real) ^ (m : Real) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hceil
      _ = _ := Real.rpow_natCast _ _
  have hBase := xi_degree_dyadic_bound hRH hC.le hCount hn hnPow
  have hThree : (m : Real) + 3 <= 5 * t := by linarith
  have hFour : (m : Real) + 4 <= 6 * t := by linarith
  have hProduct := mul_le_mul hThree hFour (by positivity) (by linarith : 0 <= 5 * t)
  have hScale := mul_le_mul_of_nonneg_left hProduct
    (show 0 <= 2 * C * Real.log 2 by positivity)
  have hSharp :
      tsum (fun p : RiemannXiDivisorZeroIndex =>
        norm (((n : Complex) / ((n : Complex) - riemannXiDivisorZeroValue p)) /
          riemannXiDivisorZeroValue p)) <= D * (Real.log (n : Real)) ^ (2 : Nat) := by
    calc
      _ <= 2 * C * Real.log 2 * ((m : Real) + 3) * ((m : Real) + 4) := hBase
      _ <= (2 * C * Real.log 2) * ((5 * t) * (6 * t)) := by nlinarith only [hScale]
      _ = _ := by
        dsimp [D, t, Real.logb]
        field_simp [hLog2.ne']
        ring
  have hLogN0 : 0 <= Real.log (n : Real) := Real.log_nonneg (by linarith)
  have hLogPlus : Real.log (n : Real) <= Real.log ((n : Real) + 2) :=
    Real.log_le_log hnPos (by linarith)
  have hSquare : (Real.log (n : Real)) ^ (2 : Nat) <=
      (Real.log ((n : Real) + 2)) ^ (2 : Nat) := by
    have h := mul_nonneg (sub_nonneg.mpr hLogPlus)
      (show 0 <= Real.log ((n : Real) + 2) + Real.log (n : Real) by linarith)
    nlinarith only [h]
  exact hSharp.trans (mul_le_mul_of_nonneg_left hSquare hD.le)

end PrimeFactorOscillations
