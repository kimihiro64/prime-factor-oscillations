/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFMinorTypeI
import PrimeFactorOscillations.Mathlib.Analysis.Complex.AbelBound

/-!
# Actual Vaughan Type I estimates with logarithmic weights

Summation by parts preserves every geometric prefix cancellation. The exact
zero-residue support and nonzero allowance are then summed together. Both
actual Type I coefficients are bounded, with all cutoffs and rational-frequency
perturbation conditions explicit. Full minor-arc assembly remains open.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem lpf_sum_Ioc_eq_range {R : Type} [AddCommMonoid R] (lo hi : Nat) (f : Nat -> R) :
    Finset.sum (Finset.Ioc lo hi) f = Finset.sum (Finset.range (hi - lo)) (fun i => f (lo + 1 + i)) := by
  symm
  apply Finset.sum_bij (fun i _ => lo + 1 + i)
  . intro i hiMem
    have h := Finset.mem_range.mp hiMem
    exact Finset.mem_Ioc.mpr (by omega)
  . intro i hiMem j hjMem hEq
    exact Nat.add_left_cancel hEq
  . intro m hm
    have h := Finset.mem_Ioc.mp hm
    refine Exists.intro (m - lo - 1) (Exists.intro (Finset.mem_range.mpr (by omega)) (by omega))
  . intro i hiMem
    rfl

theorem lpf_log_weighted_interval_of_prefix_bound (lo hi H : Nat) (hH : 1 <= H) (hHi : hi <= H)
    (f : Nat -> Complex) (T : Real) (hT : 0 <= T)
    (hPrefix : forall b, lo <= b -> b <= hi -> norm (Finset.sum (Finset.Ioc lo b) f) <= T) :
    norm (Finset.sum (Finset.Ioc lo hi) (fun m => (Real.log (m : Real) : Complex) * f m)) <=
      2 * Real.log (H : Real) * T := by
  by_cases hRange : lo <= hi
  . let a : Nat -> Real := fun i => Real.log ((lo + 1 + i : Nat) : Real)
    let g : Nat -> Complex := fun i => f (lo + 1 + i)
    have ha : Monotone a := by
      intro i j hij
      apply Real.log_le_log
      . exact Nat.cast_pos.mpr (by omega)
      . exact_mod_cast (by omega : lo + 1 + i <= lo + 1 + j)
    have ha0 : 0 <= a 0 := by
      dsimp [a]
      apply Real.log_nonneg
      exact_mod_cast (by omega : 1 <= lo + 1 + 0)
    have hW : 0 <= Real.log (H : Real) := Real.log_nonneg (by exact_mod_cast hH)
    have haW : forall i, i < hi - lo -> a i <= Real.log (H : Real) := by
      intro i hiMem
      apply Real.log_le_log
      . exact Nat.cast_pos.mpr (by omega)
      . exact_mod_cast (by omega : lo + 1 + i <= H)
    have hP : forall n, n <= hi - lo -> norm (Finset.sum (Finset.range n) g) <= T := by
      intro n hn
      have h := hPrefix (lo + n) (by omega) (by omega)
      rw [lpf_sum_Ioc_eq_range] at h
      simpa only [Nat.add_sub_cancel_left] using h
    rw [lpf_sum_Ioc_eq_range]
    have h := Finset.norm_sum_range_smul_le_of_monotone a g (hi - lo) T (Real.log (H : Real)) ha ha0 hT hW haW hP
    simpa only [a, g, Complex.real_smul] using h
  . have hEmpty : Finset.Ioc lo hi = Finset.empty := Finset.Ioc_eq_empty_of_le (by omega)
    have hW : 0 <= Real.log (H : Real) := Real.log_nonneg (by exact_mod_cast hH)
    simpa [hEmpty, Finset.empty] using (show 0 <= 2 * Real.log (H : Real) * T by positivity)

theorem lpf_typeI_window_log_minor_point_bound {N q : Nat} [NeZero N] [NeZero q]
    (k a : Int) (u : Units (ZMod q)) (hU : (a : ZMod q) = (u : ZMod q))
    (beta : Real) (D s L d H : Nat) (hd : Membership.mem (Finset.Ioc 0 D) d)
    (hH : 1 <= H) (hTop : s + L <= H)
    (hAlpha : (k : Real) / (N : Real) = (a : Real) / (q : Real) + beta)
    (hBeta : abs beta * (D : Real) <= 1 / (4 * (q : Real))) :
    norm (Finset.sum (Finset.Ioc (s / d) ((s + L) / d)) (fun m =>
      (Real.log (m : Real) : Complex) * ZMod.stdAddChar (N := N)
        ((k : ZMod N) * (m : ZMod N) * (d : ZMod N)))) <=
      2 * Real.log (H : Real) *
        ((if Dvd.dvd q d then ((s + L : Nat) : Real) / (d : Real) else 0) +
          lpfMinorResidueAllowance q 0 (((u : ZMod q) * (d : ZMod q)).val)) := by
  let T : Real := (if Dvd.dvd q d then ((s + L : Nat) : Real) / (d : Real) else 0) +
    lpfMinorResidueAllowance q 0 (((u : ZMod q) * (d : ZMod q)).val)
  have hT : 0 <= T := by
    dsimp [T]
    apply add_nonneg
    . split_ifs <;> positivity
    . exact lpfMinorResidueAllowance_nonneg q _ 0 (by norm_num)
  apply lpf_log_weighted_interval_of_prefix_bound (s / d) ((s + L) / d) H hH
    ((Nat.div_le_self _ _).trans hTop) _ T hT
  intro b hbLo hbHi
  have hdPos : 0 < d := (Finset.mem_Ioc.mp hd).1
  have hdLe : d <= D := (Finset.mem_Ioc.mp hd).2
  have hCast : ((a * (d : Int) : Int) : ZMod q) = (u : ZMod q) * (d : ZMod q) := by
    simp only [Int.cast_mul, Int.cast_natCast, hU]
  dsimp [T]
  by_cases hDiv : Dvd.dvd q d
  . have hZero := (lpf_unit_nat_residue_zero_iff u d).mpr hDiv
    rw [ite_eq_left hDiv, lpfMinorResidueAllowance, ite_eq_left hZero, add_zero]
    have hLength := norm_lpf_grid_pair_interval_le_length (N := N) k (d : Int) (s / d) b
    have hLength' : norm (Finset.sum (Finset.Ioc (s / d) b) (fun m =>
      ZMod.stdAddChar (N := N) ((k : ZMod N) * (m : ZMod N) * (d : ZMod N)))) <=
        ((b - s / d : Nat) : Real) := by simpa only [Int.cast_natCast] using hLength
    exact hLength'.trans ((Nat.cast_le.mpr ((Nat.sub_le _ _).trans hbHi)).trans
      (lpf_nat_div_cast_le (s + L) d hdPos))
  . have hZero : Not ((((u : ZMod q) * (d : ZMod q)).val) = 0) := by
      intro h
      exact hDiv ((lpf_unit_nat_residue_zero_iff u d).mp h)
    rw [ite_eq_right hDiv, zero_add, lpfMinorResidueAllowance, ite_eq_right hZero]
    have hError : abs (beta * ((d : Int) : Real)) <= 1 / (4 * (q : Real)) := by
      have hAbs : abs (d : Real) = (d : Real) := abs_of_nonneg (Nat.cast_nonneg d)
      rw [abs_mul, Int.cast_natCast, hAbs]
      exact (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hdLe) (abs_nonneg beta)).trans hBeta
    have hPositive : 0 < (((a * (d : Int) : Int) : ZMod q).val) := by rw [hCast]; exact Nat.pos_of_ne_zero hZero
    have h := lpf_grid_pair_interval_minor_bound (N := N) k a (d : Int) beta (s / d) b hAlpha hPositive hError
    simpa only [hCast, Int.cast_natCast, div_eq_mul_inv, one_mul] using h.trans (min_le_right _ _)

theorem lpf_typeI_window_log_weighted_bound {N q : Nat} [NeZero N] [NeZero q]
    (k a : Int) (u : Units (ZMod q)) (hU : (a : ZMod q) = (u : ZMod q))
    (beta : Real) (D s L H : Nat) (coeff : Nat -> Complex) (C0 : Real)
    (hC : 0 <= C0) (hH : 1 <= H) (hTop : s + L <= H)
    (hCoeff : forall d, Membership.mem (Finset.Ioc 0 D) d -> norm (coeff d) <= C0)
    (hAlpha : (k : Real) / (N : Real) = (a : Real) / (q : Real) + beta)
    (hBeta : abs beta * (D : Real) <= 1 / (4 * (q : Real))) :
    norm (Finset.sum (Finset.Ioc 0 D) (fun d => coeff d *
      Finset.sum (Finset.Ioc (s / d) ((s + L) / d)) (fun m =>
        (Real.log (m : Real) : Complex) * ZMod.stdAddChar (N := N)
          ((k : ZMod N) * (m : ZMod N) * (d : ZMod N))))) <=
      C0 * (2 * Real.log (H : Real)) *
        ((if D < q then 0 else (((s + L : Nat) : Real) / (q : Real)) *
          (1 + Real.log ((D / q : Nat) : Real))) +
          ((D / q + 1 : Nat) : Real) * (2 * (q : Real) * (1 + Real.log (q : Real)))) := by
  classical
  let K : Nat -> Complex := fun d => Finset.sum (Finset.Ioc (s / d) ((s + L) / d)) (fun m =>
    (Real.log (m : Real) : Complex) * ZMod.stdAddChar (N := N)
      ((k : ZMod N) * (m : ZMod N) * (d : ZMod N)))
  let F : Nat -> Real := fun d => lpfMinorResidueAllowance q 0 (((u : ZMod q) * (d : ZMod q)).val)
  have hLog : 0 <= Real.log (H : Real) := Real.log_nonneg (by exact_mod_cast hH)
  have hSum : norm (Finset.sum (Finset.Ioc 0 D) (fun d => coeff d * K d)) <=
      C0 * (2 * Real.log (H : Real)) *
        (Finset.sum ((Finset.Ioc 0 D).filter (fun d => Dvd.dvd q d))
          (fun d => ((s + L : Nat) : Real) / (d : Real)) + Finset.sum (Finset.Ioc 0 D) F) := by
    calc
      _ <= Finset.sum (Finset.Ioc 0 D) (fun d => norm (coeff d * K d)) := norm_sum_le _ _
      _ <= Finset.sum (Finset.Ioc 0 D) (fun d => C0 * (2 * Real.log (H : Real)) *
          ((if Dvd.dvd q d then ((s + L : Nat) : Real) / (d : Real) else 0) + F d)) := by
        apply Finset.sum_le_sum
        intro d hd
        rw [norm_mul]
        have h := (mul_le_mul_of_nonneg_right (hCoeff d hd) (norm_nonneg _)).trans
          (mul_le_mul_of_nonneg_left (lpf_typeI_window_log_minor_point_bound k a u hU beta D s L d H hd hH hTop hAlpha hBeta) hC)
        convert h using 1 <;> ring
      _ = _ := by rw [<- Finset.mul_sum, Finset.sum_add_distrib, <- Finset.sum_filter]
  have hZero := lpf_positive_divisible_inverse_sum_bound q D (Nat.pos_of_ne_zero (NeZero.ne q))
    ((s + L : Nat) : Real) (Nat.cast_nonneg _)
  have hNonzero := lpf_unit_nonzero_allowance_interval_bound u D
  exact hSum.trans (mul_le_mul_of_nonneg_left (add_le_add hZero hNonzero) (by positivity))

theorem lpf_typeI_moebius_log_window_bound {N q : Nat} [NeZero N] [NeZero q]
    (k a : Int) (u : Units (ZMod q)) (hU : (a : ZMod q) = (u : ZMod q))
    (beta : Real) (V s L H : Nat) (hH : 1 <= H) (hTop : s + L <= H)
    (hAlpha : (k : Real) / (N : Real) = (a : Real) / (q : Real) + beta)
    (hBeta : abs beta * (V : Real) <= 1 / (4 * (q : Real))) :
    norm (Finset.sum (Finset.Ioc 0 V) (fun d =>
      ((lpfArithmeticCutoff (ArithmeticFunction.moebius : ArithmeticFunction Real) V d : Real) : Complex) *
        Finset.sum (Finset.Ioc (s / d) ((s + L) / d)) (fun m =>
          (Real.log (m : Real) : Complex) * ZMod.stdAddChar (N := N)
            ((k : ZMod N) * (m : ZMod N) * (d : ZMod N))))) <=
      (2 * Real.log (H : Real)) *
        ((if V < q then 0 else (((s + L : Nat) : Real) / (q : Real)) *
          (1 + Real.log ((V / q : Nat) : Real))) +
          ((V / q + 1 : Nat) : Real) * (2 * (q : Real) * (1 + Real.log (q : Real)))) := by
  have h := lpf_typeI_window_log_weighted_bound k a u hU beta V s L H
    (fun d => ((lpfArithmeticCutoff (ArithmeticFunction.moebius : ArithmeticFunction Real) V d : Real) : Complex))
    1 (by norm_num) hH hTop (fun d _ => by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using abs_lpfArithmeticCutoff_moebius_le V d) hAlpha hBeta
  simpa only [one_mul] using h

theorem lpf_typeI_vaughanA_window_bound {N q : Nat} [NeZero N] [NeZero q]
    (k a : Int) (u : Units (ZMod q)) (hU : (a : ZMod q) = (u : ZMod q))
    (beta : Real) (U V s L H : Nat) (hH : 1 <= H) (hD : U * V <= H)
    (hAlpha : (k : Real) / (N : Real) = (a : Real) / (q : Real) + beta)
    (hBeta : abs beta * ((U * V : Nat) : Real) <= 1 / (4 * (q : Real))) :
    norm (Finset.sum (Finset.Ioc 0 (U * V)) (fun d => ((lpfVaughanA U V d : Real) : Complex) *
      Finset.sum (Finset.Ioc (s / d) ((s + L) / d)) (fun m =>
        ZMod.stdAddChar (N := N) ((k : ZMod N) * (m : ZMod N) * (d : ZMod N))))) <=
      Real.log (H : Real) *
        ((if U * V < q then 0 else (((s + L : Nat) : Real) / (q : Real)) *
          (1 + Real.log (((U * V) / q : Nat) : Real))) +
          (((U * V) / q + 1 : Nat) : Real) * (2 * (q : Real) * (1 + Real.log (q : Real)))) := by
  apply lpf_typeI_window_weighted_bound k a u hU beta (U * V) s L _ (Real.log (H : Real))
    (Real.log_nonneg (by exact_mod_cast hH)) _ hAlpha hBeta
  intro d hd
  have hRange := Finset.mem_Ioc.mp hd
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact (abs_lpfVaughanA_le_log U V d).trans
    (Real.log_le_log (Nat.cast_pos.mpr hRange.1) (Nat.cast_le.mpr (hRange.2.trans hD)))

end PrimeFactorOscillations.LPF

