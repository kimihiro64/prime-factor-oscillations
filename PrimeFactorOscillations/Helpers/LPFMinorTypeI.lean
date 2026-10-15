/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFMinorResidueMean
import PrimeFactorOscillations.Helpers.LPFMinorWeightedPacket

/-!
# Exact Type I zero-residue support and harmonic cost

Positive multiples of q through D reindex exactly as q*j with
1<=j<=floor(D/q). Their inverse-weight sum is at most
(X/q)*(1+log(floor(D/q))), and is exactly zero when D<q.
The unweighted estimate combines this exact zero-residue support with every
nonzero phase allowance. LPFMinorTypeILog supplies the logarithmic-weight
consumer. Range coverage and rational approximation remain assembly obligations.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem lpf_positive_divisible_sum_reindex {R : Type} [AddCommMonoid R]
    (q D : Nat) (hq : 0 < q) (f : Nat -> R) :
    Finset.sum ((Finset.Ioc 0 D).filter (fun d => Dvd.dvd q d)) f =
      Finset.sum (Finset.Ioc 0 (D / q)) (fun j => f (q * j)) := by
  classical
  symm
  apply Finset.sum_bij (fun j _ => q * j)
  . intro j hj
    have h := Finset.mem_Ioc.mp hj
    have hD : q * (D / q) <= D := by have hDiv := Nat.div_add_mod D q; omega
    refine Finset.mem_filter.mpr (And.intro (Finset.mem_Ioc.mpr (And.intro ?_ ?_)) (dvd_mul_right q j))
    . exact Nat.mul_pos hq h.1
    . exact (Nat.mul_le_mul_left q h.2).trans hD
  . intro j hj k hk hEq
    exact Nat.eq_of_mul_eq_mul_left hq hEq
  . intro d hd
    have h := Finset.mem_filter.mp hd
    have hRange := Finset.mem_Ioc.mp h.1
    have hProduct : q * (d / q) = d := by rw [Nat.mul_comm, Nat.div_mul_cancel h.2]
    have hPositive : 0 < d / q := by
      apply Nat.pos_of_ne_zero
      intro hZero
      rw [hZero, mul_zero] at hProduct
      omega
    refine Exists.intro (d / q) (Exists.intro ?_ hProduct)
    exact Finset.mem_Ioc.mpr (And.intro hPositive (Nat.div_le_div_right hRange.2))
  . intro j hj
    rfl

theorem lpf_positive_divisible_inverse_sum (q D : Nat) (hq : 0 < q) (X : Real) :
    Finset.sum ((Finset.Ioc 0 D).filter (fun d => Dvd.dvd q d)) (fun d => X / (d : Real)) =
      (X / (q : Real)) * Finset.sum (Finset.Ioc 0 (D / q)) (fun j => 1 / (j : Real)) := by
  rw [lpf_positive_divisible_sum_reindex q D hq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hqR : (0 : Real) < (q : Real) := Nat.cast_pos.mpr hq
  have hjR : (0 : Real) < (j : Real) := Nat.cast_pos.mpr (Finset.mem_Ioc.mp hj).1
  push_cast
  field_simp

theorem lpf_positive_divisible_inverse_sum_bound (q D : Nat) (hq : 0 < q) (X : Real) (hX : 0 <= X) :
    Finset.sum ((Finset.Ioc 0 D).filter (fun d => Dvd.dvd q d)) (fun d => X / (d : Real)) <=
      if D < q then 0 else (X / (q : Real)) * (1 + Real.log ((D / q : Nat) : Real)) := by
  rw [lpf_positive_divisible_inverse_sum q D hq]
  by_cases hD : D < q
  . rw [ite_eq_left hD, Nat.div_eq_of_lt hD]
    simp
  . rw [ite_eq_right hD]
    have hLe : q <= D := le_of_not_gt hD
    have hQuot : 1 <= D / q := (Nat.le_div_iff_mul_le hq).mpr (by simpa using hLe)
    exact mul_le_mul_of_nonneg_left (lpf_harmonic_Ioc_log_bound (D / q) (by omega)) (by positivity)

theorem lpf_unit_nonzero_allowance_interval_bound {q : Nat} [NeZero q]
    (u : Units (ZMod q)) (D : Nat) :
    Finset.sum (Finset.Ioc 0 D) (fun d =>
      lpfMinorResidueAllowance q 0 (((u : ZMod q) * (d : ZMod q)).val)) <=
        ((D / q + 1 : Nat) : Real) * (2 * (q : Real) * (1 + Real.log (q : Real))) := by
  let F : ZMod q -> Real := fun r => lpfMinorResidueAllowance q 0 r.val
  have hF : forall r, 0 <= F r := fun r => lpfMinorResidueAllowance_nonneg q r.val 0 (by norm_num)
  have hPeriod : Finset.sum Finset.univ (fun r : ZMod q => F (-r)) = Finset.sum Finset.univ F := by
    simpa using lpf_unit_difference_residue_sum (1 : Units (ZMod q)) 0 F
  have hAll : Finset.sum Finset.univ F <= 2 * (q : Real) * (1 + Real.log (q : Real)) := by
    rw [<- lpf_natural_residue_sum F]
    have hEq : Finset.sum (Finset.range q) (fun j => F (j : ZMod q)) =
        Finset.sum (Finset.range q) (lpfMinorResidueAllowance q 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [F]
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hj)]
    rw [hEq]
    simpa using lpfMinorResidueAllowance_period_bound q (Nat.pos_of_ne_zero (NeZero.ne q)) 0
  have h := lpf_unit_difference_interval_sum_bound u 0 0 D (fun r => F (-r)) (fun r => hF _)
  simp only [zero_sub, mul_neg, neg_neg, Nat.sub_zero] at h
  rw [hPeriod] at h
  exact h.trans (mul_le_mul_of_nonneg_left hAll (by positivity))

theorem lpf_unit_nat_residue_zero_iff {q : Nat} [NeZero q]
    (u : Units (ZMod q)) (d : Nat) :
    (((u : ZMod q) * (d : ZMod q)).val = 0) <-> Dvd.dvd q d := by
  have hCancel : (u : ZMod q) * (d : ZMod q) = 0 <-> (d : ZMod q) = 0 := by
    constructor
    . intro h
      have h' := congrArg (fun x : ZMod q => ((Inv.inv u : Units (ZMod q)) : ZMod q) * x) h
      simpa [<- mul_assoc] using h'
    . intro h
      rw [h, mul_zero]
  rw [ZMod.val_eq_zero, hCancel]
  constructor
  . intro h
    have h' := congrArg (fun x : ZMod q => x.val) h
    have hMod : d % q = 0 := by simpa only [ZMod.val_natCast, ZMod.val_zero] using h'
    exact Nat.dvd_of_mod_eq_zero hMod
  . intro h
    apply ZMod.val_injective
    simp only [ZMod.val_natCast, ZMod.val_zero, Nat.mod_eq_zero_of_dvd h]

theorem lpf_typeI_window_minor_point_bound {N q : Nat} [NeZero N] [NeZero q]
    (k a : Int) (u : Units (ZMod q)) (hU : (a : ZMod q) = (u : ZMod q))
    (beta : Real) (D s L d : Nat) (hd : Membership.mem (Finset.Ioc 0 D) d)
    (hAlpha : (k : Real) / (N : Real) = (a : Real) / (q : Real) + beta)
    (hBeta : abs beta * (D : Real) <= 1 / (4 * (q : Real))) :
    norm (Finset.sum (Finset.Ioc (s / d) ((s + L) / d)) (fun m =>
      ZMod.stdAddChar (N := N) ((k : ZMod N) * (m : ZMod N) * (d : ZMod N)))) <=
        (if Dvd.dvd q d then ((s + L : Nat) : Real) / (d : Real) else 0) +
          lpfMinorResidueAllowance q 0 (((u : ZMod q) * (d : ZMod q)).val) := by
  have hdPos : 0 < d := (Finset.mem_Ioc.mp hd).1
  have hdLe : d <= D := (Finset.mem_Ioc.mp hd).2
  have hCast : ((a * (d : Int) : Int) : ZMod q) = (u : ZMod q) * (d : ZMod q) := by
    simp only [Int.cast_mul, Int.cast_natCast, hU]
  by_cases hDiv : Dvd.dvd q d
  . have hZero := (lpf_unit_nat_residue_zero_iff u d).mpr hDiv
    rw [ite_eq_left hDiv, lpfMinorResidueAllowance, ite_eq_left hZero, add_zero]
    have hLength := norm_lpf_grid_pair_interval_le_length (N := N) k (d : Int) (s / d) ((s + L) / d)
    have hLength' : norm (Finset.sum (Finset.Ioc (s / d) ((s + L) / d)) (fun m =>
      ZMod.stdAddChar (N := N) ((k : ZMod N) * (m : ZMod N) * (d : ZMod N)))) <=
        (((s + L) / d - s / d : Nat) : Real) := by simpa only [Int.cast_natCast] using hLength
    exact hLength'.trans ((Nat.cast_le.mpr (Nat.sub_le _ _)).trans (lpf_nat_div_cast_le (s + L) d hdPos))
  . have hZero : Not ((((u : ZMod q) * (d : ZMod q)).val) = 0) := by
      intro h
      exact hDiv ((lpf_unit_nat_residue_zero_iff u d).mp h)
    rw [ite_eq_right hDiv, zero_add, lpfMinorResidueAllowance, ite_eq_right hZero]
    have hError : abs (beta * ((d : Int) : Real)) <= 1 / (4 * (q : Real)) := by
      have hAbs : abs (d : Real) = (d : Real) := abs_of_nonneg (Nat.cast_nonneg d)
      rw [abs_mul, Int.cast_natCast, hAbs]
      exact (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hdLe) (abs_nonneg beta)).trans hBeta
    have hPositive : 0 < (((a * (d : Int) : Int) : ZMod q).val) := by rw [hCast]; exact Nat.pos_of_ne_zero hZero
    have h := lpf_grid_pair_interval_minor_bound (N := N) k a (d : Int) beta (s / d) ((s + L) / d)
      hAlpha hPositive hError
    have h' := h.trans (min_le_right _ _)
    simpa only [hCast, Int.cast_natCast, div_eq_mul_inv, one_mul] using h'

theorem lpf_typeI_window_weighted_bound {N q : Nat} [NeZero N] [NeZero q]
    (k a : Int) (u : Units (ZMod q)) (hU : (a : ZMod q) = (u : ZMod q))
    (beta : Real) (D s L : Nat) (coeff : Nat -> Complex) (C0 : Real)
    (hC : 0 <= C0) (hCoeff : forall d, Membership.mem (Finset.Ioc 0 D) d -> norm (coeff d) <= C0)
    (hAlpha : (k : Real) / (N : Real) = (a : Real) / (q : Real) + beta)
    (hBeta : abs beta * (D : Real) <= 1 / (4 * (q : Real))) :
    norm (Finset.sum (Finset.Ioc 0 D) (fun d => coeff d *
      Finset.sum (Finset.Ioc (s / d) ((s + L) / d)) (fun m =>
        ZMod.stdAddChar (N := N) ((k : ZMod N) * (m : ZMod N) * (d : ZMod N))))) <=
      C0 * ((if D < q then 0 else (((s + L : Nat) : Real) / (q : Real)) *
        (1 + Real.log ((D / q : Nat) : Real))) +
        ((D / q + 1 : Nat) : Real) * (2 * (q : Real) * (1 + Real.log (q : Real)))) := by
  classical
  let K : Nat -> Complex := fun d => Finset.sum (Finset.Ioc (s / d) ((s + L) / d)) (fun m =>
    ZMod.stdAddChar (N := N) ((k : ZMod N) * (m : ZMod N) * (d : ZMod N)))
  let F : Nat -> Real := fun d => lpfMinorResidueAllowance q 0 (((u : ZMod q) * (d : ZMod q)).val)
  have hSum : norm (Finset.sum (Finset.Ioc 0 D) (fun d => coeff d * K d)) <=
      C0 * (Finset.sum ((Finset.Ioc 0 D).filter (fun d => Dvd.dvd q d))
        (fun d => ((s + L : Nat) : Real) / (d : Real)) + Finset.sum (Finset.Ioc 0 D) F) := by
    calc
      _ <= Finset.sum (Finset.Ioc 0 D) (fun d => norm (coeff d * K d)) := norm_sum_le _ _
      _ <= Finset.sum (Finset.Ioc 0 D) (fun d => C0 *
          ((if Dvd.dvd q d then ((s + L : Nat) : Real) / (d : Real) else 0) + F d)) := by
        apply Finset.sum_le_sum
        intro d hd
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_right (hCoeff d hd) (norm_nonneg _)).trans
          (mul_le_mul_of_nonneg_left (lpf_typeI_window_minor_point_bound k a u hU beta D s L d hd hAlpha hBeta) hC)
      _ = _ := by rw [<- Finset.mul_sum, Finset.sum_add_distrib, <- Finset.sum_filter]
  have hZero := lpf_positive_divisible_inverse_sum_bound q D (Nat.pos_of_ne_zero (NeZero.ne q))
    ((s + L : Nat) : Real) (Nat.cast_nonneg _)
  have hNonzero := lpf_unit_nonzero_allowance_interval_bound u D
  exact hSum.trans (mul_le_mul_of_nonneg_left (add_le_add hZero hNonzero) hC)


end PrimeFactorOscillations.LPF
