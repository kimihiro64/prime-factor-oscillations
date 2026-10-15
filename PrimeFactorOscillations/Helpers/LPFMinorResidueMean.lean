/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import PrimeFactorOscillations.Helpers.LPFMinorGeometric

/-!
# Residue multiplicities and the logarithmic geometric-denominator sum

Every residue has at most floor(D/q)+1 representatives in [0,D].
Unit multiplication preserves the complete residue sum. Nonzero residues
have total inverse distance at most 2*(1+log q), by exact reflection and
a logarithmic telescoping bound. Zero residues remain in the weighted
count with their supplied length allowance; none are dropped here.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem lpf_mod_fiber_card_le (q D r : Nat) :
    ((Finset.range (D + 1)).filter (fun d => d % q = r)).card <= D / q + 1 := by
  classical
  let F := (Finset.range (D + 1)).filter (fun d => d % q = r)
  have hInj : Set.InjOn (fun d => d / q) (F : Set Nat) := by
    intro x hx y hy hEq
    have hxMod := (Finset.mem_filter.mp hx).2
    have hyMod := (Finset.mem_filter.mp hy).2
    have hxId := Nat.div_add_mod x q
    have hyId := Nat.div_add_mod y q
    change x / q = y / q at hEq
    rw [hxMod, hEq] at hxId
    rw [hyMod] at hyId
    exact hxId.symm.trans hyId
  have hSubset : F.image (fun d => d / q) <= Finset.range (D / q + 1) := by
    intro j hj
    choose d hd hEq using Finset.mem_image.mp hj
    rw [<- hEq]
    apply Finset.mem_range.mpr
    have hD : d <= D := by
      have h := Finset.mem_range.mp (Finset.mem_filter.mp hd).1
      omega
    have hDiv : d / q <= D / q := Nat.div_le_div_right hD
    omega
  calc
    _ = (F.image (fun d => d / q)).card := (Finset.card_image_of_injOn hInj).symm
    _ <= (Finset.range (D / q + 1)).card := Finset.card_le_card hSubset
    _ = _ := Finset.card_range _

theorem lpf_weighted_residue_prefix_bound (q D : Nat) (hq : 0 < q)
    (F : Nat -> Real) (hF : forall r, r < q -> 0 <= F r) :
    Finset.sum (Finset.range (D + 1)) (fun d => F (d % q)) <=
      ((D / q + 1 : Nat) : Real) * Finset.sum (Finset.range q) F := by
  classical
  have hSingle (d : Nat) : Finset.sum (Finset.range q)
      (fun r => if d % q = r then F r else 0) = F (d % q) := by
    rw [Finset.sum_eq_single (d % q)]
    . simp
    . intro r hr hNe
      exact ite_eq_right (Ne.symm hNe)
    . intro hNot
      exact False.elim (hNot (Finset.mem_range.mpr (Nat.mod_lt d hq)))
  have hCount (r : Nat) : Finset.sum (Finset.range (D + 1))
      (fun d => if d % q = r then F r else 0) =
        F r * (((Finset.range (D + 1)).filter (fun d => d % q = r)).card : Real) := by
    rw [<- Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  calc
    _ = Finset.sum (Finset.range (D + 1)) (fun d =>
        Finset.sum (Finset.range q) (fun r => if d % q = r then F r else 0)) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact (hSingle d).symm
    _ = Finset.sum (Finset.range q) (fun r =>
        Finset.sum (Finset.range (D + 1)) (fun d => if d % q = r then F r else 0)) :=
      Finset.sum_comm
    _ = Finset.sum (Finset.range q) (fun r =>
        F r * (((Finset.range (D + 1)).filter (fun d => d % q = r)).card : Real)) := by
      apply Finset.sum_congr rfl
      intro r hr
      exact hCount r
    _ <= Finset.sum (Finset.range q) (fun r => F r * ((D / q + 1 : Nat) : Real)) := by
      apply Finset.sum_le_sum
      intro r hr
      have hCard : (((Finset.range (D + 1)).filter (fun d => d % q = r)).card : Real) <=
          ((D / q + 1 : Nat) : Real) := Nat.cast_le.mpr (lpf_mod_fiber_card_le q D r)
      exact mul_le_mul_of_nonneg_left hCard (hF r (Finset.mem_range.mp hr))
    _ = _ := by rw [<- Finset.sum_mul]; ring

theorem lpf_unit_residue_sum {q : Nat} [NeZero q] (a : Units (ZMod q)) (F : ZMod q -> Real) :
    Finset.sum Finset.univ (fun r => F ((a : ZMod q) * r)) = Finset.sum Finset.univ F := by
  apply Finset.sum_bij (fun r _ => (a : ZMod q) * r)
  . intro r hr
    exact Finset.mem_univ _
  . intro r hr s hs hEq
    have h := congrArg (fun z => ((Inv.inv a : Units (ZMod q)) : ZMod q) * z) hEq
    simpa [<- mul_assoc] using h
  . intro s hs
    refine Exists.intro (((Inv.inv a : Units (ZMod q)) : ZMod q) * s) (Exists.intro (Finset.mem_univ _) ?_)
    simp [<- mul_assoc]
  . intro r hr
    rfl

theorem lpf_reciprocal_log_step (x : Real) (hx : 0 < x) :
    1 / (x + 1) <= Real.log (x + 1) - Real.log x := by
  have hx1 : 0 < x + 1 := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos hx hx1)
  rw [Real.log_div (ne_of_gt hx) (ne_of_gt hx1)] at h
  have hFrac : x / (x + 1) - 1 = -(1 / (x + 1)) := by field_simp; ring
  rw [hFrac] at h
  linarith

theorem lpf_harmonic_prefix_log_bound (K : Nat) :
    Finset.sum (Finset.range (K + 1)) (fun j => 1 / ((j : Real) + 1)) <=
      1 + Real.log ((K : Real) + 1) := by
  induction K with
  | zero => norm_num
  | succ K ih =>
    rw [Finset.sum_range_succ]
    simp only [Nat.cast_succ]
    have hStep := lpf_reciprocal_log_step ((K : Real) + 1) (by positivity)
    linarith only [ih, hStep]

theorem lpf_harmonic_Ioc_log_bound (q : Nat) (hq : 0 < q) :
    Finset.sum (Finset.Ioc 0 q) (fun j => 1 / (j : Real)) <= 1 + Real.log (q : Real) := by
  have hMap : Finset.sum (Finset.range q) (fun j => 1 / ((j : Real) + 1)) =
      Finset.sum (Finset.Ioc 0 q) (fun j => 1 / (j : Real)) := by
    apply Finset.sum_bij (fun j _ => j + 1)
    . intro j hj
      have h := Finset.mem_range.mp hj
      apply Finset.mem_Ioc.mpr
      omega
    . intro j hj k hk hEq
      exact Nat.add_right_cancel hEq
    . intro j hj
      have h := Finset.mem_Ioc.mp hj
      refine Exists.intro (j - 1) (Exists.intro ?_ ?_)
      . apply Finset.mem_range.mpr
        omega
      . omega
    . intro j hj
      push_cast
      rfl
  have hNat : q - 1 + 1 = q := by omega
  have hCast : ((q - 1 : Nat) : Real) + 1 = (q : Real) := by exact_mod_cast hNat
  have hBound := lpf_harmonic_prefix_log_bound (q - 1)
  rw [hNat, hCast, hMap] at hBound
  exact hBound

theorem lpf_residue_reciprocal_sum_bound (q : Nat) (hq : 0 < q) :
    Finset.sum (Finset.Ioc 0 (q - 1))
      (fun j => 1 / ((min j (q - j) : Nat) : Real)) <= 2 * (1 + Real.log (q : Real)) := by
  have hReflect : Finset.sum (Finset.Ioc 0 (q - 1)) (fun j => 1 / ((q - j : Nat) : Real)) =
      Finset.sum (Finset.Ioc 0 (q - 1)) (fun j => 1 / (j : Real)) := by
    apply Finset.sum_bij (fun j _ => q - j)
    . intro j hj
      have h := Finset.mem_Ioc.mp hj
      apply Finset.mem_Ioc.mpr
      omega
    . intro j hj k hk hEq
      have hJ := Finset.mem_Ioc.mp hj
      have hK := Finset.mem_Ioc.mp hk
      omega
    . intro j hj
      have h := Finset.mem_Ioc.mp hj
      refine Exists.intro (q - j) (Exists.intro ?_ ?_)
      . apply Finset.mem_Ioc.mpr
        omega
      . omega
    . intro j hj
      rfl
  have hPoint : forall j, Membership.mem (Finset.Ioc 0 (q - 1)) j ->
      1 / ((min j (q - j) : Nat) : Real) <= 1 / (j : Real) + 1 / ((q - j : Nat) : Real) := by
    intro j hj
    by_cases h : j <= q - j
    . rw [min_eq_left h]
      exact le_add_of_nonneg_right (by positivity)
    . rw [min_eq_right (le_of_not_ge h)]
      exact le_add_of_nonneg_left (by positivity)
  have hSubset : Finset.Ioc 0 (q - 1) <= Finset.Ioc 0 q := by
    intro j hj
    have h := Finset.mem_Ioc.mp hj
    apply Finset.mem_Ioc.mpr
    omega
  have hHarmonic : Finset.sum (Finset.Ioc 0 (q - 1)) (fun j => 1 / (j : Real)) <=
      1 + Real.log (q : Real) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hSubset (fun j _ _ => by positivity)).trans
      (lpf_harmonic_Ioc_log_bound q hq)
  calc
    _ <= Finset.sum (Finset.Ioc 0 (q - 1)) (fun j => 1 / (j : Real) + 1 / ((q - j : Nat) : Real)) :=
      Finset.sum_le_sum hPoint
    _ = 2 * Finset.sum (Finset.Ioc 0 (q - 1)) (fun j => 1 / (j : Real)) := by
      rw [Finset.sum_add_distrib, hReflect]
      ring
    _ <= _ := mul_le_mul_of_nonneg_left hHarmonic (by norm_num)

noncomputable def lpfMinorResidueAllowance (q : Nat) (L : Real) (r : Nat) : Real :=
  if r = 0 then L else (q : Real) * (1 / ((min r (q - r) : Nat) : Real))

theorem lpfMinorResidueAllowance_nonneg (q r : Nat) (L : Real) (hL : 0 <= L) :
    0 <= lpfMinorResidueAllowance q L r := by
  unfold lpfMinorResidueAllowance
  split_ifs
  . exact hL
  . positivity

theorem lpfMinorResidueAllowance_period (q : Nat) (hq : 0 < q) (L : Real) :
    Finset.sum (Finset.range q) (lpfMinorResidueAllowance q L) =
      L + (q : Real) * Finset.sum (Finset.Ioc 0 (q - 1))
        (fun r => 1 / ((min r (q - r) : Nat) : Real)) := by
  classical
  have hZero : (Finset.range q).filter (fun r => r = 0) = {0} := by
    apply Finset.ext
    intro r
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    omega
  have hNonzero : (Finset.range q).filter (fun r => Not (r = 0)) = Finset.Ioc 0 (q - 1) := by
    apply Finset.ext
    intro r
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    omega
  unfold lpfMinorResidueAllowance
  rw [Finset.sum_ite, hZero, hNonzero, Finset.sum_singleton, <- Finset.mul_sum]

theorem lpfMinorResidueAllowance_period_bound (q : Nat) (hq : 0 < q) (L : Real) :
    Finset.sum (Finset.range q) (lpfMinorResidueAllowance q L) <=
      L + 2 * (q : Real) * (1 + Real.log (q : Real)) := by
  rw [lpfMinorResidueAllowance_period q hq]
  have h := mul_le_mul_of_nonneg_left (lpf_residue_reciprocal_sum_bound q hq)
    (Nat.cast_nonneg q : (0 : Real) <= (q : Real))
  convert add_le_add_left h L using 1 <;> ring

theorem lpfMinorResidueAllowance_prefix_bound (q D : Nat) (hq : 0 < q) (L : Real) (hL : 0 <= L) :
    Finset.sum (Finset.range (D + 1)) (fun d => lpfMinorResidueAllowance q L (d % q)) <=
      ((D / q + 1 : Nat) : Real) * (L + 2 * (q : Real) * (1 + Real.log (q : Real))) := by
  exact (lpf_weighted_residue_prefix_bound q D hq (lpfMinorResidueAllowance q L)
    (fun r hr => lpfMinorResidueAllowance_nonneg q r L hL)).trans
      (mul_le_mul_of_nonneg_left (lpfMinorResidueAllowance_period_bound q hq L) (by positivity))

theorem lpf_perturbed_residue_Ioc_allowance {q : Nat} [NeZero q] (j A B : Nat)
    (hj : j < q) (beta : Real) (hBeta : abs beta <= 1 / (4 * (q : Real))) :
    norm (Finset.sum (Finset.Ioc A B) (fun m =>
      (ZMod.stdAddChar (N := q) (j : ZMod q) *
        Complex.exp (Complex.I * ((2 * Real.pi * beta : Real) : Complex))) ^ m)) <=
          lpfMinorResidueAllowance q ((B - A : Nat) : Real) j := by
  by_cases hj0 : j = 0
  . rw [lpfMinorResidueAllowance, ite_eq_left hj0]
    apply norm_lpf_unit_Ioc_power_sum_le_length
    rw [norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, one_mul, Complex.norm_exp]
    simp
  . rw [lpfMinorResidueAllowance, ite_eq_right hj0]
    have h := lpf_perturbed_residue_Ioc_bound j A B (Nat.pos_of_ne_zero hj0) hj beta hBeta
    have hDiv : (q : Real) / ((min j (q - j) : Nat) : Real) =
        (q : Real) * (1 / ((min j (q - j) : Nat) : Real)) := by ring
    exact h.trans (by rw [<- hDiv]; exact min_le_right _ _)

theorem lpf_natural_residue_sum {q : Nat} [NeZero q] (F : ZMod q -> Real) :
    Finset.sum (Finset.range q) (fun j => F (j : ZMod q)) = Finset.sum Finset.univ F := by
  apply Finset.sum_bij (fun (j : Nat) _ => (j : ZMod q))
  . intro j hj
    exact Finset.mem_univ _
  . intro j hj k hk hEq
    have h := congrArg (fun x : ZMod q => x.val) hEq
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hj),
      Nat.mod_eq_of_lt (Finset.mem_range.mp hk)] using h
  . intro r hr
    refine Exists.intro r.val (Exists.intro (Finset.mem_range.mpr (ZMod.val_lt r)) ?_)
    exact ZMod.natCast_zmod_val r
  . intro j hj
    rfl

theorem lpf_unit_difference_residue_sum {q : Nat} [NeZero q]
    (a : Units (ZMod q)) (c : ZMod q) (F : ZMod q -> Real) :
    Finset.sum Finset.univ (fun r => F ((a : ZMod q) * (c - r))) = Finset.sum Finset.univ F := by
  apply Finset.sum_bij (fun r _ => (a : ZMod q) * (c - r))
  . intro r hr
    exact Finset.mem_univ _
  . intro r hr s hs hEq
    have h := congrArg (fun x : ZMod q => ((Inv.inv a : Units (ZMod q)) : ZMod q) * x) hEq
    have hCancel : c - r = c - s := by simpa [<- mul_assoc] using h
    have hNeg := congrArg (fun x : ZMod q => c - x) hCancel
    simpa only [sub_sub_cancel] using hNeg
  . intro s hs
    refine Exists.intro (c - ((Inv.inv a : Units (ZMod q)) : ZMod q) * s)
      (Exists.intro (Finset.mem_univ _) ?_)
    simp [<- mul_assoc]
  . intro r hr
    rfl

theorem lpf_unit_difference_range_sum_bound {q : Nat} [NeZero q]
    (a : Units (ZMod q)) (c : ZMod q) (L : Nat) (F : ZMod q -> Real)
    (hF : forall r, 0 <= F r) :
    Finset.sum (Finset.range L) (fun i => F ((a : ZMod q) * (c - (i : ZMod q)))) <=
      ((L / q + 1 : Nat) : Real) * Finset.sum Finset.univ F := by
  have hResidue (i : Nat) : ((i % q : Nat) : ZMod q) = (i : ZMod q) := by
    have h := ZMod.natCast_zmod_val (i : ZMod q)
    simpa only [ZMod.val_natCast] using h
  have hPeriod : Finset.sum (Finset.range q) (fun r => F ((a : ZMod q) * (c - (r : ZMod q)))) =
      Finset.sum Finset.univ F := by
    calc
      _ = Finset.sum Finset.univ (fun r : ZMod q => F ((a : ZMod q) * (c - r))) :=
        lpf_natural_residue_sum (fun r : ZMod q => F ((a : ZMod q) * (c - r)))
      _ = _ := lpf_unit_difference_residue_sum a c F
  have hPrefix := lpf_weighted_residue_prefix_bound q L (Nat.pos_of_ne_zero (NeZero.ne q))
    (fun r => F ((a : ZMod q) * (c - (r : ZMod q)))) (fun r hr => hF _)
  simp_rw [hResidue] at hPrefix
  rw [hPeriod] at hPrefix
  have hSubset : Finset.range L <= Finset.range (L + 1) := Finset.range_mono (by omega)
  exact (Finset.sum_le_sum_of_subset_of_nonneg hSubset (fun i _ _ => hF _)).trans hPrefix

theorem lpf_unit_difference_interval_sum_bound {q : Nat} [NeZero q]
    (a : Units (ZMod q)) (c : ZMod q) (C D : Nat) (F : ZMod q -> Real)
    (hF : forall r, 0 <= F r) :
    Finset.sum (Finset.Ioc C D) (fun n => F ((a : ZMod q) * (c - (n : ZMod q)))) <=
      (((D - C) / q + 1 : Nat) : Real) * Finset.sum Finset.univ F := by
  have hMap : Finset.sum (Finset.range (D - C))
      (fun i => F ((a : ZMod q) * ((c - ((C + 1 : Nat) : ZMod q)) - (i : ZMod q)))) =
        Finset.sum (Finset.Ioc C D) (fun n => F ((a : ZMod q) * (c - (n : ZMod q)))) := by
    apply Finset.sum_bij (fun i _ => C + 1 + i)
    . intro i hi
      apply Finset.mem_Ioc.mpr
      have h := Finset.mem_range.mp hi
      omega
    . intro i hi j hj hEq
      exact Nat.add_left_cancel hEq
    . intro n hn
      have h := Finset.mem_Ioc.mp hn
      refine Exists.intro (n - C - 1) (Exists.intro ?_ ?_)
      . apply Finset.mem_range.mpr
        omega
      . omega
    . intro i hi
      congr 1
      push_cast
      ring
  rw [<- hMap]
  exact lpf_unit_difference_range_sum_bound a (c - ((C + 1 : Nat) : ZMod q)) (D - C) F hF

theorem lpf_unit_difference_pair_sum_bound {q : Nat} [NeZero q]
    (a : Units (ZMod q)) (C D : Nat) (F : ZMod q -> Real)
    (hF : forall r, 0 <= F r) :
    Finset.sum (Finset.Ioc C D) (fun n1 => Finset.sum (Finset.Ioc C D) (fun n2 =>
      F ((a : ZMod q) * ((n1 : ZMod q) - (n2 : ZMod q))))) <=
        ((D - C : Nat) : Real) * (((D - C) / q + 1 : Nat) : Real) * Finset.sum Finset.univ F := by
  calc
    _ <= Finset.sum (Finset.Ioc C D) (fun _ =>
        (((D - C) / q + 1 : Nat) : Real) * Finset.sum Finset.univ F) := by
      apply Finset.sum_le_sum
      intro n1 hn1
      exact lpf_unit_difference_interval_sum_bound a (n1 : ZMod q) C D F hF
    _ = _ := by simp only [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]; ring

theorem lpf_unit_difference_allowance_pair_bound {q : Nat} [NeZero q]
    (a : Units (ZMod q)) (C D : Nat) (L : Real) (hL : 0 <= L) :
    Finset.sum (Finset.Ioc C D) (fun n1 => Finset.sum (Finset.Ioc C D) (fun n2 =>
      lpfMinorResidueAllowance q L (((a : ZMod q) * ((n1 : ZMod q) - (n2 : ZMod q))).val))) <=
        ((D - C : Nat) : Real) * (((D - C) / q + 1 : Nat) : Real) *
          (L + 2 * (q : Real) * (1 + Real.log (q : Real))) := by
  let F : ZMod q -> Real := fun r => lpfMinorResidueAllowance q L r.val
  have hF : forall r, 0 <= F r := fun r => lpfMinorResidueAllowance_nonneg q r.val L hL
  have hAll : Finset.sum Finset.univ F <= L + 2 * (q : Real) * (1 + Real.log (q : Real)) := by
    rw [<- lpf_natural_residue_sum F]
    calc
      _ = Finset.sum (Finset.range q) (lpfMinorResidueAllowance q L) := by
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [F]
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hj)]
      _ <= _ := lpfMinorResidueAllowance_period_bound q (Nat.pos_of_ne_zero (NeZero.ne q)) L
  exact (lpf_unit_difference_pair_sum_bound a C D F hF).trans
    (mul_le_mul_of_nonneg_left hAll (by positivity))

end PrimeFactorOscillations.LPF
