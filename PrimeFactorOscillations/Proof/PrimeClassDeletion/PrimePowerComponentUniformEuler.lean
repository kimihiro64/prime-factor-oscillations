/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeClassSamplingUniform
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimePowerComponentFiniteLaw

/-!
# A complete Euler budget uniform over finite prime sets

The geometric denominator is retained. A summable prime power weight gives
one constant for every finite subset, including the literal full-component
sampling error.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

private theorem ratio_le_exponential
    (a r : Real) (ha : 0 <= a) (har : a <= r) (hr : r < 1) :
    (1 + a) / (1 - a) <= Real.exp ((2 / (1 - r)) * a) := by
  have hd : 0 < 1 - a := sub_pos.mpr (har.trans_lt hr)
  have hdr : 0 < 1 - r := sub_pos.mpr hr
  have hfrac : 2 * a / (1 - a) <= 2 * a / (1 - r) :=
    div_le_div_of_nonneg_left (mul_nonneg (by norm_num) ha) hdr
      (sub_le_sub_left har 1)
  calc
    _ = 1 + 2 * a / (1 - a) := by
      field_simp [ne_of_gt hd]
      ring
    _ <= 1 + 2 * a / (1 - r) := by linarith
    _ = 1 + (2 / (1 - r)) * a := by ring
    _ <= _ := by
      simpa only [add_comm] using Real.add_one_le_exp ((2 / (1 - r)) * a)

theorem primePowerEulerBudget_le_exp
    (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p)
    (sigma : Real) (hs : 0 < sigma) :
    s.prod (fun p => (1 + (p : Real) ^ (-sigma)) /
        (1 - (p : Real) ^ (-sigma))) <=
      Real.exp ((2 / (1 - (2 : Real) ^ (-sigma))) *
        s.sum (fun p => (p : Real) ^ (-sigma))) := by
  have hr : (2 : Real) ^ (-sigma) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hs)
  have hlocal (p : Nat) (hp : Nat.Prime p) :
      (1 + (p : Real) ^ (-sigma)) / (1 - (p : Real) ^ (-sigma)) <=
        Real.exp ((2 / (1 - (2 : Real) ^ (-sigma))) * (p : Real) ^ (-sigma)) := by
    apply ratio_le_exponential _ _ (Real.rpow_nonneg (Nat.cast_nonneg p) _) _ hr
    exact Real.rpow_le_rpow_of_nonpos (by norm_num)
      (by exact_mod_cast hp.two_le) (neg_nonpos.mpr hs.le)
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
      have hps : forall q : Nat, Membership.mem s q -> Nat.Prime q :=
        fun q hq => hprime q (Finset.mem_insert_of_mem hq)
      rw [Finset.prod_insert hp, Finset.sum_insert hp, mul_add, Real.exp_add]
      apply mul_le_mul (hlocal p (hprime p (Finset.mem_insert_self p s))) (ih hps)
      case c0 =>
        apply Finset.prod_nonneg
        intro q hq
        have hq1 : (q : Real) ^ (-sigma) < 1 :=
          Real.rpow_lt_one_of_one_lt_of_neg
            (by exact_mod_cast (hps q hq).one_lt) (neg_neg_of_pos hs)
        exact div_nonneg
          (add_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg q) _))
          (sub_pos.mpr hq1).le
      case b0 => exact (Real.exp_pos _).le

theorem primePowerEulerBudget_uniform
    (P : Set Nat) (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p)
    (hP : forall p : Nat, Membership.mem s p -> Membership.mem P p)
    (sigma : Real) (hs : 0 < sigma)
    (hsum : Summable (classPowerWeight P sigma)) :
    s.prod (fun p => (1 + (p : Real) ^ (-sigma)) /
        (1 - (p : Real) ^ (-sigma))) <=
      Real.exp ((2 / (1 - (2 : Real) ^ (-sigma))) *
        tsum (classPowerWeight P sigma)) := by
  classical
  have hsumle : s.sum (fun p => (p : Real) ^ (-sigma)) <=
      tsum (classPowerWeight P sigma) := by
    calc
      _ = s.sum (classPowerWeight P sigma) := by
        apply Finset.sum_congr rfl
        intro p hp
        unfold classPowerWeight
        exact (ite_eq_left (And.intro (hprime p hp) (hP p hp))).symm
      _ <= _ := Summable.sum_le_tsum s
        (fun p hp => classPowerWeight_nonneg P sigma p) hsum
  apply (primePowerEulerBudget_le_exp s hprime sigma hs).trans
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left hsumle
    (div_nonneg (by norm_num)
      (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg
        (by norm_num) (neg_neg_of_pos hs))).le)

theorem finitePrimePowerComponent_l1_error_uniform
    (P : Set Nat) (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p)
    (hP : forall p : Nat, Membership.mem s p -> Membership.mem P p)
    (N : Nat) (hN : 0 < N) (sigma : Real)
    (hs : 0 < sigma) (hs1 : sigma <= 1)
    (hsum : Summable (classPowerWeight P sigma)) :
    tsum (fun a => abs (literalPrimePowerComponentProbability s N a -
      finitePrimePowerReference s a)) <=
      (N : Real) ^ (sigma - 1) *
        Real.exp ((2 / (1 - (2 : Real) ^ (-sigma))) *
          tsum (classPowerWeight P sigma)) := by
  apply (literalPrimePowerComponentProbability_full_l1_error
    s hprime N hN sigma hs hs1).2.trans
  exact mul_le_mul_of_nonneg_left
    (primePowerEulerBudget_uniform P s hprime hP sigma hs hsum)
    (Real.rpow_nonneg (Nat.cast_nonneg N) _)

private theorem geometric_product_le_complete
    (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p)
    (sigma : Real) (hs : 0 < sigma) :
    s.prod (fun p => 1 / (1 - (p : Real) ^ (-sigma))) <=
      s.prod (fun p => (1 + (p : Real) ^ (-sigma)) /
        (1 - (p : Real) ^ (-sigma))) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
      have hps : forall q : Nat, Membership.mem s q -> Nat.Prime q :=
        fun q hq => hprime q (Finset.mem_insert_of_mem hq)
      have hden (q : Nat) (hq : Nat.Prime q) :
          0 < 1 - (q : Real) ^ (-sigma) :=
        sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg
          (by exact_mod_cast hq.one_lt) (neg_neg_of_pos hs))
      have hfactor :
          1 / (1 - (p : Real) ^ (-sigma)) <=
            (1 + (p : Real) ^ (-sigma)) / (1 - (p : Real) ^ (-sigma)) := by
        apply div_le_div_of_nonneg_right _ (hden p (hprime p (Finset.mem_insert_self p s))).le
        exact le_add_of_nonneg_right (Real.rpow_nonneg (Nat.cast_nonneg p) _)
      rw [Finset.prod_insert hp, Finset.prod_insert hp]
      apply mul_le_mul hfactor (ih hps)
      case c0 =>
        apply Finset.prod_nonneg
        intro q hq
        exact div_nonneg zero_le_one (hden q (hps q hq)).le
      case b0 =>
        exact div_nonneg
          (add_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg p) _))
          (hden p (hprime p (Finset.mem_insert_self p s))).le

theorem primePowerGeometricBudget_uniform
    (P : Set Nat) (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p)
    (hP : forall p : Nat, Membership.mem s p -> Membership.mem P p)
    (sigma : Real) (hs : 0 < sigma)
    (hsum : Summable (classPowerWeight P sigma)) :
    s.prod (fun p => 1 / (1 - (p : Real) ^ (-sigma))) <=
      Real.exp ((2 / (1 - (2 : Real) ^ (-sigma))) *
        tsum (classPowerWeight P sigma)) :=
  (geometric_product_le_complete s hprime sigma hs).trans
    (primePowerEulerBudget_uniform P s hprime hP sigma hs hsum)

end PrimeFactorOscillations.PrimeClassSampling
