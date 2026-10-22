/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimePowerComponentFiber

/-!
# The complete geometric budget for component sampling

The uniform atom error is summed over an arbitrary finite set of supported
positive integers. All prime powers are retained, with the exact Euler
factor (1 + p^(-sigma)) / (1 - p^(-sigma)).
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

private theorem geometric_sum_le_reciprocal
    (q : Real) (hq0 : 0 <= q) (hq1 : q < 1) (M : Nat) :
    (Finset.range M).sum (fun k => q ^ k) <= 1 / (1 - q) := by
  have hd : 0 < 1 - q := sub_pos.mpr hq1
  have h := geom_sum_mul q M
  have hnonneg := pow_nonneg hq0 M
  have hrecip : (1 / (1 - q)) * (1 - q) = 1 := by
    field_simp [ne_of_gt hd]
  by_contra hnot
  have hstrict :
      0 < ((Finset.range M).sum (fun k => q ^ k) - 1 / (1 - q)) * (1 - q) :=
    mul_pos (sub_pos.mpr (lt_of_not_ge hnot)) hd
  nlinarith

private theorem nat_prod_power_rpow
    (s : Finset Nat) (e : Nat -> Nat) (r : Real) :
    ((s.prod (fun p => p ^ e p) : Nat) : Real) ^ r =
      s.prod (fun p => ((p : Real) ^ r) ^ e p) := by
  classical
  have hpow (p k : Nat) :
      (((p ^ k : Nat) : Real)) ^ r = ((p : Real) ^ r) ^ k := by
    rw [Nat.cast_pow]
    calc
      _ = ((p : Real) ^ (k : Real)) ^ r := by rw [Real.rpow_natCast]
      _ = (p : Real) ^ ((k : Real) * r) :=
        (Real.rpow_mul (Nat.cast_nonneg p) (k : Real) r).symm
      _ = (p : Real) ^ (r * (k : Real)) := by rw [mul_comm]
      _ = ((p : Real) ^ r) ^ (k : Real) :=
        Real.rpow_mul (Nat.cast_nonneg p) r (k : Real)
      _ = _ := Real.rpow_natCast _ k
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
      rw [Finset.prod_insert hp, Nat.cast_mul,
        Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _),
        hpow, ih, Finset.prod_insert hp]

theorem primePowerExponentBox_weight_sum_le
    (s : Finset Nat) (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p)
    (sigma : Real) (hs : 0 < sigma) (M : Nat) :
    (Finset.univ : Finset ((p : {p : Nat // Membership.mem s p}) -> Fin M)).sum
      (fun e => (Finset.univ : Finset {p : Nat // Membership.mem s p}).prod
        (fun p => ((p.val : Real) ^ (-sigma)) ^ (e p).val)) <=
      s.prod (fun p => 1 / (1 - (p : Real) ^ (-sigma))) := by
  classical
  have hsum (p : {p : Nat // Membership.mem s p}) :
      (Finset.univ : Finset (Fin M)).sum
        (fun k => ((p.val : Real) ^ (-sigma)) ^ k.val) <=
          1 / (1 - (p.val : Real) ^ (-sigma)) := by
    rw [Fin.sum_univ_eq_sum_range]
    apply geometric_sum_le_reciprocal
    case hq0 => exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    case hq1 =>
      apply Real.rpow_lt_one_of_one_lt_of_neg
      case hx => exact_mod_cast (hprime p.val p.property).one_lt
      case hz => linarith
  have hproduct (u : Finset {p : Nat // Membership.mem s p}) :
      u.prod (fun p => (Finset.univ : Finset (Fin M)).sum
        (fun k => ((p.val : Real) ^ (-sigma)) ^ k.val)) <=
      u.prod (fun p => 1 / (1 - (p.val : Real) ^ (-sigma))) := by
    induction u using Finset.induction_on with
    | empty => simp
    | @insert p u hp ih =>
        rw [Finset.prod_insert hp, Finset.prod_insert hp]
        apply mul_le_mul (hsum p) ih
        case c0 =>
          apply Finset.prod_nonneg
          intro q hq
          apply Finset.sum_nonneg
          intro k hk
          exact pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) _
        case b0 =>
          apply le_trans _ (hsum p)
          apply Finset.sum_nonneg
          intro k hk
          exact pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) _
  have h := hproduct Finset.univ
  rw [Fintype.prod_sum] at h
  change _ <= s.attach.prod (fun p => 1 / (1 - (p.val : Real) ^ (-sigma))) at h
  exact h.trans_eq (Finset.prod_attach s
    (fun p : Nat => 1 / (1 - (p : Real) ^ (-sigma))))

theorem supported_primePower_finite_sum_le_euler
    (s t : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p)
    (hpositive : forall a : Nat, Membership.mem t a -> 0 < a)
    (hsupport : forall a : Nat, Membership.mem t a ->
      forall p : Nat, Membership.mem a.factorization.support p -> Membership.mem s p)
    (sigma : Real) (hs : 0 < sigma) :
    t.sum (fun a => (a : Real) ^ (-sigma)) <=
      s.prod (fun p => 1 / (1 - (p : Real) ^ (-sigma))) := by
  classical
  let m : Nat := t.sup (fun a => s.sup (fun p => a.factorization p))
  let E := (p : {p : Nat // Membership.mem s p}) -> Fin (m + 1)
  let encode : Nat -> E := fun a p =>
    Fin.mk (min (a.factorization p.val) m)
      (Nat.lt_succ_of_le (Nat.min_le_right _ _))
  let decode : E -> Nat := fun e => s.attach.prod (fun p => p.val ^ (e p).val)
  let weight : E -> Real := fun e =>
    (Finset.univ : Finset {p : Nat // Membership.mem s p}).prod
      (fun p => ((p.val : Real) ^ (-sigma)) ^ (e p).val)
  have hencode (a : Nat) (ha : Membership.mem t a)
      (p : {p : Nat // Membership.mem s p}) :
      (encode a p).val = a.factorization p.val := by
    apply min_eq_left
    exact (Finset.le_sup (f := fun p => a.factorization p) p.property).trans
      (Finset.le_sup (f := fun a => s.sup (fun p => a.factorization p)) ha)
  have hreconstruct (a : Nat) (ha : Membership.mem t a) :
      s.prod (fun p => p ^ a.factorization p) = a := by
    rw [<- Finsupp.prod_of_support_subset a.factorization (hsupport a ha)
      (fun p k => p ^ k) (by intro p hp; exact pow_zero p)]
    exact Nat.prod_factorization_pow_eq_self (Nat.ne_of_gt (hpositive a ha))
  have hdecode (a : Nat) (ha : Membership.mem t a) : decode (encode a) = a := by
    change s.attach.prod (fun p => p.val ^ (encode a p).val) = a
    calc
      _ = s.attach.prod (fun p => p.val ^ a.factorization p.val) := by
        apply Finset.prod_congr rfl
        intro p hp
        rw [hencode a ha p]
      _ = s.prod (fun p => p ^ a.factorization p) :=
        Finset.prod_attach s (fun p : Nat => p ^ a.factorization p)
      _ = _ := hreconstruct a ha
  have hinj : Set.InjOn encode (t : Set Nat) := by
    intro a ha b hb heq
    calc
      a = decode (encode a) := (hdecode a ha).symm
      _ = decode (encode b) := congrArg decode heq
      _ = b := hdecode b hb
  have hweight (a : Nat) (ha : Membership.mem t a) :
      weight (encode a) = (a : Real) ^ (-sigma) := by
    change s.attach.prod
      (fun p => ((p.val : Real) ^ (-sigma)) ^ (encode a p).val) = _
    calc
      _ = s.attach.prod
          (fun p => ((p.val : Real) ^ (-sigma)) ^ a.factorization p.val) := by
        apply Finset.prod_congr rfl
        intro p hp
        rw [hencode a ha p]
      _ = s.prod (fun p => ((p : Real) ^ (-sigma)) ^ a.factorization p) :=
        Finset.prod_attach s
          (fun p : Nat => ((p : Real) ^ (-sigma)) ^ a.factorization p)
      _ = ((s.prod (fun p => p ^ a.factorization p) : Nat) : Real) ^ (-sigma) :=
        (nat_prod_power_rpow s (fun p => a.factorization p) (-sigma)).symm
      _ = _ := congrArg (fun n : Nat => (n : Real) ^ (-sigma)) (hreconstruct a ha)
  calc
    _ = t.sum (fun a => weight (encode a)) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact (hweight a ha).symm
    _ = (t.image encode).sum weight := (Finset.sum_image hinj).symm
    _ <= (Finset.univ : Finset E).sum weight := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro e he hnot
      apply Finset.prod_nonneg
      intro p hp
      exact pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) _
    _ <= _ := primePowerExponentBox_weight_sum_le s hprime sigma hs (m + 1)

theorem primePowerComponentFiber_finite_l1_error_le
    (s t : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p)
    (hpositive : forall a : Nat, Membership.mem t a -> 0 < a)
    (hsupport : forall a : Nat, Membership.mem t a ->
      forall p : Nat, Membership.mem a.factorization.support p -> Membership.mem s p)
    (N : Nat) (hN : 0 < N) (sigma : Real) (hs0 : 0 < sigma) (hs1 : sigma <= 1) :
    t.sum (fun a => abs
      (((primePowerComponentFiber s N a).card : Real) / (N : Real) -
        finitePrimeComponentSurvival s / (a : Real))) <=
      (N : Real) ^ (sigma - 1) *
        s.prod (fun p => (1 + (p : Real) ^ (-sigma)) /
          (1 - (p : Real) ^ (-sigma))) := by
  have hEuler :
      s.prod (fun p => (1 + (p : Real) ^ (-sigma)) /
          (1 - (p : Real) ^ (-sigma))) =
        s.prod (fun p => 1 + (p : Real) ^ (-sigma)) *
          s.prod (fun p => 1 / (1 - (p : Real) ^ (-sigma))) := by
    simp only [div_eq_mul_inv, one_mul, Finset.prod_mul_distrib]
  have hC : 0 <= (N : Real) ^ (sigma - 1) *
      s.prod (fun p => 1 + (p : Real) ^ (-sigma)) := by
    apply mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    apply Finset.prod_nonneg
    intro p hp
    exact add_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  calc
    _ <= t.sum (fun a => (N : Real) ^ (sigma - 1) * (a : Real) ^ (-sigma) *
        s.prod (fun p => 1 + (p : Real) ^ (-sigma))) := by
      apply Finset.sum_le_sum
      intro a ha
      exact abs_primePowerComponentFiber_probability_error_le s hprime N a hN
        (hpositive a ha) sigma hs0.le hs1
    _ = ((N : Real) ^ (sigma - 1) *
        s.prod (fun p => 1 + (p : Real) ^ (-sigma))) *
          t.sum (fun a => (a : Real) ^ (-sigma)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ <= ((N : Real) ^ (sigma - 1) *
        s.prod (fun p => 1 + (p : Real) ^ (-sigma))) *
          s.prod (fun p => 1 / (1 - (p : Real) ^ (-sigma))) :=
      mul_le_mul_of_nonneg_left
        (supported_primePower_finite_sum_le_euler s t hprime hpositive hsupport
          sigma hs0) hC
    _ = _ := by rw [hEuler]; ring

end PrimeFactorOscillations.PrimeClassSampling
