/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import PrimeFactorOscillations.Helpers.UniformCarrierCoefficients

/-!
# UniformCarrierPairedProbe

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

/-!
# Uniform error for paired probability probes

This private proof checks the observation error in the uncentered
inverse/plain covariance. It does not estimate that arithmetic covariance.
The normalization is the product of two square-root-normalized sums,
written with one division to avoid a square-root boundary.
-/


noncomputable section
namespace PrimeFactorOscillations.UniformCarrier.PairedProbe

def value (S : Finset Nat) (N : Real) (a b : Nat -> Complex) : Complex :=
  (S.sum a) * (S.sum b) / (N : Complex)

theorem product_error (a b f g : Complex) (delta T : Real)
    (hdelta : 0 <= delta) (hT : 0 <= T)
    (ha : norm (a - f) <= delta) (hb : norm (b - g) <= delta)
    (hf : norm f <= T) (hg : norm g <= T) :
    norm (a * b - f * g) <= 2 * T * delta + delta ^ 2 := by
  calc
    norm (a * b - f * g) =
        norm (((a - f) * (b - g) + (a - f) * g) + f * (b - g)) := by
      congr 1
      ring
    _ <= norm ((a - f) * (b - g) + (a - f) * g) +
        norm (f * (b - g)) := norm_add_le _ _
    _ <= (norm ((a - f) * (b - g)) + norm ((a - f) * g)) +
        norm (f * (b - g)) :=
      _root_.add_le_add (norm_add_le _ _) le_rfl
    _ = norm (a - f) * norm (b - g) + norm (a - f) * norm g +
        norm f * norm (b - g) := by
      rw [norm_mul, norm_mul, norm_mul]
    _ <= delta * delta + delta * T + T * delta := by
      gcongr
    _ = 2 * T * delta + delta ^ 2 := by ring

theorem normalized_product_error (a b f g : Complex) (C N E : Real)
    (hC : 0 <= C) (hN : 1 <= N) (hE : 1 <= E)
    (ha : norm (a - f) <= C / E) (hb : norm (b - g) <= C / E)
    (hf : norm f <= N) (hg : norm g <= N) :
    norm ((a * b - f * g) / (N : Complex)) <= (2 * C + C ^ 2) / E := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hEpos : 0 < E := lt_of_lt_of_le zero_lt_one hE
  have hdelta : 0 <= C / E := div_nonneg hC hEpos.le
  have hsmall : C / E <= C := div_le_self hC hE
  have hsquare : (C / E) ^ 2 <= N * C * (C / E) := by
    calc
      (C / E) ^ 2 = (C / E) * (C / E) := by ring
      _ <= C * (C / E) := mul_le_mul_of_nonneg_right hsmall hdelta
      _ = 1 * (C * (C / E)) := by ring
      _ <= N * (C * (C / E)) :=
        mul_le_mul_of_nonneg_right hN (mul_nonneg hC hdelta)
      _ = N * C * (C / E) := by ring
  have hprod := product_error a b f g (C / E) N hdelta hNpos.le ha hb hf hg
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hNpos]
  calc
    norm (a * b - f * g) / N <=
        (2 * N * (C / E) + (C / E) ^ 2) / N :=
      div_le_div_of_nonneg_right hprod hNpos.le
    _ <= (2 * N * (C / E) + N * C * (C / E)) / N :=
      div_le_div_of_nonneg_right (_root_.add_le_add le_rfl hsquare) hNpos.le
    _ = (2 * C + C ^ 2) / E := by
      field_simp [hNpos.ne', hEpos.ne']

theorem sum_error (S : Finset Nat) (a f : Nat -> Complex) (C N E : Real)
    (hC : 0 <= C) (hN : 1 <= N) (hE : 1 <= E)
    (hcard : (S.card : Real) <= N)
    (herror : forall n : Nat, Membership.mem S n -> norm (a n - f n) <= C / (N * E)) :
    norm (S.sum a - S.sum f) <= C / E := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hEpos : 0 < E := lt_of_lt_of_le zero_lt_one hE
  calc
    norm (S.sum a - S.sum f) = norm (S.sum (fun n => a n - f n)) := by
      rw [Finset.sum_sub_distrib]
    _ <= S.sum (fun n => norm (a n - f n)) := norm_sum_le _ _
    _ <= S.sum (fun _ => C / (N * E)) := Finset.sum_le_sum herror
    _ = (S.card : Real) * (C / (N * E)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ <= N * (C / (N * E)) :=
      mul_le_mul_of_nonneg_right hcard (div_nonneg hC (mul_nonneg hNpos.le hEpos.le))
    _ = C / E := by
      field_simp [hNpos.ne', hEpos.ne']

theorem sum_bound (S : Finset Nat) (f : Nat -> Complex) (N : Real)
    (hcard : (S.card : Real) <= N)
    (hf : forall n : Nat, Membership.mem S n -> norm (f n) <= 1) :
    norm (S.sum f) <= N := by
  calc
    norm (S.sum f) <= S.sum (fun n => norm (f n)) := norm_sum_le _ _
    _ <= S.sum (fun _ => (1 : Real)) := Finset.sum_le_sum hf
    _ = (S.card : Real) := by simp
    _ <= N := hcard

theorem finite_pair_error (S : Finset Nat) (a b f g : Nat -> Complex)
    (C N E : Real) (hC : 0 <= C) (hN : 1 <= N) (hE : 1 <= E)
    (hcard : (S.card : Real) <= N)
    (hf : forall n : Nat, Membership.mem S n -> norm (f n) <= 1)
    (hg : forall n : Nat, Membership.mem S n -> norm (g n) <= 1)
    (ha : forall n : Nat, Membership.mem S n -> norm (a n - f n) <= C / (N * E))
    (hb : forall n : Nat, Membership.mem S n -> norm (b n - g n) <= C / (N * E)) :
    norm (value S N a b - value S N f g) <= (2 * C + C ^ 2) / E := by
  unfold value
  rw [<- sub_div]
  exact normalized_product_error (S.sum a) (S.sum b) (S.sum f) (S.sum g) C N E
    hC hN hE (sum_error S a f C N E hC hN hE hcard ha)
    (sum_error S b g C N E hC hN hE hcard hb)
    (sum_bound S f N hcard hf) (sum_bound S g N hcard hg)

theorem power_pair_error (d N : Nat) (hd : 2 <= d) (hN : 1 <= N)
    (S : Finset Nat) (hcard : S.card <= N)
    (hrange : forall n : Nat, Membership.mem S n -> N <= n)
    (a b f g : Nat -> Complex) (C : Real) (hC : 0 <= C)
    (hf : forall n : Nat, Membership.mem S n -> norm (f n) <= 1)
    (hg : forall n : Nat, Membership.mem S n -> norm (g n) <= 1)
    (ha : forall n : Nat, Membership.mem S n ->
      norm (a n - f n) <= C / (n : Real) ^ (d - 1))
    (hb : forall n : Nat, Membership.mem S n ->
      norm (b n - g n) <= C / (n : Real) ^ (d - 1)) :
    norm (value S N a b - value S N f g) <=
      (2 * C + C ^ 2) / (N : Real) ^ (d - 2) := by
  have hNR : (1 : Real) <= N := by exact_mod_cast hN
  have hNpos : (0 : Real) < N := lt_of_lt_of_le zero_lt_one hNR
  have hE : (1 : Real) <= (N : Real) ^ (d - 2) := by
    calc
      1 = (1 : Real) ^ (d - 2) := by simp
      _ <= (N : Real) ^ (d - 2) := by gcongr
  have hpow : (N : Real) ^ (d - 1) =
      (N : Real) * (N : Real) ^ (d - 2) := by
    have hexp : d - 1 = (d - 2) + 1 := by omega
    rw [hexp, pow_succ]
    ring
  apply finite_pair_error S a b f g C N ((N : Real) ^ (d - 2)) hC hNR hE
    (by exact_mod_cast hcard) hf hg
  all_goals
    intro n hn
    have hNN : (N : Real) <= n := by exact_mod_cast hrange n hn
    have hden : (N : Real) ^ (d - 1) <= (n : Real) ^ (d - 1) := by gcongr
    have hquot : C / (n : Real) ^ (d - 1) <=
        C / ((N : Real) * (N : Real) ^ (d - 2)) := by
      rw [<- hpow]
      exact div_le_div_of_nonneg_left hC (pow_pos hNpos _) hden
    first
    | exact (ha n hn).trans hquot
    | exact (hb n hn).trans hquot

theorem exists_probability_pairs :
    exists n0 : Nat, exists C : Real, 100 <= n0 /\ 0 < C /\
      forall d : Nat, 2 <= d ->
      forall f g : Nat -> Complex,
      forall hf : (forall n : Nat, norm (f n) <= (n : Real)),
      forall hg : (forall n : Nat, norm (g n) <= (n : Real)),
      (forall n : Nat, norm (f n) <= 1) ->
      (forall n : Nat, norm (g n) <= 1) ->
      exists a b : Nat -> Complex,
        (forall n : Nat, Not (n = 0) ->
          norm (a n - f n) <= C / (n : Real) ^ (d - 1)) /\
        (forall n : Nat, Not (n = 0) ->
          norm (b n - g n) <= C / (n : Real) ^ (d - 1)) /\
        (forall n : Nat, n0 <= n ->
          exists O : CoefficientObservation d n (f n) (hf n), a n = O.value) /\
        (forall n : Nat, n0 <= n ->
          exists O : CoefficientObservation d n (g n) (hg n), b n = O.value) /\
        (forall n : Nat, n < n0 -> a n = f n /\ b n = g n) /\
        (forall (N : Nat) (S : Finset Nat), 1 <= N -> S.card <= N ->
          (forall n : Nat, Membership.mem S n -> N <= n) ->
          norm (value S N a b - value S N f g) <=
            (2 * C + C ^ 2) / (N : Real) ^ (d - 2)) := by
  choose n0 C hn0 hC hData using
    _root_.PrimeFactorOscillations.UniformCarrier.exists_probability_coefficients
  refine Exists.intro n0 (Exists.intro C (And.intro hn0 (And.intro hC ?_)))
  intro d hd f g hf hg hfUnit hgUnit
  choose a ha hObsA hSmallA using hData d hd f hf
  choose b hb hObsB hSmallB using hData d hd g hg
  refine Exists.intro a (Exists.intro b
    (And.intro ha (And.intro hb (And.intro hObsA (And.intro hObsB ?_)))))
  refine And.intro ?_ ?_
  . intro n hn
    exact And.intro (hSmallA n hn) (hSmallB n hn)
  . intro N S hN hcard hrange
    apply power_pair_error d N hd hN S hcard hrange a b f g C hC.le
    . intro n hn
      exact hfUnit n
    . intro n hn
      exact hgUnit n
    . intro n hn
      have hnPos : 1 <= n := hN.trans (hrange n hn)
      exact ha n (by omega)
    . intro n hn
      have hnPos : 1 <= n := hN.trans (hrange n hn)
      exact hb n (by omega)

namespace DirichletPair

def inverseCoefficient {q : Nat} (xi : DirichletCharacter Complex q) (n : Nat) : Complex :=
  ((ArithmeticFunction.moebius n : Int) : Complex) * xi n

def plainCoefficient {r k : Nat} (chi : DirichletCharacter Complex r)
    (eta : DirichletCharacter Complex k) (n : Nat) : Complex :=
  if n = 0 then 0 else chi n * eta n

theorem inverse_norm_le_one {q : Nat} (xi : DirichletCharacter Complex q) (n : Nat) :
    norm (inverseCoefficient xi n) <= 1 := by
  rcases ArithmeticFunction.moebius_eq_or n with hzero | hone | hneg
  . simp [inverseCoefficient, hzero]
  . simpa [inverseCoefficient, hone] using xi.norm_le_one (n : ZMod q)
  . simpa [inverseCoefficient, hneg] using xi.norm_le_one (n : ZMod q)

theorem plain_norm_le_one {r k : Nat} (chi : DirichletCharacter Complex r)
    (eta : DirichletCharacter Complex k) (n : Nat) :
    norm (plainCoefficient chi eta n) <= 1 := by
  by_cases hn : n = 0
  . simp [plainCoefficient, hn]
  . rw [plainCoefficient, ite_eq_right hn, norm_mul]
    calc
      norm (chi n) * norm (eta n) <= (1 : Real) * 1 :=
        _root_.mul_le_mul (chi.norm_le_one _) (eta.norm_le_one _) (norm_nonneg _) zero_le_one
      _ = 1 := by ring

theorem inverse_nat_bound {q : Nat} (xi : DirichletCharacter Complex q) (n : Nat) :
    norm (inverseCoefficient xi n) <= (n : Real) := by
  by_cases hn : n = 0
  . subst n
    simp [inverseCoefficient]
  . have hOne : (1 : Real) <= n := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    exact (inverse_norm_le_one xi n).trans hOne

theorem plain_nat_bound {r k : Nat} (chi : DirichletCharacter Complex r)
    (eta : DirichletCharacter Complex k) (n : Nat) :
    norm (plainCoefficient chi eta n) <= (n : Real) := by
  by_cases hn : n = 0
  . subst n
    simp [plainCoefficient]
  . have hOne : (1 : Real) <= n := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    exact (plain_norm_le_one chi eta n).trans hOne

structure Data (n0 d : Nat) (C : Real) {q r k : Nat}
    (xi : DirichletCharacter Complex q) (chi : DirichletCharacter Complex r)
    (eta : DirichletCharacter Complex k) where
  inverseData : Nat -> Complex
  plainData : Nat -> Complex
  inverse_error : forall n : Nat, Not (n = 0) ->
    norm (inverseData n - inverseCoefficient xi n) <= C / (n : Real) ^ (d - 1)
  plain_error : forall n : Nat, Not (n = 0) ->
    norm (plainData n - plainCoefficient chi eta n) <= C / (n : Real) ^ (d - 1)
  inverse_observed : forall n : Nat, n0 <= n ->
    exists O : CoefficientObservation d n (inverseCoefficient xi n) (inverse_nat_bound xi n),
      inverseData n = O.value
  plain_observed : forall n : Nat, n0 <= n ->
    exists O : CoefficientObservation d n (plainCoefficient chi eta n)
      (plain_nat_bound chi eta n), plainData n = O.value
  small_exact : forall n : Nat, n < n0 ->
    inverseData n = inverseCoefficient xi n /\ plainData n = plainCoefficient chi eta n
  paired_error : forall (N : Nat) (S : Finset Nat), 1 <= N -> S.card <= N ->
    (forall n : Nat, Membership.mem S n -> N <= n) ->
    norm (value S N inverseData plainData -
      value S N (inverseCoefficient xi) (plainCoefficient chi eta)) <=
      (2 * C + C ^ 2) / (N : Real) ^ (d - 2)

theorem exists_uniform_dirichlet_pairs :
    exists n0 : Nat, exists C : Real, 100 <= n0 /\ 0 < C /\
      forall d : Nat, 2 <= d ->
      forall q r k : Nat,
      forall xi : DirichletCharacter Complex q,
      forall chi : DirichletCharacter Complex r,
      forall eta : DirichletCharacter Complex k,
        Nonempty (Data n0 d C xi chi eta) := by
  choose n0 C hn0 hC hData using exists_probability_pairs
  refine Exists.intro n0 (Exists.intro C (And.intro hn0 (And.intro hC ?_)))
  intro d hd q r k xi chi eta
  choose a b ha hb hObsA hObsB hSmall hPair using
    hData d hd (inverseCoefficient xi) (plainCoefficient chi eta)
      (inverse_nat_bound xi) (plain_nat_bound chi eta)
      (inverse_norm_le_one xi) (plain_norm_le_one chi eta)
  exact Nonempty.intro
    { inverseData := a
      plainData := b
      inverse_error := ha
      plain_error := hb
      inverse_observed := hObsA
      plain_observed := hObsB
      small_exact := hSmall
      paired_error := hPair }

end DirichletPair

end PrimeFactorOscillations.UniformCarrier.PairedProbe
