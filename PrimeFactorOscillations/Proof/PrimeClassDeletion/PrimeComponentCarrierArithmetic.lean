/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import PrimeFactorOscillations.Helpers.ArithmeticFunctionTwist
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimePowerComponentClassSeries

/-!
# The complete arithmetic prime carrier and its signed inverse

All prime powers and the full Mobius signs are retained. The algebraic
inverse uses the shared multiplicative twist theorem. The companion Euler
and norm modules identify its exact complete l1 norm.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

open PrimeFactorOscillations.DepletedMobius

theorem classPrimePowerSupported_iff_primeDivisors (P : Set Nat) (n : Nat) :
    classPrimePowerSupported P n <->
      And (Not (n = 0)) (forall p : Nat,
        Nat.Prime p -> Dvd.dvd p n -> Membership.mem P p) := by
  constructor
  case mp =>
    intro hn
    refine And.intro (Nat.ne_of_gt hn.1) ?_
    intro p hp hd
    apply hn.2 p
    rw [Nat.support_factorization]
    exact Nat.mem_primeFactors.mpr (And.intro hp (And.intro hd (Nat.ne_of_gt hn.1)))
  case mpr =>
    intro hn
    refine And.intro (Nat.pos_of_ne_zero hn.1) ?_
    intro p hp
    rw [Nat.support_factorization] at hp
    have hd := Nat.mem_primeFactors.mp hp
    exact hn.2 p hd.1 hd.2.1

theorem classPrimePowerSupported_mul (P : Set Nat) (m n : Nat) :
    classPrimePowerSupported P (m * n) <->
      And (classPrimePowerSupported P m) (classPrimePowerSupported P n) := by
  rw [classPrimePowerSupported_iff_primeDivisors P (m * n),
    classPrimePowerSupported_iff_primeDivisors P m,
    classPrimePowerSupported_iff_primeDivisors P n]
  constructor
  case mp =>
    intro h
    have hm : Not (m = 0) := by
      intro hz
      exact h.1 (by simp [hz])
    have hn : Not (n = 0) := by
      intro hz
      exact h.1 (by simp [hz])
    exact And.intro
      (And.intro hm (fun p hp hd => h.2 p hp (dvd_mul_of_dvd_left hd n)))
      (And.intro hn (fun p hp hd => h.2 p hp (dvd_mul_of_dvd_right hd m)))
  case mpr =>
    intro h
    refine And.intro (mul_ne_zero h.1.1 h.2.1) ?_
    intro p hp hd
    exact (hp.dvd_mul.mp hd).elim (h.1.2 p hp) (h.2.2 p hp)

theorem classPrimePowerWeight_zero (P : Set Nat) (sigma : Real) :
    classPrimePowerWeight P sigma 0 = 0 := by
  simp [classPrimePowerWeight, classPrimePowerSupported]

theorem classPrimePowerWeight_mul (P : Set Nat) (sigma : Real) (m n : Nat) :
    classPrimePowerWeight P sigma (m * n) =
      classPrimePowerWeight P sigma m * classPrimePowerWeight P sigma n := by
  classical
  by_cases hmn : classPrimePowerSupported P (m * n)
  case pos =>
    have h := (classPrimePowerSupported_mul P m n).mp hmn
    have hv (a : Nat) (ha : classPrimePowerSupported P a) :
        classPrimePowerWeight P sigma a = (a : Real) ^ (-sigma) := by
      simp only [classPrimePowerWeight, ite_eq_left ha]
    rw [hv (m * n) hmn, hv m h.1, hv n h.2, Nat.cast_mul]
    exact Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)
  case neg =>
    by_cases hm : classPrimePowerSupported P m
    case pos =>
      have hn : Not (classPrimePowerSupported P n) := by
        intro hn
        exact hmn ((classPrimePowerSupported_mul P m n).mpr (And.intro hm hn))
      simp only [classPrimePowerWeight, ite_eq_right hmn, ite_eq_left hm,
        ite_eq_right hn, mul_zero]
    case neg =>
      simp only [classPrimePowerWeight, ite_eq_right hmn, ite_eq_right hm, zero_mul]

noncomputable def classPrimePowerPartition (P : Set Nat) (sigma : Real) : Real :=
  tsum (classPrimePowerWeight P sigma)

noncomputable def classPrimeComponentWeightArithmetic
    (P : Set Nat) (sigma : Real) : ArithmeticFunction Real :=
  twist (classPrimePowerWeight P sigma) (ArithmeticFunction.zeta : ArithmeticFunction Int)

noncomputable def classPrimeComponentMobiusArithmetic
    (P : Set Nat) (sigma : Real) : ArithmeticFunction Real :=
  twist (classPrimePowerWeight P sigma) ArithmeticFunction.moebius

theorem classPrimeComponentWeightArithmetic_apply (P : Set Nat) (sigma : Real) (n : Nat) :
    classPrimeComponentWeightArithmetic P sigma n = classPrimePowerWeight P sigma n := by
  by_cases hn : n = 0
  case pos =>
    subst n
    simp [classPrimeComponentWeightArithmetic, twist, classPrimePowerWeight_zero]
  case neg =>
    simp [classPrimeComponentWeightArithmetic, twist, hn]

theorem classPrimeComponentMobiusArithmetic_apply (P : Set Nat) (sigma : Real) (n : Nat) :
    classPrimeComponentMobiusArithmetic P sigma n =
      (ArithmeticFunction.moebius n : Real) * classPrimePowerWeight P sigma n := by
  rfl

theorem classPrimePowerWeight_twist_one (P : Set Nat) (sigma : Real) :
    twist (classPrimePowerWeight P sigma) (1 : ArithmeticFunction Int) = 1 := by
  ext n
  by_cases hn : n = 1
  case pos =>
    subst n
    simp [twist, classPrimePowerWeight_one]
  case neg =>
    simp [twist, ArithmeticFunction.one_apply, hn]

theorem classPrimeComponentMobius_mul_weight (P : Set Nat) (sigma : Real) :
    classPrimeComponentMobiusArithmetic P sigma *
      classPrimeComponentWeightArithmetic P sigma = 1 := by
  unfold classPrimeComponentMobiusArithmetic classPrimeComponentWeightArithmetic
  rw [<- twist_mul (classPrimePowerWeight P sigma) (classPrimePowerWeight_mul P sigma),
    ArithmeticFunction.moebius_mul_coe_zeta]
  exact classPrimePowerWeight_twist_one P sigma

noncomputable def classPrimeComponentNoiseArithmetic
    (P : Set Nat) (sigma : Real) : ArithmeticFunction Real :=
  SMul.smul (1 / classPrimePowerPartition P sigma) (classPrimeComponentWeightArithmetic P sigma)

noncomputable def classPrimeComponentInverseArithmetic
    (P : Set Nat) (sigma : Real) : ArithmeticFunction Real :=
  SMul.smul (classPrimePowerPartition P sigma) (classPrimeComponentMobiusArithmetic P sigma)

theorem classPrimeComponentNoiseArithmetic_apply (P : Set Nat) (sigma : Real) (n : Nat) :
    classPrimeComponentNoiseArithmetic P sigma n =
      classPrimePowerWeight P sigma n / classPrimePowerPartition P sigma := by
  change (1 / classPrimePowerPartition P sigma) *
    classPrimeComponentWeightArithmetic P sigma n = _
  rw [classPrimeComponentWeightArithmetic_apply]
  ring

theorem classPrimeComponentInverseArithmetic_apply (P : Set Nat) (sigma : Real) (n : Nat) :
    classPrimeComponentInverseArithmetic P sigma n =
      classPrimePowerPartition P sigma * (ArithmeticFunction.moebius n : Real) *
        classPrimePowerWeight P sigma n := by
  change classPrimePowerPartition P sigma * classPrimeComponentMobiusArithmetic P sigma n = _
  rw [classPrimeComponentMobiusArithmetic_apply]
  ring

theorem classPrimeComponentNoise_hasSum_one
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hsum : Summable (classPowerWeight P sigma)) :
    HasSum (classPrimeComponentNoiseArithmetic P sigma) 1 := by
  have hZ : Not (classPrimePowerPartition P sigma = 0) :=
    ne_of_gt (classPrimePowerWeight_tsum_pos P sigma hs hsum)
  have h := (classPrimePowerWeight_summable P sigma hs hsum).hasSum.div_const
    (classPrimePowerPartition P sigma)
  change HasSum (fun n => classPrimeComponentNoiseArithmetic P sigma n) 1
  simp_rw [classPrimeComponentNoiseArithmetic_apply]
  change HasSum _ (classPrimePowerPartition P sigma / classPrimePowerPartition P sigma) at h
  rw [div_self hZ] at h
  exact h

theorem classPrimeComponentInverse_mul_noise
    (P : Set Nat) (sigma : Real) (hs : 0 < sigma)
    (hsum : Summable (classPowerWeight P sigma)) :
    classPrimeComponentInverseArithmetic P sigma *
      classPrimeComponentNoiseArithmetic P sigma = 1 := by
  have hZ : Not (classPrimePowerPartition P sigma = 0) :=
    ne_of_gt (classPrimePowerWeight_tsum_pos P sigma hs hsum)
  have h := classPrimeComponentMobius_mul_weight P sigma
  ext n
  rw [ArithmeticFunction.mul_apply]
  calc
    _ = (classPrimeComponentMobiusArithmetic P sigma *
        classPrimeComponentWeightArithmetic P sigma) n := by
      rw [ArithmeticFunction.mul_apply]
      apply Finset.sum_congr rfl
      intro x hx
      rw [classPrimeComponentInverseArithmetic_apply, classPrimeComponentNoiseArithmetic_apply,
        classPrimeComponentMobiusArithmetic_apply, classPrimeComponentWeightArithmetic_apply]
      field_simp [hZ]
    _ = _ := congrArg (fun f : ArithmeticFunction Real => f n) h

theorem classPrimeComponentInverse_zero_of_not_squarefree
    (P : Set Nat) (sigma : Real) (n : Nat) (hn : Not (Squarefree n)) :
    classPrimeComponentInverseArithmetic P sigma n = 0 := by
  rw [classPrimeComponentInverseArithmetic_apply,
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn, Int.cast_zero, mul_zero, zero_mul]

end PrimeFactorOscillations.PrimeClassSampling
