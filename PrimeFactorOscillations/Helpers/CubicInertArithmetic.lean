/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.CubicRationalRows

/-!
# Arithmetic qualification of inert prime and twin-starter rows

Discharges maximality and lambda avoidance for rational primes congruent to
two modulo three, and transfers native conjugation to actual twin starters
other than the explicitly excluded starter three.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.CubicInertArithmetic

open OAI OAI.SevenEighths
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ShortDraftLatticeCount
local notation "Eis" => ActualEisensteinCubic.O

theorem lambda_qNat : qNat lambda = 3 := by
  rw [qNat_eq_absNorm_span]
  exact CubicEisenstein.absNorm_span_lambda

theorem prime_norm_avoids_lambda (p : Nat) (hp : Nat.Prime p) (hmod : p % 3 = 2)
    (a : Eis) (ha : qNat a = p) :
    Not (Membership.mem (Ideal.span {a}) lambda) := by
  intro h
  have hd := Ideal.mem_span_singleton.mp h
  let b : Eis := Classical.choose hd
  have hb : lambda = a * b := Classical.choose_spec hd
  have hnorm := congrArg qNat hb
  rw [lambda_qNat, qNat_mul, ha] at hnorm
  have hd3 : Dvd.dvd p 3 := Exists.intro (qNat b) hnorm
  have hp3 := Nat.le_of_dvd (by norm_num : 0 < (3 : Nat)) hd3
  have hp2 := hp.two_le
  have he : p = 2 := by omega
  rw [he] at hd3
  norm_num at hd3

theorem rational_prime_isMaximal (p : Nat) (hp : Nat.Prime p) (hmod : p % 3 = 2) :
    (Ideal.span {(p : Eis)}).IsMaximal := by
  have hcases := rational_prime_factor_cases p hp
  cases hcases with
  | inl h => exact h
  | inr h =>
    let a : Eis := Classical.choose h
    have hrest := Classical.choose_spec h
    let b : Eis := Classical.choose hrest
    have hdata := Classical.choose_spec hrest
    have hqa : qNat a = p := hdata.2.2.2.1
    letI : (Ideal.span {a}).IsMaximal := hdata.2.2.2.2.2.1
    have hgood := prime_norm_avoids_lambda p hp hmod a hqa
    have hdiv := card_sub_one_div_three (Ideal.span {a}) hgood
    have hcard : Nat.card (HasQuotient.Quotient Eis (Ideal.span {a})) = p := by
      simpa only [qNat_eq_absNorm_span, Ideal.absNorm_apply, Submodule.cardQuot_apply] using hqa
    rw [hcard] at hdiv
    have hm := Nat.mod_eq_zero_of_dvd hdiv
    have hp2 := hp.two_le
    omega

theorem rational_prime_avoids_lambda (p : Nat) (hp : Nat.Prime p) :
    Not (Membership.mem (Ideal.span {(p : Eis)}) lambda) := by
  intro h
  have hd := Ideal.mem_span_singleton.mp h
  let b : Eis := Classical.choose hd
  have hb : lambda = (p : Eis) * b := Classical.choose_spec hd
  have hnorm := congrArg qNat hb
  rw [lambda_qNat, qNat_mul, rational_qNat p hp.ne_zero] at hnorm
  have hd3 : Dvd.dvd (p ^ 2) 3 := Exists.intro (qNat b) hnorm
  have hle := Nat.le_of_dvd (by norm_num : 0 < (3 : Nat)) hd3
  have hp2 := hp.two_le
  nlinarith

theorem rational_cubicRow_conjugation (p : Nat) (hp : Nat.Prime p)
    (hmod : p % 3 = 2) (z : Eis) :
    CubicSieve.cubicRow (Ideal.span {(p : Eis)}) (conjO z) =
      star (CubicSieve.cubicRow (Ideal.span {(p : Eis)}) z) := by
  letI := rational_prime_isMaximal p hp hmod
  exact CubicRationalRows.rational_cubicRow_conjugation _ (rational_prime_avoids_lambda p hp)
    p rfl z

theorem rational_kernel_symmetric (p q : Nat) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpmod : p % 3 = 2) (hqmod : q % 3 = 2)
    (W : SchwartzMap Real Complex) (M : Real) :
    CubicPairReflection.pairedKernel (Ideal.span {(q : Eis)}) (Ideal.span {(p : Eis)}) W M =
      CubicPairReflection.pairedKernel (Ideal.span {(p : Eis)}) (Ideal.span {(q : Eis)}) W M :=
  CubicPairReflection.kernel_symmetric_of_conjugation _ _ W M
    (rational_cubicRow_conjugation p hp hpmod)
    (rational_cubicRow_conjugation q hq hqmod)

theorem twin_start_mod_three (p : Nat) (hp : Nat.Prime p)
    (hnext : Nat.Prime (p + 2)) (hp3 : Not (p = 3)) : p % 3 = 2 := by
  have hzero : Not (p % 3 = 0) := by
    intro h
    have hd := (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero h)
    cases hd with
    | inl h => norm_num at h
    | inr h => exact hp3 h.symm
  have hone : Not (p % 3 = 1) := by
    intro h
    have hm : (p + 2) % 3 = 0 := by omega
    have hd := (Nat.dvd_prime hnext).mp (Nat.dvd_of_mod_eq_zero hm)
    have hp2 := hp.two_le
    cases hd with
    | inl h => norm_num at h
    | inr h => omega
  omega

theorem twin_cubicRow_conjugation (p : Nat) (hp : Nat.Prime p)
    (hnext : Nat.Prime (p + 2)) (hp3 : Not (p = 3)) (z : Eis) :
    CubicSieve.cubicRow (Ideal.span {(p : Eis)}) (conjO z) =
      star (CubicSieve.cubicRow (Ideal.span {(p : Eis)}) z) :=
  rational_cubicRow_conjugation p hp (twin_start_mod_three p hp hnext hp3) z

theorem twin_kernel_symmetric (p q : Nat) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpnext : Nat.Prime (p + 2)) (hqnext : Nat.Prime (q + 2))
    (hp3 : Not (p = 3)) (hq3 : Not (q = 3))
    (W : SchwartzMap Real Complex) (M : Real) :
    CubicPairReflection.pairedKernel (Ideal.span {(q : Eis)}) (Ideal.span {(p : Eis)}) W M =
      CubicPairReflection.pairedKernel (Ideal.span {(p : Eis)}) (Ideal.span {(q : Eis)}) W M :=
  rational_kernel_symmetric p q hp hq
    (twin_start_mod_three p hp hpnext hp3) (twin_start_mod_three q hq hqnext hq3) W M

end PrimeFactorOscillations.CubicInertArithmetic
