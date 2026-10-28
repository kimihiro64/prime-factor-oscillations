/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.CubicPairReflection

/-!
# Native cubic input conjugation on rational prime ideals

Proves input conjugation for the canonical character and symmetry of the
paired lattice kernel under the stated maximality and lambda-avoidance hypotheses.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.CubicRationalRows

open OAI OAI.SevenEighths
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT CubicSieve
local notation "Eis" => ActualEisensteinCubic.O

theorem cubicChar_input_conjugation (P : Ideal Eis) [P.IsMaximal]
    (hgood : Not (Membership.mem P lambda))
    (hstable : forall z : Eis, Membership.mem P z <-> Membership.mem P (conjO z))
    (z : Eis) :
    cubicChar P hgood (Ideal.Quotient.mk P (conjO z)) =
      conjO (cubicChar P hgood (Ideal.Quotient.mk P z)) := by
  letI : Field ((HasQuotient.Quotient Eis P)) := Ideal.Quotient.field P
  let f : RingHom Eis (HasQuotient.Quotient Eis P) :=
    (Ideal.Quotient.mk P).comp conjO.toRingHom
  have hf : forall a : Eis, Membership.mem P a -> f a = 0 := by
    intro a ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hstable a).mp ha)
  let c : RingHom (HasQuotient.Quotient Eis P) (HasQuotient.Quotient Eis P) :=
    Ideal.Quotient.lift P f hf
  have hc (a : Eis) : c (Ideal.Quotient.mk P a) = Ideal.Quotient.mk P (conjO a) :=
    Ideal.Quotient.lift_mk P f hf
  by_cases hz : Ideal.Quotient.mk P z = 0
  . have hcz : Ideal.Quotient.mk P (conjO z) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        ((hstable z).mp (Ideal.Quotient.eq_zero_iff_mem.mp hz))
    rw [hz, hcz, MulChar.map_zero, map_zero]
  . have hcz : Not (Ideal.Quotient.mk P (conjO z) = 0) := by
      intro h
      exact hz (Ideal.Quotient.eq_zero_iff_mem.mpr
        ((hstable z).mpr (Ideal.Quotient.eq_zero_iff_mem.mp h)))
    have hcube (x : (HasQuotient.Quotient Eis P)) (hx : Not (x = 0)) :
        cubicChar P hgood x ^ 3 = 1 := by
      rw [<- MulChar.pow_apply' _ (by decide : Not ((3 : Nat) = 0)),
        cubicChar_pow_three]
      exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)
    apply cubic_roots_reduce_injective P hgood (hcube _ hcz)
      (by rw [<- map_pow, hcube _ hz, map_one])
    have hr := congrArg c (cubicChar_reduce P hgood (Ideal.Quotient.mk P z))
    rw [map_pow, hc, hc] at hr
    exact (cubicChar_reduce P hgood (Ideal.Quotient.mk P (conjO z))).trans hr.symm

theorem rational_span_conjugation (p : Nat) (z : Eis) :
    Membership.mem (Ideal.span {(p : Eis)}) z <->
      Membership.mem (Ideal.span {(p : Eis)}) (conjO z) := by
  rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  constructor
  . intro h
    let a : Eis := Classical.choose h
    have ha : z = (p : Eis) * a := Classical.choose_spec h
    refine Exists.intro (conjO a) ?_
    have he := congrArg conjO ha
    simpa only [map_mul, map_natCast] using he
  . intro h
    let a : Eis := Classical.choose h
    have ha : conjO z = (p : Eis) * a := Classical.choose_spec h
    refine Exists.intro (conjO.symm a) ?_
    have he := congrArg conjO.symm ha
    simpa only [RingEquiv.symm_apply_apply, map_mul, map_natCast] using he

theorem rational_cubicRow_conjugation (P : Ideal Eis) [P.IsMaximal]
    (hgood : Not (Membership.mem P lambda)) (p : Nat)
    (hP : P = Ideal.span {(p : Eis)}) (z : Eis) :
    CubicSieve.cubicRow P (conjO z) = star (CubicSieve.cubicRow P z) := by
  have hstable : forall a : Eis, Membership.mem P a <-> Membership.mem P (conjO a) := by
    intro a
    rw [hP]
    exact rational_span_conjugation p a
  dsimp [CubicSieve.cubicRow]
  rw [CubicJacobiGlobal.idealSymbol_prime P hgood,
    CubicJacobiGlobal.idealSymbol_prime P hgood,
    cubicChar_input_conjugation P hgood hstable z, eisEmbedding_conjO]
  rfl

theorem rational_kernel_symmetric (P Q : Ideal Eis) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : Not (Membership.mem P lambda))
    (hQgood : Not (Membership.mem Q lambda)) (p q : Nat)
    (hP : P = Ideal.span {(p : Eis)}) (hQ : Q = Ideal.span {(q : Eis)})
    (W : SchwartzMap Real Complex) (M : Real) :
    CubicPairReflection.pairedKernel Q P W M =
      CubicPairReflection.pairedKernel P Q W M :=
  CubicPairReflection.kernel_symmetric_of_conjugation P Q W M
    (rational_cubicRow_conjugation P hPgood p hP)
    (rational_cubicRow_conjugation Q hQgood q hQ)

end PrimeFactorOscillations.CubicRationalRows
