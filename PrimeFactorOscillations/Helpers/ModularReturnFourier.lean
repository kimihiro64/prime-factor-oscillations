/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.CarmichaelConditionalRigidity
import PrimeFactorOscillations.Helpers.PrimeCarrierFourier

/-!
# Physical prime carriers recovered by additive Fourier zeros

The coefficients and Fourier transform below live on the actual residue
ring, with its standard faithful additive character. Squarefree CRT is a
proof coordinate change, not a replacement sampling space.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.ModularReturnFourier

open scoped BigOperators
open PrimeCarrierFourier PrimeOrderReturnIndex

local instance factorPrime (B : Nat) (p : B.primeFactors) :
    Fact (Nat.Prime (p.val : Nat)) :=
  Fact.mk (Nat.mem_primeFactors.mp p.property).1

def squarefreeResidueEquiv (B : Nat) [NeZero B] (hSq : Squarefree B) :
    RingEquiv (ZMod B) ((p : B.primeFactors) -> ZMod (p.val : Nat)) := by
  have hVal : forall p : B.primeFactors, B.factorization (p.val : Nat) = 1 := by
    intro p
    have hp := Nat.mem_primeFactors.mp p.property
    exact Nat.factorization_eq_one_of_squarefree hSq hp.1 hp.2.1
  exact (ZMod.equivPi B (NeZero.ne B)).trans
    (RingEquiv.piCongrRight (fun p : B.primeFactors =>
      ZMod.ringEquivCongr (by rw [hVal p, pow_one])))

def residueFourier (B : Nat) [NeZero B] (f : ZMod B -> Rat) (h : Nat) : Complex :=
  Finset.univ.sum (fun x : ZMod B =>
    (f x : Complex) * ZMod.stdAddChar ((h : ZMod B) * x))

def residueTensor (B : Nat) [NeZero B] (hSq : Squarefree B)
    (f : (p : B.primeFactors) -> ZMod (p.val : Nat) -> Rat) (x : ZMod B) : Rat :=
  Finset.univ.prod (fun p => f p (squarefreeResidueEquiv B hSq x p))

def crtCharacter (B : Nat) [NeZero B] (hSq : Squarefree B) :
    AddChar ((p : B.primeFactors) -> ZMod (p.val : Nat)) Complex :=
  ZMod.stdAddChar.compAddMonoidHom (squarefreeResidueEquiv B hSq).symm.toAddMonoidHom

theorem crt_character_injective (B : Nat) [NeZero B] (hSq : Squarefree B) :
    Function.Injective (crtCharacter B hSq) :=
  ZMod.injective_stdAddChar.comp (squarefreeResidueEquiv B hSq).symm.injective

theorem residue_fourier_eq_tensor (B : Nat) [NeZero B] (hSq : Squarefree B)
    (f : (p : B.primeFactors) -> ZMod (p.val : Nat) -> Rat) (h : Nat) :
    residueFourier B (residueTensor B hSq f) h =
      tensorFourier (fun p : B.primeFactors => (p.val : Nat)) (crtCharacter B hSq) f h := by
  classical
  let e := squarefreeResidueEquiv B hSq
  have hchar (y : (p : B.primeFactors) -> ZMod (p.val : Nat)) :
      crtCharacter B hSq ((h : (p : B.primeFactors) -> ZMod (p.val : Nat)) * y) =
        ZMod.stdAddChar ((h : ZMod B) * e.symm y) := by
    change ZMod.stdAddChar (e.symm ((h : (p : B.primeFactors) -> ZMod (p.val : Nat)) * y)) = _
    rw [map_mul, map_natCast]
  unfold residueFourier
  rw [<- e.symm.toEquiv.sum_comp]
  unfold tensorFourier
  apply Finset.sum_congr rfl
  intro y _
  rw [hchar]
  change (((Finset.univ.prod (fun p => f p (e (e.symm y) p))) : Rat) : Complex) *
    ZMod.stdAddChar ((h : ZMod B) * e.symm y) = _
  simp only [e.apply_symm_apply, Rat.cast_prod]

theorem residue_tensor_zero_iff (B : Nat) [NeZero B] (hSq : Squarefree B)
    (f : (p : B.primeFactors) -> ZMod (p.val : Nat) -> Rat) (h : Nat) :
    residueFourier B (residueTensor B hSq f) h = 0 <->
      exists p : B.primeFactors,
        (Dvd.dvd (p.val : Nat) h /\ Finset.univ.sum (f p) = 0) \/
        (Not (Dvd.dvd (p.val : Nat) h) /\ forall x y, f p x = f p y) := by
  rw [residue_fourier_eq_tensor]
  exact tensor_fourier_zero_iff _ _ (crt_character_injective B hSq) f h

theorem residue_unique_carrier_zero_iff (B : Nat) [NeZero B] (hSq : Squarefree B)
    (f : (p : B.primeFactors) -> ZMod (p.val : Nat) -> Rat)
    (hnc : forall p, Not (forall x y, f p x = f p y))
    (q : B.primeFactors) (hmean : forall p, Finset.univ.sum (f p) = 0 <-> p = q)
    (h : Nat) :
    residueFourier B (residueTensor B hSq f) h = 0 <-> Dvd.dvd (q.val : Nat) h := by
  rw [residue_fourier_eq_tensor]
  exact unique_carrier_zero_iff _ _ (crt_character_injective B hSq) f hnc q hmean h

def unitWeight (p : Nat) (x : ZMod p) : Rat := if x = 0 then 0 else 1

def returnWeight (p k : Nat) (x : ZMod p) : Rat :=
  if x = 0 then 0 else if x ^ k = 1 then 1 else 0

def centeredReturn (p : Nat) [Fact (Nat.Prime p)] (k : Nat) (x : ZMod p) : Rat :=
  (Finset.univ.sum (unitWeight p)) * returnWeight p k x -
    (Finset.univ.sum (returnWeight p k)) * unitWeight p x

theorem unit_weight_nonconstant (p : Nat) [Fact (Nat.Prime p)] :
    Not (forall x y, unitWeight p x = unitWeight p y) := by
  intro h
  have hz := h 0 1
  norm_num [unitWeight] at hz

theorem unit_mass_pos (p : Nat) [Fact (Nat.Prime p)] :
    0 < Finset.univ.sum (unitWeight p) := by
  apply Finset.sum_pos'
  { intro x _
    by_cases hx : x = 0 <;> simp [unitWeight, hx] }
  { exact Exists.intro 1 (And.intro (Finset.mem_univ _) (by simp [unitWeight])) }

theorem centered_return_sum_zero (p : Nat) [Fact (Nat.Prime p)] (k : Nat) :
    Finset.univ.sum (centeredReturn p k) = 0 := by
  unfold centeredReturn
  rw [Finset.sum_sub_distrib, <- Finset.mul_sum, <- Finset.mul_sum]
  exact sub_eq_zero.mpr (mul_comm _ _)

theorem period_failure_witness (p : Nat) [Fact (Nat.Prime p)] (k : Nat)
    (hndiv : Not (Dvd.dvd (p - 1) k)) :
    exists x : ZMod p, Not (x = 0) /\ Not (x ^ k = 1) := by
  have hp : Nat.Prime p := Fact.out
  have hex : exists u : Units (ZMod p), Not (u ^ k = 1) := by
    by_contra hno
    have hall : forall u : Units (ZMod p), u ^ k = 1 := by
      intro u
      by_contra hu
      exact hno (Exists.intro u hu)
    apply hndiv
    rw [<- prime_unit_exponent (Subtype.mk p hp)]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one hall
  choose u hu using hex
  refine Exists.intro (u : ZMod p) (And.intro (Units.ne_zero u) ?_)
  intro h
  apply hu
  apply Units.ext
  simpa using h

theorem centered_return_nonconstant (p : Nat) [Fact (Nat.Prime p)] (k : Nat)
    (hndiv : Not (Dvd.dvd (p - 1) k)) :
    Not (forall x y, centeredReturn p k x = centeredReturn p k y) := by
  choose x hx using period_failure_witness p k hndiv
  intro h
  have he := h 1 x
  simp only [centeredReturn, returnWeight, unitWeight, one_ne_zero,
    if_false, one_pow, if_true, hx.1, hx.2, mul_one, mul_zero, zero_sub] at he
  have hpos := unit_mass_pos p
  linarith

def carrierWeights (B k : Nat) (q : B.primeFactors)
    (p : B.primeFactors) (x : ZMod (p.val : Nat)) : Rat :=
  if p = q then centeredReturn (p.val : Nat) k x else unitWeight (p.val : Nat) x

def carrierObservable (B : Nat) [NeZero B] (hSq : Squarefree B) (k : Nat)
    (q : B.primeFactors) : ZMod B -> Rat :=
  residueTensor B hSq (carrierWeights B k q)

theorem carrier_observable_zero_iff (B : Nat) [NeZero B] (hSq : Squarefree B)
    (k : Nat) (q : B.primeFactors)
    (hq : Not (Dvd.dvd ((q.val : Nat) - 1) k)) (h : Nat) :
    residueFourier B (carrierObservable B hSq k q) h = 0 <->
      Dvd.dvd (q.val : Nat) h := by
  classical
  apply residue_unique_carrier_zero_iff B hSq (carrierWeights B k q) _ q _
  { intro p
    by_cases hp : p = q
    { subst p
      simpa only [carrierWeights, if_true] using
        centered_return_nonconstant (q.val : Nat) k hq }
    { simpa only [carrierWeights, hp, if_false] using unit_weight_nonconstant (p.val : Nat) } }
  { intro p
    by_cases hp : p = q
    { subst p
      have hw : carrierWeights B k q q = centeredReturn (q.val : Nat) k := by
        funext x
        simp only [carrierWeights, ite_true]
      rw [hw, centered_return_sum_zero]
      simp }
    { have hw : carrierWeights B k q p = unitWeight (p.val : Nat) := by
        funext x
        simp only [carrierWeights, hp, ite_false]
      rw [hw]
      simp only [hp, iff_false]
      exact ne_of_gt (unit_mass_pos (p.val : Nat)) } }

theorem local_period_annihilates (p : Nat) [Fact (Nat.Prime p)] (k : Nat)
    (hdiv : Dvd.dvd (p - 1) k) (x : ZMod p) (hx : Not (x = 0)) :
    x ^ k = 1 := by
  have hp : Nat.Prime p := Fact.out
  have hd : Dvd.dvd (Monoid.exponent (Units (ZMod p))) k := by
    rw [prime_unit_exponent (Subtype.mk p hp)]
    exact hdiv
  have hu := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hd (Units.mk0 x hx)
  have hval := congrArg (fun u : Units (ZMod p) => (u : ZMod p)) hu
  simpa using hval

theorem isUnit_iff_nonzero_coordinates (B : Nat) [NeZero B] (hSq : Squarefree B)
    (x : ZMod B) :
    IsUnit x <-> forall p : B.primeFactors,
      Not (squarefreeResidueEquiv B hSq x p = 0) := by
  let e := squarefreeResidueEquiv B hSq
  have he : IsUnit (e x) <-> IsUnit x := by
    constructor
    { intro h
      have hm := h.map e.symm.toMonoidHom
      change IsUnit (e.symm (e x)) at hm
      rwa [e.symm_apply_apply] at hm }
    { intro h
      exact h.map e.toMonoidHom }
  rw [<- he, Pi.isUnit_iff]
  simp only [isUnit_iff_ne_zero]
  rfl

theorem power_return_iff_owner (B : Nat) [NeZero B] (hSq : Squarefree B)
    (k : Nat) (q : B.primeFactors)
    (hothers : forall p : B.primeFactors, Not (p = q) ->
      Dvd.dvd ((p.val : Nat) - 1) k)
    (x : ZMod B) (hx : IsUnit x) :
    x ^ k = 1 <-> (squarefreeResidueEquiv B hSq x q) ^ k = 1 := by
  let e := squarefreeResidueEquiv B hSq
  constructor
  { intro h
    have hval := congrArg (fun z : ZMod B => e z q) h
    simpa only [map_pow, map_one, Pi.pow_apply, Pi.one_apply] using hval }
  { intro h
    apply e.injective
    rw [map_pow, map_one]
    funext p
    change (e x p) ^ k = 1
    by_cases hp : p = q
    { subst p
      exact h }
    { exact local_period_annihilates (p.val : Nat) k (hothers p hp) (e x p)
        ((isUnit_iff_nonzero_coordinates B hSq x).mp hx p) } }

def ownerPowerObservable (B k : Nat) (q : B.primeFactors) (x : ZMod B) : Rat := by
  classical
  exact if IsUnit x then
    (Finset.univ.sum (unitWeight (q.val : Nat))) * (if x ^ k = 1 then 1 else 0) -
      Finset.univ.sum (returnWeight (q.val : Nat) k)
    else 0

theorem carrier_eq_owner_power (B : Nat) [NeZero B] (hSq : Squarefree B)
    (k : Nat) (q : B.primeFactors)
    (hothers : forall p : B.primeFactors, Not (p = q) ->
      Dvd.dvd ((p.val : Nat) - 1) k) :
    carrierObservable B hSq k q = ownerPowerObservable B k q := by
  classical
  funext x
  by_cases hx : IsUnit x
  { have hc := (isUnit_iff_nonzero_coordinates B hSq x).mp hx
    have hprod : carrierObservable B hSq k q x =
        centeredReturn (q.val : Nat) k (squarefreeResidueEquiv B hSq x q) := by
      unfold carrierObservable residueTensor
      rw [Finset.prod_eq_single q]
      { simp only [carrierWeights, ite_true] }
      { intro p _ hp
        simp only [carrierWeights, hp, ite_false, unitWeight, hc p] }
      { intro hq
        exact (hq (Finset.mem_univ q)).elim }
    rw [hprod]
    have hpow := power_return_iff_owner B hSq k q hothers x hx
    simp only [centeredReturn, ownerPowerObservable, hx, ite_true, returnWeight,
      unitWeight, hc q, ite_false, mul_one, hpow] }
  { have hex : exists p : B.primeFactors, squarefreeResidueEquiv B hSq x p = 0 := by
      by_contra h
      apply hx
      apply (isUnit_iff_nonzero_coordinates B hSq x).mpr
      intro p hp
      exact h (Exists.intro p hp)
    choose p hp using hex
    have hzero : carrierObservable B hSq k q x = 0 := by
      unfold carrierObservable residueTensor
      apply Finset.prod_eq_zero (Finset.mem_univ p)
      simp only [carrierWeights, centeredReturn, returnWeight, unitWeight, hp,
        ite_true, mul_zero, sub_self, ite_self]
    rw [hzero]
    simp only [ownerPowerObservable, hx, ite_false] }

theorem owner_power_zero_iff (B : Nat) [NeZero B] (hSq : Squarefree B)
    (k : Nat) (q : B.primeFactors)
    (hq : Not (Dvd.dvd ((q.val : Nat) - 1) k))
    (hothers : forall p : B.primeFactors, Not (p = q) ->
      Dvd.dvd ((p.val : Nat) - 1) k) (h : Nat) :
    residueFourier B (ownerPowerObservable B k q) h = 0 <->
      Dvd.dvd (q.val : Nat) h := by
  rw [<- carrier_eq_owner_power B hSq k q hothers]
  exact carrier_observable_zero_iff B hSq k q hq h

end PrimeFactorOscillations.ModularReturnFourier
