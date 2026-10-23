/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ModularReturnFourier

/-!
# Local power-return factors in a fully compensated Fourier packet

Rational Fourier evaluation at a nontrivial prime character is injective
once the coefficient at zero is fixed. A nonreturning unit therefore
changes the local return sum, while it preserves the unit-mask sum.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimeReturnFourier

open scoped BigOperators
open PrimeCarrierFourier ModularReturnFourier

def primeFourier (p : Nat) [Fact (Nat.Prime p)]
    (psi : AddChar (ZMod p) Complex) (f : ZMod p -> Rat) : Complex :=
  Finset.univ.sum (fun x : ZMod p => (f x : Complex) * psi x)

def unitMulEquiv (p : Nat) (u : Units (ZMod p)) : Equiv (ZMod p) (ZMod p) where
  toFun x := (u : ZMod p) * x
  invFun x := ((Inv.inv u : Units (ZMod p)) : ZMod p) * x
  left_inv x := by simp [<- mul_assoc]
  right_inv x := by simp [<- mul_assoc]

theorem prime_fourier_injective_at_zero (p : Nat) [Fact (Nat.Prime p)]
    (psi : AddChar (ZMod p) Complex) (hpsi : Function.Injective psi)
    (f g : ZMod p -> Rat) (hzero : f 0 = g 0)
    (hsum : primeFourier p psi f = primeFourier p psi g) : f = g := by
  have hd : primeFourier p psi (fun x => f x - g x) = 0 := by
    unfold primeFourier at *
    simp only [Rat.cast_sub, sub_mul, Finset.sum_sub_distrib, hsum, sub_self]
  have hc := (prime_rational_fourier_eq_zero_iff p psi hpsi
    (fun x => f x - g x)).mp hd
  funext x
  have hx := hc x 0
  rw [sub_eq_zero.mpr hzero] at hx
  exact sub_eq_zero.mp hx

theorem shifted_eq_pullback (p : Nat) [Fact (Nat.Prime p)]
    (psi : AddChar (ZMod p) Complex) (f : ZMod p -> Rat) (u : Units (ZMod p)) :
    Finset.univ.sum (fun x : ZMod p => (f x : Complex) * psi ((u : ZMod p) * x)) =
      primeFourier p psi
        (fun x => f (((Inv.inv u : Units (ZMod p)) : ZMod p) * x)) := by
  let e := unitMulEquiv p u
  have he := e.sum_comp (fun x : ZMod p =>
    (f (((Inv.inv u : Units (ZMod p)) : ZMod p) * x) : Complex) * psi x)
  change (Finset.univ.sum (fun x : ZMod p =>
    (f (((Inv.inv u : Units (ZMod p)) : ZMod p) * ((u : ZMod p) * x)) : Complex) *
      psi ((u : ZMod p) * x))) = _ at he
  have hinv : ((Inv.inv u : Units (ZMod p)) : ZMod p) * (u : ZMod p) = 1 := u.inv_val
  simpa only [primeFourier, <- mul_assoc, hinv, one_mul] using he

theorem unit_shift_eq (p : Nat) [Fact (Nat.Prime p)]
    (psi : AddChar (ZMod p) Complex) (u : Units (ZMod p)) :
    Finset.univ.sum (fun x : ZMod p =>
      (unitWeight p x : Complex) * psi ((u : ZMod p) * x)) =
      primeFourier p psi (unitWeight p) := by
  rw [shifted_eq_pullback]
  unfold primeFourier
  apply Finset.sum_congr rfl
  intro x _
  have hm : unitWeight p (((Inv.inv u : Units (ZMod p)) : ZMod p) * x) =
      unitWeight p x := by
    have hinv : Not (((Inv.inv u : Units (ZMod p)) : ZMod p) = 0) :=
      Units.ne_zero (Inv.inv u)
    simp only [unitWeight, mul_eq_zero, hinv, false_or]
  change (unitWeight p (((Inv.inv u : Units (ZMod p)) : ZMod p) * x) : Complex) *
    psi x = _
  rw [hm]

theorem return_weight_nonconstant (p : Nat) [Fact (Nat.Prime p)] (k : Nat) :
    Not (forall x y, returnWeight p k x = returnWeight p k y) := by
  intro h
  have he := h 0 1
  norm_num [returnWeight] at he

theorem return_mass_pos (p : Nat) [Fact (Nat.Prime p)] (k : Nat) :
    0 < Finset.univ.sum (returnWeight p k) := by
  apply Finset.sum_pos'
  { intro x _
    by_cases hx : x = 0
    { simp [returnWeight, hx] }
    { by_cases hr : x ^ k = 1 <;> simp [returnWeight, hx, hr] } }
  { exact Exists.intro 1 (And.intro (Finset.mem_univ _) (by simp [returnWeight])) }

theorem return_shift_ne (p : Nat) [Fact (Nat.Prime p)] (k : Nat)
    (psi : AddChar (ZMod p) Complex) (hpsi : Function.Injective psi)
    (u : Units (ZMod p)) (hu : Not ((u : ZMod p) ^ k = 1)) :
    Not (Finset.univ.sum (fun x : ZMod p =>
      (returnWeight p k x : Complex) * psi ((u : ZMod p) * x)) =
      primeFourier p psi (returnWeight p k)) := by
  intro he
  rw [shifted_eq_pullback] at he
  let g : ZMod p -> Rat :=
    fun x => returnWeight p k (((Inv.inv u : Units (ZMod p)) : ZMod p) * x)
  have hzero : g 0 = returnWeight p k 0 := by
    change returnWeight p k (((Inv.inv u : Units (ZMod p)) : ZMod p) * 0) = _
    rw [mul_zero]
  have hfg := prime_fourier_injective_at_zero p psi hpsi g
    (returnWeight p k) hzero he
  have hz := congrFun hfg (u : ZMod p)
  change returnWeight p k (((Inv.inv u : Units (ZMod p)) : ZMod p) * (u : ZMod p)) =
    returnWeight p k (u : ZMod p) at hz
  have hinv : ((Inv.inv u : Units (ZMod p)) : ZMod p) * (u : ZMod p) = 1 := u.inv_val
  rw [hinv] at hz
  have hret1 : returnWeight p k 1 = 1 := by
    simp only [returnWeight, one_ne_zero, ite_false, one_pow, ite_true]
  have hretu : returnWeight p k (u : ZMod p) = 0 := by
    simp only [returnWeight, Units.ne_zero u, ite_false, hu]
  rw [hret1, hretu] at hz
  exact one_ne_zero hz

theorem return_weight_eq_unit_of_period_dvd (p : Nat) [Fact (Nat.Prime p)]
    (k : Nat) (hd : Dvd.dvd (p - 1) k) :
    returnWeight p k = unitWeight p := by
  funext x
  by_cases hx : x = 0
  { simp only [returnWeight, unitWeight, hx, ite_true] }
  { simp only [returnWeight, unitWeight, hx, ite_false,
      local_period_annihilates p k hd x hx, ite_true] }

end PrimeFactorOscillations.PrimeReturnFourier
