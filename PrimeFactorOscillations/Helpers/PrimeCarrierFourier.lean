/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Exact additive Fourier zero sets of rational prime-coordinate tensors

The prime-coordinate nonvanishing input is the classical rational
root-of-unity lemma already proved in Mathlib. The consumer retains the
complete CRT tensor: every zero is classified by a local zero mean at a
frequency divisible by that prime, or by a constant coefficient at a
nondivisible frequency. In particular a unique centered nonconstant
coordinate is recovered from precisely its divisible frequencies.

The native modular power-return consumer is supplied separately.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.PrimeCarrierFourier

open scoped BigOperators

theorem prime_character_root (p : Nat) [Fact (Nat.Prime p)]
    (psi : AddChar (ZMod p) Complex) (hpsi : Function.Injective psi) :
    IsPrimitiveRoot (psi 1) p := by
  have hp : Nat.Prime p := Fact.out
  have hpw : psi 1 ^ p = 1 := by
    simpa [nsmul_eq_mul] using (AddChar.map_nsmul_eq_pow psi p (1 : ZMod p)).symm
  have hne : Not (psi 1 = 1) := by
    intro h
    have hz : (1 : ZMod p) = 0 := hpsi (h.trans psi.map_zero_eq_one.symm)
    exact one_ne_zero hz
  have hord : orderOf (psi 1) = p := orderOf_eq_prime hpw hne
  refine IsPrimitiveRoot.mk_of_lt _ hp.pos hpw ?_
  intro n hn hnp hpow
  have hd : p = orderOf (psi 1) := hord.symm
  have hdiv : Dvd.dvd p n := by
    rw [hd]
    exact orderOf_dvd_of_pow_eq_one hpow
  exact (Nat.not_le.mpr hnp) (Nat.le_of_dvd hn hdiv)

theorem character_eq_pow_val (p : Nat) [NeZero p]
    (psi : AddChar (ZMod p) Complex) (x : ZMod p) :
    psi x = psi 1 ^ x.val := by
  simpa [nsmul_eq_mul] using AddChar.map_nsmul_eq_pow psi x.val (1 : ZMod p)

theorem prime_rational_fourier_eq_zero_iff (p : Nat) [Fact (Nat.Prime p)]
    (psi : AddChar (ZMod p) Complex) (hpsi : Function.Injective psi)
    (f : ZMod p -> Rat) :
    (Finset.univ.sum (fun x : ZMod p => (f x : Complex) * psi x) = 0) <->
      forall x y, f x = f y := by
  have hp : Nat.Prime p := Fact.out
  let e := (ZMod.finEquiv p).toEquiv
  have hv (i : Fin p) : (e i).val = i.val := by
    cases p with
    | zero => exact (hp.ne_zero rfl).elim
    | succ n => rfl
  have hs : Finset.univ.sum (fun x : ZMod p => (f x : Complex) * psi x) =
      Finset.univ.sum (fun i : Fin p => (f (e i) : Complex) * psi 1 ^ i.val) := by
    calc
      _ = Finset.univ.sum (fun i : Fin p => (f (e i) : Complex) * psi (e i)) :=
        (e.sum_comp (fun x : ZMod p => (f x : Complex) * psi x)).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [character_eq_pow_val p psi (e i), hv]
  rw [hs, IsPrimitiveRoot.sum_eq_zero_iff_forall_eq
    (show Nat.Prime p from Fact.out) (prime_character_root p psi hpsi)]
  constructor
  { intro h x y
    simpa only [e.apply_symm_apply] using h (e.symm x) (e.symm y) }
  { intro h i j
    exact h (e i) (e j) }

theorem character_finite_sum {R : Type*} [AddCommMonoid R]
    (psi : AddChar R Complex) {J : Type*} (s : Finset J) (f : J -> R) :
    psi (s.sum f) = s.prod (fun j => psi (f j)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.prod_empty, AddChar.map_zero_eq_one]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, psi.map_add_eq_mul, ih]

variable {I : Type*} [Fintype I] [DecidableEq I]
    (p : I -> Nat) [forall i, Fact (Nat.Prime (p i))]

def localCharacter (psi : AddChar ((i : I) -> ZMod (p i)) Complex)
    (h : Nat) (i : I) : AddChar (ZMod (p i)) Complex :=
  (psi.compAddMonoidHom (AddMonoidHom.single (fun i => ZMod (p i)) i)).mulShift
    (h : ZMod (p i))

def tensorFourier (psi : AddChar ((i : I) -> ZMod (p i)) Complex)
    (f : (i : I) -> ZMod (p i) -> Rat) (h : Nat) : Complex :=
  Finset.univ.sum (fun x : (i : I) -> ZMod (p i) =>
    (Finset.univ.prod (fun i => (f i (x i) : Complex))) *
      psi ((h : (i : I) -> ZMod (p i)) * x))

theorem tensor_fourier_factorization
    (psi : AddChar ((i : I) -> ZMod (p i)) Complex)
    (f : (i : I) -> ZMod (p i) -> Rat) (h : Nat) :
    tensorFourier p psi f h =
      Finset.univ.prod (fun i =>
        Finset.univ.sum (fun x : ZMod (p i) =>
          (f i x : Complex) * localCharacter p psi h i x)) := by
  classical
  unfold tensorFourier
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  have he : psi ((h : (i : I) -> ZMod (p i)) * x) =
      Finset.univ.prod (fun i => localCharacter p psi h i (x i)) := by
    change psi ((h : (i : I) -> ZMod (p i)) * x) =
      Finset.univ.prod (fun i => psi (Pi.single i ((h : ZMod (p i)) * x i)))
    rw [<- character_finite_sum psi]
    congr 1
    funext i
    simp
  rw [he, Finset.prod_mul_distrib]

theorem local_character_injective
    (psi : AddChar ((i : I) -> ZMod (p i)) Complex)
    (hpsi : Function.Injective psi) (h : Nat) (i : I)
    (hndiv : Not (Dvd.dvd (p i) h)) :
    Function.Injective (localCharacter p psi h i) := by
  intro x y hxy
  change psi (Pi.single i ((h : ZMod (p i)) * x)) =
    psi (Pi.single i ((h : ZMod (p i)) * y)) at hxy
  have hsingle := hpsi hxy
  have hm : (h : ZMod (p i)) * x = (h : ZMod (p i)) * y := by
    simpa only [Pi.single_eq_same] using congrFun hsingle i
  have hz : Not ((h : ZMod (p i)) = 0) := by
    intro hz
    exact hndiv ((CharP.cast_eq_zero_iff (ZMod (p i)) (p i) h).mp hz)
  exact (mul_eq_mul_left_iff.mp hm).resolve_right hz

theorem local_character_trivial
    (psi : AddChar ((i : I) -> ZMod (p i)) Complex)
    (h : Nat) (i : I) (hdiv : Dvd.dvd (p i) h) (x : ZMod (p i)) :
    localCharacter p psi h i x = 1 := by
  have hz : (h : ZMod (p i)) = 0 :=
    (CharP.cast_eq_zero_iff (ZMod (p i)) (p i) h).mpr hdiv
  simp [localCharacter, AddChar.mulShift_apply, AddChar.compAddMonoidHom_apply, hz]

theorem local_fourier_zero_iff
    (psi : AddChar ((i : I) -> ZMod (p i)) Complex)
    (hpsi : Function.Injective psi) (i : I) (f : ZMod (p i) -> Rat) (h : Nat) :
    (Finset.univ.sum (fun x : ZMod (p i) =>
      (f x : Complex) * localCharacter p psi h i x) = 0) <->
      (Dvd.dvd (p i) h /\ Finset.univ.sum f = 0) \/
      (Not (Dvd.dvd (p i) h) /\ forall x y, f x = f y) := by
  classical
  by_cases hd : Dvd.dvd (p i) h
  { simp only [local_character_trivial p psi h i hd, mul_one, hd,
      true_and, not_true_eq_false, false_and, or_false]
    exact_mod_cast (Iff.rfl : Finset.univ.sum f = 0 <-> Finset.univ.sum f = 0) }
  { simp only [hd, false_and, not_false_eq_true, true_and, false_or]
    exact prime_rational_fourier_eq_zero_iff (p i)
      (localCharacter p psi h i) (local_character_injective p psi hpsi h i hd) f }

theorem tensor_fourier_zero_iff
    (psi : AddChar ((i : I) -> ZMod (p i)) Complex)
    (hpsi : Function.Injective psi) (f : (i : I) -> ZMod (p i) -> Rat) (h : Nat) :
    tensorFourier p psi f h = 0 <->
      exists i : I,
        (Dvd.dvd (p i) h /\ Finset.univ.sum (f i) = 0) \/
        (Not (Dvd.dvd (p i) h) /\ forall x y, f i x = f i y) := by
  rw [tensor_fourier_factorization, Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and]
  apply exists_congr
  intro i
  exact local_fourier_zero_iff p psi hpsi i (f i) h

theorem nonconstant_tensor_zero_iff
    (psi : AddChar ((i : I) -> ZMod (p i)) Complex)
    (hpsi : Function.Injective psi) (f : (i : I) -> ZMod (p i) -> Rat)
    (hnc : forall i, Not (forall x y, f i x = f i y)) (h : Nat) :
    tensorFourier p psi f h = 0 <->
      exists i : I, Dvd.dvd (p i) h /\ Finset.univ.sum (f i) = 0 := by
  rw [tensor_fourier_zero_iff p psi hpsi]
  simp only [hnc, and_false, or_false]

theorem unique_carrier_zero_iff
    (psi : AddChar ((i : I) -> ZMod (p i)) Complex)
    (hpsi : Function.Injective psi) (f : (i : I) -> ZMod (p i) -> Rat)
    (hnc : forall i, Not (forall x y, f i x = f i y))
    (q : I) (hmean : forall i, Finset.univ.sum (f i) = 0 <-> i = q) (h : Nat) :
    tensorFourier p psi f h = 0 <-> Dvd.dvd (p q) h := by
  rw [nonconstant_tensor_zero_iff p psi hpsi f hnc]
  simp only [hmean, exists_eq_right]

end PrimeFactorOscillations.PrimeCarrierFourier
