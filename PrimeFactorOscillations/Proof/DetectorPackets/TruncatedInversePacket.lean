/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import OAI.NumberTheory.DirichletL.Arithmetic.IdealMobius

/-!
# TruncatedInversePacket

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
# Exact truncated inverse packets

The identity is coefficientwise and unconditional. It retains the inverse
convolution constraint before a packet estimate takes absolute values.
The cutoff remainder vanishes on the whole interval n <= U^2.
No analytic estimate or zero-free hypothesis occurs in this module.
-/


noncomputable section
namespace PrimeFactorOscillations.TruncatedInversePacket

variable {R : Type*} [CommRing R]

def cutoff (f : ArithmeticFunction R) (U : Nat) : ArithmeticFunction R where
  toFun n := if n <= U then f n else 0
  map_zero' := by simp

theorem cutoff_of_le (f : ArithmeticFunction R) (U n : Nat) (hn : n <= U) :
    cutoff f U n = f n := by
  change (if n <= U then f n else 0) = f n
  exact ite_eq_left hn

theorem factor_right_le {n : Nat} {ab : Prod Nat Nat}
    (hab : Membership.mem n.divisorsAntidiagonal ab) : ab.2 <= n := by
  have hm := Nat.mem_divisorsAntidiagonal.mp hab
  have ha : 1 <= ab.1 := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro hz
    have he := hm.1
    rw [hz, zero_mul] at he
    exact hm.2 he.symm
  calc
    ab.2 = 1 * ab.2 := by simp
    _ <= ab.1 * ab.2 := Nat.mul_le_mul_right ab.2 ha
    _ = n := hm.1

theorem mul_cutoff_of_le (f b : ArithmeticFunction R) (U n : Nat)
    (hn : n <= U) : (b * cutoff f U) n = (b * f) n := by
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro ab hab
  rw [cutoff_of_le f U ab.2 ((factor_right_le hab).trans hn)]

theorem residual_zero (f b : ArithmeticFunction R) (hfb : f * b = 1)
    (U n : Nat) (hn : n <= U) :
    (1 - b * cutoff f U) n = 0 := by
  have hbf : b * f = 1 := by rw [mul_comm]; exact hfb
  simp only [sub_eq_add_neg, ArithmeticFunction.add_apply,
    ArithmeticFunction.neg_apply]
  rw [mul_cutoff_of_le f b U n hn, hbf, add_neg_cancel]

theorem square_zero (E : ArithmeticFunction R) (U : Nat)
    (hE : forall n : Nat, n <= U -> E n = 0)
    (n : Nat) (hn : n <= U ^ 2) : (E * E) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro ab hab
  by_cases ha : ab.1 <= U
  . rw [hE ab.1 ha, zero_mul]
  . by_cases hb : ab.2 <= U
    . rw [hE ab.2 hb, mul_zero]
    . have hmul := (Nat.mem_divisorsAntidiagonal.mp hab).1
      have hprod := Nat.mul_le_mul (Nat.succ_le_of_lt (Nat.lt_of_not_ge ha))
        (Nat.succ_le_of_lt (Nat.lt_of_not_ge hb))
      exfalso
      nlinarith

theorem product_square_zero (f E : ArithmeticFunction R) (U : Nat)
    (hE : forall n : Nat, n <= U -> E n = 0)
    (n : Nat) (hn : n <= U ^ 2) : (f * (E * E)) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro ab hab
  rw [square_zero E U hE ab.2 ((factor_right_le hab).trans hn), mul_zero]

theorem truncated_inverse (f b : ArithmeticFunction R) (hfb : f * b = 1)
    (U n : Nat) (hn : n <= U ^ 2) :
    f n = cutoff f U n + cutoff f U n -
      (b * cutoff f U * cutoff f U) n := by
  let M := cutoff f U
  let E : ArithmeticFunction R := 1 - b * M
  have hz (m : Nat) (hm : m <= U) : E m = 0 :=
    residual_zero f b hfb U m hm
  have he : f * (E * E) = f - M - M + b * M * M := by
    calc
      f * (E * E) =
          f - (f * b) * M - (f * b) * M + (f * b) * b * M * M := by
        dsimp [E]
        ring
      _ = f - M - M + b * M * M := by rw [hfb]; simp
  have hid : f = M + M - b * M * M + f * (E * E) := by
    rw [he]
    ring
  have hv := congrArg (fun a : ArithmeticFunction R => a n) hid
  simp only [sub_eq_add_neg, ArithmeticFunction.add_apply,
    ArithmeticFunction.neg_apply] at hv
  rw [product_square_zero f E U hz n hn, add_zero] at hv
  simpa only [sub_eq_add_neg] using hv

theorem moebius_truncated (U n : Nat) (hn : n <= U ^ 2) :
    ArithmeticFunction.moebius n =
      cutoff ArithmeticFunction.moebius U n +
      cutoff ArithmeticFunction.moebius U n -
      ((ArithmeticFunction.zeta : ArithmeticFunction Int) *
        cutoff ArithmeticFunction.moebius U *
        cutoff ArithmeticFunction.moebius U) n :=
  truncated_inverse ArithmeticFunction.moebius
    (ArithmeticFunction.zeta : ArithmeticFunction Int)
    ArithmeticFunction.moebius_mul_coe_zeta U n hn


def coeffMap {T : Type*} [CommRing T] (phi : RingHom R T)
    (f : ArithmeticFunction R) : ArithmeticFunction T where
  toFun n := phi (f n)
  map_zero' := by simp

theorem coeffMap_apply {T : Type*} [CommRing T] (phi : RingHom R T)
    (f : ArithmeticFunction R) (n : Nat) :
    coeffMap phi f n = phi (f n) := rfl

theorem coeffMap_one {T : Type*} [CommRing T] (phi : RingHom R T) :
    coeffMap phi (1 : ArithmeticFunction R) = 1 := by
  ext n
  simp only [coeffMap_apply, ArithmeticFunction.one_apply]
  split_ifs <;> simp

theorem coeffMap_mul {T : Type*} [CommRing T] (phi : RingHom R T)
    (f g : ArithmeticFunction R) :
    coeffMap phi (f * g) = coeffMap phi f * coeffMap phi g := by
  ext n
  simp only [coeffMap_apply, ArithmeticFunction.mul_apply, map_sum, map_mul]

theorem coeffMap_inverse {T : Type*} [CommRing T] (phi : RingHom R T)
    (f b : ArithmeticFunction R) (hfb : f * b = 1) :
    coeffMap phi f * coeffMap phi b = 1 := by
  rw [<- coeffMap_mul, hfb, coeffMap_one]

def mobiusCoeff : ArithmeticFunction R :=
  coeffMap (Int.castRingHom R) ArithmeticFunction.moebius

def zetaCoeff : ArithmeticFunction R :=
  coeffMap (Int.castRingHom R)
    (ArithmeticFunction.zeta : ArithmeticFunction Int)

theorem base_inverse : (mobiusCoeff : ArithmeticFunction R) * zetaCoeff = 1 :=
  coeffMap_inverse (Int.castRingHom R) ArithmeticFunction.moebius
    (ArithmeticFunction.zeta : ArithmeticFunction Int)
    ArithmeticFunction.moebius_mul_coe_zeta

def twist (chi : MonoidHom Nat R) (f : ArithmeticFunction R) :
    ArithmeticFunction R where
  toFun n := chi n * f n
  map_zero' := by simp

theorem twist_apply (chi : MonoidHom Nat R) (f : ArithmeticFunction R) (n : Nat) :
    twist chi f n = chi n * f n := rfl

theorem twist_one (chi : MonoidHom Nat R) :
    twist chi (1 : ArithmeticFunction R) = 1 := by
  ext n
  simp only [twist_apply, ArithmeticFunction.one_apply]
  by_cases hn : n = 1
  . simp [hn]
  . simp [hn]

theorem twist_mul (chi : MonoidHom Nat R) (f g : ArithmeticFunction R) :
    twist chi (f * g) = twist chi f * twist chi g := by
  ext n
  rw [twist_apply, ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ab hab
  have hm := (Nat.mem_divisorsAntidiagonal.mp hab).1
  rw [<- hm, map_mul]
  simp only [twist_apply]
  ring

theorem twist_inverse (chi : MonoidHom Nat R) (f b : ArithmeticFunction R)
    (hfb : f * b = 1) : twist chi f * twist chi b = 1 := by
  rw [<- twist_mul, hfb, twist_one]

theorem pair_inverse (f b g c : ArithmeticFunction R)
    (hfb : f * b = 1) (hgc : g * c = 1) : (f * g) * (b * c) = 1 := by
  calc
    (f * g) * (b * c) = (f * b) * (g * c) := by ring
    _ = 1 := by rw [hfb, hgc, mul_one]

def pairMobius (chi psi : MonoidHom Nat R) : ArithmeticFunction R :=
  twist chi mobiusCoeff * twist psi mobiusCoeff

def pairZeta (chi psi : MonoidHom Nat R) : ArithmeticFunction R :=
  twist chi zetaCoeff * twist psi zetaCoeff

theorem pair_character_inverse (chi psi : MonoidHom Nat R) :
    pairMobius chi psi * pairZeta chi psi = 1 :=
  pair_inverse _ _ _ _
    (twist_inverse chi _ _ base_inverse)
    (twist_inverse psi _ _ base_inverse)

def mix {J : Type*} (A : Finset J) (w : J -> Complex)
    (f : J -> ArithmeticFunction Complex) (n : Nat) : Complex :=
  A.sum (fun j => w j * f j n)

def shortMix {J : Type*} (A : Finset J) (w : J -> Complex)
    (f : J -> ArithmeticFunction Complex) (U n : Nat) : Complex :=
  A.sum (fun j => w j * cutoff (f j) U n)

def plainMix {J : Type*} (A : Finset J) (w : J -> Complex)
    (f b : J -> ArithmeticFunction Complex) (U n : Nat) : Complex :=
  A.sum (fun j => w j * (b j * cutoff (f j) U * cutoff (f j) U) n)

theorem mix_decomposition {J : Type*} (A : Finset J) (w : J -> Complex)
    (f b : J -> ArithmeticFunction Complex)
    (hfb : forall j, Membership.mem A j -> f j * b j = 1)
    (U n : Nat) (hn : n <= U ^ 2) :
    mix A w f n = shortMix A w f U n + shortMix A w f U n -
      plainMix A w f b U n := by
  unfold mix shortMix plainMix
  calc
    A.sum (fun j => w j * f j n) =
        A.sum (fun j => w j * (cutoff (f j) U n +
          cutoff (f j) U n - (b j * cutoff (f j) U * cutoff (f j) U) n)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [truncated_inverse (f j) (b j) (hfb j hj) U n hn]
    _ = _ := by
      simp only [mul_sub, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib]

def packet (S : Finset Nat) (K : Nat -> Nat -> Complex)
    (a b : Nat -> Complex) : Complex :=
  S.sum (fun n => S.sum (fun m => K n m * a n * star (b m)))

theorem packet_decomposition (S : Finset Nat) (K : Nat -> Nat -> Complex)
    (a s t : Nat -> Complex)
    (ha : forall n, Membership.mem S n -> a n = s n + s n - t n) :
    packet S K a a =
      4 * packet S K s s - 2 * packet S K s t -
        2 * packet S K t s + packet S K t t := by
  have hp (n m : Nat) (hn : Membership.mem S n) (hm : Membership.mem S m) :
      K n m * a n * star (a m) =
        4 * (K n m * s n * star (s m)) -
        2 * (K n m * s n * star (t m)) -
        2 * (K n m * t n * star (s m)) +
          K n m * t n * star (t m) := by
    rw [ha n hn, ha m hm]
    simp only [star_sub, star_add]
    ring
  unfold packet
  calc
    S.sum (fun n => S.sum (fun m => K n m * a n * star (a m))) =
        S.sum (fun n => S.sum (fun m =>
          4 * (K n m * s n * star (s m)) -
          2 * (K n m * s n * star (t m)) -
          2 * (K n m * t n * star (s m)) +
            K n m * t n * star (t m))) := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      exact hp n m hn hm
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]

theorem family_packet {J : Type*} (A : Finset J) (w : J -> Complex)
    (f b : J -> ArithmeticFunction Complex)
    (hfb : forall j, Membership.mem A j -> f j * b j = 1)
    (U : Nat) (S : Finset Nat)
    (hS : forall n, Membership.mem S n -> n <= U ^ 2)
    (K : Nat -> Nat -> Complex) :
    packet S K (mix A w f) (mix A w f) =
      4 * packet S K (shortMix A w f U) (shortMix A w f U) -
      2 * packet S K (shortMix A w f U) (plainMix A w f b U) -
      2 * packet S K (plainMix A w f b U) (shortMix A w f U) +
        packet S K (plainMix A w f b U) (plainMix A w f b U) :=
  packet_decomposition S K _ _ _
    (fun n hn => mix_decomposition A w f b hfb U n (hS n hn))

theorem character_family_packet {J : Type*} (A : Finset J) (w : J -> Complex)
    (chi psi : J -> MonoidHom Nat Complex) (U : Nat) (S : Finset Nat)
    (hS : forall n, Membership.mem S n -> n <= U ^ 2)
    (K : Nat -> Nat -> Complex) :
    let f := fun j => pairMobius (chi j) (psi j)
    let b := fun j => pairZeta (chi j) (psi j)
    packet S K (mix A w f) (mix A w f) =
      4 * packet S K (shortMix A w f U) (shortMix A w f U) -
      2 * packet S K (shortMix A w f U) (plainMix A w f b U) -
      2 * packet S K (plainMix A w f b U) (shortMix A w f U) +
        packet S K (plainMix A w f b U) (plainMix A w f b U) := by
  exact family_packet A w _ _
    (fun j _ => pair_character_inverse (chi j) (psi j)) U S hS K

end PrimeFactorOscillations.TruncatedInversePacket
