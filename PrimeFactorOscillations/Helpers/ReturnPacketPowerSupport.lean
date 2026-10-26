/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.OddReturnCharacterSupport

/-!
# Complete power support of a prime-return packet

A packet with labels dividing P is invariant under every P-th-power
translation. Its entire signed character sum vanishes unless the
character itself has P-th power one. No character phase is discarded.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.ReturnPacketPowerSupport

open PrimeOrderReturnLaw OddReturnCharacterSupport

variable {G : Type*} [CommGroup G] [Fintype G]

local instance vacancyDecidable (L : Nat) (S : Finset Nat.Primes) (g : G) :
    Decidable (vacancy L S g) := Classical.propDecidable _

theorem packet_sum_eq_zero_of_not_power (L P : Nat) (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) L)
    (hP : forall p : S, Dvd.dvd (p.val : Nat) P)
    (hAnn : forall g : G, g ^ L = 1)
    (chi : MonoidHom G Complex)
    (hPower : Not (forall g : G, (chi g) ^ P = 1))
    (f : ((p : S) -> returnImage (G := G) L (p.val : Nat)) -> Complex) :
    Finset.univ.sum (fun g : G => f (packetProjection L S g) * chi g) = 0 := by
  classical
  choose a ha using (not_forall.mp hPower)
  let T : Complex :=
    Finset.univ.sum (fun g : G => f (packetProjection L S g) * chi g)
  have hTranslate := Equiv.sum_comp (Equiv.mulLeft (a ^ P))
    (fun g : G => f (packetProjection L S g) * chi g)
  have hScaled : (chi a) ^ P * T = T := by
    calc
      _ = Finset.univ.sum (fun g : G =>
          f (packetProjection L S (a ^ P * g)) * chi (a ^ P * g)) := by
        simp only [T, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro g _
        rw [packet_projection_fixed_by_annihilator L P S hDiv hP hAnn,
          map_mul, map_pow]
        ring
      _ = T := hTranslate
  have hProduct : ((chi a) ^ P - 1) * T = 0 := by
    rw [sub_mul, one_mul, hScaled, sub_self]
  exact (mul_eq_zero.mp hProduct).resolve_left (sub_ne_zero.mpr ha)

theorem vacancy_sum_eq_zero_of_not_power (L P : Nat) (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) L)
    (hP : forall p : S, Dvd.dvd (p.val : Nat) P)
    (hAnn : forall g : G, g ^ L = 1)
    (chi : MonoidHom G Complex)
    (hPower : Not (forall g : G, (chi g) ^ P = 1)) :
    Finset.univ.sum (fun g : G =>
      (if vacancy L S g then (1 : Complex) else 0) * chi g) = 0 := by
  classical
  let f : ((p : S) -> returnImage (G := G) L (p.val : Nat)) -> Complex :=
    fun y => if forall p : S, Not (y p = 1) then 1 else 0
  have h := packet_sum_eq_zero_of_not_power L P S hDiv hP hAnn chi hPower f
  have hWeight (g : G) : f (packetProjection L S g) =
      if vacancy L S g then (1 : Complex) else 0 := by
    dsimp [f]
    simp only [<- vacancy_iff_projection]
  simpa only [hWeight] using h

theorem vacancy_sum_eq_zero_outside_label_product
    (L : Nat) (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) L)
    (hAnn : forall g : G, g ^ L = 1)
    (chi : MonoidHom G Complex)
    (hPower : Not (forall g : G, (chi g) ^ S.prod (fun p => (p : Nat)) = 1)) :
    Finset.univ.sum (fun g : G =>
      (if vacancy L S g then (1 : Complex) else 0) * chi g) = 0 := by
  apply vacancy_sum_eq_zero_of_not_power L (S.prod (fun p => (p : Nat))) S hDiv
    (fun p => Finset.dvd_prod_of_mem (fun q : Nat.Primes => (q : Nat))
      (a := p.val) (s := S) p.property) hAnn chi hPower

theorem packet_sum_eq_zero_of_kernel_witness
    (L : Nat) (S : Finset Nat.Primes) (chi : MonoidHom G Complex)
    (hWitness : exists a : G,
      packetProjection L S a = 1 /\ Not (chi a = 1))
    (f : ((p : S) -> returnImage (G := G) L (p.val : Nat)) -> Complex) :
    Finset.univ.sum (fun g : G => f (packetProjection L S g) * chi g) = 0 := by
  classical
  choose a hA ha using hWitness
  let T : Complex :=
    Finset.univ.sum (fun g : G => f (packetProjection L S g) * chi g)
  have hTranslate := Equiv.sum_comp (Equiv.mulLeft a)
    (fun g : G => f (packetProjection L S g) * chi g)
  have hScaled : chi a * T = T := by
    calc
      _ = Finset.univ.sum (fun g : G =>
          f (packetProjection L S (a * g)) * chi (a * g)) := by
        simp only [T, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro g _
        rw [map_mul, hA, one_mul, map_mul]
        ring
      _ = T := hTranslate
  have hProduct : (chi a - 1) * T = 0 := by
    rw [sub_mul, one_mul, hScaled, sub_self]
  exact (mul_eq_zero.mp hProduct).resolve_left (sub_ne_zero.mpr ha)

theorem vacancy_sum_eq_zero_of_kernel_witness
    (L : Nat) (S : Finset Nat.Primes) (chi : MonoidHom G Complex)
    (hWitness : exists a : G,
      packetProjection L S a = 1 /\ Not (chi a = 1)) :
    Finset.univ.sum (fun g : G =>
      (if vacancy L S g then (1 : Complex) else 0) * chi g) = 0 := by
  classical
  let f : ((p : S) -> returnImage (G := G) L (p.val : Nat)) -> Complex :=
    fun y => if forall p : S, Not (y p = 1) then 1 else 0
  have h := packet_sum_eq_zero_of_kernel_witness L S chi hWitness f
  have hWeight (g : G) : f (packetProjection L S g) =
      if vacancy L S g then (1 : Complex) else 0 := by
    dsimp [f]
    simp only [<- vacancy_iff_projection]
  simpa only [hWeight] using h

end PrimeFactorOscillations.ReturnPacketPowerSupport
