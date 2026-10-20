/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.RamanujanProductEnergy

/-!
# RamanujanMobiusTransfer

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

set_option maxHeartbeats 2200000

noncomputable section
namespace OAI.SevenEighths.RamanujanIncidenceGram
open scoped Classical BigOperators
open IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem signed_subset_expansion {I : Type*} [DecidableEq I]
    (S : Finset I) (q : I -> Complex) (b : I -> Prop) [DecidablePred b] :
    (S.prod fun p => if b p then q p - 1 else -1) =
      (-1 : Complex) ^ S.card *
        ((S.filter b).powerset.sum fun T =>
          (-1 : Complex) ^ T.card * T.prod q) := by
  have hp : (S.prod fun p => if b p then q p - 1 else -1) =
      (-1 : Complex) ^ S.card * (S.filter b).prod (fun p => 1 - q p) := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert p S hp ih =>
      by_cases hb : b p
      . simp [hp, hb, Finset.filter_insert, ih, pow_succ] <;> ring
      . simp [hp, hb, Finset.filter_insert, ih, pow_succ] <;> ring
  rw [hp]
  congr 1
  rw [show (fun p => 1 - q p) = (fun p => 1 + -q p) from rfl,
    Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro T _
  have ht : T.prod (fun p => -q p) = T.prod (fun p => (-1 : Complex) * q p) := by
    apply Finset.prod_congr rfl
    intro p _
    ring
  rw [ht, Finset.prod_mul_distrib, Finset.prod_const]

theorem common_divisors_image (A Q : Id) (hA : Not (A = 0)) (hQ : Squarefree Q) :
    (idealDivisors Q).filter (fun D => Dvd.dvd D A) =
      ((primeSupport Q).filter (fun P => Dvd.dvd P A)).powerset.image
        (fun T => T.prod id) := by
  ext D
  constructor
  . intro hD
    have hDQ := (mem_idealDivisors hQ.ne_zero).mp (Finset.mem_filter.mp hD).1
    have hDA := (Finset.mem_filter.mp hD).2
    have hsf := Squarefree.squarefree_of_dvd hDQ hQ
    have hSQ := squarefree_divisor_support hQ.ne_zero hsf hDQ
    have hSA := squarefree_divisor_support hA hsf hDA
    apply Finset.mem_image.mpr
    refine Exists.intro (primeSupport D) (And.intro ?_ ?_)
    . apply Finset.mem_powerset.mpr
      intro P hP
      apply Finset.mem_filter.mpr
      exact And.intro (hSQ hP)
        ((mem_normalizedFactors_iff hA).mp (Multiset.mem_toFinset.mp (hSA hP))).2
    . exact squarefree_support_product_self hsf
  . intro hD
    choose T hT he using Finset.mem_image.mp hD
    have hTS := Finset.mem_powerset.mp hT
    have hTQ : forall P, Membership.mem T P -> Membership.mem (primeSupport Q) P :=
      fun P hP => (Finset.mem_filter.mp (hTS hP)).1
    have hTA : forall P, Membership.mem T P -> Membership.mem (primeSupport A) P := by
      intro P hP
      have hh := Finset.mem_filter.mp (hTS hP)
      exact Multiset.mem_toFinset.mpr
        ((mem_normalizedFactors_iff hA).mpr (And.intro (support_prime hh.1) hh.2))
    rw [<-he]
    exact Finset.mem_filter.mpr (And.intro
      ((mem_idealDivisors hQ.ne_zero).mpr (support_product_dvd hQ.ne_zero hTQ))
      (support_product_dvd hA hTA))

theorem primeNumerator_mobius (A Q : Id) (hA : Not (A = 0)) (hQ : Squarefree Q) :
    (primeNumerator A Q : Complex) =
      (moebius Q : Complex) *
        ((idealDivisors Q).filter (fun D => Dvd.dvd D A)).sum
          (fun D => (moebius D : Complex) * (D.absNorm : Complex)) := by
  let S := (primeSupport Q).filter (fun P => Dvd.dvd P A)
  have hSQ : forall P, Membership.mem S P -> Membership.mem (primeSupport Q) P :=
    fun P hP => (Finset.mem_filter.mp hP).1
  have hsum :
      ((idealDivisors Q).filter (fun D => Dvd.dvd D A)).sum
        (fun D => (moebius D : Complex) * (D.absNorm : Complex)) =
      S.powerset.sum (fun T => (-1 : Complex) ^ T.card *
        T.prod (fun P => (P.absNorm : Complex))) := by
    rw [common_divisors_image A Q hA hQ, Finset.sum_image]
    . apply Finset.sum_congr rfl
      intro T hT
      have hTQ := fun P hP => hSQ P ((Finset.mem_powerset.mp hT) hP)
      change (moebius (T.prod fun P => P) : Complex) *
        (Ideal.absNorm (T.prod fun P => P) : Complex) = _
      rw [moebius_support_product hTQ]
      simp only [map_prod, Nat.cast_prod, id_eq]
    . intro T hT U hU he
      exact support_product_injective
        (fun P hP => hSQ P ((Finset.mem_powerset.mp hT) hP))
        (fun P hP => hSQ P ((Finset.mem_powerset.mp hU) hP)) he
  have hmu : (moebius Q : Complex) = (-1 : Complex) ^ (primeSupport Q).card := by
    have he := moebius_support_product (I := Q) (S := primeSupport Q) (fun _ h => h)
    rw [squarefree_support_product_self hQ] at he
    exact he
  have hc : (primeNumerator A Q : Complex) =
      (primeSupport Q).prod (fun P => if Dvd.dvd P A then (P.absNorm : Complex) - 1 else -1) := by
    rw [primeNumerator, Complex.ofReal_prod]
    apply Finset.prod_congr rfl
    intro P _
    split_ifs <;> simp only [Complex.ofReal_sub, Complex.ofReal_natCast,
      Complex.ofReal_one, Complex.ofReal_neg]
  rw [hc, hmu, hsum]
  exact signed_subset_expansion (primeSupport Q) (fun P => (P.absNorm : Complex))
    (fun P => Dvd.dvd P A)

theorem primePacket_signed_divisors (A Q : Id) (hA : Not (A = 0)) (hQ : Squarefree Q) :
    primePacket A Q =
      (moebius Q : Complex) / (Real.sqrt (Q.absNorm : Real) : Complex) *
        (idealDivisors A).sum (fun D =>
          if Dvd.dvd D Q then (moebius D : Complex) * (D.absNorm : Complex) else 0) := by
  have hset :
      (idealDivisors Q).filter (fun D => Dvd.dvd D A) =
        (idealDivisors A).filter (fun D => Dvd.dvd D Q) := by
    ext D
    simp only [Finset.mem_filter, mem_idealDivisors hA,
      mem_idealDivisors hQ.ne_zero, and_comm]
  rw [primePacket, primeNumerator_mobius A Q hA hQ, hset, Finset.sum_filter]
  ring

theorem finite_mobius_transfer (A : Id) (hA : Not (A = 0)) (C : Finset Id)
    (hC : forall Q, Membership.mem C Q -> Squarefree Q) (b : Id -> Complex) :
    (C.sum fun Q => b Q * primePacket A Q) =
      (idealDivisors A).sum (fun D => (moebius D : Complex) * (D.absNorm : Complex) *
        ((C.filter fun Q => Dvd.dvd D Q).sum fun Q =>
          b Q * (moebius Q : Complex) / (Real.sqrt (Q.absNorm : Real) : Complex))) := by
  calc
    _ = C.sum (fun Q => (idealDivisors A).sum fun D =>
        (moebius D : Complex) * (D.absNorm : Complex) *
          (if Dvd.dvd D Q then
            b Q * (moebius Q : Complex) / (Real.sqrt (Q.absNorm : Real) : Complex)
          else 0)) := by
      apply Finset.sum_congr rfl
      intro Q hQ
      rw [primePacket_signed_divisors A Q hA (hC Q hQ), Finset.mul_sum,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro D _
      split_ifs <;> ring
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro D _
      rw [Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro Q _
      split_ifs <;> ring

end OAI.SevenEighths.RamanujanIncidenceGram
