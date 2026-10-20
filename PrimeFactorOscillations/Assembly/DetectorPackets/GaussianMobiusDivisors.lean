/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.UniqueFactorizationDomain.Moebius
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Assembly.DetectorPackets.GaussianResidueField

/-!
# GaussianMobiusDivisors

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
# Gaussian ideal divisor interface for the signed Mobius packet

Use the actual Gaussian ideal monoid. Norms bound the finite support;
they do not replace ideals or the coprimality masks by natural numbers.
-/


noncomputable section
namespace PrimeFactorOscillations.GaussianMobiusDivisors

abbrev G := Zsqrtd (-1)

def integerCoordinates : AddEquiv G (Prod Int Int) := by
  exact
    { toFun := fun x => Prod.mk x.re x.im
      invFun := fun x => Zsqrtd.mk x.1 x.2
      left_inv := by intro x; cases x; rfl
      right_inv := by intro x; cases x; rfl
      map_add' := by intro x y; rfl }

def integerLinearCoordinates :=
  @AddEquiv.toIntLinearEquiv G (Prod Int Int) _ _
    (inferInstance : Module Int G) (inferInstance : Module Int (Prod Int Int))
    integerCoordinates

instance gaussianFree : Module.Free Int G :=
  Module.Free.of_equiv integerLinearCoordinates.symm

instance gaussianFinite : Module.Finite Int G :=
  Module.Finite.of_surjective integerLinearCoordinates.symm.toLinearMap
    integerLinearCoordinates.symm.surjective

instance gaussianInfinite : Infinite G := by
  apply Infinite.of_injective (fun n : Int => (Zsqrtd.mk n 0 : G))
  intro a b h
  exact congrArg Zsqrtd.re h

def divisors (I : Ideal G) : Finset (Ideal G) := by
  classical
  exact (Ideal.finite_setOfPred_absNorm_le (S := G) (Ideal.absNorm I)).toFinset.filter
    (fun J => Dvd.dvd J I)

theorem mem_divisors {I J : Ideal G} (hI : Not (I = 0)) :
    Membership.mem (divisors I) J <-> Dvd.dvd J I := by
  classical
  simp only [divisors, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  constructor
  . exact And.right
  . intro hJI
    have hn : 0 < Ideal.absNorm I :=
      Nat.pos_iff_ne_zero.mpr (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
    exact And.intro (Nat.le_of_dvd hn (map_dvd Ideal.absNorm hJI)) hJI

theorem divisor_ne_zero {I J : Ideal G} (hI : Not (I = 0))
    (hJ : Membership.mem (divisors I) J) : Not (J = 0) := by
  choose K hK using (mem_divisors hI).mp hJ
  intro hJzero
  rw [hJzero, zero_mul] at hK
  exact hI hK

theorem mobius_norm_le_one (I : Ideal G) :
    norm ((UniqueFactorizationMonoid.moebius I : Int) : Complex) <= 1 := by
  classical
  by_cases hI : Squarefree I
  . simp [hI.moebius_eq]
  . simp [UniqueFactorizationMonoid.moebius_of_not_squarefree hI]


open UniqueFactorizationMonoid
open scoped Classical

/- The prime-support proof is adapted from the pinned OAI ideal Mobius
argument at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. The ring, finite
divisors, integer basis and norm instances here are Gaussian. -/

def support (I : Ideal G) : Finset (Ideal G) :=
  (normalizedFactors I).toFinset

def Included (S T : Finset (Ideal G)) : Prop :=
  forall {P : Ideal G}, Membership.mem S P -> Membership.mem T P

theorem support_prime {I P : Ideal G}
    (hP : Membership.mem (support I) P) : Prime P :=
  prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)

theorem support_product_ne_zero {I : Ideal G} {S : Finset (Ideal G)}
    (hS : Included S (support I)) : Not (S.prod id = 0) := by
  classical
  exact Finset.prod_ne_zero_iff.mpr (fun P hP => (support_prime (hS hP)).ne_zero)

theorem factors_support_product {I : Ideal G} {S : Finset (Ideal G)}
    (hS : Included S (support I)) :
    normalizedFactors (S.prod id) = S.val := by
  classical
  have hp : forall P, Membership.mem S.val P -> Prime P :=
    fun P hP => support_prime (hS hP)
  simpa using (normalizedFactors_prod_of_prime (m := S.val) hp)

theorem squarefree_support_product {I : Ideal G} {S : Finset (Ideal G)}
    (hS : Included S (support I)) : Squarefree (S.prod id) := by
  rw [squarefree_iff_nodup_normalizedFactors (support_product_ne_zero hS),
    factors_support_product hS]
  exact S.nodup

theorem support_product_dvd {I : Ideal G} (hI : Not (I = 0))
    {S : Finset (Ideal G)} (hS : Included S (support I)) :
    Dvd.dvd (S.prod id) I := by
  apply (dvd_iff_normalizedFactors_le_normalizedFactors
    (support_product_ne_zero hS) hI).mpr
  rw [factors_support_product hS]
  apply (Multiset.le_iff_subset S.nodup).mpr
  intro P hP
  exact Multiset.mem_toFinset.mp (hS hP)

theorem mobius_support_product {I : Ideal G} {S : Finset (Ideal G)}
    (hS : Included S (support I)) :
    (moebius (S.prod id) : Complex) = (-1 : Complex) ^ S.card := by
  rw [(squarefree_support_product hS).moebius_eq, factors_eq_normalizedFactors,
    factors_support_product hS]
  simp

theorem support_product_injective {I : Ideal G} {S T : Finset (Ideal G)}
    (hS : Included S (support I)) (hT : Included T (support I))
    (h : S.prod id = T.prod id) : S = T := by
  have hf := congrArg normalizedFactors h
  rw [factors_support_product hS, factors_support_product hT] at hf
  exact Finset.val_inj.mp hf

theorem squarefree_divisor_support {I J : Ideal G} (hI : Not (I = 0))
    (hJ : Squarefree J) (hJI : Dvd.dvd J I) :
    Included (support J) (support I) := by
  have hf := (dvd_iff_normalizedFactors_le_normalizedFactors hJ.ne_zero hI).mp hJI
  intro P hP
  exact Multiset.mem_toFinset.mpr
    (Multiset.mem_of_le hf (Multiset.mem_toFinset.mp hP))

theorem support_product_self {J : Ideal G} (hJ : Squarefree J) :
    (support J).prod id = J := by
  classical
  have hn : (normalizedFactors J).Nodup :=
    (squarefree_iff_nodup_normalizedFactors hJ.ne_zero).mp hJ
  have hv : (support J).val = normalizedFactors J := by
    simpa only [support, Multiset.toFinset_val] using hn.dedup
  calc
    _ = (support J).val.prod := (Finset.prod_val _).symm
    _ = (normalizedFactors J).prod := by rw [hv]
    _ = J := Ideal.prod_normalizedFactors_eq_self hJ.ne_zero

theorem squarefree_divisors_eq_image (I : Ideal G) (hI : Not (I = 0)) :
    (divisors I).filter Squarefree =
      (support I).powerset.image (fun S => S.prod id) := by
  classical
  ext J
  simp only [Finset.mem_filter, mem_divisors hI,
    Finset.mem_image, Finset.mem_powerset]
  constructor
  . intro h
    refine Exists.intro (support J) (And.intro ?_ (support_product_self h.2))
    intro P hP
    exact squarefree_divisor_support hI h.2 h.1 hP
  . intro h
    choose S hS using h
    rw [<-hS.2]
    exact And.intro
      (support_product_dvd hI (fun {P} hP => hS.1 hP))
      (squarefree_support_product (I := I) (fun {P} hP => hS.1 hP))

theorem support_empty_iff (I : Ideal G) (hI : Not (I = 0)) :
    support I = {} <-> I = 1 := by
  classical
  constructor
  . intro h
    have hz : normalizedFactors I = 0 := Multiset.toFinset_eq_empty.mp h
    have hp := Ideal.prod_normalizedFactors_eq_self hI
    rw [hz, Multiset.prod_zero] at hp
    exact hp.symm
  . intro h
    subst I
    rw [support, normalizedFactors_one]
    rfl

theorem sum_subset_sign {T : Type} [DecidableEq T] (S : Finset T) :
    S.powerset.sum (fun A => (-1 : Complex) ^ A.card) =
      if S = {} then 1 else 0 := by
  have hp := Finset.prod_sub (fun _ : T => (1 : Complex)) (fun _ => 1) S
  by_cases hS : S = {}
  . simp [hS]
  . have hc : Not (S.card = 0) :=
      Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
    simpa [hS, hc] using hp.symm

theorem sum_mobius_divisors (I : Ideal G) (hI : Not (I = 0)) :
    (divisors I).sum (fun J => (moebius J : Complex)) =
      if I = 1 then 1 else 0 := by
  classical
  have hfilter :
      (divisors I).sum (fun J => (moebius J : Complex)) =
        ((divisors I).filter Squarefree).sum (fun J => (moebius J : Complex)) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro J hJ hnot
    have hn : Not (Squarefree J) := by
      intro hsq
      exact hnot (Finset.mem_filter.mpr (And.intro hJ hsq))
    rw [moebius_of_not_squarefree hn, Int.cast_zero]
  rw [hfilter, squarefree_divisors_eq_image I hI, Finset.sum_image]
  . have heq :
        (support I).powerset.sum (fun S => (moebius (S.prod id) : Complex)) =
          (support I).powerset.sum (fun S => (-1 : Complex) ^ S.card) := by
      exact Finset.sum_congr rfl
        (fun S hS => mobius_support_product (I := I)
          (fun {P} hP => (Finset.mem_powerset.mp hS) hP))
    rw [heq, sum_subset_sign]
    simp only [support_empty_iff I hI]
  . intro S hS T hT hST
    exact support_product_injective (I := I)
      (fun {P} hP => (Finset.mem_powerset.mp hS) hP)
      (fun {P} hP => (Finset.mem_powerset.mp hT) hP) hST

def cofactor (I J : Ideal G) : Ideal G := by
  classical
  exact if h : Dvd.dvd J I then Classical.choose h else 0

theorem cofactor_spec {I J : Ideal G} (hJI : Dvd.dvd J I) :
    J * cofactor I J = I := by
  classical
  simpa only [cofactor, dite_eq_left hJI] using (Classical.choose_spec hJI).symm

theorem twisted_mobius_divisor_sum (I : Ideal G) (hI : Not (I = 0))
    (phi : MonoidHom (Ideal G) Complex) :
    (divisors I).sum (fun J =>
      (moebius J : Complex) * phi J * phi (cofactor I J)) =
        if I = 1 then 1 else 0 := by
  classical
  calc
    _ = phi I * (divisors I).sum (fun J => (moebius J : Complex)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro J hJ
      have hp : phi J * phi (cofactor I J) = phi I := by
        rw [<-map_mul, cofactor_spec ((mem_divisors hI).mp hJ)]
      calc
        _ = (moebius J : Complex) * (phi J * phi (cofactor I J)) := by ring
        _ = phi I * (moebius J : Complex) := by rw [hp]; ring
    _ = if I = 1 then 1 else 0 := by
      rw [sum_mobius_divisors I hI]
      by_cases h : I = 1
      . simp only [ite_eq_left h]
        rw [h, map_one, mul_one]
      . simp only [ite_eq_right h, mul_zero]


def masked (phi : MonoidHom (Ideal G) Complex) (B : Ideal G) :
    MonoidHom (Ideal G) Complex where
  toFun I := if IsRelPrime I B then phi I else 0
  map_one' := by
    rw [ite_eq_left isRelPrime_one_left, map_one]
  map_mul' I J := by
    by_cases hi : IsRelPrime I B <;> by_cases hj : IsRelPrime J B <;>
      simp only [IsRelPrime.mul_left_iff, hi, hj, false_and, and_false,
        true_and, and_true, ite_true, ite_false, map_mul, mul_zero, zero_mul]

theorem masked_norm_le_one (phi : MonoidHom (Ideal G) Complex)
    (hphi : forall I, norm (phi I) <= 1) (B I : Ideal G) :
    norm (masked phi B I) <= 1 := by
  classical
  change norm (if IsRelPrime I B then phi I else 0) <= 1
  by_cases h : IsRelPrime I B
  . simpa only [ite_eq_left h] using hphi I
  . simp only [ite_eq_right h, norm_zero, zero_le_one]

def normLift {q : Nat} (chi : DirichletCharacter Complex q) :
    MonoidHom (Ideal G) Complex where
  toFun I := chi (Ideal.absNorm I)
  map_one' := by rw [map_one, Nat.cast_one, map_one]
  map_mul' I J := by rw [map_mul, Nat.cast_mul, map_mul]

theorem normLift_norm_le_one {q : Nat} (chi : DirichletCharacter Complex q)
    (I : Ideal G) : norm (normLift chi I) <= 1 :=
  chi.norm_le_one (Ideal.absNorm I : ZMod q)

theorem masked_dirichlet_inverse {q : Nat}
    (chi : DirichletCharacter Complex q) (B I : Ideal G)
    (hI : Not (I = 0)) :
    (divisors I).sum (fun J =>
      (moebius J : Complex) * masked (normLift chi) B J *
        masked (normLift chi) B (cofactor I J)) =
          if I = 1 then 1 else 0 :=
  twisted_mobius_divisor_sum I hI (masked (normLift chi) B)

end PrimeFactorOscillations.GaussianMobiusDivisors
