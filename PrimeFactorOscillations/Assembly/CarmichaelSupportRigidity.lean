/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelAscentCriterion
import PrimeFactorOscillations.Assembly.CarmichaelCorrelationFloor

/-!
# Zero-support rigidity for every active native return packet

All odd labels retain a uniformly positive factor in the complete kernel.
The only possible zero is the label-two factor at return index two.
A nonzero full kernel has a uniform positive gap, independent of the group.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelSupportRigidity

open CarmichaelCorrelation CarmichaelCorrelationLocal CarmichaelCorrelationFloor
open PrimeOrderReturnLaw

variable {G : Type*} [CommGroup G] [Fintype G]

def twoLabel : Nat.Primes := Subtype.mk 2 (by decide)

theorem canonical_product_over_labels (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent G)) (g : G) :
    kernel (vacancyWeight (G := G) (Monoid.exponent G) S) g =
      S.prod (fun p : Nat.Primes =>
        localFactor (returnIndex (G := G) (Monoid.exponent G) (p : Nat))
          (returnBit (Monoid.exponent G) (p : Nat) g)) := by
  rw [canonical_kernel_eq_product S hDiv]
  exact Finset.prod_attach S (fun p : Nat.Primes =>
    localFactor (returnIndex (G := G) (Monoid.exponent G) (p : Nat))
      (returnBit (Monoid.exponent G) (p : Nat) g))

theorem kernel_ge_half_of_two_not_mem (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent G))
    (hTwo : Not (Membership.mem S twoLabel)) (g : G) :
    (1 / 2 : Real) <= kernel (vacancyWeight (G := G) (Monoid.exponent G) S) g := by
  apply canonical_odd_kernel_ge_half S hDiv
  intro p hEq
  have hp : p.val = twoLabel := Subtype.ext hEq
  apply hTwo
  simpa only [hp] using p.property

theorem erase_two_kernel_floor (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent G)) (g : G) :
    (1 / 2 : Real) <=
      kernel (vacancyWeight (G := G) (Monoid.exponent G) (S.erase twoLabel)) g := by
  have hErase : forall p : S.erase twoLabel,
      Dvd.dvd (p.val : Nat) (Monoid.exponent G) := by
    intro p
    exact hDiv (Subtype.mk p.val (Finset.mem_erase.mp p.property).2)
  apply kernel_ge_half_of_two_not_mem (S.erase twoLabel) hErase
  intro h
  exact (Finset.mem_erase.mp h).1 rfl

theorem kernel_split_two (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent G))
    (hTwo : Membership.mem S twoLabel) (g : G) :
    kernel (vacancyWeight (G := G) (Monoid.exponent G) S) g =
      localFactor (returnIndex (G := G) (Monoid.exponent G) 2)
        (returnBit (Monoid.exponent G) 2 g) *
      kernel (vacancyWeight (G := G) (Monoid.exponent G) (S.erase twoLabel)) g := by
  classical
  have hErase : forall p : S.erase twoLabel,
      Dvd.dvd (p.val : Nat) (Monoid.exponent G) := by
    intro p
    exact hDiv (Subtype.mk p.val (Finset.mem_erase.mp p.property).2)
  rw [canonical_product_over_labels S hDiv,
    canonical_product_over_labels (S.erase twoLabel) hErase]
  let f : Nat.Primes -> Real := fun p =>
    localFactor (returnIndex (G := G) (Monoid.exponent G) (p : Nat))
      (returnBit (Monoid.exponent G) (p : Nat) g)
  change S.prod f = f twoLabel * (S.erase twoLabel).prod f
  have hNot : Not (Membership.mem (S.erase twoLabel) twoLabel) := by
    intro h
    exact (Finset.mem_erase.mp h).1 rfl
  have hProduct : (insert twoLabel (S.erase twoLabel)).prod f =
      f twoLabel * (S.erase twoLabel).prod f := Finset.prod_insert hNot
  rw [Finset.insert_erase hTwo] at hProduct
  exact hProduct

theorem localFactor_ge_three_quarters (d : Nat) (hd : 3 <= d) (b : Bool) :
    (3 / 4 : Real) <= localFactor d b := by
  have hdR : (3 : Real) <= d := by exact_mod_cast hd
  have hSq : (4 : Real) <= ((d : Real) - 1) ^ 2 := by nlinarith
  have hInv := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 4) hSq
  have hLower := localFactor_lower d (by omega : 2 <= d) b
  norm_num at hInv
  simp only [one_div] at hLower
  linarith

theorem localFactor_zero_iff (d : Nat) (hd : 2 <= d) (b : Bool) :
    localFactor d b = 0 <-> d = 2 /\ b = false := by
  by_cases hTwo : d = 2
  . subst d
    cases b <;> norm_num [localFactor]
  . have hLower := localFactor_ge_three_quarters d (by omega : 3 <= d) b
    constructor
    . intro hZero
      rw [hZero] at hLower
      norm_num at hLower
    . intro h
      exact False.elim (hTwo h.1)

theorem localFactor_nonzero_gap (d : Nat) (hd : 2 <= d) (b : Bool)
    (hNonzero : Not (localFactor d b = 0)) :
    (3 / 4 : Real) <= localFactor d b := by
  by_cases hTwo : d = 2
  . subst d
    cases b
    . exact False.elim (hNonzero (by norm_num [localFactor]))
    . norm_num [localFactor]
  . exact localFactor_ge_three_quarters d (by omega) b

theorem canonical_kernel_zero_iff (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent G)) (g : G) :
    kernel (vacancyWeight (G := G) (Monoid.exponent G) S) g = 0 <->
      Membership.mem S twoLabel /\
        returnIndex (G := G) (Monoid.exponent G) 2 = 2 /\
          returnBit (Monoid.exponent G) 2 g = false := by
  by_cases hTwo : Membership.mem S twoLabel
  . have hSplit := kernel_split_two S hDiv hTwo g
    have hOdd := erase_two_kernel_floor S hDiv g
    have hOddNot : Not
        (kernel (vacancyWeight (G := G) (Monoid.exponent G) (S.erase twoLabel)) g = 0) :=
      ne_of_gt (by linarith)
    have hD : 2 <= returnIndex (G := G) (Monoid.exponent G) 2 :=
      divisor_le_returnIndex (G := G) 2 (hDiv (Subtype.mk twoLabel hTwo))
    constructor
    . intro hZero
      rw [hSplit] at hZero
      have hFactor := (mul_eq_zero.mp hZero).resolve_right hOddNot
      exact And.intro hTwo ((localFactor_zero_iff _ hD _).mp hFactor)
    . intro h
      rw [hSplit, (localFactor_zero_iff _ hD _).mpr h.2, zero_mul]
  . constructor
    . intro hZero
      have hLower := kernel_ge_half_of_two_not_mem S hDiv hTwo g
      rw [hZero] at hLower
      norm_num at hLower
    . intro h
      exact False.elim (hTwo h.1)

theorem canonical_kernel_nonzero_gap (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent G)) (g : G)
    (hNonzero : Not (kernel (vacancyWeight (G := G) (Monoid.exponent G) S) g = 0)) :
    (3 / 8 : Real) <= kernel (vacancyWeight (G := G) (Monoid.exponent G) S) g := by
  by_cases hTwo : Membership.mem S twoLabel
  . have hSplit := kernel_split_two S hDiv hTwo g
    have hOdd := erase_two_kernel_floor S hDiv g
    have hD : 2 <= returnIndex (G := G) (Monoid.exponent G) 2 :=
      divisor_le_returnIndex (G := G) 2 (hDiv (Subtype.mk twoLabel hTwo))
    have hFactorNot : Not (localFactor
        (returnIndex (G := G) (Monoid.exponent G) 2)
        (returnBit (Monoid.exponent G) 2 g) = 0) := by
      intro h
      apply hNonzero
      rw [hSplit, h, zero_mul]
    have hLocal := localFactor_nonzero_gap _ hD _ hFactorNot
    calc
      (3 / 8 : Real) = (3 / 4 : Real) * (1 / 2) := by norm_num
      _ <= localFactor (returnIndex (G := G) (Monoid.exponent G) 2)
          (returnBit (Monoid.exponent G) 2 g) *
          kernel (vacancyWeight (G := G) (Monoid.exponent G) (S.erase twoLabel)) g :=
        mul_le_mul hLocal hOdd (by norm_num) (by linarith)
      _ = _ := hSplit.symm
  . have hLower := kernel_ge_half_of_two_not_mem S hDiv hTwo g
    linarith

theorem canonical_kernel_same_zero_set (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent G))
    (hTwo : Membership.mem S twoLabel) (g : G) :
    kernel (vacancyWeight (G := G) (Monoid.exponent G) S) g = 0 <->
      kernel (vacancyWeight (G := G) (Monoid.exponent G) {twoLabel}) g = 0 := by
  have hSingle : forall p : ({twoLabel} : Finset Nat.Primes),
      Dvd.dvd (p.val : Nat) (Monoid.exponent G) := by
    intro p
    have hEq : p.val = twoLabel := Finset.mem_singleton.mp p.property
    simpa only [hEq] using hDiv (Subtype.mk twoLabel hTwo)
  rw [canonical_kernel_zero_iff S hDiv g, canonical_kernel_zero_iff {twoLabel} hSingle g]
  simp only [hTwo, Finset.mem_singleton_self, true_and]

theorem canonical_kernel_zero_iff_not_return (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent G)) (g : G) :
    kernel (vacancyWeight (G := G) (Monoid.exponent G) S) g = 0 <->
      Membership.mem S twoLabel /\
        returnIndex (G := G) (Monoid.exponent G) 2 = 2 /\
          Not (g ^ (Monoid.exponent G / 2) = 1) := by
  rw [canonical_kernel_zero_iff S hDiv g]
  simp only [returnBit, decide_eq_false_iff_not]

theorem primeWeight_same_zero_set (q : Nat) [NeZero q] (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q))))
    (hTwo : Membership.mem S twoLabel) (n : Nat) :
    carmichaelPrimeWeight q S n = 0 <->
      carmichaelPrimeWeight q {twoLabel} n = 0 := by
  classical
  by_cases hn : Nat.Coprime n q
  . simp only [carmichaelPrimeWeight, dite_eq_left hn]
    exact canonical_kernel_same_zero_set S hDiv hTwo (ZMod.unitOfCoprime n hn)
  . simp only [carmichaelPrimeWeight, dite_eq_right hn]

theorem primeWeight_nonzero_gap (q : Nat) [NeZero q] (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q))))
    (n : Nat) (hNonzero : Not (carmichaelPrimeWeight q S n = 0)) :
    (3 / 8 : Real) <= carmichaelPrimeWeight q S n := by
  classical
  by_cases hn : Nat.Coprime n q
  . simp only [carmichaelPrimeWeight, dite_eq_left hn] at hNonzero
    simpa only [carmichaelPrimeWeight, dite_eq_left hn] using
      canonical_kernel_nonzero_gap S hDiv (ZMod.unitOfCoprime n hn) hNonzero
  . exact False.elim (hNonzero
      (carmichaelPrimeWeight_eq_zero_of_not_coprime q S n hn))

theorem primeWeight_nonneg_all_packets (q : Nat) [NeZero q] (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q))))
    (n : Nat) : 0 <= carmichaelPrimeWeight q S n := by
  by_cases h : carmichaelPrimeWeight q S n = 0
  . rw [h]
  . exact (by norm_num : (0 : Real) <= 3 / 8).trans
      (primeWeight_nonzero_gap q S hDiv n h)

theorem primeWeight_support_mass_lower {I : Type*} (q : Nat) [NeZero q]
    (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q))))
    (T : Finset I) (n : I -> Nat) :
    (3 / 8 : Real) *
      ((T.filter (fun i => Not (carmichaelPrimeWeight q S (n i) = 0))).card : Real) <=
        T.sum (fun i => carmichaelPrimeWeight q S (n i)) := by
  classical
  let R := T.filter (fun i => Not (carmichaelPrimeWeight q S (n i) = 0))
  have hCount : (3 / 8 : Real) * (R.card : Real) =
      R.sum (fun _ : I => (3 / 8 : Real)) := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  have hSum : R.sum (fun i => carmichaelPrimeWeight q S (n i)) =
      T.sum (fun i => carmichaelPrimeWeight q S (n i)) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hNot
    by_contra hNZ
    apply hNot
    exact Finset.mem_filter.mpr (And.intro hi hNZ)
  calc
    _ = R.sum (fun _ : I => (3 / 8 : Real)) := hCount
    _ <= R.sum (fun i => carmichaelPrimeWeight q S (n i)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact primeWeight_nonzero_gap q S hDiv (n i) (Finset.mem_filter.mp hi).2
    _ = _ := hSum

end PrimeFactorOscillations.CarmichaelSupportRigidity
