/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelKernelCoset
import PrimeFactorOscillations.Assembly.CarmichaelPermutationKernel
import PrimeFactorOscillations.Helpers.DirichletPacketMellin

/-!
# Explicit integral Dirichlet spectrum of native return kernels

The full permutation trace is expanded over every supported subset.
Exact subgroup character sums give nonnegative integer multiplicities.
The original zero-extended natural weight and every signed finite sample
are retained, including all Mangoldt prime-power coefficients.
-/


set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelIntegralSpectrum

open PrimeOrderReturnLaw CarmichaelCorrelationLocal CarmichaelPermutationKernel
open CarmichaelCorrelation CarmichaelCorrelationSpectrum

variable {q : Nat} [NeZero q]

local instance groupDecidableEq : DecidableEq (Units (ZMod q)) :=
  Classical.typeDecidableEq _

local instance imageFintype (L l : Nat) :
    Fintype (returnImage (G := Units (ZMod q)) L l) := Fintype.ofFinite _

local instance kernelFintype (T : Finset Nat.Primes) :
    Fintype ((packetProjection (G := Units (ZMod q))
      (Monoid.exponent (Units (ZMod q))) T).ker) := Fintype.ofFinite _

def degree (T : Finset Nat.Primes) : Nat :=
  T.prod (fun p : Nat.Primes =>
    returnIndex (G := Units (ZMod q)) (Monoid.exponent (Units (ZMod q))) (p : Nat))

def cofactor (S T : Finset Nat.Primes) : Nat :=
  (S \ T).prod (fun p : Nat.Primes =>
    localCopies (returnIndex (G := Units (ZMod q))
      (Monoid.exponent (Units (ZMod q))) (p : Nat)))

def trivialOnKernel (T : Finset Nat.Primes) (chi : DirichletCharacter Complex q) : Prop :=
  forall h : (packetProjection (G := Units (ZMod q))
    (Monoid.exponent (Units (ZMod q))) T).ker, unitCharacter chi h.val = 1

local instance trivialKernelDecidable (T : Finset Nat.Primes)
    (chi : DirichletCharacter Complex q) : Decidable (trivialOnKernel T chi) :=
  Classical.propDecidable _

def multiplicity (S : Finset Nat.Primes) (chi : DirichletCharacter Complex q) : Nat := by
  classical
  exact S.powerset.sum (fun T =>
    if trivialOnKernel T chi then cofactor (q := q) S T else 0)

theorem return_product (T : Finset Nat.Primes) (g : Units (ZMod q)) :
    T.prod (fun p : Nat.Primes =>
      if g ^ (Monoid.exponent (Units (ZMod q)) / (p : Nat)) = 1
      then returnIndex (G := Units (ZMod q))
        (Monoid.exponent (Units (ZMod q))) (p : Nat) else 0) =
    if packetProjection (Monoid.exponent (Units (ZMod q))) T g = 1
      then degree (q := q) T else 0 := by
  classical
  by_cases h : packetProjection (Monoid.exponent (Units (ZMod q))) T g = 1
  . rw [ite_eq_left h]
    apply Finset.prod_congr rfl
    intro p hp
    have hReturn : g ^ (Monoid.exponent (Units (ZMod q)) / (p : Nat)) = 1 :=
      congrArg Subtype.val (congrFun h (Subtype.mk p hp))
    exact ite_eq_left hReturn
  . rw [ite_eq_right h]
    have hNot : Not (forall p : T,
        g ^ (Monoid.exponent (Units (ZMod q)) / (p.val : Nat)) = 1) := by
      intro ha
      apply h
      funext p
      exact Subtype.ext (ha p)
    choose p hp using not_forall.mp hNot
    exact Finset.prod_eq_zero p.property (ite_eq_right hp)

theorem fixed_card_powerset (S : Finset Nat.Primes) (g : Units (ZMod q)) :
    Fintype.card (PacketFixed S g) =
      S.powerset.sum (fun T => cofactor (q := q) S T *
        if packetProjection (Monoid.exponent (Units (ZMod q))) T g = 1
        then degree (q := q) T else 0) := by
  classical
  calc
    _ = S.prod (fun p : Nat.Primes =>
        Fintype.card (LocalFixed (Monoid.exponent (Units (ZMod q))) (p : Nat) g)) :=
      by simpa only [<- Nat.card_eq_fintype_card] using packetFixed_card S g
    _ = S.prod (fun p : Nat.Primes =>
        (if g ^ (Monoid.exponent (Units (ZMod q)) / (p : Nat)) = 1
         then returnIndex (G := Units (ZMod q))
           (Monoid.exponent (Units (ZMod q))) (p : Nat) else 0) +
        localCopies (returnIndex (G := Units (ZMod q))
          (Monoid.exponent (Units (ZMod q))) (p : Nat))) := by
      apply Finset.prod_congr rfl
      intro p _
      have hLocal := localFixed_card (Monoid.exponent (Units (ZMod q))) (p : Nat) g
      apply Eq.trans (by simpa only [<- Nat.card_eq_fintype_card] using hLocal)
      exact Nat.add_comm _ _
    _ = _ := by
      rw [Finset.prod_add]
      apply Finset.sum_congr rfl
      intro T _
      rw [return_product]
      exact Nat.mul_comm _ _

theorem source_card (T : Finset Nat.Primes)
    (hDiv : forall p : T,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q)))) :
    Fintype.card (Units (ZMod q)) =
      degree (q := q) T *
        Fintype.card ((packetProjection (G := Units (ZMod q))
          (Monoid.exponent (Units (ZMod q))) T).ker) := by
  have h := FiniteHomProbability.source_card
    (packetProjection (G := Units (ZMod q)) (Monoid.exponent (Units (ZMod q))) T)
    (packetProjection_surjective _ T hDiv (fun g => Monoid.pow_exponent_eq_one g))
  have hProduct :
      Fintype.card ((p : T) -> returnImage (G := Units (ZMod q))
        (Monoid.exponent (Units (ZMod q))) (p.val : Nat)) = degree (q := q) T := by
    rw [Fintype.card_pi]
    exact Finset.prod_attach T (fun p : Nat.Primes =>
      returnIndex (G := Units (ZMod q)) (Monoid.exponent (Units (ZMod q))) (p : Nat))
  simpa only [Nat.card_eq_fintype_card, hProduct] using h

theorem kernel_character_sum (T : Finset Nat.Primes)
    (chi : DirichletCharacter Complex q) :
    Finset.univ.sum (fun g : Units (ZMod q) =>
      if packetProjection (Monoid.exponent (Units (ZMod q))) T g = 1
      then unitCharacter chi g else 0) =
    Finset.univ.sum (fun h : (packetProjection (G := Units (ZMod q))
      (Monoid.exponent (Units (ZMod q))) T).ker => unitCharacter chi h.val) := by
  classical
  rw [<- Finset.sum_filter]
  apply Finset.sum_subtype
  intro g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, MonoidHom.mem_ker]

theorem regular_character_sum (T : Finset Nat.Primes)
    (hDiv : forall p : T,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q))))
    (chi : DirichletCharacter Complex q) :
    (degree (q := q) T : Complex) *
      Finset.univ.sum (fun g : Units (ZMod q) =>
        if packetProjection (Monoid.exponent (Units (ZMod q))) T g = 1
        then unitCharacter chi g else 0) =
      (Fintype.card (Units (ZMod q)) : Complex) *
        if trivialOnKernel T chi then 1 else 0 := by
  classical
  rw [kernel_character_sum]
  by_cases h : trivialOnKernel T chi
  . have hSum :
        Finset.univ.sum (fun v : (packetProjection (G := Units (ZMod q))
          (Monoid.exponent (Units (ZMod q))) T).ker => unitCharacter chi v.val) =
        (Fintype.card ((packetProjection (G := Units (ZMod q))
          (Monoid.exponent (Units (ZMod q))) T).ker) : Complex) := by
      have hValue : forall v : (packetProjection (G := Units (ZMod q))
          (Monoid.exponent (Units (ZMod q))) T).ker, unitCharacter chi v.val = 1 := h
      simp only [hValue, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [hSum, ite_eq_left h, mul_one]
    exact_mod_cast (source_card T hDiv).symm
  . rw [CarmichaelKernelCoset.restriction_sum_zero _ chi h, ite_eq_right h, mul_zero, mul_zero]


theorem fixed_card_character_sum (S : Finset Nat.Primes)
    (hDiv : forall p : S,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q))))
    (chi : DirichletCharacter Complex q) :
    Finset.univ.sum (fun g : Units (ZMod q) =>
      (Fintype.card (PacketFixed S g) : Complex) * unitCharacter chi g) =
    (Fintype.card (Units (ZMod q)) : Complex) * (multiplicity S chi : Complex) := by
  classical
  have hPoint (g : Units (ZMod q)) :
      (Fintype.card (PacketFixed S g) : Complex) * unitCharacter chi g =
      S.powerset.sum (fun T =>
        (cofactor (q := q) S T : Complex) * (degree (q := q) T : Complex) *
          if packetProjection (Monoid.exponent (Units (ZMod q))) T g = 1
          then unitCharacter chi g else 0) := by
    calc
      _ = ((S.powerset.sum (fun T => cofactor (q := q) S T *
          if packetProjection (Monoid.exponent (Units (ZMod q))) T g = 1
          then degree (q := q) T else 0) : Nat) : Complex) * unitCharacter chi g :=
        congrArg (fun n : Nat => (n : Complex) * unitCharacter chi g)
          (fixed_card_powerset S g)
      _ = _ := by
        rw [Nat.cast_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro T _
        by_cases ht : packetProjection (Monoid.exponent (Units (ZMod q))) T g = 1
        . simp only [ht, ite_true, Nat.cast_mul]
        . simp only [ht, ite_false, mul_zero, Nat.cast_zero, zero_mul]
  calc
    _ = Finset.univ.sum (fun g : Units (ZMod q) => S.powerset.sum (fun T =>
        (cofactor (q := q) S T : Complex) * (degree (q := q) T : Complex) *
          if packetProjection (Monoid.exponent (Units (ZMod q))) T g = 1
          then unitCharacter chi g else 0)) := Finset.sum_congr rfl (fun g _ => hPoint g)
    _ = S.powerset.sum (fun T => Finset.univ.sum (fun g : Units (ZMod q) =>
        (cofactor (q := q) S T : Complex) * (degree (q := q) T : Complex) *
          if packetProjection (Monoid.exponent (Units (ZMod q))) T g = 1
          then unitCharacter chi g else 0)) := Finset.sum_comm
    _ = S.powerset.sum (fun T =>
        (cofactor (q := q) S T : Complex) *
        ((Fintype.card (Units (ZMod q)) : Complex) *
          if trivialOnKernel T chi then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro T hT
      have hDivT : forall p : T,
          Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q))) := by
        intro p
        exact hDiv (Subtype.mk p.val ((Finset.mem_powerset.mp hT) p.property))
      calc
        _ = (cofactor (q := q) S T : Complex) *
            ((degree (q := q) T : Complex) * Finset.univ.sum
              (fun g : Units (ZMod q) =>
                if packetProjection (Monoid.exponent (Units (ZMod q))) T g = 1
                then unitCharacter chi g else 0)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro g _
          exact mul_assoc _ _ _
        _ = _ := congrArg (fun z : Complex => (cofactor (q := q) S T : Complex) * z)
          (regular_character_sum T hDivT chi)
    _ = _ := by
      unfold multiplicity
      rw [Nat.cast_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T _
      by_cases ht : trivialOnKernel T chi
      . simp only [ht, ite_true, mul_one]
        exact mul_comm _ _
      . simp only [ht, ite_false, Nat.cast_zero, mul_zero]

theorem normalization_mul_coefficient (S : Finset Nat.Primes)
    (hDiv : forall p : S,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q))))
    (chi : DirichletCharacter Complex q) :
    (normalization (G := Units (ZMod q)) S : Real) *
      coefficient (vacancyWeight (G := Units (ZMod q))
        (Monoid.exponent (Units (ZMod q))) S) chi =
      (multiplicity S chi : Real) := by
  let w := vacancyWeight (G := Units (ZMod q)) (Monoid.exponent (Units (ZMod q))) S
  have hn : Not ((Fintype.card (Units (ZMod q)) : Complex) = 0) := by
    exact_mod_cast Fintype.card_ne_zero
  have hCoeff : characterSum (kernel w) (unitCharacter chi) =
      (coefficient w chi : Complex) * (Fintype.card (Units (ZMod q)) : Complex) := by
    apply (div_eq_iff hn).mp
    exact kernel_coefficient_eq w (unitCharacter chi)
  have hTrace :
      (normalization (G := Units (ZMod q)) S : Complex) *
        characterSum (kernel w) (unitCharacter chi) =
      (Fintype.card (Units (ZMod q)) : Complex) * (multiplicity S chi : Complex) := by
    calc
      _ = Finset.univ.sum (fun g : Units (ZMod q) =>
          ((normalization (G := Units (ZMod q)) S : Complex) * (kernel w g : Complex)) *
            unitCharacter chi g) := by
        unfold characterSum
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro g _
        exact (mul_assoc _ _ _).symm
      _ = Finset.univ.sum (fun g : Units (ZMod q) =>
          (Fintype.card (PacketFixed S g) : Complex) * unitCharacter chi g) := by
        apply Finset.sum_congr rfl
        intro g _
        apply congrArg (fun z : Complex => z * unitCharacter chi g)
        have hScale : (normalization (G := Units (ZMod q)) S : Real) * kernel w g =
            (Fintype.card (PacketFixed S g) : Real) := by
          simpa only [<- Nat.card_eq_fintype_card] using scaled_kernel_eq_fixed_card S hDiv g
        exact_mod_cast hScale
      _ = _ := fixed_card_character_sum S hDiv chi
  have hComplex :
      (normalization (G := Units (ZMod q)) S : Complex) * (coefficient w chi : Complex) =
        (multiplicity S chi : Complex) := by
    have hProduct :
        (Fintype.card (Units (ZMod q)) : Complex) *
          ((normalization (G := Units (ZMod q)) S : Complex) * (coefficient w chi : Complex) -
            (multiplicity S chi : Complex)) = 0 := by
      calc
        _ = (normalization (G := Units (ZMod q)) S : Complex) *
            characterSum (kernel w) (unitCharacter chi) -
            (Fintype.card (Units (ZMod q)) : Complex) * (multiplicity S chi : Complex) := by
          rw [hCoeff]
          ring
        _ = 0 := sub_eq_zero.mpr hTrace
    exact sub_eq_zero.mp ((mul_eq_zero.mp hProduct).resolve_left hn)
  exact_mod_cast hComplex

theorem multiplicity_principal (S : Finset Nat.Primes)
    (hDiv : forall p : S,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q)))) :
    multiplicity S (1 : DirichletCharacter Complex q) =
      normalization (G := Units (ZMod q)) S := by
  have h := normalization_mul_coefficient S hDiv (1 : DirichletCharacter Complex q)
  rw [coefficient_principal _ (canonical_vacancy_weightSum_pos S hDiv), mul_one] at h
  exact_mod_cast h.symm

theorem odd_multiplicity_quadratic_zero (S : Finset Nat.Primes)
    (hDiv : forall p : S,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q))))
    (hOdd : forall p : S, Not ((p.val : Nat) = 2))
    (chi : DirichletCharacter Complex q) (hChi : Not (chi = 1))
    (hSquare : forall u : Units (ZMod q), (chi (u : ZMod q)) ^ 2 = 1) :
    multiplicity S chi = 0 := by
  have h := normalization_mul_coefficient S hDiv chi
  rw [odd_vacancy_coefficient_zero q S hDiv hOdd chi hChi hSquare, mul_zero] at h
  exact_mod_cast h.symm


theorem coefficient_eq_multiplicity_div (S : Finset Nat.Primes)
    (hDiv : forall p : S,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q))))
    (chi : DirichletCharacter Complex q) :
    coefficient (vacancyWeight (G := Units (ZMod q))
      (Monoid.exponent (Units (ZMod q))) S) chi =
      (multiplicity S chi : Real) / (normalization (G := Units (ZMod q)) S : Real) := by
  have hM : Not ((normalization (G := Units (ZMod q)) S : Real) = 0) := by
    exact_mod_cast Nat.ne_of_gt (normalization_pos S hDiv)
  apply (eq_div_iff hM).mpr
  simpa only [mul_comm] using normalization_mul_coefficient S hDiv chi

theorem nonzero_coefficient_lower (S : Finset Nat.Primes)
    (hDiv : forall p : S,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q))))
    (chi : DirichletCharacter Complex q)
    (hNonzero : Not (coefficient (vacancyWeight (G := Units (ZMod q))
      (Monoid.exponent (Units (ZMod q))) S) chi = 0)) :
    (1 : Real) / (normalization (G := Units (ZMod q)) S : Real) <=
      coefficient (vacancyWeight (G := Units (ZMod q))
        (Monoid.exponent (Units (ZMod q))) S) chi := by
  have hM : (0 : Real) < normalization (G := Units (ZMod q)) S := by
    exact_mod_cast normalization_pos S hDiv
  have hMu : Not (multiplicity S chi = 0) := by
    intro h
    apply hNonzero
    rw [coefficient_eq_multiplicity_div S hDiv chi, h, Nat.cast_zero, zero_div]
  have hMuReal : (1 : Real) <= multiplicity S chi := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hMu
  rw [coefficient_eq_multiplicity_div S hDiv chi]
  exact (div_le_div_iff_of_pos_right hM).mpr hMuReal

theorem kernel_inverse (S : Finset Nat.Primes)
    (hDiv : forall p : S,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q))))
    (g : Units (ZMod q)) :
    kernel (vacancyWeight (G := Units (ZMod q))
      (Monoid.exponent (Units (ZMod q))) S) (Inv.inv g) =
    kernel (vacancyWeight (G := Units (ZMod q))
      (Monoid.exponent (Units (ZMod q))) S) g := by
  calc
    _ = S.prod (fun p : Nat.Primes =>
        CarmichaelCorrelationLocal.localFactor
          (returnIndex (G := Units (ZMod q)) (Monoid.exponent (Units (ZMod q))) (p : Nat))
          (CarmichaelCorrelationLocal.returnBit
            (Monoid.exponent (Units (ZMod q))) (p : Nat) (Inv.inv g))) :=
      CarmichaelSupportRigidity.canonical_product_over_labels S hDiv _
    _ = S.prod (fun p : Nat.Primes =>
        CarmichaelCorrelationLocal.localFactor
          (returnIndex (G := Units (ZMod q)) (Monoid.exponent (Units (ZMod q))) (p : Nat))
          (CarmichaelCorrelationLocal.returnBit
            (Monoid.exponent (Units (ZMod q))) (p : Nat) g)) := by
      apply Finset.prod_congr rfl
      intro p _
      simp only [CarmichaelCorrelationLocal.returnBit, inv_pow, inv_eq_one]
    _ = _ := (CarmichaelSupportRigidity.canonical_product_over_labels S hDiv g).symm

theorem integer_character_expansion (S : Finset Nat.Primes)
    (hDiv : forall p : S,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q))))
    (g : Units (ZMod q)) :
    (normalization (G := Units (ZMod q)) S : Complex) *
      (kernel (vacancyWeight (G := Units (ZMod q))
        (Monoid.exponent (Units (ZMod q))) S) g : Complex) =
    Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
      (multiplicity S chi : Complex) * unitCharacter chi g) := by
  let w := vacancyWeight (G := Units (ZMod q)) (Monoid.exponent (Units (ZMod q))) S
  have hExpand := kernel_expansion w (Inv.inv g)
  change (kernel (vacancyWeight (G := Units (ZMod q))
    (Monoid.exponent (Units (ZMod q))) S) (Inv.inv g) : Complex) = _ at hExpand
  rw [kernel_inverse S hDiv g, inv_inv] at hExpand
  calc
    _ = (normalization (G := Units (ZMod q)) S : Complex) *
      Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
        (coefficient w chi : Complex) * unitCharacter chi g) :=
      congrArg (fun z : Complex => (normalization (G := Units (ZMod q)) S : Complex) * z)
        hExpand
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro chi _
      have hMu :
          (normalization (G := Units (ZMod q)) S : Complex) * (coefficient w chi : Complex) =
          (multiplicity S chi : Complex) := by
        exact_mod_cast normalization_mul_coefficient S hDiv chi
      rw [<- mul_assoc, hMu]


theorem natural_character_expansion (S : Finset Nat.Primes)
    (hDiv : forall p : S,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q)))) (n : Nat) :
    (normalization (G := Units (ZMod q)) S : Complex) *
      (carmichaelPrimeWeight q S n : Complex) =
    Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
      (multiplicity S chi : Complex) * chi (n : ZMod q)) := by
  classical
  by_cases hn : Nat.Coprime n q
  . simp only [carmichaelPrimeWeight, dite_eq_left hn]
    have h := integer_character_expansion S hDiv (ZMod.unitOfCoprime n hn)
    apply Eq.trans h
    apply Finset.sum_congr rfl
    intro chi _
    apply congrArg (fun z : Complex => (multiplicity S chi : Complex) * z)
    change chi ((ZMod.unitOfCoprime n hn : Units (ZMod q)) : ZMod q) = chi (n : ZMod q)
    exact congrArg chi (ZMod.coe_unitOfCoprime n hn)
  . simp only [carmichaelPrimeWeight, dite_eq_right hn, Complex.ofReal_zero, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro chi _
    have hNonunit : Not (IsUnit (n : ZMod q)) := by
      intro h
      exact hn ((ZMod.isUnit_iff_coprime n q).mp h)
    rw [MulChar.map_nonunit chi hNonunit, mul_zero]

theorem mangoldt_coefficient_expansion (S : Finset Nat.Primes)
    (hDiv : forall p : S,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q)))) (n : Nat) :
    ((normalization (G := Units (ZMod q)) S : Complex) *
      (carmichaelPrimeWeight q S n : Complex)) * (ArithmeticFunction.vonMangoldt n : Complex) =
    Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
      (multiplicity S chi : Complex) * DirichletPacketMellin.coefficient chi n) := by
  rw [natural_character_expansion S hDiv n, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro chi _
  exact mul_assoc _ _ _

theorem signed_finite_packet (S : Finset Nat.Primes)
    (hDiv : forall p : S,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q))))
    (T : Finset Nat) (f : Nat -> Complex) :
    T.sum (fun n =>
      ((normalization (G := Units (ZMod q)) S : Complex) *
        (carmichaelPrimeWeight q S n : Complex)) * f n) =
    Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
      (multiplicity S chi : Complex) * T.sum (fun n => chi (n : ZMod q) * f n)) := by
  calc
    _ = T.sum (fun n => Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
        (multiplicity S chi : Complex) * (chi (n : ZMod q) * f n))) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [natural_character_expansion S hDiv n, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro chi _
      exact mul_assoc _ _ _
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro chi _
      exact (Finset.mul_sum T (fun n => chi (n : ZMod q) * f n)
        (multiplicity S chi : Complex)).symm

end PrimeFactorOscillations.CarmichaelIntegralSpectrum
