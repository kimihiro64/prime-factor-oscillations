/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelCorrelation

/-!
# Exact local factors of the two-base return kernel

Both vacancy events use the same base. Their full intersection is pushed
through the proved simultaneous return map. Every overlap is retained.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelCorrelationLocal

open CarmichaelCorrelation PrimeOrderReturnLaw FiniteHomProbability

variable {G : Type*} [CommGroup G] [Fintype G]

local instance groupDecidableEq : DecidableEq G := Classical.typeDecidableEq G

local instance imageFintype (L l : Nat) : Fintype (returnImage (G := G) L l) :=
  PrimeOrderReturnLaw.imageFintype L l

def coordinatePairSet (L l : Nat) (z : returnImage (G := G) L l) :
    Finset (returnImage (G := G) L l) := by
  classical
  exact (Finset.univ.erase 1).erase (Inv.inv z)

theorem coordinatePairSet_mem (L l : Nat) (z x : returnImage (G := G) L l) :
    Membership.mem (coordinatePairSet L l z) x <->
      And (Not (x = 1)) (Not (x * z = 1)) := by
  classical
  have hEq : x = Inv.inv z <-> x * z = 1 := by
    constructor
    . intro h
      rw [h, inv_mul_cancel]
    . intro h
      have ht := congrArg (fun y : returnImage (G := G) L l => y * Inv.inv z) h
      simpa only [mul_assoc, mul_inv_cancel, mul_one, one_mul] using ht
  simp only [coordinatePairSet, Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  . intro h
    exact And.intro h.2 (fun ht => h.1 (hEq.mpr ht))
  . intro h
    exact And.intro (fun ht => h.2 (hEq.mp ht)) h.1

theorem coordinatePairSet_card (L l : Nat) (z : returnImage (G := G) L l) :
    (coordinatePairSet L l z).card =
      if z = 1 then returnIndex (G := G) L l - 1 else returnIndex (G := G) L l - 2 := by
  classical
  by_cases hz : z = 1
  . subst z
    simp [coordinatePairSet, returnIndex]
  . have hMem : Membership.mem
        (Finset.univ.erase (1 : returnImage (G := G) L l)) (Inv.inv z) := by
      simp [hz]
    rw [coordinatePairSet, Finset.card_erase_of_mem hMem,
      Finset.card_erase_of_mem (Finset.mem_univ (1 : returnImage (G := G) L l)),
      ite_eq_right hz]
    change (Fintype.card (returnImage (G := G) L l) - 1) - 1 =
      Fintype.card (returnImage (G := G) L l) - 2
    omega

def imagePairSet (L : Nat) (S : Finset Nat.Primes) (g : G) :
    Finset ((p : S) -> returnImage (G := G) L (p.val : Nat)) := by
  classical
  exact Fintype.piFinset (fun p : S =>
    coordinatePairSet L (p.val : Nat) (packetProjection L S g p))

theorem imagePairSet_mem (L : Nat) (S : Finset Nat.Primes) (g : G)
    (y : (p : S) -> returnImage (G := G) L (p.val : Nat)) :
    Membership.mem (imagePairSet L S g) y <->
      forall p : S, And (Not (y p = 1))
        (Not (y p * packetProjection L S g p = 1)) := by
  classical
  unfold imagePairSet
  rw [Fintype.mem_piFinset]
  apply forall_congr'
  intro p
  exact coordinatePairSet_mem L (p.val : Nat) _ _

theorem imagePairSet_card (L : Nat) (S : Finset Nat.Primes) (g : G) :
    (imagePairSet L S g).card =
      Finset.univ.prod (fun p : S => if packetProjection L S g p = 1
        then returnIndex (G := G) L (p.val : Nat) - 1
        else returnIndex (G := G) L (p.val : Nat) - 2) := by
  classical
  unfold imagePairSet
  rw [Fintype.card_piFinset]
  apply Finset.prod_congr rfl
  intro p _
  exact coordinatePairSet_card L (p.val : Nat) _

/-- The two vacancy events stay coupled at the same sampled base. -/
theorem raw_correlation_eq_pair_probability (L : Nat) (S : Finset Nat.Primes) (g : G) :
    rawCorrelation (vacancyWeight (G := G) L S) g / (Fintype.card G : Real) =
      uniformProbability (fun h : G => And (OddReturnCharacterSupport.vacancy L S h)
        (OddReturnCharacterSupport.vacancy L S (h * g))) := by
  classical
  have hIndicator (h : G) :
      vacancyWeight L S h * vacancyWeight L S (h * g) =
        if And (OddReturnCharacterSupport.vacancy L S h)
          (OddReturnCharacterSupport.vacancy L S (h * g)) then (1 : Real) else 0 := by
    unfold vacancyWeight
    split_ifs <;> simp_all
  unfold rawCorrelation
  simp_rw [hIndicator]
  rw [Finset.sum_boole]
  simp only [uniformProbability, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The full joint law is a product only after the exact surjective pushforward. -/
theorem pair_probability_eq_product (L : Nat) (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) L)
    (hAnn : forall g : G, g ^ L = 1)
    (hTwo : forall p : S, 2 <= returnIndex (G := G) L (p.val : Nat)) (g : G) :
    uniformProbability (fun h : G => And (OddReturnCharacterSupport.vacancy L S h)
      (OddReturnCharacterSupport.vacancy L S (h * g))) =
        Finset.univ.prod (fun p : S => if packetProjection L S g p = 1
          then 1 - 1 / (returnIndex (G := G) L (p.val : Nat) : Real)
          else 1 - 2 / (returnIndex (G := G) L (p.val : Nat) : Real)) := by
  classical
  let H := (p : S) -> returnImage (G := G) L (p.val : Nat)
  let T : Finset H := imagePairSet L S g
  have hPred :
      (fun h : G => And (OddReturnCharacterSupport.vacancy L S h)
        (OddReturnCharacterSupport.vacancy L S (h * g))) =
      (fun h : G => Membership.mem T (packetProjection L S h)) := by
    funext h
    apply propext
    rw [imagePairSet_mem]
    constructor
    . intro hh p
      refine And.intro ((OddReturnCharacterSupport.vacancy_iff_projection L S h).mp hh.1 p) ?_
      have hp := (OddReturnCharacterSupport.vacancy_iff_projection L S (h * g)).mp hh.2 p
      simpa only [map_mul, Pi.mul_apply] using hp
    . intro hh
      refine And.intro ((OddReturnCharacterSupport.vacancy_iff_projection L S h).mpr
        (fun p => (hh p).1)) ?_
      apply (OddReturnCharacterSupport.vacancy_iff_projection L S (h * g)).mpr
      intro p
      simpa only [map_mul, Pi.mul_apply] using (hh p).2
  rw [hPred, uniformProbability_preimage _ (packetProjection_surjective L S hDiv hAnn)]
  unfold uniformProbability
  change (Nat.card T : Real) / (Nat.card H : Real) = _
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, Nat.card_eq_fintype_card,
    Fintype.card_pi, imagePairSet_card]
  simp only [Nat.cast_prod]
  rw [<- Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p _
  have he : 2 <= returnIndex (G := G) L (p.val : Nat) := hTwo p
  have he0 : Not ((returnIndex (G := G) L (p.val : Nat) : Real) = 0) := by
    exact_mod_cast (show Not (returnIndex (G := G) L (p.val : Nat) = 0) by omega)
  change ((if packetProjection L S g p = 1
      then returnIndex (G := G) L (p.val : Nat) - 1
      else returnIndex (G := G) L (p.val : Nat) - 2 : Nat) : Real) /
        (returnIndex (G := G) L (p.val : Nat) : Real) = _
  by_cases h : packetProjection L S g p = 1
  . rw [ite_eq_left h, ite_eq_left h, Nat.cast_sub (by omega), Nat.cast_one,
      sub_div, div_self he0]
  . rw [ite_eq_right h, ite_eq_right h, Nat.cast_sub he, Nat.cast_ofNat,
      sub_div, div_self he0]

def returnBit (L l : Nat) (g : G) : Bool := by
  classical
  exact decide (g ^ (L / l) = 1)

def localFactor (d : Nat) (b : Bool) : Real :=
  (if b then 1 - 1 / (d : Real) else 1 - 2 / (d : Real)) /
    (1 - 1 / (d : Real)) ^ 2

theorem canonical_kernel_eq_product (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent G)) (g : G) :
    kernel (vacancyWeight (G := G) (Monoid.exponent G) S) g =
      Finset.univ.prod (fun p : S =>
        localFactor (returnIndex (G := G) (Monoid.exponent G) (p.val : Nat))
          (returnBit (Monoid.exponent G) (p.val : Nat) g)) := by
  classical
  let L := Monoid.exponent G
  let w := vacancyWeight (G := G) L S
  have hn : Not ((Fintype.card G : Real) = 0) := by exact_mod_cast Fintype.card_ne_zero
  have hSum := canonical_vacancy_weightSum_pos (G := G) S hDiv
  have hNormalize : kernel w g =
      (rawCorrelation w g / (Fintype.card G : Real)) / weightMean w ^ 2 := by
    unfold kernel weightMean
    field_simp [hn, ne_of_gt hSum]
  have hTwo (p : S) : 2 <= returnIndex (G := G) L (p.val : Nat) :=
    p.val.property.two_le.trans (divisor_le_returnIndex (G := G) _ (hDiv p))
  have hMean : weightMean w = Finset.univ.prod (fun p : S =>
      1 - 1 / (returnIndex (G := G) L (p.val : Nat) : Real)) :=
    OddReturnCharacterSupport.vacancy_mean_eq_product L S hDiv
      (fun h : G => Monoid.pow_exponent_eq_one h)
  rw [hNormalize, raw_correlation_eq_pair_probability,
    pair_probability_eq_product L S hDiv (fun h => Monoid.pow_exponent_eq_one h) hTwo,
    hMean, pow_two, <- Finset.prod_mul_distrib, <- Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p _
  have hBit : packetProjection L S g p = 1 <-> g ^ (L / (p.val : Nat)) = 1 := by
    constructor
    . intro h
      exact congrArg Subtype.val h
    . intro h
      exact Subtype.ext h
  by_cases hg : g ^ (L / (p.val : Nat)) = 1
  . have hp := hBit.mpr hg
    simp [localFactor, returnBit, L, hg, hp, pow_two]
  . have hp : Not (packetProjection L S g p = 1) := fun h => hg (hBit.mp h)
    simp [localFactor, returnBit, L, hg, hp, pow_two]

end PrimeFactorOscillations.CarmichaelCorrelationLocal
