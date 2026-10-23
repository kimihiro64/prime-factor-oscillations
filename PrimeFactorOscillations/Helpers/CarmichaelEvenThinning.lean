/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.CarmichaelProfileLifts

/-!
# Conditional return probabilities inside a Carmichael extension fiber

The probability is taken over all lifts of one fixed old unit.
A failed old return cannot be restored. A successful old return is
independently retained with the exact auxiliary image probability.
At the singly-even label this probability is two to minus omega(B).
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelEvenThinning

open FiniteHomProbability PrimeOrderReturnLaw PrimeOrderReturnIndex
  CarmichaelProfileExtension CarmichaelProfileLifts

theorem uniformProbability_equiv {A D : Type*} (e : Equiv A D) (P : D -> Prop) :
    uniformProbability (fun a : A => P (e a)) = uniformProbability P := by
  let eP : Equiv {a : A // P (e a)} {d : D // P d} :=
    { toFun := fun a => Subtype.mk (e a.val) a.property
      invFun := fun d => Subtype.mk (e.symm d.val) (by simpa only [e.apply_symm_apply] using d.property)
      left_inv := fun a => Subtype.ext (e.symm_apply_apply a.val)
      right_inv := fun d => Subtype.ext (e.apply_symm_apply d.val) }
  unfold uniformProbability
  rw [Nat.card_congr eP, Nat.card_congr e]

theorem uniformProbability_true {A : Type*} [Fintype A] [Nonempty A] :
    uniformProbability (fun _ : A => True) = 1 := by
  classical
  have hPos : 0 < Nat.card A := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos_iff.mpr inferInstance
  have hNonzero : Not ((Nat.card A : Real) = 0) := by
    exact_mod_cast (Nat.ne_of_gt hPos)
  unfold uniformProbability
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_true, <- Nat.card_eq_fintype_card]
  exact div_self hNonzero

theorem uniformProbability_false {A : Type*} :
    uniformProbability (fun _ : A => False) = 0 := by
  unfold uniformProbability
  simp

theorem single_return_probability {G : Type*} [CommGroup G] [Fintype G]
    (L : Nat) (l : Nat.Primes) (hl : Dvd.dvd (l : Nat) L)
    (hAnn : forall g : G, g ^ L = 1) (bit : Bool) :
    uniformProbability (fun g : G =>
      if bit then g ^ (L / (l : Nat)) = 1 else Not (g ^ (L / (l : Nat)) = 1)) =
      if bit then 1 / (returnIndex (G := G) L (l : Nat) : Real)
      else 1 - 1 / (returnIndex (G := G) L (l : Nat) : Real) := by
  classical
  let S : Finset Nat.Primes := {l}
  have hLabel (p : S) : p.val = l := Finset.mem_singleton.mp p.property
  have hDiv : forall p : S, Dvd.dvd (p.val : Nat) L := by
    intro p
    rw [hLabel p]
    exact hl
  have hProb := returnPatternProbability_eq_product (G := G) L S hDiv hAnn (fun _ => bit)
  have hPred :
      (fun g : G => forall p : S,
        if bit then g ^ (L / (p.val : Nat)) = 1 else Not (g ^ (L / (p.val : Nat)) = 1)) =
      (fun g : G => if bit then g ^ (L / (l : Nat)) = 1 else Not (g ^ (L / (l : Nat)) = 1)) := by
    funext g
    apply propext
    constructor
    { intro h
      exact h (Subtype.mk l (Finset.mem_singleton_self l)) }
    { intro h p
      rw [hLabel p]
      exact h }
  unfold returnPatternProbability at hProb
  rw [hPred] at hProb
  have hTerm :
      (fun p : S => if bit then 1 / (returnIndex (G := G) L (p.val : Nat) : Real)
        else 1 - 1 / (returnIndex (G := G) L (p.val : Nat) : Real)) =
      (fun _ : S => if bit then 1 / (returnIndex (G := G) L (l : Nat) : Real)
        else 1 - 1 / (returnIndex (G := G) L (l : Nat) : Real)) := by
    funext p
    rw [hLabel p]
  rw [hTerm, Finset.prod_const] at hProb
  simpa only [Finset.card_univ, Fintype.card_coe, S, Finset.card_singleton, pow_one] using hProb

theorem auxiliary_exponent_annihilates (m B : Nat)
    (hCoprime : Nat.Coprime m B) (b : Units (ZMod B)) :
    b ^ (Monoid.exponent (Units (ZMod (m * B)))) = 1 := by
  let u := (unitProductEquiv m B hCoprime).symm (Prod.mk 1 b)
  have h := congrArg (unitReduction (dvd_mul_left B m)) (Monoid.pow_exponent_eq_one u)
  simp only [map_pow, map_one] at h
  have hRed : unitReduction (dvd_mul_left B m) u = b := by
    rw [<- unitProductEquiv_snd m B hCoprime]
    exact congrArg Prod.snd ((unitProductEquiv m B hCoprime).apply_symm_apply (Prod.mk 1 b))
  rwa [hRed] at h

/-- Uniform probability over every actual lift of one fixed old base. -/
def liftReturnProbability (m B : Nat) (a : Units (ZMod m)) (l : Nat) (bit : Bool) : Real :=
  uniformProbability
    (fun u : {u : Units (ZMod (m * B)) // unitReduction (dvd_mul_right m B) u = a} =>
      if bit then u.val ^ (Monoid.exponent (Units (ZMod (m * B))) / l) = 1
      else Not (u.val ^ (Monoid.exponent (Units (ZMod (m * B))) / l) = 1))

theorem conditional_return_probability (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)]
    (hSqM : Squarefree m) (hSqB : Squarefree B) (hCoprime : Nat.Coprime m B)
    (hTwo : Dvd.dvd 2 (Monoid.exponent (Units (ZMod m))))
    (hFactors : forall p : Nat, Nat.Prime p -> Dvd.dvd p B ->
      Dvd.dvd (4 * Monoid.exponent (Units (ZMod m))) (p + 1))
    (a : Units (ZMod m)) (l : Nat.Primes)
    (hl : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod m)))) (bit : Bool) :
    liftReturnProbability m B a (l : Nat) bit =
      if a ^ (Monoid.exponent (Units (ZMod m)) / (l : Nat)) = 1 then
        if bit then
          1 / (returnIndex (G := Units (ZMod B))
            (Monoid.exponent (Units (ZMod (m * B)))) (l : Nat) : Real)
        else 1 - 1 / (returnIndex (G := Units (ZMod B))
            (Monoid.exponent (Units (ZMod (m * B)))) (l : Nat) : Real)
      else if bit then 0 else 1 := by
  classical
  let L := Monoid.exponent (Units (ZMod m))
  let E := Monoid.exponent (Units (ZMod (m * B)))
  let e := unitLiftFiberEquiv m B hCoprime a
  let P : Units (ZMod B) -> Prop := fun b =>
    if bit then And (a ^ (L / (l : Nat)) = 1) (b ^ (E / (l : Nat)) = 1)
    else Not (And (a ^ (L / (l : Nat)) = 1) (b ^ (E / (l : Nat)) = 1))
  have hPred :
      (fun u : {u : Units (ZMod (m * B)) // unitReduction (dvd_mul_right m B) u = a} =>
        if bit then u.val ^ (E / (l : Nat)) = 1 else Not (u.val ^ (E / (l : Nat)) = 1)) =
      (fun u => P (e u)) := by
    funext u
    apply propext
    have h := reduction_return_factorization m B hSqM hSqB hCoprime hTwo hFactors l hl u.val
    rw [u.property] at h
    have hAux : e u = unitReduction (dvd_mul_left B m) u.val :=
      unitProductEquiv_snd m B hCoprime u.val
    change (if bit then u.val ^ (E / (l : Nat)) = 1 else Not (u.val ^ (E / (l : Nat)) = 1)) <->
      (if bit then And (a ^ (L / (l : Nat)) = 1) ((e u) ^ (E / (l : Nat)) = 1)
      else Not (And (a ^ (L / (l : Nat)) = 1) ((e u) ^ (E / (l : Nat)) = 1)))
    rw [hAux]
    cases bit
    { exact not_congr h }
    { exact h }
  unfold liftReturnProbability
  rw [hPred, uniformProbability_equiv e P]
  change uniformProbability P =
    if a ^ (L / (l : Nat)) = 1 then
      if bit then 1 / (returnIndex (G := Units (ZMod B)) E (l : Nat) : Real)
      else 1 - 1 / (returnIndex (G := Units (ZMod B)) E (l : Nat) : Real)
    else if bit then 0 else 1
  by_cases hOld : a ^ (L / (l : Nat)) = 1
  { simp only [hOld, ite_true, P, true_and]
    have hLE : Dvd.dvd L E := by
      choose K hK using exponent_coprime_multiplier m B hSqM hSqB hCoprime hTwo hFactors
      exact Exists.intro K hK.2
    exact single_return_probability E l (dvd_trans hl hLE)
      (auxiliary_exponent_annihilates m B hCoprime) bit }
  { simp only [hOld, ite_false, P, false_and, not_false_eq_true]
    cases bit
    { exact uniformProbability_true }
    { exact uniformProbability_false } }

theorem auxiliary_even_returnIndex (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)]
    (hSqM : Squarefree m) (hSqB : Squarefree B) (hCoprime : Nat.Coprime m B)
    (hTwo : Dvd.dvd 2 (Monoid.exponent (Units (ZMod m))))
    (hFour : Not (Dvd.dvd 4 (Monoid.exponent (Units (ZMod m)))))
    (hFactors : forall p : Nat, Nat.Prime p -> Dvd.dvd p B ->
      Dvd.dvd (4 * Monoid.exponent (Units (ZMod m))) (p + 1)) :
    returnIndex (G := Units (ZMod B))
      (Monoid.exponent (Units (ZMod (m * B)))) 2 = 2 ^ B.primeFactors.card := by
  classical
  let L := Monoid.exponent (Units (ZMod m))
  let E := Monoid.exponent (Units (ZMod (m * B)))
  have hSqNew : Squarefree (m * B) := (Nat.squarefree_mul hCoprime).mpr (And.intro hSqM hSqB)
  choose K hK using exponent_coprime_multiplier m B hSqM hSqB hCoprime hTwo hFactors
  have hLE : Dvd.dvd L E := Exists.intro K hK.2
  rw [squarefree_index_finset B hSqB]
  calc
    B.primeFactors.prod (fun p : Nat => (p - 1) / Nat.gcd (p - 1) (E / 2)) =
        B.primeFactors.prod (fun _ => 2) := by
      apply Finset.prod_congr rfl
      intro p hpB
      have hp := (Nat.mem_primeFactors.mp hpB).1
      have hDiv := (Nat.mem_primeFactors.mp hpB).2.1
      have hpE := prime_period_dvd_exponent (m * B) hSqNew p hp
        (dvd_trans hDiv (dvd_mul_left B m))
      have h := auxiliary_image_factor p L E K hp hTwo hLE hK.2 hK.1
        (hFactors p hp hDiv) hpE (Subtype.mk 2 Nat.prime_two) hTwo
      simpa [L, hFour] using h
    _ = 2 ^ B.primeFactors.card := Finset.prod_const 2

theorem conditional_even_thinning (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)]
    (hSqM : Squarefree m) (hSqB : Squarefree B) (hCoprime : Nat.Coprime m B)
    (hTwo : Dvd.dvd 2 (Monoid.exponent (Units (ZMod m))))
    (hFour : Not (Dvd.dvd 4 (Monoid.exponent (Units (ZMod m)))))
    (hFactors : forall p : Nat, Nat.Prime p -> Dvd.dvd p B ->
      Dvd.dvd (4 * Monoid.exponent (Units (ZMod m))) (p + 1))
    (a : Units (ZMod m)) (bit : Bool) :
    liftReturnProbability m B a 2 bit =
      if a ^ (Monoid.exponent (Units (ZMod m)) / 2) = 1 then
        if bit then 1 / ((2 ^ B.primeFactors.card : Nat) : Real)
        else 1 - 1 / ((2 ^ B.primeFactors.card : Nat) : Real)
      else if bit then 0 else 1 := by
  have h := conditional_return_probability m B hSqM hSqB hCoprime hTwo hFactors
    a (Subtype.mk 2 Nat.prime_two) hTwo bit
  rw [auxiliary_even_returnIndex m B hSqM hSqB hCoprime hTwo hFour hFactors] at h
  exact h


local instance patternDecidable (m : Nat) (S : Finset Nat.Primes) (bits : S -> Bool)
    (a : Units (ZMod m)) : Decidable (matchesPattern m S bits a) :=
  Classical.propDecidable _

/-- The entire safe pattern is kept jointly with an additional return bit. -/
def liftJointProbability (m B : Nat) (a : Units (ZMod m))
    (S : Finset Nat.Primes) (bits : S -> Bool) (l : Nat) (bit : Bool) : Real :=
  uniformProbability
    (fun u : {u : Units (ZMod (m * B)) // unitReduction (dvd_mul_right m B) u = a} =>
      And (matchesPattern (m * B) S bits u.val)
        (if bit then u.val ^ (Monoid.exponent (Units (ZMod (m * B))) / l) = 1
         else Not (u.val ^ (Monoid.exponent (Units (ZMod (m * B))) / l) = 1)))

theorem joint_lift_probability (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)]
    (hSqM : Squarefree m) (hSqB : Squarefree B) (hCoprime : Nat.Coprime m B)
    (hTwo : Dvd.dvd 2 (Monoid.exponent (Units (ZMod m))))
    (hFactors : forall p : Nat, Nat.Prime p -> Dvd.dvd p B ->
      Dvd.dvd (4 * Monoid.exponent (Units (ZMod m))) (p + 1))
    (a : Units (ZMod m)) (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod m))))
    (hSafe : forall p : S, Not (And ((p.val : Nat) = 2)
      (Not (Dvd.dvd 4 (Monoid.exponent (Units (ZMod m)))))))
    (bits : S -> Bool) (l : Nat) (bit : Bool) :
    liftJointProbability m B a S bits l bit =
      if matchesPattern m S bits a then liftReturnProbability m B a l bit else 0 := by
  classical
  have hMatch (u : {u : Units (ZMod (m * B)) //
      unitReduction (dvd_mul_right m B) u = a}) :
      matchesPattern (m * B) S bits u.val <-> matchesPattern m S bits a := by
    rw [reduction_preserves_pattern m B hSqM hSqB hCoprime hTwo hFactors S hDiv hSafe,
      u.property]
  by_cases hOld : matchesPattern m S bits a
  { rw [ite_eq_left hOld]
    unfold liftJointProbability liftReturnProbability
    congr 1
    funext u
    apply propext
    exact and_iff_right ((hMatch u).mpr hOld) }
  { rw [ite_eq_right hOld]
    unfold liftJointProbability
    have hPred :
        (fun u : {u : Units (ZMod (m * B)) // unitReduction (dvd_mul_right m B) u = a} =>
          And (matchesPattern (m * B) S bits u.val)
            (if bit then u.val ^ (Monoid.exponent (Units (ZMod (m * B))) / l) = 1
             else Not (u.val ^ (Monoid.exponent (Units (ZMod (m * B))) / l) = 1))) =
        (fun _ => False) := by
      funext u
      apply propext
      have hNot : Not (matchesPattern (m * B) S bits u.val) := by
        intro h
        exact hOld ((hMatch u).mp h)
      simp only [hNot, false_and]
    rw [hPred]
    exact uniformProbability_false }

theorem conditional_odd_even_profile (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)]
    (hSqM : Squarefree m) (hSqB : Squarefree B) (hCoprime : Nat.Coprime m B)
    (hTwo : Dvd.dvd 2 (Monoid.exponent (Units (ZMod m))))
    (hFour : Not (Dvd.dvd 4 (Monoid.exponent (Units (ZMod m)))))
    (hFactors : forall p : Nat, Nat.Prime p -> Dvd.dvd p B ->
      Dvd.dvd (4 * Monoid.exponent (Units (ZMod m))) (p + 1))
    (a : Units (ZMod m)) (S : Finset Nat.Primes)
    (hDiv : forall p : S, Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod m))))
    (hOdd : forall p : S, Not ((p.val : Nat) = 2))
    (bits : S -> Bool) (bit : Bool) :
    liftJointProbability m B a S bits 2 bit =
      if matchesPattern m S bits a then
        if a ^ (Monoid.exponent (Units (ZMod m)) / 2) = 1 then
          if bit then 1 / ((2 ^ B.primeFactors.card : Nat) : Real)
          else 1 - 1 / ((2 ^ B.primeFactors.card : Nat) : Real)
        else if bit then 0 else 1
      else 0 := by
  have hSafe : forall p : S, Not (And ((p.val : Nat) = 2)
      (Not (Dvd.dvd 4 (Monoid.exponent (Units (ZMod m)))))) := by
    intro p hp
    exact hOdd p hp.1
  rw [joint_lift_probability m B hSqM hSqB hCoprime hTwo hFactors a S hDiv hSafe,
    conditional_even_thinning m B hSqM hSqB hCoprime hTwo hFour hFactors]

end PrimeFactorOscillations.CarmichaelEvenThinning
