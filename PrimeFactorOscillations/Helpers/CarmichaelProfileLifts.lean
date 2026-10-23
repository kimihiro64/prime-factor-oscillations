/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Group.Prod
import PrimeFactorOscillations.Helpers.CarmichaelProfileExtension

/-!
# Pointwise lifts of native Carmichael return profiles

The CRT coordinates are the actual unit-reduction homomorphisms.
Every old unit has an explicit complete fiber, and prime-order returns
are transported pointwise under the separated profile extension.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelProfileLifts

open PrimeOrderReturnLaw PrimeOrderReturnIndex CarmichaelProfileExtension

/-- Canonical reduction on units for a divisor modulus. -/
def unitReduction {d c : Nat} (hDiv : Dvd.dvd d c) :
    MonoidHom (Units (ZMod c)) (Units (ZMod d)) :=
  Units.map (ZMod.castHom hDiv (ZMod d))

/-- Actual CRT on all modular units, retaining both coordinate homomorphisms. -/
def unitProductEquiv (m B : Nat) (hCoprime : Nat.Coprime m B) :
    MulEquiv (Units (ZMod (m * B))) (Prod (Units (ZMod m)) (Units (ZMod B))) :=
  (Units.mapEquiv (ZMod.chineseRemainder hCoprime).toMulEquiv).trans MulEquiv.prodUnits

theorem unitProductEquiv_fst (m B : Nat) (hCoprime : Nat.Coprime m B)
    (u : Units (ZMod (m * B))) :
    (unitProductEquiv m B hCoprime u).1 = unitReduction (dvd_mul_right m B) u := by
  apply Units.ext
  change (ZMod.cast u.val : Prod (ZMod m) (ZMod B)).1 = (ZMod.cast u.val : ZMod m)
  rw [Prod.fst_zmod_cast]

theorem unitProductEquiv_snd (m B : Nat) (hCoprime : Nat.Coprime m B)
    (u : Units (ZMod (m * B))) :
    (unitProductEquiv m B hCoprime u).2 = unitReduction (dvd_mul_left B m) u := by
  apply Units.ext
  change (ZMod.cast u.val : Prod (ZMod m) (ZMod B)).2 = (ZMod.cast u.val : ZMod B)
  rw [Prod.snd_zmod_cast]

/-- The entire fiber of each old unit is parametrized by the auxiliary units. -/
def unitLiftFiberEquiv (m B : Nat) (hCoprime : Nat.Coprime m B) (a : Units (ZMod m)) :
    Equiv {u : Units (ZMod (m * B)) // unitReduction (dvd_mul_right m B) u = a}
      (Units (ZMod B)) := by
  refine
    { toFun := fun u => (unitProductEquiv m B hCoprime u.val).2
      invFun := fun b => Subtype.mk ((unitProductEquiv m B hCoprime).symm (Prod.mk a b)) ?_
      left_inv := ?_
      right_inv := ?_ }
  { rw [<- unitProductEquiv_fst m B hCoprime,
      (unitProductEquiv m B hCoprime).apply_symm_apply] }
  { intro u
    apply Subtype.ext
    apply (unitProductEquiv m B hCoprime).injective
    rw [(unitProductEquiv m B hCoprime).apply_symm_apply]
    apply Prod.ext
    { rw [unitProductEquiv_fst m B hCoprime]
      exact u.property.symm }
    { rfl } }
  { intro b
    change (unitProductEquiv m B hCoprime
      ((unitProductEquiv m B hCoprime).symm (Prod.mk a b))).2 = b
    rw [(unitProductEquiv m B hCoprime).apply_symm_apply] }

theorem unit_lift_fiber_card (m B : Nat) [NeZero B]
    (hCoprime : Nat.Coprime m B) (a : Units (ZMod m)) :
    Nat.card {u : Units (ZMod (m * B)) // unitReduction (dvd_mul_right m B) u = a} =
      Nat.totient B := by
  rw [Nat.card_congr (unitLiftFiberEquiv m B hCoprime a),
    Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

/-- A coprime exponent multiplier cannot kill a nonidentity element. -/
theorem pow_coprime_exponent_eq_one {G : Type*} [Group G]
    (x : G) (K : Nat) (hCoprime : Nat.Coprime K (Monoid.exponent G)) :
    x ^ K = 1 <-> x = 1 := by
  constructor
  { intro h
    apply orderOf_eq_one_iff.mp
    apply Nat.dvd_one.mp
    have hDvd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h) (Monoid.order_dvd_exponent x)
    change Nat.gcd K (Monoid.exponent G) = 1 at hCoprime
    rwa [hCoprime] at hDvd }
  { intro h
    rw [h, one_pow] }

/-- The full pointwise return identity keeps the auxiliary coordinate. -/
theorem reduction_return_factorization (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)]
    (hSqM : Squarefree m) (hSqB : Squarefree B) (hCoprime : Nat.Coprime m B)
    (hTwo : Dvd.dvd 2 (Monoid.exponent (Units (ZMod m))))
    (hFactors : forall p : Nat, Nat.Prime p -> Dvd.dvd p B ->
      Dvd.dvd (4 * Monoid.exponent (Units (ZMod m))) (p + 1))
    (l : Nat.Primes) (hl : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod m))))
    (u : Units (ZMod (m * B))) :
    u ^ (Monoid.exponent (Units (ZMod (m * B))) / (l : Nat)) = 1 <->
      And ((unitReduction (dvd_mul_right m B) u) ^
        (Monoid.exponent (Units (ZMod m)) / (l : Nat)) = 1)
        ((unitReduction (dvd_mul_left B m) u) ^
          (Monoid.exponent (Units (ZMod (m * B))) / (l : Nat)) = 1) := by
  let L := Monoid.exponent (Units (ZMod m))
  let E := Monoid.exponent (Units (ZMod (m * B)))
  choose K hK using exponent_coprime_multiplier m B hSqM hSqB hCoprime hTwo hFactors
  have hQuot : E / (l : Nat) = (L / (l : Nat)) * K := by
    rw [show E = L * K from hK.2, Nat.mul_comm L K, Nat.mul_div_assoc K hl,
      Nat.mul_comm K (L / (l : Nat))]
  constructor
  { intro hReturn
    have hOld := congrArg (unitReduction (dvd_mul_right m B)) hReturn
    simp only [map_pow, map_one] at hOld
    rw [hQuot, pow_mul] at hOld
    have hNew := congrArg (unitReduction (dvd_mul_left B m)) hReturn
    simp only [map_pow, map_one] at hNew
    exact And.intro ((pow_coprime_exponent_eq_one _ K hK.1).mp hOld) hNew }
  { intro hReturn
    apply (unitProductEquiv m B hCoprime).injective
    rw [map_pow, map_one]
    apply Prod.ext
    { change (unitProductEquiv m B hCoprime u).1 ^ (E / (l : Nat)) = 1
      rw [unitProductEquiv_fst, hQuot, pow_mul, hReturn.1, one_pow] }
    { change (unitProductEquiv m B hCoprime u).2 ^ (E / (l : Nat)) = 1
      rw [unitProductEquiv_snd]
      exact hReturn.2 } }

/-- All auxiliary bases return at every label outside the even exception. -/
theorem auxiliary_return_one (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)]
    (hSqM : Squarefree m) (hSqB : Squarefree B) (hCoprime : Nat.Coprime m B)
    (hTwo : Dvd.dvd 2 (Monoid.exponent (Units (ZMod m))))
    (hFactors : forall p : Nat, Nat.Prime p -> Dvd.dvd p B ->
      Dvd.dvd (4 * Monoid.exponent (Units (ZMod m))) (p + 1))
    (l : Nat.Primes) (hl : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod m))))
    (hSafe : Not (And ((l : Nat) = 2)
      (Not (Dvd.dvd 4 (Monoid.exponent (Units (ZMod m)))))))
    (b : Units (ZMod B)) :
    b ^ (Monoid.exponent (Units (ZMod (m * B))) / (l : Nat)) = 1 := by
  classical
  let L := Monoid.exponent (Units (ZMod m))
  let E := Monoid.exponent (Units (ZMod (m * B)))
  have hSqNew : Squarefree (m * B) := (Nat.squarefree_mul hCoprime).mpr (And.intro hSqM hSqB)
  choose K hK using exponent_coprime_multiplier m B hSqM hSqB hCoprime hTwo hFactors
  have hLE : Dvd.dvd L E := Exists.intro K hK.2
  have hAnn : Dvd.dvd (Monoid.exponent (Units (ZMod B))) (E / (l : Nat)) := by
    apply exponent_dvd_of_prime_periods B hSqB
    intro p hp hpB
    have hpE := prime_period_dvd_exponent (m * B) hSqNew p hp
      (dvd_trans hpB (dvd_mul_left B m))
    have hRatio := auxiliary_image_factor p L E K hp hTwo hLE hK.2 hK.1
      (hFactors p hp hpB) hpE l hl
    rw [ite_eq_right hSafe] at hRatio
    have hEqual : p - 1 = Nat.gcd (p - 1) (E / (l : Nat)) := by
      calc
        p - 1 = ((p - 1) / Nat.gcd (p - 1) (E / (l : Nat))) *
            Nat.gcd (p - 1) (E / (l : Nat)) :=
          (Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)).symm
        _ = Nat.gcd (p - 1) (E / (l : Nat)) := by rw [hRatio, one_mul]
    rw [hEqual]
    exact Nat.gcd_dvd_right _ _
  exact (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hAnn) b

/-- Pointwise preservation holds for all original labels except the even exception. -/
theorem reduction_preserves_return (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)]
    (hSqM : Squarefree m) (hSqB : Squarefree B) (hCoprime : Nat.Coprime m B)
    (hTwo : Dvd.dvd 2 (Monoid.exponent (Units (ZMod m))))
    (hFactors : forall p : Nat, Nat.Prime p -> Dvd.dvd p B ->
      Dvd.dvd (4 * Monoid.exponent (Units (ZMod m))) (p + 1))
    (l : Nat.Primes) (hl : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod m))))
    (hSafe : Not (And ((l : Nat) = 2)
      (Not (Dvd.dvd 4 (Monoid.exponent (Units (ZMod m)))))))
    (u : Units (ZMod (m * B))) :
    u ^ (Monoid.exponent (Units (ZMod (m * B))) / (l : Nat)) = 1 <->
      (unitReduction (dvd_mul_right m B) u) ^
        (Monoid.exponent (Units (ZMod m)) / (l : Nat)) = 1 := by
  rw [reduction_return_factorization m B hSqM hSqB hCoprime hTwo hFactors l hl u]
  have h := auxiliary_return_one m B hSqM hSqB hCoprime hTwo hFactors l hl hSafe
    (unitReduction (dvd_mul_left B m) u)
  simp only [h, and_true]

/-- The full signed binary event at the actual canonical exponent. -/
def matchesPattern (c : Nat) (S : Finset Nat.Primes) (bits : S -> Bool)
    (u : Units (ZMod c)) : Prop :=
  forall l : S, if bits l then
    u ^ (Monoid.exponent (Units (ZMod c)) / (l.val : Nat)) = 1
  else Not (u ^ (Monoid.exponent (Units (ZMod c)) / (l.val : Nat)) = 1)

local instance matchesPatternDecidable (c : Nat) (S : Finset Nat.Primes)
    (bits : S -> Bool) (u : Units (ZMod c)) : Decidable (matchesPattern c S bits u) :=
  Classical.propDecidable _

theorem reduction_preserves_pattern (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)]
    (hSqM : Squarefree m) (hSqB : Squarefree B) (hCoprime : Nat.Coprime m B)
    (hTwo : Dvd.dvd 2 (Monoid.exponent (Units (ZMod m))))
    (hFactors : forall p : Nat, Nat.Prime p -> Dvd.dvd p B ->
      Dvd.dvd (4 * Monoid.exponent (Units (ZMod m))) (p + 1))
    (S : Finset Nat.Primes)
    (hDiv : forall l : S, Dvd.dvd (l.val : Nat) (Monoid.exponent (Units (ZMod m))))
    (hSafe : forall l : S, Not (And ((l.val : Nat) = 2)
      (Not (Dvd.dvd 4 (Monoid.exponent (Units (ZMod m)))))))
    (bits : S -> Bool) (u : Units (ZMod (m * B))) :
    matchesPattern (m * B) S bits u <->
      matchesPattern m S bits (unitReduction (dvd_mul_right m B) u) := by
  unfold matchesPattern
  apply forall_congr'
  intro l
  have h := reduction_preserves_return m B hSqM hSqB hCoprime hTwo hFactors
    l.val (hDiv l) (hSafe l) u
  by_cases hb : bits l = true
  { simp only [hb, ite_true]
    exact h }
  { simp only [hb, ite_false]
    exact not_congr h }

/-- Every old base has either its whole fiber of matching lifts, or none. -/
theorem pattern_lift_fiber_card (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)]
    (hSqM : Squarefree m) (hSqB : Squarefree B) (hCoprime : Nat.Coprime m B)
    (hTwo : Dvd.dvd 2 (Monoid.exponent (Units (ZMod m))))
    (hFactors : forall p : Nat, Nat.Prime p -> Dvd.dvd p B ->
      Dvd.dvd (4 * Monoid.exponent (Units (ZMod m))) (p + 1))
    (S : Finset Nat.Primes)
    (hDiv : forall l : S, Dvd.dvd (l.val : Nat) (Monoid.exponent (Units (ZMod m))))
    (hSafe : forall l : S, Not (And ((l.val : Nat) = 2)
      (Not (Dvd.dvd 4 (Monoid.exponent (Units (ZMod m)))))))
    (bits : S -> Bool) (a : Units (ZMod m)) :
    Nat.card {u : Units (ZMod (m * B)) //
        And (unitReduction (dvd_mul_right m B) u = a) (matchesPattern (m * B) S bits u)} =
      if matchesPattern m S bits a then Nat.totient B else 0 := by
  classical
  have hPred :
      (fun u : Units (ZMod (m * B)) =>
        And (unitReduction (dvd_mul_right m B) u = a) (matchesPattern (m * B) S bits u)) =
      (fun u : Units (ZMod (m * B)) =>
        And (unitReduction (dvd_mul_right m B) u = a) (matchesPattern m S bits a)) := by
    funext u
    apply propext
    rw [reduction_preserves_pattern m B hSqM hSqB hCoprime hTwo hFactors S hDiv hSafe bits u]
    constructor
    { intro h
      exact And.intro h.1 (by simpa only [h.1] using h.2) }
    { intro h
      exact And.intro h.1 (by simpa only [h.1] using h.2) }
  change Nat.card (Subtype (fun u : Units (ZMod (m * B)) =>
    And (unitReduction (dvd_mul_right m B) u = a) (matchesPattern (m * B) S bits u))) = _
  rw [hPred]
  split_ifs with hMatch
  { simpa only [hMatch, and_true] using unit_lift_fiber_card m B hCoprime a }
  { simp only [hMatch, and_false]
    simp }

/-- The auxiliary identity selects a group-homomorphic section of reduction. -/
def canonicalUnitLift (m B : Nat) (hCoprime : Nat.Coprime m B) :
    MonoidHom (Units (ZMod m)) (Units (ZMod (m * B))) :=
  (unitProductEquiv m B hCoprime).symm.toMonoidHom.comp
    ((MonoidHom.id (Units (ZMod m))).prod
      (1 : MonoidHom (Units (ZMod m)) (Units (ZMod B))))

theorem canonicalUnitLift_apply (m B : Nat) (hCoprime : Nat.Coprime m B)
    (a : Units (ZMod m)) :
    canonicalUnitLift m B hCoprime a =
      (unitProductEquiv m B hCoprime).symm (Prod.mk a 1) := rfl

theorem reduction_canonicalUnitLift (m B : Nat) (hCoprime : Nat.Coprime m B)
    (a : Units (ZMod m)) :
    unitReduction (dvd_mul_right m B) (canonicalUnitLift m B hCoprime a) = a := by
  rw [canonicalUnitLift_apply, <- unitProductEquiv_fst m B hCoprime,
    (unitProductEquiv m B hCoprime).apply_symm_apply]

theorem cofactor_reduction_canonicalUnitLift (m B : Nat) (hCoprime : Nat.Coprime m B)
    (a : Units (ZMod m)) :
    unitReduction (dvd_mul_left B m) (canonicalUnitLift m B hCoprime a) = 1 := by
  rw [canonicalUnitLift_apply, <- unitProductEquiv_snd m B hCoprime,
    (unitProductEquiv m B hCoprime).apply_symm_apply]

theorem canonicalUnitLift_injective (m B : Nat) (hCoprime : Nat.Coprime m B) :
    Function.Injective (canonicalUnitLift m B hCoprime) := by
  intro a b h
  have hReduce := congrArg (unitReduction (dvd_mul_right m B)) h
  simpa only [reduction_canonicalUnitLift] using hReduce

/-- The canonical lift preserves every original return, including the even exception. -/
theorem canonical_lift_preserves_return (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)]
    (hSqM : Squarefree m) (hSqB : Squarefree B) (hCoprime : Nat.Coprime m B)
    (hTwo : Dvd.dvd 2 (Monoid.exponent (Units (ZMod m))))
    (hFactors : forall p : Nat, Nat.Prime p -> Dvd.dvd p B ->
      Dvd.dvd (4 * Monoid.exponent (Units (ZMod m))) (p + 1))
    (l : Nat.Primes) (hl : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod m))))
    (a : Units (ZMod m)) :
    (canonicalUnitLift m B hCoprime a) ^
        (Monoid.exponent (Units (ZMod (m * B))) / (l : Nat)) = 1 <->
      a ^ (Monoid.exponent (Units (ZMod m)) / (l : Nat)) = 1 := by
  rw [reduction_return_factorization m B hSqM hSqB hCoprime hTwo hFactors l hl,
    reduction_canonicalUnitLift, cofactor_reduction_canonicalUnitLift]
  simp only [one_pow, and_true]

theorem canonical_lift_preserves_pattern (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)]
    (hSqM : Squarefree m) (hSqB : Squarefree B) (hCoprime : Nat.Coprime m B)
    (hTwo : Dvd.dvd 2 (Monoid.exponent (Units (ZMod m))))
    (hFactors : forall p : Nat, Nat.Prime p -> Dvd.dvd p B ->
      Dvd.dvd (4 * Monoid.exponent (Units (ZMod m))) (p + 1))
    (S : Finset Nat.Primes)
    (hDiv : forall l : S, Dvd.dvd (l.val : Nat) (Monoid.exponent (Units (ZMod m))))
    (bits : S -> Bool) (a : Units (ZMod m)) :
    matchesPattern (m * B) S bits (canonicalUnitLift m B hCoprime a) <->
      matchesPattern m S bits a := by
  unfold matchesPattern
  apply forall_congr'
  intro l
  have h := canonical_lift_preserves_return m B hSqM hSqB hCoprime hTwo hFactors l.val (hDiv l) a
  by_cases hb : bits l = true
  { simp only [hb, ite_true]
    exact h }
  { simp only [hb, ite_false]
    exact not_congr h }

/-- Complete Carmichael consumer with a preserving section and exact safe fibers. -/
theorem carmichael_pattern_lift_fibers (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)]
    (hM : CarmichaelSeed.KorseltCertificate m)
    (hL : 4 <= Monoid.exponent (Units (ZMod m)))
    (hTwo : Dvd.dvd 2 (Monoid.exponent (Units (ZMod m))))
    (hB : 1 < B) (hSqB : Squarefree B) (hCoprime : Nat.Coprime m B)
    (hEven : Even B.primeFactors.card)
    (hFactors : forall p : Nat, Nat.Prime p -> Dvd.dvd p B ->
      Dvd.dvd (4 * Monoid.exponent (Units (ZMod m))) (p + 1))
    (hHalf : forall p : Nat, Nat.Prime p -> Dvd.dvd p B ->
      Dvd.dvd ((p - 1) / 2) (m * B - 1)) :
    And (CarmichaelSeed.KorseltCertificate (m * B))
      (And
        (forall (S : Finset Nat.Primes)
          (hDiv : forall l : S, Dvd.dvd (l.val : Nat) (Monoid.exponent (Units (ZMod m))))
          (bits : S -> Bool) (a : Units (ZMod m)),
          matchesPattern (m * B) S bits (canonicalUnitLift m B hCoprime a) <->
            matchesPattern m S bits a)
        (forall (S : Finset Nat.Primes)
          (hDiv : forall l : S, Dvd.dvd (l.val : Nat) (Monoid.exponent (Units (ZMod m))))
          (hSafe : forall l : S, Not (And ((l.val : Nat) = 2)
            (Not (Dvd.dvd 4 (Monoid.exponent (Units (ZMod m)))))))
          (bits : S -> Bool) (a : Units (ZMod m)),
          Nat.card {u : Units (ZMod (m * B)) //
            And (unitReduction (dvd_mul_right m B) u = a)
              (matchesPattern (m * B) S bits u)} =
            if matchesPattern m S bits a then Nat.totient B else 0)) := by
  refine And.intro
    (negative_one_extension_korselt m B hM hL hTwo hB hSqB hCoprime hEven hFactors hHalf) ?_
  refine And.intro ?_ ?_
  { intro S hDiv bits a
    exact canonical_lift_preserves_pattern m B hM.2.2.1 hSqB hCoprime hTwo hFactors S hDiv bits a }
  { intro S hDiv hSafe bits a
    exact pattern_lift_fiber_card m B hM.2.2.1 hSqB hCoprime hTwo hFactors S hDiv hSafe bits a }

end PrimeFactorOscillations.CarmichaelProfileLifts
