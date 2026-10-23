/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.CarmichaelEvenThinning

/-!
# Exact criterion for preserving every lifted prime-order return bit

For arbitrary coprime nonzero moduli m and B, with old and new
canonical exponents L and E, every lift preserves an old prime-label
return exactly when lambda(B) divides E/l. This is a converse as
well as a sufficiency theorem, with no separated seed assumption.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelProfileCriterion

open CarmichaelProfileLifts CarmichaelEvenThinning

theorem crt_power_eq_one (m B : Nat) (hCoprime : Nat.Coprime m B)
    (u : Units (ZMod (m * B))) (n : Nat) :
    u ^ n = 1 <->
      And ((unitReduction (dvd_mul_right m B) u) ^ n = 1)
        ((unitReduction (dvd_mul_left B m) u) ^ n = 1) := by
  constructor
  { intro h
    have hOld := congrArg (unitReduction (dvd_mul_right m B)) h
    have hAux := congrArg (unitReduction (dvd_mul_left B m)) h
    simp only [map_pow, map_one] at hOld hAux
    exact And.intro hOld hAux }
  { intro h
    apply (unitProductEquiv m B hCoprime).injective
    rw [map_pow, map_one]
    apply Prod.ext
    { change (unitProductEquiv m B hCoprime u).1 ^ n = 1
      rw [unitProductEquiv_fst]
      exact h.1 }
    { change (unitProductEquiv m B hCoprime u).2 ^ n = 1
      rw [unitProductEquiv_snd]
      exact h.2 } }

theorem old_exponent_dvd (m B : Nat) (hCoprime : Nat.Coprime m B) :
    Dvd.dvd (Monoid.exponent (Units (ZMod m)))
      (Monoid.exponent (Units (ZMod (m * B)))) := by
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro a
  have h := congrArg (unitReduction (dvd_mul_right m B))
    (Monoid.pow_exponent_eq_one (canonicalUnitLift m B hCoprime a))
  simp only [map_pow, map_one, reduction_canonicalUnitLift] at h
  exact h

theorem prime_quotient_not_annihilating (c : Nat) [NeZero c] (l : Nat.Primes)
    (hl : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod c)))) :
    Not (forall a : Units (ZMod c),
      a ^ (Monoid.exponent (Units (ZMod c)) / (l : Nat)) = 1) := by
  intro hAnn
  have hDiv := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hAnn
  have hPos : 0 < Monoid.exponent (Units (ZMod c)) :=
    Nat.pos_of_ne_zero (Monoid.exponent_ne_zero_of_finite (G := Units (ZMod c)))
  have hQuotPos : 0 < Monoid.exponent (Units (ZMod c)) / (l : Nat) :=
    Nat.div_pos (Nat.le_of_dvd hPos hl) l.property.pos
  have hLe := Nat.le_of_dvd hQuotPos hDiv
  exact (Nat.not_le_of_lt (Nat.div_lt_self hPos l.property.one_lt)) hLe

theorem pow_coprime_period_eq_one {G : Type*} [Group G] (x : G)
    (K l : Nat) (hPeriod : x ^ l = 1) (hCoprime : Nat.Coprime K l) :
    x ^ K = 1 <-> x = 1 := by
  constructor
  { intro h
    apply orderOf_eq_one_iff.mp
    apply Nat.dvd_one.mp
    have hDiv := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h)
      (orderOf_dvd_of_pow_eq_one hPeriod)
    change Nat.gcd K l = 1 at hCoprime
    rwa [hCoprime] at hDiv }
  { intro h
    rw [h, one_pow] }

/-- Exact necessary and sufficient criterion, with the actual reduction map. -/
theorem preserves_label_iff_auxiliary_exponent_dvd (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)] (hCoprime : Nat.Coprime m B)
    (l : Nat.Primes)
    (hl : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod m)))) :
    (forall u : Units (ZMod (m * B)),
      u ^ (Monoid.exponent (Units (ZMod (m * B))) / (l : Nat)) = 1 <->
        (unitReduction (dvd_mul_right m B) u) ^
          (Monoid.exponent (Units (ZMod m)) / (l : Nat)) = 1) <->
      Dvd.dvd (Monoid.exponent (Units (ZMod B)))
        (Monoid.exponent (Units (ZMod (m * B))) / (l : Nat)) := by
  classical
  let L := Monoid.exponent (Units (ZMod m))
  let E := Monoid.exponent (Units (ZMod (m * B)))
  constructor
  { intro hPreserve
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro b
    let u := (unitProductEquiv m B hCoprime).symm (Prod.mk 1 b)
    have hOld : unitReduction (dvd_mul_right m B) u = 1 := by
      rw [<- unitProductEquiv_fst m B hCoprime]
      exact congrArg Prod.fst ((unitProductEquiv m B hCoprime).apply_symm_apply (Prod.mk 1 b))
    have hNew := (hPreserve u).mpr (by rw [hOld, one_pow])
    have h := congrArg (unitReduction (dvd_mul_left B m)) hNew
    simp only [map_pow, map_one] at h
    have hAux : unitReduction (dvd_mul_left B m) u = b := by
      rw [<- unitProductEquiv_snd m B hCoprime]
      exact congrArg Prod.snd ((unitProductEquiv m B hCoprime).apply_symm_apply (Prod.mk 1 b))
    rwa [hAux] at h }
  { intro hAuxDiv
    have hAux := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hAuxDiv
    have hLE : Dvd.dvd L E := old_exponent_dvd m B hCoprime
    let K := E / L
    have hE : E = L * K := (Nat.mul_div_cancel' hLE).symm
    have hQuot : E / (l : Nat) = (L / (l : Nat)) * K := by
      rw [hE, Nat.mul_comm L K, Nat.mul_div_assoc K hl,
        Nat.mul_comm K (L / (l : Nat))]
    have hNot : Not (Dvd.dvd (l : Nat) K) := by
      intro hDiv
      choose t ht using hDiv
      have hOldDiv : Dvd.dvd L (E / (l : Nat)) := by
        rw [hQuot, ht, <- Nat.mul_assoc, Nat.div_mul_cancel hl]
        exact dvd_mul_right L t
      have hOld := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hOldDiv
      have hAnn : forall u : Units (ZMod (m * B)), u ^ (E / (l : Nat)) = 1 := by
        intro u
        apply (crt_power_eq_one m B hCoprime u (E / (l : Nat))).mpr
        exact And.intro (hOld _) (hAux _)
      exact prime_quotient_not_annihilating (m * B) l (dvd_trans hl hLE) hAnn
    have hCop : Nat.Coprime K (l : Nat) :=
      (l.property.coprime_iff_not_dvd.mpr hNot).symm
    intro u
    rw [crt_power_eq_one m B hCoprime u (E / (l : Nat))]
    have hPeriod :
        ((unitReduction (dvd_mul_right m B) u) ^ (L / (l : Nat))) ^ (l : Nat) = 1 := by
      rw [<- pow_mul, Nat.div_mul_cancel hl]
      exact Monoid.pow_exponent_eq_one _
    have hOldReturn :
        (unitReduction (dvd_mul_right m B) u) ^ (E / (l : Nat)) = 1 <->
          (unitReduction (dvd_mul_right m B) u) ^ (L / (l : Nat)) = 1 := by
      rw [hQuot, pow_mul]
      exact pow_coprime_period_eq_one _ K (l : Nat) hPeriod hCop
    rw [hOldReturn]
    exact and_iff_left (hAux _) }

theorem preserves_packet_iff_auxiliary_exponent_dvd (m B : Nat)
    [NeZero m] [NeZero B] [NeZero (m * B)] (hCoprime : Nat.Coprime m B)
    (S : Finset Nat.Primes)
    (hDiv : forall l : S, Dvd.dvd (l.val : Nat) (Monoid.exponent (Units (ZMod m)))) :
    (forall l : S, forall u : Units (ZMod (m * B)),
      u ^ (Monoid.exponent (Units (ZMod (m * B))) / (l.val : Nat)) = 1 <->
        (unitReduction (dvd_mul_right m B) u) ^
          (Monoid.exponent (Units (ZMod m)) / (l.val : Nat)) = 1) <->
      (forall l : S, Dvd.dvd (Monoid.exponent (Units (ZMod B)))
        (Monoid.exponent (Units (ZMod (m * B))) / (l.val : Nat))) := by
  constructor
  { intro h l
    exact (preserves_label_iff_auxiliary_exponent_dvd m B hCoprime l.val (hDiv l)).mp (h l) }
  { intro h l
    exact (preserves_label_iff_auxiliary_exponent_dvd m B hCoprime l.val (hDiv l)).mpr (h l) }


theorem canonical_exponent_product_lcm (m B : Nat) (hCoprime : Nat.Coprime m B) :
    Monoid.exponent (Units (ZMod (m * B))) =
      Nat.lcm (Monoid.exponent (Units (ZMod m))) (Monoid.exponent (Units (ZMod B))) := by
  apply Nat.dvd_antisymm
  { apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro u
    apply (crt_power_eq_one m B hCoprime u _).mpr
    exact And.intro
      ((Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (Nat.dvd_lcm_left _ _)) _)
      ((Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (Nat.dvd_lcm_right _ _)) _) }
  { apply Nat.lcm_dvd (old_exponent_dvd m B hCoprime)
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      (auxiliary_exponent_annihilates m B hCoprime) }

/-- If the criterion fails, the identity old base already has a failing lift. -/
theorem nonpreservation_witness_over_identity (m B : Nat)
    (hCoprime : Nat.Coprime m B) (l : Nat)
    (hNot : Not (Dvd.dvd (Monoid.exponent (Units (ZMod B)))
      (Monoid.exponent (Units (ZMod (m * B))) / l))) :
    Exists (fun u : Units (ZMod (m * B)) =>
      And (unitReduction (dvd_mul_right m B) u = 1)
        (Not (u ^ (Monoid.exponent (Units (ZMod (m * B))) / l) = 1))) := by
  classical
  have hExists : Exists (fun b : Units (ZMod B) =>
      Not (b ^ (Monoid.exponent (Units (ZMod (m * B))) / l) = 1)) := by
    apply Classical.byContradiction
    intro hNone
    apply hNot
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro b
    apply Classical.byContradiction
    intro hFail
    exact hNone (Exists.intro b hFail)
  choose b hb using hExists
  let u := (unitProductEquiv m B hCoprime).symm (Prod.mk 1 b)
  refine Exists.intro u (And.intro ?_ ?_)
  { rw [<- unitProductEquiv_fst m B hCoprime]
    exact congrArg Prod.fst ((unitProductEquiv m B hCoprime).apply_symm_apply (Prod.mk 1 b)) }
  { intro h
    have hRed := congrArg (unitReduction (dvd_mul_left B m)) h
    simp only [map_pow, map_one] at hRed
    have hAux : unitReduction (dvd_mul_left B m) u = b := by
      rw [<- unitProductEquiv_snd m B hCoprime]
      exact congrArg Prod.snd ((unitProductEquiv m B hCoprime).apply_symm_apply (Prod.mk 1 b))
    rw [hAux] at hRed
    exact hb hRed }

end PrimeFactorOscillations.CarmichaelProfileCriterion
