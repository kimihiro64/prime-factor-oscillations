/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.PrimePowerComponentInfiniteProjection

/-!
# Geometric coordinates of the full component reference law

Finite prescribed prime valuations determine one supported component atom.
Its exact mass factors into the normalized geometric coordinate masses.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.PrimeClassSampling

noncomputable def finitePrimeValuationPattern (s : Finset Nat) (k : Nat -> Nat) :
    Finsupp Nat Nat := by
  classical
  exact Finsupp.onFinset s (fun p => if Membership.mem s p then k p else 0)
    (by
      intro p hp
      by_contra hnot
      exact hp (ite_eq_right hnot))

theorem finitePrimeValuationPattern_apply (s : Finset Nat) (k : Nat -> Nat) (p : Nat) :
    finitePrimeValuationPattern s k p =
      @ite Nat (Membership.mem s p) (Classical.propDecidable _) (k p) 0 := by
  classical
  simp [finitePrimeValuationPattern]

def finitePrimeValuationAtom (s : Finset Nat) (k : Nat -> Nat) : Nat :=
  s.prod (fun p => p ^ k p)

theorem finitePrimeValuationAtom_pos
    (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p) (k : Nat -> Nat) :
    0 < finitePrimeValuationAtom s k := by
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (hprime p hp).pos _

theorem finitePrimeValuationAtom_factorization
    (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p) (k : Nat -> Nat) :
    (finitePrimeValuationAtom s k).factorization = finitePrimeValuationPattern s k := by
  classical
  have hsupport : forall p : Nat,
      Membership.mem (finitePrimeValuationPattern s k).support p ->
        Membership.mem s p := by
    intro p hp
    have hn := Finsupp.mem_support_iff.mp hp
    by_contra hnot
    exact hn (by rw [finitePrimeValuationPattern_apply, ite_eq_right hnot])
  have hprod : (finitePrimeValuationPattern s k).prod (fun p e => p ^ e) =
      finitePrimeValuationAtom s k := by
    rw [Finsupp.prod_of_support_subset _ hsupport
      (fun p e => p ^ e) (by intro p hp; exact pow_zero p)]
    apply Finset.prod_congr rfl
    intro p hp
    rw [finitePrimeValuationPattern_apply, ite_eq_left hp]
  rw [<- hprod]
  apply Nat.prod_pow_factorization_eq_self
  intro p hp
  exact hprime p (hsupport p hp)

theorem finitePrimeValuationAtom_supported
    (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p) (k : Nat -> Nat) :
    primePowerSupportedOn s (finitePrimeValuationAtom s k) := by
  classical
  refine And.intro (finitePrimeValuationAtom_pos s hprime k) ?_
  intro p hp
  rw [finitePrimeValuationAtom_factorization s hprime k] at hp
  have hn := Finsupp.mem_support_iff.mp hp
  by_contra hnot
  exact hn (by rw [finitePrimeValuationPattern_apply, ite_eq_right hnot])

theorem finitePrimePowerComponent_eq_valuationAtom_iff
    (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p)
    (k : Nat -> Nat) (m : Nat) :
    finitePrimePowerComponent s m = finitePrimeValuationAtom s k <->
      forall p : Nat, Membership.mem s p -> m.factorization p = k p := by
  classical
  constructor
  case mp =>
    intro h p hp
    have hv := congrArg (fun n : Nat => n.factorization p) h
    rw [finitePrimePowerComponent_factorization s hprime m,
      Finsupp.filter_apply, ite_eq_left hp,
      finitePrimeValuationAtom_factorization s hprime k,
      finitePrimeValuationPattern_apply, ite_eq_left hp] at hv
    exact hv
  case mpr =>
    intro h
    have hf : (finitePrimePowerComponent s m).factorization =
        (finitePrimeValuationAtom s k).factorization := by
      apply Finsupp.ext
      intro p
      rw [finitePrimePowerComponent_factorization s hprime m,
        Finsupp.filter_apply, finitePrimeValuationAtom_factorization s hprime k,
        finitePrimeValuationPattern_apply]
      by_cases hp : Membership.mem s p
      case pos =>
        rw [ite_eq_left hp, ite_eq_left hp]
        exact h p hp
      case neg => rw [ite_eq_right hp, ite_eq_right hp]
    calc
      _ = (finitePrimePowerComponent s m).factorization.prod
          (fun p e => p ^ e) :=
        (Nat.prod_factorization_pow_eq_self
          (Nat.ne_of_gt (finitePrimePowerComponent_pos s hprime m))).symm
      _ = (finitePrimeValuationAtom s k).factorization.prod
          (fun p e => p ^ e) := congrArg (fun f => f.prod (fun p e => p ^ e)) hf
      _ = _ := Nat.prod_factorization_pow_eq_self
        (Nat.ne_of_gt (finitePrimeValuationAtom_pos s hprime k))

theorem finitePrimePowerReference_valuationAtom
    (s : Finset Nat)
    (hprime : forall p : Nat, Membership.mem s p -> Nat.Prime p) (k : Nat -> Nat) :
    finitePrimePowerReference s (finitePrimeValuationAtom s k) =
      s.prod (fun p => (1 - 1 / (p : Real)) / (p : Real) ^ k p) := by
  classical
  unfold finitePrimePowerReference
  rw [ite_eq_left (finitePrimeValuationAtom_supported s hprime k)]
  simp only [finitePrimeComponentSurvival, finitePrimeValuationAtom,
    Nat.cast_prod, Nat.cast_pow, Finset.prod_div_distrib]

end PrimeFactorOscillations.PrimeClassSampling
