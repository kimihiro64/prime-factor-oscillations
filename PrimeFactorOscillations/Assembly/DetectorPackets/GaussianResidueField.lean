/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import PrimeFactorOscillations.Proof.DetectorPackets.GaussianEuclidean
import PrimeFactorOscillations.Proof.DetectorPackets.GaussianLatticeCount

/-!
# GaussianResidueField

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
# Finite Gaussian residue fields for the actual character sieve

Euclidean remainders map the previously checked Gaussian norm ball onto
each nonzero principal quotient. The construction is on Zsqrtd (-1).
The cardinality bound is an upper bound; equality with the Gaussian norm
is a separate obligation.
-/


noncomputable section
namespace PrimeFactorOscillations.GaussianResidueField

abbrev G := Zsqrtd (-1)

abbrev Quotient (I : Ideal G) := HasQuotient.Quotient G I

def principal (p : G) : Ideal G := Ideal.span ({p} : Set G)

abbrev Residue (p : G) := Quotient (principal p)

def representativeMap (I : Ideal G) (N : Nat) :
    {x : G // Membership.mem (GaussianLatticeCount.ball N) x} -> Quotient I :=
  fun x => (Ideal.Quotient.mk I) x.val

theorem map_mod_eq (I : Ideal G) (p x : G) (hp : Membership.mem I p) :
    (Ideal.Quotient.mk I) (x%p) = (Ideal.Quotient.mk I) x := by
  rw [GaussianArithmetic.GaussianInt.mod_def, map_sub, map_mul]
  have hp0 : (Ideal.Quotient.mk I) p = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hp
  rw [hp0, zero_mul, sub_zero]

theorem representativeMap_surjective (I : Ideal G) (p : G)
    (hp : Membership.mem I p) (hpn : Not (p = 0)) :
    Function.Surjective (representativeMap I p.norm.natAbs) := by
  classical
  intro y
  choose x hx using Ideal.Quotient.mk_surjective y
  have hr : Membership.mem (GaussianLatticeCount.ball p.norm.natAbs) (x%p) := by
    apply (GaussianLatticeCount.mem_ball p.norm.natAbs (x%p)).mpr
    simpa only [GaussianArithmetic.GaussianInt.abs_natCast_norm] using
      le_of_lt (GaussianArithmetic.GaussianInt.norm_mod_lt x hpn)
  refine Exists.intro (Subtype.mk (x%p) hr) ?_
  exact (map_mod_eq I p x hp).trans hx

theorem finite_quotient_of_nonzero_mem (I : Ideal G) (p : G)
    (hp : Membership.mem I p) (hpn : Not (p = 0)) :
    Finite (Quotient I) := by
  classical
  exact Finite.of_surjective (representativeMap I p.norm.natAbs)
    (representativeMap_surjective I p hp hpn)

instance hasFiniteQuotients : Ring.HasFiniteQuotients G where
  finiteQuotient := by
    intro I hI
    classical
    have hex : Exists (fun p : G => Membership.mem I p /\ Not (p = 0)) := by
      by_contra hn
      apply hI
      apply SetLike.ext
      intro x
      constructor
      . intro hx
        change x = 0
        by_contra hxn
        exact hn (Exists.intro x (And.intro hx hxn))
      . intro hx
        change x = 0 at hx
        rw [hx]
        exact I.zero_mem
    choose p hp using hex
    exact finite_quotient_of_nonzero_mem I p hp.1 hp.2

theorem principal_mem (p : G) : Membership.mem (principal p) p :=
  Ideal.subset_span (by simp)

theorem finite_residue (p : G) (hp : Not (p = 0)) : Finite (Residue p) :=
  finite_quotient_of_nonzero_mem (principal p) p (principal_mem p) hp

@[instance_reducible] def residueFintype (p : G) (hp : Not (p = 0)) : Fintype (Residue p) := by
  letI := finite_residue p hp
  exact Fintype.ofFinite (Residue p)

theorem residue_card_le (p : G) (hp : Not (p = 0)) :
    @Fintype.card (Residue p) (residueFintype p hp) <= 9*p.norm.natAbs := by
  classical
  let _ := residueFintype p hp
  have hN : 1 <= p.norm.natAbs := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro hn
    exact hp (GaussianArithmetic.GaussianInt.norm_eq_zero.mp (Int.natAbs_eq_zero.mp hn))
  calc
    Fintype.card (Residue p) <=
        Fintype.card {x : G // Membership.mem (GaussianLatticeCount.ball p.norm.natAbs) x} :=
      Fintype.card_le_of_surjective (representativeMap (principal p) p.norm.natAbs)
        (representativeMap_surjective (principal p) p (principal_mem p) hp)
    _ = (GaussianLatticeCount.ball p.norm.natAbs).card :=
      Fintype.card_coe (GaussianLatticeCount.ball p.norm.natAbs)
    _ <= 9*p.norm.natAbs := GaussianLatticeCount.ball_card_le p.norm.natAbs hN

theorem prime_isMaximal (p : G) (hp : Prime p) : (principal p).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible

@[instance_reducible] def residueField (p : G) (hp : Prime p) : Field (Residue p) := by
  letI := prime_isMaximal p hp
  exact Ideal.Quotient.field (principal p)

theorem mk_eq_zero_iff_dvd (p x : G) :
    (Ideal.Quotient.mk (principal p)) x = 0 <-> Dvd.dvd p x := by
  rw [Ideal.Quotient.eq_zero_iff_mem, principal, Ideal.mem_span_singleton]

theorem mk_ne_zero_of_not_dvd (p x : G) (h : Not (Dvd.dvd p x)) :
    Not ((Ideal.Quotient.mk (principal p)) x = 0) := by
  intro hh
  exact h ((mk_eq_zero_iff_dvd p x).mp hh)

theorem residue_two_ne_zero (p : G) (hodd : Not (Dvd.dvd p (2:G))) :
    Not ((2:Residue p) = 0) := by
  have htwo : (Ideal.Quotient.mk (principal p)) (2:G) = (2:Residue p) := by
    have hh : (2:G) = 1+1 := by norm_num
    rw [hh, map_add, map_one]
    norm_num
  intro hh
  exact mk_ne_zero_of_not_dvd p (2:G) hodd (htwo.trans hh)

def imaginaryUnit : G := Zsqrtd.mk 0 1

theorem imaginaryUnit_sq : imaginaryUnit^2 = -(1:G) := by
  apply Zsqrtd.ext <;> norm_num [imaginaryUnit, pow_two]

def residueI (p : G) : Residue p :=
  (Ideal.Quotient.mk (principal p)) imaginaryUnit

theorem residueI_sq (p : G) : (residueI p)^2 = -(1:Residue p) := by
  unfold residueI
  rw [<-map_pow, imaginaryUnit_sq, map_neg, map_one]

end PrimeFactorOscillations.GaussianResidueField

