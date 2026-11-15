/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianOrbitSigns

/-! # The actual invariant-subset Hamiltonian coefficient

The signed coefficient uses the determinant sign of the actual restricted
permutation. Transport over complete orbit unions identifies it exactly
with the orbit coefficient, over every commutative coefficient ring.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota R : Type*} [Fintype Iota] [DecidableEq Iota] [CommRing R]

theorem hamiltonianInvariant_restriction_sign_cast (f : Equiv.Perm Iota)
    (S : Finset Iota) (hS : hamiltonianPermutationInvariant f S) :
    (-1 : R) ^ S.card *
      ((Equiv.Perm.sign
        (Equiv.Perm.subtypePerm f (p := fun x => Membership.mem S x) hS) : Int) : R) =
        (-1) ^ (hamiltonianSelectedOrbits f S).card := by
  classical
  have h := congrArg (fun u : Units Int => ((u : Int) : R))
    (hamiltonianInvariant_restriction_sign f S hS)
  simpa using h

def hamiltonianInvariantCoefficient (f : Equiv.Perm Iota) : R := by
  classical
  exact -Finset.sum Finset.univ
    (fun S : {S : Finset Iota // hamiltonianPermutationInvariant f S} =>
      (S.val.card : R) * ((-1 : R) ^ S.val.card *
        ((Equiv.Perm.sign (Equiv.Perm.subtypePerm f
          (p := fun x => Membership.mem S.val x) S.property) : Int) : R)))

theorem hamiltonianInvariantCoefficient_eq_orbit (f : Equiv.Perm Iota) :
    hamiltonianInvariantCoefficient (R := R) f =
      hamiltonianPermutationOrbitCoefficient (R := R) f := by
  classical
  let w : {S : Finset Iota // hamiltonianPermutationInvariant f S} -> R :=
    fun S => (S.val.card : R) * ((-1 : R) ^ S.val.card *
      ((Equiv.Perm.sign (Equiv.Perm.subtypePerm f
        (p := fun x => Membership.mem S.val x) S.property) : Int) : R))
  have hSum : Finset.sum Finset.univ w =
      Finset.sum Finset.univ
        (fun C : {C : Finset (Finset Iota) // C <= hamiltonianPermutationOrbits f} =>
          (-1 : R) ^ C.val.card * ((hamiltonianOrbitUnion C.val).card : R)) := by
    calc
      _ = Finset.sum Finset.univ
          (fun C : {C : Finset (Finset Iota) // C <= hamiltonianPermutationOrbits f} =>
            w (hamiltonianOrbitInvariantEquiv f C)) :=
        (Equiv.sum_comp (hamiltonianOrbitInvariantEquiv f) w).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro C hC
        change ((hamiltonianOrbitUnion C.val).card : R) *
            ((-1 : R) ^ (hamiltonianOrbitUnion C.val).card *
              ((Equiv.Perm.sign (Equiv.Perm.subtypePerm f
                (p := fun x => Membership.mem (hamiltonianOrbitUnion C.val) x)
                (hamiltonianOrbitUnion_invariant f C.val C.property)) : Int) : R)) =
          (-1 : R) ^ C.val.card * ((hamiltonianOrbitUnion C.val).card : R)
        rw [hamiltonianInvariant_restriction_sign_cast,
          hamiltonianSelectedOrbits_union f C.val C.property]
        exact mul_comm _ _
  have hPower :
      Finset.sum (hamiltonianPermutationOrbits f).powerset
          (fun C => (-1 : R) ^ C.card * ((hamiltonianOrbitUnion C).card : R)) =
        Finset.sum Finset.univ
          (fun C : {C : Finset (Finset Iota) // C <= hamiltonianPermutationOrbits f} =>
            (-1 : R) ^ C.val.card * ((hamiltonianOrbitUnion C.val).card : R)) :=
    Finset.sum_subtype (hamiltonianPermutationOrbits f).powerset
      (fun _ => Finset.mem_powerset)
      (fun C => (-1 : R) ^ C.card * ((hamiltonianOrbitUnion C).card : R))
  change -Finset.sum Finset.univ w =
    -Finset.sum (hamiltonianPermutationOrbits f).powerset
      (fun C => (-1 : R) ^ C.card * ((hamiltonianOrbitUnion C).card : R))
  rw [hSum, hPower]

theorem hamiltonianInvariantCoefficient_eq (f : Equiv.Perm Iota) :
    hamiltonianInvariantCoefficient (R := R) f =
      if (hamiltonianPermutationOrbits f).card = 1 then (Fintype.card Iota : R) else 0 :=
  (hamiltonianInvariantCoefficient_eq_orbit f).trans
    (hamiltonianPermutationOrbitCoefficient_eq f)

end PrimeFactorOscillations
