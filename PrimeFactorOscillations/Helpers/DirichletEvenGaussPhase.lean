/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import OAI.NumberTheory.DirichletL.CubicSieve.PairPoisson

/-!
# Actual even Dirichlet Gauss phases

At a prime modulus, for any primitive additive character, every
nonprincipal even character has its normalized native Gauss phase. Principal and odd characters are assigned phase one.
The resulting phase is unitary and compatible with character inversion.
Cubic characters are even, so their phase uses the actual Gauss sum.
These are finite phase identities, not a prime-sampled estimate.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.DirichletEvenGaussPhase


def phase (q : Nat) [NeZero q] (psi : AddChar (ZMod q) Complex)
    (chi : DirichletCharacter Complex q) : Complex := by
  classical
  exact if chi = 1 then 1 else if chi (-1) = 1 then
    ((Inv.inv (Real.sqrt (Fintype.card (ZMod q))) : Real) : Complex) *
      gaussSum chi psi else 1

theorem phase_principal (q : Nat) [NeZero q] (psi : AddChar (ZMod q) Complex) :
    phase q psi (1 : DirichletCharacter Complex q) = 1 := by
  classical
  simp [phase]

theorem phase_norm (q : Nat) [NeZero q] [Fact (Nat.Prime q)]
    (psi : AddChar (ZMod q) Complex) (hPsi : psi.IsPrimitive)
    (chi : DirichletCharacter Complex q) : norm (phase q psi chi) = 1 := by
  classical
  unfold phase
  split_ifs with hp he
  . exact norm_one
  . simpa only [Complex.ofReal_inv] using OAI.ShortDraftGauss.norm_normalized_gaussSum
      chi psi hp hPsi
  . exact norm_one

theorem phase_inverse (q : Nat) [NeZero q] (psi : AddChar (ZMod q) Complex)
    (chi : DirichletCharacter Complex q) :
    phase q psi (Inv.inv chi) = star (phase q psi chi) := by
  classical
  by_cases hp : chi = 1
  . subst chi
    simp only [inv_one, phase_principal, star_one]
  . have hi : Not (Inv.inv chi = 1) := inv_ne_one.mpr hp
    by_cases he : chi (-1) = 1
    . have hie : (Inv.inv chi) (-1) = 1 := by
        rw [MulChar.inv_apply_eq_inv', he, inv_one]
      simp only [phase, if_neg hp, if_neg hi, if_pos he, if_pos hie]
      rw [OAI.SevenEighths.CubicSieve.gaussSum_inverse_of_even chi psi he]
      change _ = (starRingEnd Complex) _
      rw [map_mul, Complex.conj_ofReal]
      rfl
    . have hie : Not ((Inv.inv chi) (-1) = 1) := by
        rw [MulChar.inv_apply_eq_inv']
        exact inv_ne_one.mpr he
      simp only [phase, if_neg hp, if_neg hi, if_neg he, if_neg hie, star_one]

theorem cubic_even (q : Nat) [NeZero q] (chi : DirichletCharacter Complex q)
    (hCube : chi ^ 3 = 1) : chi (-1) = 1 := by
  have hTwo : chi (-1) ^ 2 = 1 := by
    have h := map_pow chi (-1 : ZMod q) 2
    have hs : (-1 : ZMod q) ^ 2 = 1 := by ring
    rw [hs, map_one] at h
    exact h.symm
  have hThree : chi (-1) ^ 3 = 1 := by
    rw [<- MulChar.pow_apply' _ (by decide : Not ((3 : Nat) = 0)), hCube]
    exact MulChar.one_apply (isUnit_one.neg : IsUnit (-1 : ZMod q))
  calc
    _ = chi (-1) * 1 := (mul_one _).symm
    _ = chi (-1) * chi (-1) ^ 2 := by rw [hTwo]
    _ = chi (-1) ^ 3 := by ring
    _ = 1 := hThree

theorem phase_cubic (q : Nat) [NeZero q] (psi : AddChar (ZMod q) Complex)
    (chi : DirichletCharacter Complex q)
    (hChi : Not (chi = 1)) (hCube : chi ^ 3 = 1) :
    phase q psi chi =
      ((Inv.inv (Real.sqrt (Fintype.card (ZMod q))) : Real) : Complex) *
        gaussSum chi psi := by
  classical
  simp only [phase, if_neg hChi, if_pos (cubic_even q chi hCube)]

end PrimeFactorOscillations.DirichletEvenGaussPhase
