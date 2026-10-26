/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelPrimePowerChebyshev
import PrimeFactorOscillations.Helpers.TwoPowerCharacterConductor

/-!
# Native two-power spectral rigidity and genuine zero masks

Every level 2^(a+4) has actual return index two. All nonprincipal survivors
are even quadratic characters with primitive conductor exactly eight and
coefficient one. The original kernel takes exactly the Boolean values
zero and two. The exceptional levels two, four and eight are explicit.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelTwoPowerConductor

open CarmichaelPrimePacket CarmichaelCorrelation CarmichaelCorrelationSpectrum
open CarmichaelPrimePacketSpectrum PrimeOrderReturnLaw PrimeOrderReturnIndex
open TwoPowerCharacterConductor

def labelTwo : Nat.Primes := Subtype.mk 2 Nat.prime_two

theorem two_divides_exponent (a : Nat) :
    Dvd.dvd 2 (Monoid.exponent (Units (ZMod (2 ^ (a + 3))))) := by
  rw [unit_exponent]
  exact dvd_pow_self 2 (by omega : Not (a + 1 = 0))

theorem large_half_exponent (a : Nat) :
    Monoid.exponent (Units (ZMod (2 ^ (a + 4)))) / 2 = 2 ^ (a + 1) := by
  rw [unit_exponent (a + 1)]
  rw [pow_succ, Nat.mul_div_cancel _ (by decide : 0 < 2)]

theorem large_index (a : Nat) :
    index (2 ^ (a + 4)) labelTwo = 2 := by
  have hLow := index_ge_two (2 ^ (a + 4)) labelTwo (two_divides_exponent (a + 1))
  have hHigh : index (2 ^ (a + 4)) labelTwo <= 2 := by
    change returnIndex (G := Units (ZMod (2 ^ (a + 4))))
      (Monoid.exponent (Units (ZMod (2 ^ (a + 4))))) 2 <= 2
    rw [returnIndex_eq_natCard]
    change Nat.card ((powMonoidHom
      (Monoid.exponent (Units (ZMod (2 ^ (a + 4)))) / 2) :
        MonoidHom (Units (ZMod (2 ^ (a + 4))))
          (Units (ZMod (2 ^ (a + 4))))).range) <= 2
    rw [large_half_exponent]
    exact shortened_image_card_le_two a
  omega

theorem large_survivor_even (a : Nat)
    (chi : DirichletCharacter Complex (2 ^ (a + 4)))
    (hNonzero : Not (coefficient (weight (2 ^ (a + 4)) labelTwo) chi = 0)) :
    chi (-1 : ZMod (2 ^ (a + 4))) = 1 := by
  have hReturn : (-1 : Units (ZMod (2 ^ (a + 4)))) ^
      (Monoid.exponent (Units (ZMod (2 ^ (a + 4)))) / 2) = 1 := by
    rw [large_half_exponent]
    calc
      (-1 : Units (ZMod (2 ^ (a + 4)))) ^ (2 ^ (a + 1)) =
          (-1 : Units (ZMod (2 ^ (a + 4)))) ^ (2 * 2 ^ a) :=
        congrArg (fun n : Nat => (-1 : Units (ZMod (2 ^ (a + 4)))) ^ n)
          (pow_succ' 2 a)
      _ = ((-1 : Units (ZMod (2 ^ (a + 4)))) ^ 2) ^ (2 ^ a) :=
        pow_mul _ _ _
      _ = 1 := by rw [neg_one_sq, one_pow]
  exact (coefficient_nonzero_iff_trivial_return (2 ^ (a + 4)) labelTwo
    (two_divides_exponent (a + 1)) chi).mp hNonzero (-1) hReturn

theorem large_survivor_factorsThrough_eight (a : Nat)
    (chi : DirichletCharacter Complex (2 ^ (a + 4)))
    (hNonzero : Not (coefficient (weight (2 ^ (a + 4)) labelTwo) chi = 0)) :
    chi.FactorsThrough 8 :=
  quadratic_factorsThrough_eight (a + 1) chi
    (nonzero_coefficient_prime_power (2 ^ (a + 4)) labelTwo
      (two_divides_exponent (a + 1)) chi hNonzero)

theorem large_nonprincipal_survivor_conductor (a : Nat)
    (chi : DirichletCharacter Complex (2 ^ (a + 4)))
    (hNonzero : Not (coefficient (weight (2 ^ (a + 4)) labelTwo) chi = 0))
    (hChi : Not (chi = 1)) :
    chi.conductor = 8 :=
  even_quadratic_nonprincipal_conductor (a + 1) chi
    (nonzero_coefficient_prime_power (2 ^ (a + 4)) labelTwo
      (two_divides_exponent (a + 1)) chi hNonzero)
    (large_survivor_even a chi hNonzero) hChi

theorem large_nonprincipal_coefficient (a : Nat)
    (chi : DirichletCharacter Complex (2 ^ (a + 4)))
    (hNonzero : Not (coefficient (weight (2 ^ (a + 4)) labelTwo) chi = 0))
    (hChi : Not (chi = 1)) :
    coefficient (weight (2 ^ (a + 4)) labelTwo) chi = 1 := by
  rw [coefficient_of_trivial_return (2 ^ (a + 4)) labelTwo
    (two_divides_exponent (a + 1)) chi hChi
    ((coefficient_nonzero_iff_trivial_return (2 ^ (a + 4)) labelTwo
      (two_divides_exponent (a + 1)) chi).mp hNonzero), large_index]
  norm_num

theorem large_kernel_boolean (a : Nat)
    (u : Units (ZMod (2 ^ (a + 4)))) :
    kernel (weight (2 ^ (a + 4)) labelTwo) u =
      if CarmichaelCorrelationLocal.returnBit
        (Monoid.exponent (Units (ZMod (2 ^ (a + 4))))) 2 u then 2 else 0 := by
  rw [kernel_closed (2 ^ (a + 4)) labelTwo
    (two_divides_exponent (a + 1)) u, large_index]
  simp only [labelTwo]
  split_ifs <;> simp_all <;> norm_num

theorem large_zero_mask_iff (a : Nat)
    (u : Units (ZMod (2 ^ (a + 4)))) :
    kernel (weight (2 ^ (a + 4)) labelTwo) u = 0 <->
      Not (CarmichaelCorrelationLocal.returnBit
        (Monoid.exponent (Units (ZMod (2 ^ (a + 4))))) 2 u) := by
  rw [large_kernel_boolean]
  split_ifs <;> simp_all

theorem exists_large_conductor_eight_survivor (a : Nat) :
    exists chi : DirichletCharacter Complex (2 ^ (a + 4)),
      Not (chi = 1) /\ chi.conductor = 8 /\
        coefficient (weight (2 ^ (a + 4)) labelTwo) chi = 1 := by
  choose chi hChi hSquare hCoefficient using exists_nonprincipal_prime_character
    (2 ^ (a + 4)) labelTwo (two_divides_exponent (a + 1))
  have hCoefficientOne : coefficient (weight (2 ^ (a + 4)) labelTwo) chi = 1 := by
    rw [large_index] at hCoefficient
    norm_num at hCoefficient
    exact hCoefficient
  have hNonzero : Not (coefficient (weight (2 ^ (a + 4)) labelTwo) chi = 0) := by
    rw [hCoefficientOne]
    norm_num
  exact Exists.intro chi (And.intro hChi
    (And.intro (large_nonprincipal_survivor_conductor a chi hNonzero hChi)
      hCoefficientOne))

theorem level_two_inadmissible :
    Not (Dvd.dvd 2 (Monoid.exponent (Units (ZMod 2)))) := by
  let : IsCyclic (Units (ZMod 2)) := ZMod.isCyclic_units_two
  rw [IsCyclic.exponent_eq_card, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  norm_num

theorem level_four_index : index 4 labelTwo = 2 := by
  let : IsCyclic (Units (ZMod 4)) := ZMod.isCyclic_units_four
  change returnIndex (G := Units (ZMod 4)) (Monoid.exponent (Units (ZMod 4))) 2 = 2
  rw [returnIndex_cyclic, IsCyclic.exponent_eq_card, Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient]
  decide

theorem level_eight_index : index 8 labelTwo = 4 := by
  change returnIndex (G := Units (ZMod 8)) (Monoid.exponent (Units (ZMod 8))) 2 = 4
  rw [returnIndex_eq_natCard]
  have hQuot : Monoid.exponent (Units (ZMod 8)) / 2 = 1 := by
    change Monoid.exponent (Units (ZMod (2 ^ (0 + 3)))) / 2 = 1
    rw [unit_exponent 0]
    decide
  change Nat.card ((powMonoidHom (Monoid.exponent (Units (ZMod 8)) / 2) :
    MonoidHom (Units (ZMod 8)) (Units (ZMod 8))).range) = 4
  rw [hQuot]
  have hRange : (powMonoidHom 1 :
      MonoidHom (Units (ZMod 8)) (Units (ZMod 8))).range = Top.top := by
    apply MonoidHom.range_eq_top.mpr
    intro v
    exact Exists.intro v (pow_one v)
  rw [hRange, Subgroup.card_top, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  decide

theorem level_four_nonprincipal_conductor
    (chi : DirichletCharacter Complex 4) (hChi : Not (chi = 1)) :
    chi.conductor = 4 :=
  nonprincipal_conductor_four chi hChi

theorem level_eight_nonprincipal_conductor
    (chi : DirichletCharacter Complex 8) (hChi : Not (chi = 1)) :
    Or (chi.conductor = 4) (chi.conductor = 8) :=
  nonprincipal_conductor_four_or_eight (by decide) chi chi.conductor_dvd_level hChi

theorem large_other_coefficient_zero (a : Nat)
    (chi psi : DirichletCharacter Complex (2 ^ (a + 4)))
    (hChi : Not (chi = 1))
    (hNonzero : Not (coefficient (weight (2 ^ (a + 4)) labelTwo) chi = 0))
    (hPsi : Not (psi = 1)) (hNe : Not (psi = chi)) :
    coefficient (weight (2 ^ (a + 4)) labelTwo) psi = 0 := by
  classical
  let T := Finset.univ.erase (1 : DirichletCharacter Complex (2 ^ (a + 4)))
  let c := coefficient (weight (2 ^ (a + 4)) labelTwo)
  have hMass : T.sum c = 1 := by
    have h := nonprincipal_coefficient_mass (2 ^ (a + 4)) labelTwo
      (two_divides_exponent (a + 1))
    rw [large_index] at h
    change T.sum c = 1 / ((2 : Real) - 1) at h
    calc
      T.sum c = 1 / ((2 : Real) - 1) := h
      _ = 1 := by norm_num
  have hOne : c chi = 1 := large_nonprincipal_coefficient a chi hNonzero hChi
  have hMem : Membership.mem T chi := by simp [T, hChi]
  have hErase : (T.erase chi).sum c = 0 := by
    have h := Finset.sum_erase_add T c hMem
    rw [hMass, hOne] at h
    linarith
  have hMemPsi : Membership.mem (T.erase chi) psi := by simp [T, hPsi, hNe]
  have hLe := Finset.single_le_sum
    (fun gamma _ => coefficient_nonneg (weight (2 ^ (a + 4)) labelTwo) gamma) hMemPsi
  change c psi <= (T.erase chi).sum c at hLe
  rw [hErase] at hLe
  exact le_antisymm hLe (coefficient_nonneg _ psi)

theorem large_survivor_unique (a : Nat)
    (chi psi : DirichletCharacter Complex (2 ^ (a + 4)))
    (hChi : Not (chi = 1))
    (hChiNonzero : Not (coefficient (weight (2 ^ (a + 4)) labelTwo) chi = 0))
    (hPsi : Not (psi = 1))
    (hPsiNonzero : Not (coefficient (weight (2 ^ (a + 4)) labelTwo) psi = 0)) :
    chi = psi := by
  apply Classical.byContradiction
  intro hNe
  exact hPsiNonzero
    (large_other_coefficient_zero a chi psi hChi hChiNonzero hPsi (Ne.symm hNe))

theorem exists_unique_large_nonprincipal_mode (a : Nat) :
    ExistsUnique (fun chi : DirichletCharacter Complex (2 ^ (a + 4)) =>
      Not (chi = 1) /\
        coefficient (weight (2 ^ (a + 4)) labelTwo) chi = 1 /\
          chi.conductor = 8) := by
  choose chi hChi hConductor hCoefficient using exists_large_conductor_eight_survivor a
  have hNonzero : Not (coefficient (weight (2 ^ (a + 4)) labelTwo) chi = 0) := by
    rw [hCoefficient]
    norm_num
  refine Exists.intro chi (And.intro
    (And.intro hChi (And.intro hCoefficient hConductor)) ?_)
  intro psi hPsi
  have hPsiNonzero : Not (coefficient (weight (2 ^ (a + 4)) labelTwo) psi = 0) := by
    rw [hPsi.right.left]
    norm_num
  exact large_survivor_unique a psi chi hPsi.left hPsiNonzero hChi hNonzero

theorem large_kernel_two_modes (a : Nat)
    (chi : DirichletCharacter Complex (2 ^ (a + 4)))
    (hChi : Not (chi = 1))
    (hNonzero : Not (coefficient (weight (2 ^ (a + 4)) labelTwo) chi = 0))
    (u : Units (ZMod (2 ^ (a + 4)))) :
    (kernel (weight (2 ^ (a + 4)) labelTwo) u : Complex) =
      1 + unitCharacter chi (Inv.inv u) := by
  classical
  let f := fun psi : DirichletCharacter Complex (2 ^ (a + 4)) =>
    (coefficient (weight (2 ^ (a + 4)) labelTwo) psi : Complex) *
      unitCharacter psi (Inv.inv u)
  have hSum : Finset.univ.sum f = ({1, chi} : Finset _).sum f := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro psi _ hNot
    have hPsi : Not (psi = 1) := by
      intro h
      apply hNot
      simp [h]
    have hNe : Not (psi = chi) := by
      intro h
      apply hNot
      simp [h]
    rw [large_other_coefficient_zero a chi psi hChi hNonzero hPsi hNe]
    simp
  rw [kernel_expansion]
  change Finset.univ.sum f = _
  rw [hSum]
  have hPrincipal := coefficient_principal (weight (2 ^ (a + 4)) labelTwo)
    (weightSum_pos (2 ^ (a + 4)) labelTwo (two_divides_exponent (a + 1)))
  have hOne := large_nonprincipal_coefficient a chi hNonzero hChi
  simp [f, Ne.symm hChi, hPrincipal, hOne, unitCharacter_one]

theorem exists_large_survivor_chebyshev_bound :
    exists A : Real, And (0 < A)
      (forall (a : Nat) (chi : DirichletCharacter Complex (2 ^ (a + 4))),
        Not (coefficient (weight (2 ^ (a + 4)) labelTwo) chi = 0) ->
        Not (chi = 1) -> forall {x : Nat}, 2 <= x ->
          norm (BombieriVinogradov.SiegelWalfisz.characterChebyshevSum x chi) <=
            A * (x : Real) ^ (7 / 8 : Real) *
              (1 + 3 * Real.log 2 + Real.log ((x : Real) + 2)) ^ 2) := by
  choose A hA hBound using CarmichaelPrimePowerChebyshev.exists_primePower_chebyshev_bound
  refine Exists.intro A (And.intro hA ?_)
  intro a chi hNonzero hChi x hx
  have hConductor := large_nonprincipal_survivor_conductor a chi hNonzero hChi
  have h := hBound 2 (a + 1) 2 chi hConductor hChi hx
  norm_num at h
  exact h

theorem level_four_kernel_boolean (u : Units (ZMod 4)) :
    kernel (weight 4 labelTwo) u =
      if CarmichaelCorrelationLocal.returnBit
        (Monoid.exponent (Units (ZMod 4))) 2 u then 2 else 0 := by
  rw [kernel_closed 4 labelTwo
    (PrimePowerWildCharacterConductor.prime_dvd_exponent 2 0 Nat.prime_two) u,
    level_four_index]
  simp only [labelTwo]
  split_ifs <;> simp_all <;> norm_num

theorem level_eight_kernel_positive (u : Units (ZMod 8)) :
    kernel (weight 8 labelTwo) u =
      if CarmichaelCorrelationLocal.returnBit
        (Monoid.exponent (Units (ZMod 8))) 2 u then 4 / 3 else 8 / 9 := by
  rw [kernel_closed 8 labelTwo (two_divides_exponent 0) u, level_eight_index]
  simp only [labelTwo]
  split_ifs <;> simp_all <;> norm_num

end PrimeFactorOscillations.CarmichaelTwoPowerConductor
