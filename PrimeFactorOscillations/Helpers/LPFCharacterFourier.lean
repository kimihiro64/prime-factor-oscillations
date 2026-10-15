/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.DirichletCharacter.ResidueCount
import PrimeFactorOscillations.Mathlib.NumberTheory.GaussSum.FiniteRingEnergy

/-!
# Exact unit Fourier transfer

Character reconstruction and Parseval retain the principal coefficient.
The weighted centered transfer has square-root totient cost. Nonunit inputs
are excluded explicitly here and must be retained by any full-sum consumer.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

namespace PrimeFactorOscillations.LPF

private theorem unit_inverse_value {N : Nat} [NeZero N] (b : Units (ZMod N)) :
    ((Inv.inv b : Units (ZMod N)) : ZMod N) = Inv.inv (b : ZMod N) := by
  have hProd : Inv.inv (b : ZMod N) * (b : ZMod N) = 1 :=
    (ZMod.inv_mul_eq_one_of_isUnit b.isUnit (b : ZMod N)).mpr rfl
  calc
    _ = ((Inv.inv b : Units (ZMod N)) : ZMod N) *
        (Inv.inv (b : ZMod N) * (b : ZMod N)) := by rw [hProd, mul_one]
    _ = Inv.inv (b : ZMod N) *
        (((Inv.inv b : Units (ZMod N)) : ZMod N) * (b : ZMod N)) := by ring
    _ = _ := by simp

noncomputable def unitFourierCoefficient {N : Nat} [NeZero N]
    (g : ZMod N -> Complex) (chi : DirichletCharacter Complex N) : Complex :=
  Finset.sum Finset.univ (fun a : Units (ZMod N) =>
    g (a : ZMod N) * chi ((Inv.inv a : Units (ZMod N)) : ZMod N))

theorem unitFourier_reconstruction {N : Nat} [NeZero N]
    (g : ZMod N -> Complex) (a : Units (ZMod N)) :
    Finset.sum Finset.univ (fun chi : DirichletCharacter Complex N =>
      unitFourierCoefficient g chi * chi (a : ZMod N)) =
        (N.totient : Complex) * g (a : ZMod N) := by
  classical
  simp only [unitFourierCoefficient, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hAt (b : Units (ZMod N)) :
      Finset.sum Finset.univ (fun chi : DirichletCharacter Complex N =>
        (g (b : ZMod N) * chi ((Inv.inv b : Units (ZMod N)) : ZMod N)) *
          chi (a : ZMod N)) =
      g (b : ZMod N) * (if b = a then (N.totient : Complex) else 0) := by
    simp only [mul_assoc, <- Finset.mul_sum]
    have hInv : ((Inv.inv b : Units (ZMod N)) : ZMod N) = Inv.inv (b : ZMod N) :=
      unit_inverse_value b
    rw [hInv]
    have hOrth := DirichletCharacter.sum_char_inv_mul_char_eq Complex b.isUnit (a : ZMod N)
    rw [hOrth]
    by_cases h : b = a
    . simp [h]
    . have hVal : Not ((b : ZMod N) = (a : ZMod N)) := fun hh => h (Units.ext hh)
      simp [h, hVal]
  simp_rw [hAt]
  simp [mul_comm]

theorem unitFourier_cross_orthogonality {N : Nat} [NeZero N]
    (a b : Units (ZMod N)) :
    Finset.sum Finset.univ (fun chi : DirichletCharacter Complex N =>
      chi ((Inv.inv a : Units (ZMod N)) : ZMod N) *
        (starRingEnd Complex) (chi ((Inv.inv b : Units (ZMod N)) : ZMod N))) =
      if a = b then (N.totient : Complex) else 0 := by
  classical
  have hConj (chi : DirichletCharacter Complex N) :
      (starRingEnd Complex) (chi ((Inv.inv b : Units (ZMod N)) : ZMod N)) =
        chi (b : ZMod N) := by
    have hProd : chi ((Inv.inv b : Units (ZMod N)) : ZMod N) * chi (b : ZMod N) = 1 := by
      rw [<- map_mul]
      simp
    have hNorm : chi ((Inv.inv b : Units (ZMod N)) : ZMod N) *
        (starRingEnd Complex) (chi ((Inv.inv b : Units (ZMod N)) : ZMod N)) = 1 := by
      rw [Complex.mul_conj, MulChar.normSq_apply_unit]
      simp
    have hNZ : Not (chi ((Inv.inv b : Units (ZMod N)) : ZMod N) = 0) := by
      intro hZero
      rw [hZero, zero_mul] at hProd
      exact zero_ne_one hProd
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp (show chi ((Inv.inv b : Units (ZMod N)) : ZMod N) *
      ((starRingEnd Complex) (chi ((Inv.inv b : Units (ZMod N)) : ZMod N)) -
        chi (b : ZMod N)) = 0 from by rw [mul_sub, hNorm, hProd, sub_self])).resolve_left hNZ
  simp_rw [hConj]
  rw [unit_inverse_value]
  rw [DirichletCharacter.sum_char_inv_mul_char_eq Complex a.isUnit (b : ZMod N)]
  by_cases h : a = b
  . simp [h]
  . have hVal : Not ((a : ZMod N) = (b : ZMod N)) := fun hh => h (Units.ext hh)
    simp [h, hVal]

theorem unitFourier_parseval {N : Nat} [NeZero N] (g : ZMod N -> Complex) :
    Finset.sum Finset.univ (fun chi : DirichletCharacter Complex N =>
      Complex.normSq (unitFourierCoefficient g chi)) =
      (N.totient : Real) * Finset.sum Finset.univ
        (fun a : Units (ZMod N) => Complex.normSq (g (a : ZMod N))) := by
  classical
  have hExpand (chi : DirichletCharacter Complex N) :
      unitFourierCoefficient g chi * (starRingEnd Complex) (unitFourierCoefficient g chi) =
      Finset.sum Finset.univ (fun a : Units (ZMod N) => Finset.sum Finset.univ
        (fun b : Units (ZMod N) =>
          (g (a : ZMod N) * (starRingEnd Complex) (g (b : ZMod N))) *
            (chi ((Inv.inv a : Units (ZMod N)) : ZMod N) *
              (starRingEnd Complex) (chi ((Inv.inv b : Units (ZMod N)) : ZMod N))))) := by
    simp only [unitFourierCoefficient, map_sum, map_mul, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hC : Finset.sum Finset.univ (fun chi : DirichletCharacter Complex N =>
      unitFourierCoefficient g chi * (starRingEnd Complex) (unitFourierCoefficient g chi)) =
      (N.totient : Complex) * Finset.sum Finset.univ
        (fun a : Units (ZMod N) => g (a : ZMod N) * (starRingEnd Complex) (g (a : ZMod N))) := by
    simp_rw [hExpand]
    rw [Finset.sum_comm]
    have hInner (a : Units (ZMod N)) :
        Finset.sum Finset.univ (fun chi : DirichletCharacter Complex N =>
          Finset.sum Finset.univ (fun b : Units (ZMod N) =>
            (g (a : ZMod N) * (starRingEnd Complex) (g (b : ZMod N))) *
              (chi ((Inv.inv a : Units (ZMod N)) : ZMod N) *
                (starRingEnd Complex) (chi ((Inv.inv b : Units (ZMod N)) : ZMod N))))) =
          (N.totient : Complex) *
            (g (a : ZMod N) * (starRingEnd Complex) (g (a : ZMod N))) := by
      rw [Finset.sum_comm]
      simp_rw [<- Finset.mul_sum, unitFourier_cross_orthogonality]
      simp [mul_comm]
    simp_rw [hInner]
    rw [Finset.mul_sum]
  simp_rw [Complex.mul_conj] at hC
  have hReal := congrArg Complex.re hC
  simpa [Complex.mul_re, map_sum] using hReal

theorem unitFourier_norm_sum_le {N : Nat} [NeZero N]
    (g : ZMod N -> Complex) (hg : forall a : Units (ZMod N), norm (g (a : ZMod N)) <= 1) :
    Finset.sum Finset.univ (fun chi : DirichletCharacter Complex N =>
      norm (unitFourierCoefficient g chi)) <=
        (N.totient : Real) * Real.sqrt (N.totient : Real) := by
  classical
  let T : Finset (DirichletCharacter Complex N) := Finset.univ
  let F (chi : DirichletCharacter Complex N) : Real := norm (unitFourierCoefficient g chi)
  have hCard : T.card = N.totient := by
    simpa only [T, Finset.card_univ, Nat.card_eq_fintype_card] using
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity Complex N
  have hPhi : 0 <= (N.totient : Real) := Nat.cast_nonneg _
  have hEnergy : Finset.sum T (fun chi => F chi ^ 2) <= (N.totient : Real) ^ 2 := by
    simp only [T, F, <- Complex.normSq_eq_norm_sq]
    rw [unitFourier_parseval]
    have hTerm (a : Units (ZMod N)) : Complex.normSq (g (a : ZMod N)) <= 1 := by
      rw [Complex.normSq_eq_norm_sq]
      have h := mul_le_mul (hg a) (hg a) (norm_nonneg _) zero_le_one
      simpa only [pow_two, one_mul] using h
    have hSum := Finset.sum_le_sum (fun a (_ : Membership.mem Finset.univ a) => hTerm a)
    have hUnits : (Fintype.card (Units (ZMod N)) : Real) = (N.totient : Real) := by
      rw [ZMod.card_units_eq_totient]
    have hSum' : Finset.sum Finset.univ
        (fun a : Units (ZMod N) => Complex.normSq (g (a : ZMod N))) <= (N.totient : Real) := by
      simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hUnits] using hSum
    simpa only [pow_two] using mul_le_mul_of_nonneg_left hSum' hPhi
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq T (fun _ => (1 : Real)) F
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, hCard] at hCS
  have hSq : (Finset.sum T F) ^ 2 <= (N.totient : Real) ^ 3 := by
    have h := hCS.trans (mul_le_mul_of_nonneg_left hEnergy hPhi)
    convert h using 1
    ring
  have hRight : ((N.totient : Real) * Real.sqrt (N.totient : Real)) ^ 2 =
      (N.totient : Real) ^ 3 := by
    rw [mul_pow, Real.sq_sqrt hPhi]
    ring
  have hNonneg : 0 <= Finset.sum T F := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hRightNonneg : 0 <= (N.totient : Real) * Real.sqrt (N.totient : Real) := by positivity
  change Finset.sum T F <= _
  nlinarith only [hSq, hRight, hNonneg, hRightNonneg]

noncomputable def weightedUnitSum {I : Type*} {N : Nat} [NeZero N]
    (S : Finset I) (f : I -> ZMod N) (w : I -> Complex) (g : ZMod N -> Complex) : Complex := by
  classical
  exact Finset.sum (S.filter (fun i => IsUnit (f i))) (fun i => w i * g (f i))

noncomputable def weightedCharacterSum {I : Type*} {N : Nat}
    (S : Finset I) (f : I -> ZMod N) (w : I -> Complex)
    (chi : DirichletCharacter Complex N) : Complex :=
  Finset.sum S (fun i => w i * chi (f i))

theorem unitFourier_weighted_center {I : Type*} {N : Nat} [NeZero N]
    (S : Finset I) (f : I -> ZMod N) (w : I -> Complex) (g : ZMod N -> Complex) (X : Complex) :
    Finset.sum Finset.univ (fun chi : DirichletCharacter Complex N =>
      unitFourierCoefficient g chi * (weightedCharacterSum S f w chi -
        if chi = 1 then X else 0)) =
      (N.totient : Complex) * weightedUnitSum S f w g - X * unitFourierCoefficient g 1 := by
  classical
  have hAt (i : I) : Finset.sum Finset.univ (fun chi : DirichletCharacter Complex N =>
      unitFourierCoefficient g chi * (w i * chi (f i))) =
      if IsUnit (f i) then (N.totient : Complex) * (w i * g (f i)) else 0 := by
    by_cases h : IsUnit (f i)
    . rw [ite_eq_left h]
      have hRecon := unitFourier_reconstruction g h.unit
      rw [h.unit_spec] at hRecon
      calc
        _ = w i * Finset.sum Finset.univ (fun chi : DirichletCharacter Complex N =>
            unitFourierCoefficient g chi * chi (f i)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro chi _
          ring
        _ = _ := by rw [hRecon]; ring
    . rw [ite_eq_right h]
      simp only [MulChar.map_nonunit _ h, mul_zero, Finset.sum_const_zero]
  have hAll : Finset.sum Finset.univ (fun chi : DirichletCharacter Complex N =>
      unitFourierCoefficient g chi * weightedCharacterSum S f w chi) =
      (N.totient : Complex) * weightedUnitSum S f w g := by
    simp only [weightedCharacterSum, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [hAt]
    simp only [weightedUnitSum, Finset.mul_sum, Finset.sum_filter, mul_ite, mul_zero]
  have hMain : Finset.sum Finset.univ (fun chi : DirichletCharacter Complex N =>
      unitFourierCoefficient g chi * (if chi = 1 then X else 0)) =
      X * unitFourierCoefficient g 1 := by simp [mul_comm]
  simp only [mul_sub, Finset.sum_sub_distrib, hAll, hMain]

theorem norm_weightedUnitSum_sub_center_le {I : Type*} {N : Nat} [NeZero N]
    (S : Finset I) (f : I -> ZMod N) (w : I -> Complex) (g : ZMod N -> Complex)
    (X : Complex) (E : Real) (hE : 0 <= E)
    (hg : forall a : Units (ZMod N), norm (g (a : ZMod N)) <= 1)
    (hPrefix : forall chi : DirichletCharacter Complex N,
      norm (weightedCharacterSum S f w chi - if chi = 1 then X else 0) <= E) :
    norm (weightedUnitSum S f w g -
      X / (N.totient : Complex) * unitFourierCoefficient g 1) <=
        Real.sqrt (N.totient : Real) * E := by
  classical
  have hPhiN : 0 < N.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hPhi : 0 < (N.totient : Real) := Nat.cast_pos.mpr hPhiN
  have hPhiC : Not ((N.totient : Complex) = 0) := by exact_mod_cast hPhiN.ne'
  have hIdentity : (N.totient : Complex) *
      (weightedUnitSum S f w g - X / (N.totient : Complex) * unitFourierCoefficient g 1) =
      Finset.sum Finset.univ (fun chi : DirichletCharacter Complex N =>
        unitFourierCoefficient g chi * (weightedCharacterSum S f w chi -
          if chi = 1 then X else 0)) := by
    rw [unitFourier_weighted_center]
    field_simp [hPhiC]
  have hNorm : norm (Finset.sum Finset.univ (fun chi : DirichletCharacter Complex N =>
        unitFourierCoefficient g chi * (weightedCharacterSum S f w chi -
          if chi = 1 then X else 0))) <=
      (N.totient : Real) * (Real.sqrt (N.totient : Real) * E) := by
    calc
      _ <= Finset.sum Finset.univ (fun chi : DirichletCharacter Complex N =>
          norm (unitFourierCoefficient g chi * (weightedCharacterSum S f w chi -
            if chi = 1 then X else 0))) := norm_sum_le _ _
      _ <= Finset.sum Finset.univ (fun chi : DirichletCharacter Complex N =>
          norm (unitFourierCoefficient g chi) * E) := by
        apply Finset.sum_le_sum
        intro chi _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hPrefix chi) (norm_nonneg _)
      _ = (Finset.sum Finset.univ (fun chi : DirichletCharacter Complex N =>
          norm (unitFourierCoefficient g chi))) * E := by rw [Finset.sum_mul]
      _ <= ((N.totient : Real) * Real.sqrt (N.totient : Real)) * E :=
        mul_le_mul_of_nonneg_right (unitFourier_norm_sum_le g hg) hE
      _ = _ := by ring
  rw [<- hIdentity, norm_mul] at hNorm
  have hDenom : norm (N.totient : Complex) = (N.totient : Real) := by simp
  rw [hDenom] at hNorm
  exact (mul_le_mul_iff_of_pos_left hPhi).mp hNorm

end PrimeFactorOscillations.LPF
