/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCoprimeFourier

/-! # Exact conductor reduction of every signed coprime frequency

Surjective reduction of unit groups is averaged before the primitive
character sum is evaluated. This retains nonsquarefree moduli and
all conductors; no absolute estimate replaces the signed eigenvalue.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

noncomputable section

namespace PrimeFactorOscillations

theorem hamiltonian_surjective_group_sum
    {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
    (f : MonoidHom G H) (hSurj : Function.Surjective f) (F : H -> Complex) :
    (Fintype.card H : Complex) * Finset.univ.sum (fun g => F (f g)) =
      (Fintype.card G : Complex) * Finset.univ.sum F := by
  classical
  have hRight (h : H) :
      Finset.univ.sum (fun g : G => F (f g * h)) =
        Finset.univ.sum (fun g : G => F (f g)) := by
    choose g0 hg0 using hSurj h
    apply Fintype.sum_equiv (Equiv.mulRight g0)
    intro g
    change F (f g * h) = F (f (g * g0))
    rw [map_mul, hg0]
  have hLeft (g : G) :
      Finset.univ.sum (fun h : H => F (f g * h)) = Finset.univ.sum F := by
    apply Fintype.sum_equiv (Equiv.mulLeft (f g))
    intro h
    rfl
  calc
    _ = Finset.univ.sum (fun h : H =>
        Finset.univ.sum (fun g : G => F (f g * h))) := by
      simp only [hRight, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = Finset.univ.sum (fun g : G =>
        Finset.univ.sum (fun h : H => F (f g * h))) := Finset.sum_comm
    _ = _ := by
      simp only [hLeft, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem hamiltonian_scaled_standard_character
    (g t c : Nat) [NeZero g] [NeZero t] :
    ZMod.stdAddChar (N := g * t) ((g * c : Nat) : ZMod (g * t)) =
      ZMod.stdAddChar (N := t) (c : ZMod t) := by
  have hg : Not ((g : Complex) = 0) := by exact_mod_cast (NeZero.ne g)
  have ht : Not ((t : Complex) = 0) := by exact_mod_cast (NeZero.ne t)
  have hLeft := ZMod.stdAddChar_coe (N := g * t) ((g * c : Nat) : Int)
  have hRight := ZMod.stdAddChar_coe (N := t) (c : Int)
  simp only [Int.cast_natCast] at hLeft hRight
  rw [hLeft, hRight]
  congr 1
  simp only [Nat.cast_mul]
  field_simp
  <;> ring

theorem hamiltonian_unit_reduction_value
    {n t : Nat} [NeZero n] (hDiv : Dvd.dvd t n) (a : Units (ZMod n)) :
    ((ZMod.unitsMap hDiv a : Units (ZMod t)) : ZMod t) =
      ((a : ZMod n).val : ZMod t) := by
  calc
    _ = (ZMod.castHom hDiv (ZMod t)) (a : ZMod n) := by
      rw [ZMod.unitsMap_def]
      rfl
    _ = (ZMod.castHom hDiv (ZMod t)) (((a : ZMod n).val : Nat) : ZMod n) := by
      rw [ZMod.natCast_zmod_val]
    _ = _ := by simp only [map_natCast]

theorem hamiltonian_unit_reduction_phase
    (g t b : Nat) [NeZero g] [NeZero t] (a : Units (ZMod (g * t))) :
    ZMod.stdAddChar ((a : ZMod (g * t)) * ((g * b : Nat) : ZMod (g * t))) =
      ZMod.stdAddChar
        (((ZMod.unitsMap (dvd_mul_left t g) a : Units (ZMod t)) : ZMod t) *
          (b : ZMod t)) := by
  rw [hamiltonian_unit_reduction_value]
  calc
    _ = ZMod.stdAddChar (N := g * t)
        ((g * ((a : ZMod (g * t)).val * b) : Nat) : ZMod (g * t)) := by
      congr 1
      simp only [Nat.cast_mul, ZMod.natCast_zmod_val]
      ring
    _ = ZMod.stdAddChar (N := t)
        (((a : ZMod (g * t)).val * b : Nat) : ZMod t) :=
      hamiltonian_scaled_standard_character g t _
    _ = _ := by simp only [Nat.cast_mul]

theorem hamiltonian_coprime_conductor_cross_product
    (g t b : Nat) [NeZero g] [NeZero t] (hCoprime : Nat.Coprime b t) :
    (t.totient : Complex) * LPF.lpfRamanujanSum (q := g * t) (g * b) =
      ((g * t).totient : Complex) * (ArithmeticFunction.moebius t : Complex) := by
  let f := ZMod.unitsMap (dvd_mul_left t g)
  let F : Units (ZMod t) -> Complex :=
    fun a => ZMod.stdAddChar ((a : ZMod t) * (b : ZMod t))
  have h := hamiltonian_surjective_group_sum f
    (ZMod.unitsMap_surjective (dvd_mul_left t g)) F
  have hLarge : Finset.univ.sum (fun a : Units (ZMod (g * t)) => F (f a)) =
      LPF.lpfRamanujanSum (q := g * t) (g * b) := by
    unfold LPF.lpfRamanujanSum
    apply Finset.sum_congr rfl
    intro a ha
    exact (hamiltonian_unit_reduction_phase g t b a).symm
  have hUnit : IsUnit (b : ZMod t) := (ZMod.isUnit_iff_coprime b t).mpr hCoprime
  have hSmall : Finset.univ.sum F = (ArithmeticFunction.moebius t : Complex) := by
    have hp := hamiltonian_coprime_primitive_frequency hUnit.unit
    simpa only [LPF.lpfRamanujanSum, ZMod.natCast_zmod_val, hUnit.unit_spec, F] using hp
  rw [ZMod.card_units_eq_totient, ZMod.card_units_eq_totient, hLarge, hSmall] at h
  exact h

theorem hamiltonian_coprime_conductor_ratio
    (g t b : Nat) [NeZero g] [NeZero t] (hCoprime : Nat.Coprime b t) :
    LPF.lpfRamanujanSum (q := g * t) (g * b) / ((g * t).totient : Complex) =
      (ArithmeticFunction.moebius t : Complex) / (t.totient : Complex) := by
  have ht : Not ((t.totient : Complex) = 0) := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos t)).ne'
  have hn : Not (((g * t).totient : Complex) = 0) := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.mul_pos (NeZero.pos g) (NeZero.pos t))).ne'
  apply (div_eq_div_iff hn ht).mpr
  have h := hamiltonian_coprime_conductor_cross_product g t b hCoprime
  simpa only [mul_comm] using h

theorem hamiltonian_coprime_nonprincipal_conductor_gap
    (g t b : Nat) [NeZero g] [NeZero t] (hCoprime : Nat.Coprime b t)
    (hT : 3 <= t) :
    norm (LPF.lpfRamanujanSum (q := g * t) (g * b) /
      ((g * t).totient : Complex)) <= (1 / 2 : Real) := by
  have hPhiPos : 0 < t.totient := Nat.totient_pos.mpr (NeZero.pos t)
  have hPhi : 2 <= t.totient := by
    by_contra hNot
    have hOne : t.totient = 1 := by omega
    have hCases := Nat.totient_eq_one_iff.mp hOne
    omega
  have hPhiReal : (2 : Real) <= (t.totient : Real) := by exact_mod_cast hPhi
  have hMu : norm (ArithmeticFunction.moebius t : Complex) <= 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := t)
  rw [hamiltonian_coprime_conductor_ratio g t b hCoprime, norm_div, Complex.norm_natCast]
  have hPos : (0 : Real) < (t.totient : Real) := by exact_mod_cast hPhiPos
  have hNe : Not ((t.totient : Real) = 0) := ne_of_gt hPos
  apply (mul_le_mul_iff_of_pos_right hPos).mp
  have hCancel : (norm (ArithmeticFunction.moebius t : Complex) / (t.totient : Real)) *
      (t.totient : Real) = norm (ArithmeticFunction.moebius t : Complex) := by field_simp
  rw [hCancel]
  nlinarith only [hMu, hPhiReal]

end PrimeFactorOscillations
