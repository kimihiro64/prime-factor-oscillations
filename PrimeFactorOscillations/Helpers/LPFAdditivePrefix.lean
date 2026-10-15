/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFCharacterFourier
import PrimeFactorOscillations.Helpers.LPFCharacterPrefix

/-!
# Full prime-prefix residue phase bounds

The actual all-character source controls every bounded residue phase with
one constant before the modulus, phase and cutoff. The principal coefficient
is exact. Nonunit prime powers retain their finite Euler allowance. These
prefix bounds do not by themselves establish the complete Goldbach estimate.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

namespace PrimeFactorOscillations.LPF

theorem exists_primePrefix_unitPhase_power_bound :
    exists A : Real, And (0 < A)
      (forall {N : Nat} [NeZero N] (g : ZMod N -> Complex),
        (forall a : Units (ZMod N), norm (g (a : ZMod N)) <= 1) ->
        forall {x : Nat}, 65536 <= x ->
          norm (weightedUnitSum (Finset.Icc 1 x) (fun n : Nat => (n : ZMod N))
              (fun n : Nat => (ArithmeticFunction.vonMangoldt n : Complex)) g -
            (x : Complex) / (N.totient : Complex) * unitFourierCoefficient g 1) <=
              A * Real.sqrt (N.totient : Real) * (x : Real) ^ (15 / 16 : Real) *
                (1 + Real.log N + Real.log ((x : Real) + 2)) ^ 2) := by
  classical
  choose A hA hSource using QRH.exists_all_characterChebyshevSum_power_bound
  refine Exists.intro A (And.intro hA ?_)
  intro N inst g hg x hx
  have hFactor : 0 <= A * (x : Real) ^ (15 / 16 : Real) *
      (1 + Real.log N + Real.log ((x : Real) + 2)) ^ 2 := by positivity
  have h := norm_weightedUnitSum_sub_center_le (Finset.Icc 1 x)
    (fun n : Nat => (n : ZMod N))
    (fun n : Nat => (ArithmeticFunction.vonMangoldt n : Complex)) g (x : Complex)
    (A * (x : Real) ^ (15 / 16 : Real) *
      (1 + Real.log N + Real.log ((x : Real) + 2)) ^ 2) hFactor hg
    (fun chi => by
      have hC := hSource chi hx
      simpa only [weightedCharacterSum,
        BombieriVinogradov.SiegelWalfisz.characterChebyshevSum,
        BombieriVinogradov.VaughanMeanValue.psiCharacterSum,
        QRH.lpfCharacterPrefixCenter, mul_ite, mul_one, mul_zero] using hC)
  convert h using 1
  ring

open BombieriVinogradov.SiegelWalfisz

theorem norm_primePrefix_nonunit_phase_le {N x : Nat} [NeZero N] (hx : 0 < x)
    (g : ZMod N -> Complex) (hg : forall z, norm (g z) <= 1) :
    norm (Finset.sum ((Finset.Icc 1 x).filter (fun n : Nat => Not (IsUnit (n : ZMod N))))
      (fun n => (ArithmeticFunction.vonMangoldt n : Complex) * g (n : ZMod N))) <=
        Real.log N * Real.log (x : Real) / Real.log (2 : Real) := by
  classical
  let S : Finset Nat := Finset.Icc 1 x
  let V : Finset Nat := S.filter (fun n => Not (IsUnit (n : ZMod N)))
  have hPrincipal (z : ZMod N) :
      (1 : DirichletCharacter Complex N) z = if IsUnit z then 1 else 0 := by
    by_cases h : IsUnit z
    . rw [ite_eq_left h]
      exact MulChar.one_apply_coe h.unit
    . rw [ite_eq_right h]
      exact MulChar.map_nonunit _ h
  have hPrimitive : characterChebyshevSum x
      (1 : DirichletCharacter Complex N).primitiveCharacter =
      Finset.sum S (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) := by
    have hLevel : (1 : DirichletCharacter Complex N).conductor = 1 :=
      @DirichletCharacter.conductor_one Complex inferInstance N inferInstance
    rw [@DirichletCharacter.primitiveCharacter_one Complex inferInstance N inferInstance,
      hLevel]
    have hOne (n : Nat) : (1 : DirichletCharacter Complex 1) (n : ZMod 1) = 1 := by
      rw [show (n : ZMod 1) = 1 from Subsingleton.elim _ _]
      exact map_one _
    simp only [characterChebyshevSum, BombieriVinogradov.VaughanMeanValue.psiCharacterSum,
      hOne, mul_one, S]
  have hDifference : characterChebyshevSum x (1 : DirichletCharacter Complex N) -
      Finset.sum S (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) =
      -Finset.sum V (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) := by
    change Finset.sum S (fun n => (ArithmeticFunction.vonMangoldt n : Complex) *
      (1 : DirichletCharacter Complex N) (n : ZMod N)) -
      Finset.sum S (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) = _
    rw [<- Finset.sum_sub_distrib]
    simp only [V, Finset.sum_filter, <- Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n _
    by_cases h : IsUnit (n : ZMod N)
    . simp [hPrincipal, h]
    . simp [hPrincipal, h]
  have hCorrection := norm_characterChebyshevSum_sub_primitive_le
    (NeZero.ne N) (1 : DirichletCharacter Complex N) hx
  rw [hPrimitive, hDifference, norm_neg] at hCorrection
  have hCast : ((Finset.sum V (fun n => ArithmeticFunction.vonMangoldt n) : Real) : Complex) =
      Finset.sum V (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) := by simp
  have hNonneg : 0 <= Finset.sum V (fun n => ArithmeticFunction.vonMangoldt n) :=
    Finset.sum_nonneg (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  rw [<- hCast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hNonneg] at hCorrection
  change norm (Finset.sum V (fun n => (ArithmeticFunction.vonMangoldt n : Complex) *
    g (n : ZMod N))) <= _
  calc
    _ <= Finset.sum V (fun n => norm ((ArithmeticFunction.vonMangoldt n : Complex) *
        g (n : ZMod N))) := norm_sum_le _ _
    _ <= Finset.sum V (fun n => ArithmeticFunction.vonMangoldt n) := by
      apply Finset.sum_le_sum
      intro n _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hg (n : ZMod N))
        ArithmeticFunction.vonMangoldt_nonneg
    _ <= _ := hCorrection

theorem primePrefix_phase_sum_split {N x : Nat} [NeZero N]
    (g : ZMod N -> Complex) :
    Finset.sum (Finset.Icc 1 x) (fun n => (ArithmeticFunction.vonMangoldt n : Complex) *
      g (n : ZMod N)) =
      weightedUnitSum (Finset.Icc 1 x) (fun n : Nat => (n : ZMod N))
        (fun n : Nat => (ArithmeticFunction.vonMangoldt n : Complex)) g +
      Finset.sum ((Finset.Icc 1 x).filter (fun n : Nat => Not (IsUnit (n : ZMod N))))
        (fun n => (ArithmeticFunction.vonMangoldt n : Complex) * g (n : ZMod N)) := by
  classical
  simp only [weightedUnitSum, Finset.sum_filter, <- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h : IsUnit (n : ZMod N) <;> simp [h]

theorem exists_primePrefix_phase_power_bound :
    exists A : Real, And (0 < A)
      (forall {N : Nat} [NeZero N] (g : ZMod N -> Complex),
        (forall z, norm (g z) <= 1) -> forall {x : Nat}, 65536 <= x ->
          norm (Finset.sum (Finset.Icc 1 x)
              (fun n => (ArithmeticFunction.vonMangoldt n : Complex) * g (n : ZMod N)) -
            (x : Complex) / (N.totient : Complex) * unitFourierCoefficient g 1) <=
              A * Real.sqrt (N.totient : Real) * (x : Real) ^ (15 / 16 : Real) *
                (1 + Real.log N + Real.log ((x : Real) + 2)) ^ 2 +
              Real.log N * Real.log (x : Real) / Real.log (2 : Real)) := by
  classical
  choose A hA hSource using exists_primePrefix_unitPhase_power_bound
  refine Exists.intro A (And.intro hA ?_)
  intro N inst g hg x hx
  have hUnit := hSource g (fun a => hg (a : ZMod N)) hx
  have hNonunit := norm_primePrefix_nonunit_phase_le (by omega : 0 < x) g hg
  rw [primePrefix_phase_sum_split]
  have hTriangle : norm (weightedUnitSum (Finset.Icc 1 x) (fun n : Nat => (n : ZMod N))
      (fun n : Nat => (ArithmeticFunction.vonMangoldt n : Complex)) g +
      Finset.sum ((Finset.Icc 1 x).filter (fun n : Nat => Not (IsUnit (n : ZMod N))))
        (fun n => (ArithmeticFunction.vonMangoldt n : Complex) * g (n : ZMod N)) -
      (x : Complex) / (N.totient : Complex) * unitFourierCoefficient g 1) <=
      norm (weightedUnitSum (Finset.Icc 1 x) (fun n : Nat => (n : ZMod N))
        (fun n : Nat => (ArithmeticFunction.vonMangoldt n : Complex)) g -
        (x : Complex) / (N.totient : Complex) * unitFourierCoefficient g 1) +
      norm (Finset.sum ((Finset.Icc 1 x).filter (fun n : Nat => Not (IsUnit (n : ZMod N))))
        (fun n => (ArithmeticFunction.vonMangoldt n : Complex) * g (n : ZMod N))) := by
    calc
      _ = norm ((weightedUnitSum (Finset.Icc 1 x) (fun n : Nat => (n : ZMod N))
          (fun n : Nat => (ArithmeticFunction.vonMangoldt n : Complex)) g -
          (x : Complex) / (N.totient : Complex) * unitFourierCoefficient g 1) +
          Finset.sum ((Finset.Icc 1 x).filter (fun n : Nat => Not (IsUnit (n : ZMod N))))
            (fun n => (ArithmeticFunction.vonMangoldt n : Complex) * g (n : ZMod N))) := by
        congr 1
        ring
      _ <= _ := norm_add_le _ _
  exact hTriangle.trans (add_le_add hUnit hNonunit)


end PrimeFactorOscillations.LPF
