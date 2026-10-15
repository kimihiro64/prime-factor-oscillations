/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFMajorArc
import PrimeFactorOscillations.Helpers.LPFRationalGrid

/-!
# Lossless small-denominator source transfer to the auxiliary grid

The prime-prefix input is used at q, never at the potentially huge grid N.
Signed offsets k become radians 2*pi*k/N. The complete consumer retains
the major bound 8*E^2*P*M+6*E^4*P^3/M, plus both tails and the minor
packet. This is an exact adapter for the arithmetic error E; it does not
assert the complete Goldbach bound or density entry of generated states.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

namespace PrimeFactorOscillations.LPF

noncomputable def lpfGridRadians (N : Nat) (k : Int) : Real :=
  2 * Real.pi * (k : Real) / (N : Real)

theorem lpfGrid_character_phase {N : Nat} [NeZero N] (k : Int) (n : Nat) :
    ZMod.stdAddChar ((k : ZMod N) * (n : ZMod N)) = lpfPhase (lpfGridRadians N k) n := by
  have hCast : (((k * (n : Int) : Int) : ZMod N)) = (k : ZMod N) * (n : ZMod N) := by
    simp only [Int.cast_mul, Int.cast_natCast]
  have hPsi := ZMod.stdAddChar_coe (N := N) (k * (n : Int))
  rw [hCast] at hPsi
  rw [hPsi]
  unfold lpfPhase lpfGridRadians
  congr 1
  push_cast
  ring

theorem lpfRationalGridPoint_phase {N q : Nat} [NeZero N] [NeZero q]
    (a : Units (ZMod q)) (hDiv : Dvd.dvd q N) (k : Int) (n : Nat) :
    ZMod.stdAddChar (lpfRationalGridPoint N q (a : ZMod q).val k * (n : ZMod N)) =
      lpfPhase (lpfRationalFrequency a + lpfGridRadians N k) n := by
  let m : Int := ((N / q * (a : ZMod q).val : Nat) : Int) + k
  have hPoint : lpfRationalGridPoint N q (a : ZMod q).val k = (m : ZMod N) := by
    simp only [lpfRationalGridPoint, m, Int.cast_add, Int.cast_natCast]
  have hN : Not ((N : Real) = 0) := by exact_mod_cast (NeZero.ne N)
  have hq : Not ((q : Real) = 0) := by exact_mod_cast (NeZero.ne q)
  have hMul : ((N / q : Nat) : Real) * (q : Real) = (N : Real) := by
    exact_mod_cast (Nat.div_mul_cancel hDiv)
  have hWeighted := congrArg (fun z : Real => ((a : ZMod q).val : Real) * z) hMul
  have hAngle : lpfGridRadians N m = lpfRationalFrequency a + lpfGridRadians N k := by
    unfold lpfGridRadians lpfRationalFrequency m
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    field_simp [hN, hq]
    nlinarith only [hWeighted]
  rw [hPoint, lpfGrid_character_phase, hAngle]

noncomputable def lpfGridIntervalWeight (N : Nat) [NeZero N] (s L : Nat) (x : ZMod N) : Complex :=
  Finset.sum (Finset.range L) (fun i => (ArithmeticFunction.vonMangoldt (s + 1 + i) : Complex) *
    ZMod.stdAddChar (x * ((s + 1 + i : Nat) : ZMod N)))

noncomputable def lpfGridIntervalKernel (N : Nat) [NeZero N] (s L : Nat) (k : Int) : Complex :=
  Finset.sum (Finset.range L) (fun i => ZMod.stdAddChar ((k : ZMod N) * ((s + 1 + i : Nat) : ZMod N)))

theorem exists_primeGridInterval_point_power_bound :
    exists A : Real, And (0 < A)
      (forall {N : Nat} [NeZero N] {q : Nat} [NeZero q] (a : Units (ZMod q)),
        forall (s L : Nat) (k : Int), Dvd.dvd q N -> 65536 <= s -> abs (lpfGridRadians N k) <= 1 ->
          norm (lpfGridIntervalWeight N s L (lpfRationalGridPoint N q (a : ZMod q).val k) -
            lpfRationalCoefficient q * lpfGridIntervalKernel N s L k) <=
            2 * (1 + 2 * (L : Real) * abs (lpfGridRadians N k)) * lpfPhaseAllowance A q (s + L)) := by
  choose A hA hSource using exists_primeInterval_rational_phase_power_bound
  refine Exists.intro A (And.intro hA ?_)
  intro N instN q instQ a s L k hDiv hs hBeta
  have h := hSource a s L (lpfGridRadians N k) hs hBeta
  simpa only [lpfGridIntervalWeight, lpfGridIntervalKernel, lpfRationalCoefficient,
    lpfRationalGridPoint_phase a hDiv k, lpfGrid_character_phase k] using h

noncomputable def lpfGridIntervalInputs (s L : Nat) : Finset Nat :=
  (Finset.range L).image (fun i => s + 1 + i)

theorem lpfGridIntervalInputs_card (s L : Nat) : (lpfGridIntervalInputs s L).card = L := by
  have hinj : Function.Injective (fun i : Nat => s + 1 + i) := by
    intro i j h
    exact Nat.add_left_cancel h
  rw [lpfGridIntervalInputs, Finset.card_image_of_injective _ hinj, Finset.card_range]

theorem lpfGridIntervalInputs_le (s L n : Nat) (hn : Membership.mem (lpfGridIntervalInputs s L) n) :
    n <= s + L := by
  choose i hi hEq using Finset.mem_image.mp hn
  have hRange := Finset.mem_range.mp hi
  omega

theorem lpfGridIntervalKernel_eq_transform {N : Nat} [NeZero N] (s L : Nat) (k : Int) :
    lpfGridIntervalKernel N s L k = lpfFiniteTransform (lpfGridIntervalInputs s L)
      (fun n => (n : ZMod N)) (fun _ => (1 : Complex)) (k : ZMod N) := by
  have hinj : Set.InjOn (fun i : Nat => s + 1 + i) ((Finset.range L) : Set Nat) := by
    intro i _ j _ h
    exact Nat.add_left_cancel h
  unfold lpfGridIntervalKernel lpfFiniteTransform lpfGridIntervalInputs
  rw [Finset.sum_image hinj]
  simp only [one_mul]

theorem lpfGridIntervalWeight_eq_transform {N : Nat} [NeZero N] (s L : Nat) (x : ZMod N) :
    lpfGridIntervalWeight N s L x = lpfFiniteTransform (lpfGridIntervalInputs s L)
      (fun n => (n : ZMod N)) (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) x := by
  have hinj : Set.InjOn (fun i : Nat => s + 1 + i) ((Finset.range L) : Set Nat) := by
    intro i _ j _ h
    exact Nat.add_left_cancel h
  unfold lpfGridIntervalWeight lpfFiniteTransform lpfGridIntervalInputs
  rw [Finset.sum_image hinj]

end PrimeFactorOscillations.LPF
