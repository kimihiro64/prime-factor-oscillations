/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFRamanujan

/-!
# Prime-interval major-arc source

The rational frequency is measured in radians: 2*pi*a.val/q. The offset
beta is also in radians. The exact main term is mu(q)/phi(q) times the
geometric offset sum, with nonunit prime powers included in the error.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

namespace PrimeFactorOscillations.LPF

noncomputable def lpfRationalFrequency {q : Nat} [NeZero q] (a : Units (ZMod q)) : Real :=
  2 * Real.pi * ((a : ZMod q).val : Real) / (q : Real)

theorem lpfResiduePhase_natCast {q : Nat} [NeZero q] (a : Units (ZMod q)) (n : Nat) :
    lpfResiduePhase a (n : ZMod q) = lpfPhase (lpfRationalFrequency a) n := by
  have hCast : ((((a : ZMod q).val * n : Nat) : Int) : ZMod q) =
      (a : ZMod q) * (n : ZMod q) := by
    simp only [Nat.cast_mul, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hPsi := ZMod.stdAddChar_coe (N := q) (((a : ZMod q).val * n : Nat) : Int)
  rw [hCast] at hPsi
  rw [lpfResiduePhase, hPsi]
  unfold lpfPhase lpfRationalFrequency
  congr 1
  push_cast
  ring

theorem lpfResiduePhase_mul_lpfPhase {q : Nat} [NeZero q]
    (a : Units (ZMod q)) (beta : Real) (n : Nat) :
    lpfResiduePhase a (n : ZMod q) * lpfPhase beta n =
      lpfPhase (lpfRationalFrequency a + beta) n := by
  rw [lpfResiduePhase_natCast]
  unfold lpfPhase
  rw [<- Complex.exp_add]
  congr 1
  push_cast
  ring

theorem exists_primeInterval_rational_phase_power_bound :
    exists A : Real, And (0 < A)
      (forall {q : Nat} [NeZero q] (a : Units (ZMod q)),
        forall (s L : Nat) (beta : Real), 65536 <= s -> abs beta <= 1 ->
          norm (Finset.sum (Finset.range L) (fun i =>
              (ArithmeticFunction.vonMangoldt (s + 1 + i) : Complex) *
                lpfPhase (lpfRationalFrequency a + beta) (s + 1 + i)) -
            (ArithmeticFunction.moebius q : Complex) / (q.totient : Complex) *
              Finset.sum (Finset.range L) (fun i => lpfPhase beta (s + 1 + i))) <=
            2 * (1 + 2 * (L : Real) * abs beta) * lpfPhaseAllowance A q (s + L)) := by
  choose A hA hSource using exists_primeInterval_phase_power_bound
  refine Exists.intro A (And.intro hA ?_)
  intro q inst a s L beta hs hBeta
  have h := hSource (lpfResiduePhase a) (fun z => (norm_lpfResiduePhase a z).le)
    s L beta hs hBeta
  rw [unitFourierCoefficient_lpfResiduePhase] at h
  simpa only [mul_assoc, lpfResiduePhase_mul_lpfPhase] using h

end PrimeFactorOscillations.LPF
