/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFMajorCharacterNumeric
import PrimeFactorOscillations.Helpers.LPFUniformMajor

/-!
# Numerical residue and rational major-arc phases

The actual all-character Chebyshev estimate supplies coefficient 65536 before
the modulus and residue phase. The principal residue mean is exact, and the
nonunit Mangoldt correction log(q)*log(x)/log(2) is retained. Finite summation
by parts gives the interval variation factor, followed by the exact rational
frequency and auxiliary-grid adapters. This is not a generated-state estimate.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

namespace PrimeFactorOscillations.LPF

theorem lpf_primePrefix_unitPhase_numeric :
    forall {N : Nat} [NeZero N] (g : ZMod N -> Complex),
        (forall a : Units (ZMod N), norm (g (a : ZMod N)) <= 1) ->
        forall {x : Nat}, 65536 <= x ->
          norm (weightedUnitSum (Finset.Icc 1 x) (fun n : Nat => (n : ZMod N))
              (fun n : Nat => (ArithmeticFunction.vonMangoldt n : Complex)) g -
            (x : Complex) / (N.totient : Complex) * unitFourierCoefficient g 1) <=
              65536 * Real.sqrt (N.totient : Real) * (x : Real) ^ (15 / 16 : Real) *
                (1 + Real.log N + Real.log ((x : Real) + 2)) ^ 2 := by
  classical
  intro N inst g hg x hx
  have hFactor : 0 <= 65536 * (x : Real) ^ (15 / 16 : Real) *
      (1 + Real.log N + Real.log ((x : Real) + 2)) ^ 2 := by positivity
  have h := norm_weightedUnitSum_sub_center_le (Finset.Icc 1 x)
    (fun n : Nat => (n : ZMod N))
    (fun n : Nat => (ArithmeticFunction.vonMangoldt n : Complex)) g (x : Complex)
    (65536 * (x : Real) ^ (15 / 16 : Real) *
      (1 + Real.log N + Real.log ((x : Real) + 2)) ^ 2) hFactor hg
    (fun chi => by
      have hC := QRH.lpf_character_chebyshev_numeric chi (show 4 <= x by omega)
      simpa only [weightedCharacterSum,
        BombieriVinogradov.SiegelWalfisz.characterChebyshevSum,
        BombieriVinogradov.VaughanMeanValue.psiCharacterSum,
        QRH.lpfCharacterPrefixCenter, mul_ite, mul_one, mul_zero] using hC)
  convert h using 1
  ring

theorem lpf_primePrefix_phase_numeric :
    forall {N : Nat} [NeZero N] (g : ZMod N -> Complex),
        (forall z, norm (g z) <= 1) -> forall {x : Nat}, 65536 <= x ->
          norm (Finset.sum (Finset.Icc 1 x)
              (fun n => (ArithmeticFunction.vonMangoldt n : Complex) * g (n : ZMod N)) -
            (x : Complex) / (N.totient : Complex) * unitFourierCoefficient g 1) <=
              65536 * Real.sqrt (N.totient : Real) * (x : Real) ^ (15 / 16 : Real) *
                (1 + Real.log N + Real.log ((x : Real) + 2)) ^ 2 +
              Real.log N * Real.log (x : Real) / Real.log (2 : Real) := by
  classical
  intro N inst g hg x hx
  have hUnit := lpf_primePrefix_unitPhase_numeric g (fun a => hg (a : ZMod N)) hx
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

private theorem lpf_numeric_sum_range_primeWeight_eq_Icc {q : Nat} [NeZero q]
    (g : ZMod q -> Complex) (x : Nat) :
    Finset.sum (Finset.range x) (fun n => (ArithmeticFunction.vonMangoldt (n + 1) : Complex) *
      g ((n + 1 : Nat) : ZMod q)) =
      Finset.sum (Finset.Icc 1 x) (fun n => (ArithmeticFunction.vonMangoldt n : Complex) *
        g (n : ZMod q)) := by
  apply Finset.sum_bij (fun n _ => n + 1)
  . intro n hn
    simp only [Finset.mem_range] at hn
    exact Finset.mem_Icc.mpr (And.intro (by omega) (by omega))
  . intro n hn m hm hEq
    omega
  . intro n hn
    have h := Finset.mem_Icc.mp hn
    refine Exists.intro (n - 1) (Exists.intro ?_ ?_)
    . exact Finset.mem_range.mpr (by omega)
    . omega
  . intro n hn
    rfl

private theorem lpf_numeric_sum_range_shift_center (F : Nat -> Complex) (rho : Complex) (a k : Nat) :
    Finset.sum (Finset.range k) (fun i => F (a + i) - rho) =
      (Finset.sum (Finset.range (a + k)) F - ((a + k : Nat) : Complex) * rho) -
      (Finset.sum (Finset.range a) F - (a : Complex) * rho) := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Finset.sum_range_add]
  simp only [Nat.cast_add]
  ring


theorem lpf_primeInterval_phase_numeric :
    forall {q : Nat} [NeZero q] (g : ZMod q -> Complex),
        (forall z, norm (g z) <= 1) -> forall (a N : Nat) (beta : Real),
          65536 <= a -> abs beta <= 1 ->
          norm (Finset.sum (Finset.range N) (fun i =>
            (ArithmeticFunction.vonMangoldt (a + 1 + i) : Complex) *
              g ((a + 1 + i : Nat) : ZMod q) * lpfPhase beta (a + 1 + i)) -
            (unitFourierCoefficient g 1 / (q.totient : Complex)) *
              Finset.sum (Finset.range N) (fun i => lpfPhase beta (a + 1 + i))) <=
            2 * (1 + 2 * (N : Real) * abs beta) * lpfPhaseAllowance 65536 q (a + N) := by
  classical
  intro q inst g hg a N beta ha hBeta
  let rho : Complex := unitFourierCoefficient g 1 / (q.totient : Complex)
  let F (n : Nat) : Complex := (ArithmeticFunction.vonMangoldt (n + 1) : Complex) *
    g ((n + 1 : Nat) : ZMod q)
  let B : Real := lpfPhaseAllowance 65536 q (a + N)
  have hCenter (x : Nat) : (x : Complex) * rho =
      (x : Complex) / (q.totient : Complex) * unitFourierCoefficient g 1 := by
    dsimp [rho]
    ring
  have hCut (k : Nat) (hk : k <= N) :
      norm (Finset.sum (Finset.range (a + k)) F - ((a + k : Nat) : Complex) * rho) <= B := by
    have hSrc := lpf_primePrefix_phase_numeric g hg (by omega : 65536 <= a + k)
    change norm (Finset.sum (Finset.range (a + k)) (fun n =>
      (ArithmeticFunction.vonMangoldt (n + 1) : Complex) * g ((n + 1 : Nat) : ZMod q)) -
        ((a + k : Nat) : Complex) * rho) <= _
    rw [lpf_numeric_sum_range_primeWeight_eq_Icc, hCenter]
    exact hSrc.trans (lpfPhaseAllowance_mono 65536 q (a + k) (a + N) (by norm_num)
      (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) (by omega) (Nat.add_le_add_left hk a))
  have hPrefix (k : Nat) (hk : k <= N) :
      norm (Finset.sum (Finset.range k) (fun i => F (a + i) - rho)) <= 2 * B := by
    have hIdentity : Finset.sum (Finset.range k) (fun i => F (a + i) - rho) =
        (Finset.sum (Finset.range (a + k)) F - ((a + k : Nat) : Complex) * rho) -
        (Finset.sum (Finset.range a) F - (a : Complex) * rho) := by
      exact lpf_numeric_sum_range_shift_center F rho a k
    rw [hIdentity]
    have h0 := hCut 0 (Nat.zero_le N)
    simp only [Nat.add_zero] at h0
    calc
      _ <= norm (Finset.sum (Finset.range (a + k)) F - ((a + k : Nat) : Complex) * rho) +
          norm (Finset.sum (Finset.range a) F - (a : Complex) * rho) := norm_sub_le _ _
      _ <= B + B := add_le_add (hCut k hk) h0
      _ = _ := by ring
  have h := norm_sum_range_phase_mul_le (fun i => F (a + i) - rho) (a + 1) N beta (2 * B)
    hBeta hPrefix
  have hIndex (i : Nat) : a + i + 1 = a + 1 + i := by omega
  have hIdentity : Finset.sum (Finset.range N) (fun i =>
      (ArithmeticFunction.vonMangoldt (a + 1 + i) : Complex) *
        g ((a + 1 + i : Nat) : ZMod q) * lpfPhase beta (a + 1 + i)) -
      rho * Finset.sum (Finset.range N) (fun i => lpfPhase beta (a + 1 + i)) =
      Finset.sum (Finset.range N) (fun i => lpfPhase beta (a + 1 + i) * (F (a + i) - rho)) := by
    rw [Finset.mul_sum, <- Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [F]
    rw [hIndex]
    ring
  change norm (_ - rho * _) <= _
  rw [hIdentity]
  convert h using 1
  dsimp [B]
  ring

theorem lpf_primeInterval_rational_phase_numeric :
    forall {q : Nat} [NeZero q] (a : Units (ZMod q)),
        forall (s L : Nat) (beta : Real), 65536 <= s -> abs beta <= 1 ->
          norm (Finset.sum (Finset.range L) (fun i =>
              (ArithmeticFunction.vonMangoldt (s + 1 + i) : Complex) *
                lpfPhase (lpfRationalFrequency a + beta) (s + 1 + i)) -
            (ArithmeticFunction.moebius q : Complex) / (q.totient : Complex) *
              Finset.sum (Finset.range L) (fun i => lpfPhase beta (s + 1 + i))) <=
            2 * (1 + 2 * (L : Real) * abs beta) * lpfPhaseAllowance 65536 q (s + L) := by
  classical
  intro q inst a s L beta hs hBeta
  have h := lpf_primeInterval_phase_numeric (lpfResiduePhase a) (fun z => (norm_lpfResiduePhase a z).le)
    s L beta hs hBeta
  rw [unitFourierCoefficient_lpfResiduePhase] at h
  simpa only [mul_assoc, lpfResiduePhase_mul_lpfPhase] using h

theorem lpf_primeGridInterval_point_numeric :
    forall {N : Nat} [NeZero N] {q : Nat} [NeZero q] (a : Units (ZMod q)),
        forall (s L : Nat) (k : Int), Dvd.dvd q N -> 65536 <= s -> abs (lpfGridRadians N k) <= 1 ->
          norm (lpfGridIntervalWeight N s L (lpfRationalGridPoint N q (a : ZMod q).val k) -
            lpfRationalCoefficient q * lpfGridIntervalKernel N s L k) <=
            2 * (1 + 2 * (L : Real) * abs (lpfGridRadians N k)) * lpfPhaseAllowance 65536 q (s + L) := by
  classical
  intro N instN q instQ a s L k hDiv hs hBeta
  have h := lpf_primeInterval_rational_phase_numeric a s L (lpfGridRadians N k) hs hBeta
  simpa only [lpfGridIntervalWeight, lpfGridIntervalKernel, lpfRationalCoefficient,
    lpfRationalGridPoint_phase a hDiv k, lpfGrid_character_phase k] using h

end PrimeFactorOscillations.LPF

