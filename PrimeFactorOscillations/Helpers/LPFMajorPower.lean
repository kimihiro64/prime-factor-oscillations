/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import PrimeFactorOscillations.Helpers.LPFUniformMajor

/-!
The proved arithmetic major packet has power 119/40 when P <= M^(1/40).
This is a bound on the complete major square-difference, not on a separately
discarded component. The minor and the two tail packets remain outstanding.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem lpfMajorEnvelope_le_power (K M P : Real) (hM : 1 <= M)
    (hP0 : 0 <= P) (hP : P <= M ^ (1 / 40 : Real)) :
    8 * K ^ 2 * P ^ 4 * (M ^ (15 / 16 : Real)) ^ 2 * M * (1 + Real.log M) ^ 4 +
      6 * K ^ 4 * P ^ 9 * (M ^ (15 / 16 : Real)) ^ 4 * (1 + Real.log M) ^ 8 / M <=
      (8 * K ^ 2 * (1 + Real.log M) ^ 4 + 6 * K ^ 4 * (1 + Real.log M) ^ 8) *
        M ^ (119 / 40 : Real) := by
  have hMpos : 0 < M := by linarith
  have hM0 : 0 <= M := hMpos.le
  have hPP (n : Nat) : P ^ n <= M ^ ((n : Real) / 40) := by
    calc
      _ <= (M ^ (1 / 40 : Real)) ^ n := by gcongr
      _ = M ^ ((1 / 40 : Real) * (n : Real)) := by
        rw [<- Real.rpow_natCast, <- Real.rpow_mul hM0]
      _ = _ := by congr 1; ring
  have h4 : P ^ 4 <= M ^ (1 / 10 : Real) := by
    have h := hPP 4
    norm_num at h
    exact h
  have h9 : P ^ 9 <= M ^ (9 / 40 : Real) := by simpa using hPP 9
  have h2 : (M ^ (15 / 16 : Real)) ^ 2 = M ^ (15 / 8 : Real) := by
    rw [<- Real.rpow_natCast, <- Real.rpow_mul hM0]
    norm_num
  have hFourth : (M ^ (15 / 16 : Real)) ^ 4 = M ^ (15 / 4 : Real) := by
    rw [<- Real.rpow_natCast, <- Real.rpow_mul hM0]
    norm_num
  have hTerm1 : P ^ 4 * (M ^ (15 / 16 : Real)) ^ 2 * M <= M ^ (119 / 40 : Real) := by
    calc
      _ <= M ^ (1 / 10 : Real) * (M ^ (15 / 16 : Real)) ^ 2 * M :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h4 (sq_nonneg _)) hM0
      _ = M ^ ((1 / 10 : Real) + 15 / 8 + 1) := by
        rw [h2, Real.rpow_add hMpos, Real.rpow_add hMpos, Real.rpow_one]
      _ = _ := by norm_num
  have hTerm2 : P ^ 9 * (M ^ (15 / 16 : Real)) ^ 4 / M <= M ^ (119 / 40 : Real) := by
    calc
      _ <= M ^ (9 / 40 : Real) * (M ^ (15 / 16 : Real)) ^ 4 / M :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h9 (by positivity)) hM0
      _ = M ^ ((9 / 40 : Real) + 15 / 4 - 1) := by
        rw [hFourth, Real.rpow_sub hMpos, Real.rpow_add hMpos, Real.rpow_one]
      _ = _ := by norm_num
  have hTotal := add_le_add
    (mul_le_mul_of_nonneg_left hTerm1 (by positivity : 0 <= 8 * K ^ 2 * (1 + Real.log M) ^ 4))
    (mul_le_mul_of_nonneg_left hTerm2 (by positivity : 0 <= 6 * K ^ 4 * (1 + Real.log M) ^ 8))
  convert hTotal using 1 <;> ring

theorem exists_primeGridInterval_major_power_bound :
    exists K : Real, And (0 < K)
      (forall {N : Nat} [NeZero N] (M P s L : Nat) (T : Finset (ZMod N)),
        0 < P -> 8 * P <= M -> Dvd.dvd M N ->
        (forall q, 0 < q -> q <= P -> Dvd.dvd q N) -> 2 * P ^ 3 < M ->
        65536 <= s -> L <= M -> s + L <= 2 * M -> s + L < N ->
        (P : Real) <= (M : Real) ^ (1 / 40 : Real) ->
        Finset.sum T (fun t => Complex.normSq (lpfCyclicInverse
          (fun x => if Membership.mem (lpfRationalGrid N P ((N / M) * P)) x then
            (lpfGridIntervalWeight N s L x) ^ 2 -
            (lpfRationalGridReference N P ((N / M) * P) (lpfGridIntervalKernel N s L) x) ^ 2
            else 0) t)) <=
          (8 * K ^ 2 * (1 + Real.log (M : Real)) ^ 4 +
            6 * K ^ 4 * (1 + Real.log (M : Real)) ^ 8) * (M : Real) ^ (119 / 40 : Real)) := by
  choose K hK hSource using exists_primeGridInterval_complete_major_bound
  refine Exists.intro K (And.intro hK ?_)
  intro N instN M P s L T hP hEight hDivM hDiv hSmall hs hL hX hNoWrap hPower
  have hM : (1 : Real) <= (M : Real) := by exact_mod_cast (show 1 <= M by omega)
  exact (hSource M P s L T hP hEight hDivM hDiv hSmall hs hL hX hNoWrap).trans
    (lpfMajorEnvelope_le_power K (M : Real) (P : Real) hM (Nat.cast_nonneg _) hPower)

end PrimeFactorOscillations.LPF
