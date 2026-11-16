/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCountPowerDecay
import PrimeFactorOscillations.Helpers.HamiltonianPrimeOperatorComparison

/-! # Admissible integer cutoffs with an arbitrarily small complete scale

The cutoff is floor(M^(1/160)). Every physical, major, minor and spectral
power constraint is checked on the same all-large-M domain. The final
logarithmic ratio can be made smaller than any prescribed positive value.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.LPF

def hamiltonianPrimeCutoff (M : Nat) : Nat :=
  Nat.floor ((M : Real) ^ (1 / 160 : Real))

theorem hamiltonian_prime_cutoff_admissible (eps : Real) (hEps : 0 < eps) :
    exists M0 : Nat, And (2 ^ 18 <= M0)
      (forall M : Nat, M0 <= M ->
        let Q := hamiltonianPrimeCutoff M
        And (4 <= Q)
          (And ((Q : Real) <= (M : Real) ^ ((1 : Real) / 40))
            (And (8 * Q ^ 2 <= M)
              (And (4 * Q ^ 4 <= M)
                (And ((Q : Real) ^ 5 <= (M : Real))
                  (And ((Q : Real) ^ 4 * (M : Real) ^ (15 / 16 : Real) <= (M : Real))
                    (And ((M : Real) ^ (8 / 5 : Real) * (Q : Real) <= (M : Real) ^ 2)
                      ((1 + Real.log (2 * (M : Real))) ^ 5 /
                        Real.sqrt (Q : Real) <= eps)))))))) := by
  let a : Real := 1 / 160
  let C : Real := 2048 / eps ^ 2
  have hC : 0 < C := by dsimp [C]; positivity
  choose A hA hEight using hamiltonian_log_power_dominated_uniform
    8 (by norm_num) 0 a (by norm_num [a])
  choose B hB hSmall using hamiltonian_log_power_dominated_uniform
    C hC 10 a (by norm_num [a])
  let M0 := max (2 ^ 18) (max A B)
  refine Exists.intro M0 (And.intro (le_max_left _ _) ?_)
  intro M hM
  have hMA : A <= M := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hM
  have hMB : B <= M := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hM
  have hM256 : 256 <= M := hA.trans hMA
  have hMR : (1 : Real) <= (M : Real) := by exact_mod_cast (show 1 <= M by omega)
  have hMPos : (0 : Real) < (M : Real) := by linarith only [hMR]
  let x : Real := (M : Real) ^ a
  let Q := hamiltonianPrimeCutoff M
  let ell : Real := 1 + Real.log (2 * (M : Real))
  have hx8 : (8 : Real) <= x := by
    simpa only [pow_zero, mul_one] using hEight M hMA
  have hQUpper : (Q : Real) <= x := Nat.floor_le (by positivity)
  have hFloor : x < (Q : Real) + 1 := Nat.lt_floor_add_one x
  have hQLower : x <= 2 * (Q : Real) := by linarith only [hFloor, hx8]
  have hQ4 : 4 <= Q := by
    have h : (4 : Real) <= (Q : Real) := by linarith only [hFloor, hx8]
    exact_mod_cast h
  have hQR : (0 : Real) < (Q : Real) := by exact_mod_cast (show 0 < Q by omega)
  have hPower (k : Nat) : (Q : Real) ^ k <= (M : Real) ^ (a * (k : Real)) := by
    calc
      _ <= x ^ k := wick_nonnegative_power_le _ _ hQR.le hQUpper k
      _ = _ := by dsimp [x]; rw [<- Real.rpow_natCast, <- Real.rpow_mul hMPos.le]
  have hExponent (b : Real) (hb : b <= 1) : (M : Real) ^ b <= (M : Real) :=
    (Real.rpow_le_rpow_of_exponent_le hMR hb).trans_eq (Real.rpow_one _)
  have hQForty : (Q : Real) <= (M : Real) ^ ((1 : Real) / 40) := by
    exact hQUpper.trans (Real.rpow_le_rpow_of_exponent_le hMR (by norm_num [a]))
  have hEightReal : 8 * (Q : Real) ^ 2 <= (M : Real) := by
    calc
      _ <= x * (M : Real) ^ (a * (2 : Real)) :=
        mul_le_mul hx8 (hPower 2) (sq_nonneg _) (by dsimp [x]; positivity)
      _ = (M : Real) ^ (a + a * 2) := by
        dsimp [x]
        rw [Real.rpow_add hMPos]
      _ <= _ := hExponent _ (by norm_num [a])
  have hEightNat : 8 * Q ^ 2 <= M := by exact_mod_cast hEightReal
  have hFourReal : 4 * (Q : Real) ^ 4 <= (M : Real) := by
    calc
      _ <= x * (M : Real) ^ (a * (4 : Real)) :=
        mul_le_mul (by linarith only [hx8]) (hPower 4) (by positivity)
          (by dsimp [x]; positivity)
      _ = (M : Real) ^ (a + a * 4) := by
        dsimp [x]
        rw [Real.rpow_add hMPos]
      _ <= _ := hExponent _ (by norm_num [a])
  have hFourNat : 4 * Q ^ 4 <= M := by exact_mod_cast hFourReal
  have hFive : (Q : Real) ^ 5 <= (M : Real) :=
    (hPower 5).trans (hExponent _ (by norm_num [a]))
  have hMajor : (Q : Real) ^ 4 * (M : Real) ^ (15 / 16 : Real) <= (M : Real) := by
    calc
      _ <= (M : Real) ^ (a * (4 : Real)) * (M : Real) ^ (15 / 16 : Real) :=
        mul_le_mul_of_nonneg_right (hPower 4) (by positivity)
      _ = (M : Real) ^ (a * 4 + 15 / 16) := (Real.rpow_add hMPos _ _).symm
      _ <= _ := hExponent _ (by norm_num [a])
  have hMinor : (M : Real) ^ (8 / 5 : Real) * (Q : Real) <= (M : Real) ^ 2 := by
    calc
      _ <= (M : Real) ^ (8 / 5 : Real) * x :=
        mul_le_mul_of_nonneg_left hQUpper (by positivity)
      _ = (M : Real) ^ (8 / 5 + a) := by dsimp [x]; rw [Real.rpow_add hMPos]
      _ <= (M : Real) ^ (2 : Real) :=
        Real.rpow_le_rpow_of_exponent_le hMR (by norm_num [a])
      _ = _ := Real.rpow_natCast _ 2
  have hLog2 : (1 / 2 : Real) <= Real.log (2 : Real) := by
    have h := Real.log_le_sub_one_of_pos
      (by norm_num : (0 : Real) < (2 : Real) ^ (-1 : Int))
    rw [zpow_neg_one, Real.log_inv] at h
    norm_num at h
    linarith
  have hLog4 : Real.log (4 : Real) = 2 * Real.log (2 : Real) := by
    have h : (4 : Real) = 2 ^ (2 : Nat) := by norm_num
    rw [h, Real.log_pow]
    norm_num
  have hLog : 1 <= Real.log (2 * (M : Real)) := by
    have h := Real.log_le_log (by norm_num : (0 : Real) < 4)
      (by linarith only [hMR, show (256 : Real) <= (M : Real) by exact_mod_cast hM256] :
        (4 : Real) <= 2 * (M : Real))
    linarith only [hLog2, hLog4, h]
  have hEll : 0 <= ell := by dsimp [ell]; linarith only [hLog]
  have hEllLog : ell <= 2 * Real.log (2 * (M : Real)) := by
    dsimp [ell]
    linarith only [hLog]
  have hEllPower := wick_nonnegative_power_le _ _ hEll hEllLog 10
  rw [mul_pow] at hEllPower
  have hBudget : 2048 * Real.log (2 * (M : Real)) ^ 10 <= x * eps ^ 2 := by
    calc
      _ = (C * Real.log (2 * (M : Real)) ^ 10) * eps ^ 2 := by
        dsimp [C]
        field_simp
      _ <= x * eps ^ 2 := mul_le_mul_of_nonneg_right (hSmall M hMB) (sq_nonneg eps)
  have hQBudget := mul_le_mul_of_nonneg_right hQLower (sq_nonneg eps)
  have hEllBudget : ell ^ 10 <= eps ^ 2 * (Q : Real) := by
    norm_num at hEllPower
    nlinarith only [hEllPower, hBudget, hQBudget]
  have hSqrt : Real.sqrt (Q : Real) ^ 2 = (Q : Real) := Real.sq_sqrt hQR.le
  have hSqrtPos : 0 < Real.sqrt (Q : Real) := Real.sqrt_pos.mpr hQR
  have hCrossSquare : (ell ^ 5) ^ 2 <= (eps * Real.sqrt (Q : Real)) ^ 2 := by
    rw [mul_pow, hSqrt]
    nlinarith only [hEllBudget]
  have hCross : ell ^ 5 <= eps * Real.sqrt (Q : Real) := by
    have hLeft : 0 <= ell ^ 5 := pow_nonneg hEll _
    have hRight : 0 <= eps * Real.sqrt (Q : Real) := by positivity
    nlinarith only [hCrossSquare, hLeft, hRight]
  have hRatio : ell ^ 5 / Real.sqrt (Q : Real) <= eps := by
    calc
      _ <= (eps * Real.sqrt (Q : Real)) / Real.sqrt (Q : Real) :=
        div_le_div_of_nonneg_right hCross hSqrtPos.le
      _ = _ := by field_simp
  exact And.intro hQ4 (And.intro hQForty (And.intro hEightNat
    (And.intro hFourNat (And.intro hFive (And.intro hMajor (And.intro hMinor hRatio))))))

end PrimeFactorOscillations.LPF
