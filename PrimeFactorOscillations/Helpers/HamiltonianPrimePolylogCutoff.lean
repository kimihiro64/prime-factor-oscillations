/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianLogMomentChoice
import PrimeFactorOscillations.Helpers.HamiltonianPrimeCutoffSelection

/-! # A genuinely polylogarithmic cutoff with every physical range retained -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.LPF

def hamiltonianPrimePolylogCutoff (b M : Nat) : Nat :=
  Nat.floor ((1 + Real.log (2 * (M : Real))) ^ (2 * (b + 6)))

theorem hamiltonian_prime_polylog_cutoff_admissible
    (b : Nat) (eps : Real) (hEps : 0 < eps) :
    exists M0 : Nat, 2 ^ 18 <= M0 /\
      forall M : Nat, M0 <= M ->
        let Q := hamiltonianPrimePolylogCutoff b M
        And (4 <= Q)
          (And ((Q : Real) <= (M : Real) ^ ((1 : Real) / 40))
            (And (8 * Q ^ 2 <= M)
              (And (4 * Q ^ 4 <= M)
                (And ((Q : Real) ^ 5 <= (M : Real))
                  (And ((Q : Real) ^ 4 * (M : Real) ^ (15 / 16 : Real) <= (M : Real))
                    (And ((M : Real) ^ (8 / 5 : Real) * (Q : Real) <= (M : Real) ^ 2)
                      (((1 + Real.log (2 * (M : Real))) ^ 5 /
                        Real.sqrt (Q : Real)) *
                        (1 + Real.log (2 * (M : Real))) ^ b <= eps))))))) := by
  let a : Real := 1 / 160
  let k := 2 * (b + 6)
  let r := max 8 (2 / eps)
  have hC : 0 < (2 : Real) ^ k := pow_pos (by norm_num) k
  choose A hA hEight using hamiltonian_log_power_dominated_uniform
    8 (by norm_num) 0 a (by norm_num [a])
  choose B hB hSmall using hamiltonian_log_power_dominated_uniform
    ((2 : Real) ^ k) hC k a (by norm_num [a])
  let E := Nat.ceil (Real.exp r)
  let M0 := max (2 ^ 18) (max A (max B E))
  refine Exists.intro M0 (And.intro (le_max_left _ _) ?_)
  intro M hM
  have hMA : A <= M :=
    (le_max_left A (max B E)).trans ((le_max_right (2 ^ 18) _).trans hM)
  have hMB : B <= M :=
    (le_max_left B E).trans ((le_max_right A _).trans ((le_max_right (2 ^ 18) _).trans hM))
  have hME : E <= M :=
    (le_max_right B E).trans ((le_max_right A _).trans ((le_max_right (2 ^ 18) _).trans hM))
  have hM256 : 256 <= M := hB.trans hMB
  have hMR : (1 : Real) <= (M : Real) := by exact_mod_cast (show 1 <= M by omega)
  have hMPos : (0 : Real) < (M : Real) := by linarith only [hMR]
  let ell : Real := 1 + Real.log (2 * (M : Real))
  let Y := ell ^ k
  let x : Real := (M : Real) ^ a
  let Q := hamiltonianPrimePolylogCutoff b M
  have hExp : Real.exp r <= (M : Real) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hME)
  have hLogM : r <= Real.log (M : Real) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos r) hExp
  have hLogDouble : Real.log (M : Real) <= Real.log (2 * (M : Real)) :=
    Real.log_le_log hMPos (by linarith only [hMR])
  have hEllR : r <= ell := by dsimp [ell]; linarith only [hLogM, hLogDouble]
  have hEll8 : 8 <= ell := (le_max_left 8 (2 / eps)).trans hEllR
  have hEll : 0 <= ell := by linarith only [hEll8]
  have hLog : 1 <= Real.log (2 * (M : Real)) := by
    dsimp [ell] at hEll8
    linarith only [hEll8]
  have hEllLog : ell <= 2 * Real.log (2 * (M : Real)) := by
    dsimp [ell]
    linarith only [hLog]
  have hPowOne (t : Nat) : 1 <= ell ^ t := by
    induction t with
    | zero => simp only [pow_zero, le_refl]
    | succ t ih =>
      rw [pow_succ]
      have h := mul_le_mul ih (show 1 <= ell by linarith only [hEll8])
        (by norm_num : (0 : Real) <= 1) (pow_nonneg hEll t)
      simpa only [one_mul] using h
  have hK : k = (k - 1) + 1 := by dsimp [k]; omega
  have hYLower : ell <= Y := by
    change ell <= ell ^ k
    rw [hK, pow_succ]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hPowOne (k - 1)) hEll
  have hY8 : 8 <= Y := hEll8.trans hYLower
  have hEllPower := wick_nonnegative_power_le _ _ hEll hEllLog k
  rw [mul_pow] at hEllPower
  have hYUpper : Y <= x := hEllPower.trans (hSmall M hMB)
  have hx8 : (8 : Real) <= x := by
    simpa only [pow_zero, mul_one] using hEight M hMA
  have hQUpper : (Q : Real) <= x :=
    (Nat.floor_le (pow_nonneg hEll k)).trans hYUpper
  have hFloor : Y < (Q : Real) + 1 := Nat.lt_floor_add_one Y
  have hQ4 : 4 <= Q := by
    have h : (4 : Real) <= (Q : Real) := by linarith only [hFloor, hY8]
    exact_mod_cast h
  have hQR : (0 : Real) < (Q : Real) := by exact_mod_cast (show 0 < Q by omega)
  have hQLower : Y <= 2 * (Q : Real) := by linarith only [hFloor, hY8]
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
  have hEllEps : 2 / eps <= ell := (le_max_right 8 (2 / eps)).trans hEllR
  have hEpsEll : 2 <= eps * ell := by
    have h := mul_le_mul_of_nonneg_left hEllEps hEps.le
    have he : eps * (2 / eps) = 2 := by field_simp [ne_of_gt hEps]
    rw [he] at h
    exact h
  have hEpsSquare : (4 : Real) <= (eps * ell) ^ 2 := by
    nlinarith only [hEpsEll]
  let j := 2 * (b + 5)
  have hIdentity : eps ^ 2 * Y = ell ^ j * (eps * ell) ^ 2 := by
    have hkj : k = j + 2 := by dsimp [k, j]; omega
    dsimp [Y]
    rw [hkj, pow_add]
    ring
  have hQBudget := mul_le_mul_of_nonneg_left hQLower (sq_nonneg eps)
  rw [hIdentity] at hQBudget
  have hRestore := mul_le_mul_of_nonneg_left hEpsSquare (pow_nonneg hEll j)
  have hEllBudget : ell ^ j <= eps ^ 2 * (Q : Real) := by
    nlinarith only [hQBudget, hRestore, pow_nonneg hEll j]
  have hSqrt : Real.sqrt (Q : Real) ^ 2 = (Q : Real) := Real.sq_sqrt hQR.le
  have hSqrtPos : 0 < Real.sqrt (Q : Real) := Real.sqrt_pos.mpr hQR
  have hCrossSquare : (ell ^ (b + 5)) ^ 2 <= (eps * Real.sqrt (Q : Real)) ^ 2 := by
    calc
      _ = ell ^ j := by dsimp [j]; rw [<- pow_mul]; congr 1 <;> omega
      _ <= eps ^ 2 * (Q : Real) := hEllBudget
      _ = _ := by rw [mul_pow, hSqrt]
  have hCross : ell ^ (b + 5) <= eps * Real.sqrt (Q : Real) := by
    have hLeft : 0 <= ell ^ (b + 5) := pow_nonneg hEll _
    have hRight : 0 <= eps * Real.sqrt (Q : Real) := mul_nonneg hEps.le hSqrtPos.le
    nlinarith only [hCrossSquare, hLeft, hRight]
  have hRatio : (ell ^ 5 / Real.sqrt (Q : Real)) * ell ^ b <= eps := by
    calc
      _ = ell ^ (b + 5) / Real.sqrt (Q : Real) := by rw [pow_add]; ring
      _ <= (eps * Real.sqrt (Q : Real)) / Real.sqrt (Q : Real) :=
        div_le_div_of_nonneg_right hCross hSqrtPos.le
      _ = _ := by field_simp [ne_of_gt hSqrtPos]
  exact And.intro hQ4 (And.intro hQForty (And.intro hEightNat
    (And.intro hFourNat (And.intro hFive (And.intro hMajor (And.intro hMinor hRatio))))))

end PrimeFactorOscillations.LPF
