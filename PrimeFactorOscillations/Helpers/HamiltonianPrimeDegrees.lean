/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianTruePrimeGap
import PrimeFactorOscillations.Helpers.HamiltonianUniformThetaError

/-! # Uniform degrees of the actual distinct-prime matrix

Every physical row is exactly a theta interval, including its endpoints.
The loop is retained separately and absorbed on the same all-large-order
domain. The resulting row error has every fixed logarithmic accuracy.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.LPF

theorem hamiltonian_finite_shift_window (n a : Nat) (f : Nat -> Real) :
    Finset.univ.sum (fun j : Fin n => f (a + (j.val + 1))) =
      (Finset.Ioc a (a + n)).sum f := by
  apply Finset.sum_bij (fun j _ => a + (j.val + 1))
  . intro j hj
    have h := j.isLt
    exact Finset.mem_Ioc.mpr (And.intro (by omega) (by omega))
  . intro i hi j hj h
    apply Fin.ext
    omega
  . intro t ht
    have h := Finset.mem_Ioc.mp ht
    let j : Fin n := Fin.mk (t - a - 1) (by omega)
    refine Exists.intro j (Exists.intro (Finset.mem_univ _) ?_)
    dsimp [j]
    omega
  . intro j hj
    rfl

theorem hamiltonian_prime_value_prefix (M : Nat) :
    (Finset.Ioc 0 M).sum hamiltonianPrimeValue = Chebyshev.theta (M : Real) := by
  rw [Chebyshev.theta, Nat.floor_natCast, Finset.sum_filter]
  rfl

theorem hamiltonian_prime_value_window (n a : Nat) :
    Finset.univ.sum (fun j : Fin n => hamiltonianPrimeValue (a + (j.val + 1))) =
      Chebyshev.theta ((a + n : Nat) : Real) - Chebyshev.theta (a : Real) := by
  have hDisjoint : Disjoint (Finset.Ioc 0 a) (Finset.Ioc a (a + n)) := by
    apply Finset.disjoint_left.mpr
    intro t ht hu
    have h := Finset.mem_Ioc.mp ht
    have h' := Finset.mem_Ioc.mp hu
    omega
  have hUnion : Union.union (Finset.Ioc 0 a) (Finset.Ioc a (a + n)) =
      Finset.Ioc 0 (a + n) := by
    apply Finset.ext
    intro t
    simp only [Finset.mem_union, Finset.mem_Ioc]
    omega
  have hSum : (Finset.Ioc 0 (a + n)).sum hamiltonianPrimeValue =
      (Finset.Ioc 0 a).sum hamiltonianPrimeValue +
        (Finset.Ioc a (a + n)).sum hamiltonianPrimeValue := by
    rw [<- hUnion, Finset.sum_union hDisjoint]
  rw [hamiltonian_finite_shift_window]
  rw [<- hamiltonian_prime_value_prefix (a + n), <- hamiltonian_prime_value_prefix a]
  linarith only [hSum]

def hamiltonianPrimeRawDegree (n : Nat) (i : Fin n) : Real :=
  (Finset.univ.sum (fun j : Fin n =>
    hamiltonianPrimeValue ((i.val + 1) + (j.val + 1)))) / (n : Real)

def hamiltonianPrimeDegree (n : Nat) (i : Fin n) : Real :=
  hamiltonianPrimeRawDegree n i -
    hamiltonianPrimeValue ((i.val + 1) + (i.val + 1)) / (n : Real)

theorem hamiltonian_prime_raw_degree_formula (n : Nat) (i : Fin n) :
    hamiltonianPrimeRawDegree n i =
      (Chebyshev.theta (((i.val + 1) + n : Nat) : Real) -
        Chebyshev.theta ((i.val + 1 : Nat) : Real)) / (n : Real) := by
  unfold hamiltonianPrimeRawDegree
  rw [hamiltonian_prime_value_window]

theorem hamiltonian_prime_raw_degree_cast (n : Nat) (i : Fin n) :
    Finset.univ.sum (fun j : Fin n => hamiltonianPrimeRawMatrix n i j) =
      (hamiltonianPrimeRawDegree n i : Complex) := by
  unfold hamiltonianPrimeRawMatrix hamiltonianPrimeRawDegree
  push_cast
  rw [<- Finset.sum_div]

theorem hamiltonian_prime_degree_cast (n : Nat) (i : Fin n) :
    Finset.univ.sum (fun j : Fin n => hamiltonianPrimeSumMatrix n i j) =
      (hamiltonianPrimeDegree n i : Complex) := by
  classical
  unfold hamiltonianPrimeSumMatrix
  simp only [Matrix.sub_apply, Finset.sum_sub_distrib]
  have hDiag : Finset.univ.sum (fun j : Fin n =>
      Matrix.diagonal (fun k => hamiltonianPrimeRawMatrix n k k) i j) =
        hamiltonianPrimeRawMatrix n i i := by simp [Matrix.diagonal_apply]
  rw [hDiag, hamiltonian_prime_raw_degree_cast]
  unfold hamiltonianPrimeDegree hamiltonianPrimeRawMatrix
  push_cast <;> rfl

theorem hamiltonian_prime_raw_degree_uniform (m : Nat) :
    exists D : Real, And (0 < D)
      (exists N0 : Nat, And (256 <= N0)
        (forall n : Nat, N0 <= n -> forall i : Fin n,
          abs (hamiltonianPrimeRawDegree n i - 1) <=
            D / Real.log (n : Real) ^ m)) := by
  choose C hC N0 hN0 hUniform using hamiltonian_uniform_theta_error m
  refine Exists.intro (2 * C) (And.intro (by positivity)
    (Exists.intro N0 (And.intro hN0 ?_)))
  intro n hn i
  let a := i.val + 1
  have hi := i.isLt
  have hn0 : 0 < (n : Real) := by exact_mod_cast (show 0 < n by omega)
  have hUp : (((a + n : Nat) : Real)) <= 2 * (n : Real) := by
    exact_mod_cast (show a + n <= 2 * n by dsimp [a]; omega)
  have hLow : (a : Real) <= 2 * (n : Real) := by
    exact_mod_cast (show a <= 2 * n by dsimp [a]; omega)
  have hUpper := hUniform n hn ((a + n : Nat) : Real) (Nat.cast_nonneg _) hUp
  have hLower := hUniform n hn (a : Real) (Nat.cast_nonneg _) hLow
  have hExact : hamiltonianPrimeRawDegree n i - 1 =
      ((Chebyshev.theta ((a + n : Nat) : Real) - ((a + n : Nat) : Real)) -
        (Chebyshev.theta (a : Real) - (a : Real))) / (n : Real) := by
    rw [hamiltonian_prime_raw_degree_formula]
    change (Chebyshev.theta ((a + n : Nat) : Real) - Chebyshev.theta (a : Real)) /
      (n : Real) - 1 = _
    push_cast
    field_simp <;> ring
  rw [hExact, abs_div, abs_of_pos hn0]
  calc
    _ <= (abs (Chebyshev.theta ((a + n : Nat) : Real) - ((a + n : Nat) : Real)) +
      abs (Chebyshev.theta (a : Real) - (a : Real))) / (n : Real) :=
      div_le_div_of_nonneg_right (abs_sub _ _) hn0.le
    _ <= (C * (n : Real) / Real.log (n : Real) ^ m +
      C * (n : Real) / Real.log (n : Real) ^ m) / (n : Real) :=
      div_le_div_of_nonneg_right (add_le_add hUpper hLower) hn0.le
    _ = _ := by field_simp <;> ring

theorem hamiltonian_prime_degree_uniform (m : Nat) :
    exists D : Real, And (0 < D)
      (exists N0 : Nat, And (256 <= N0)
        (forall n : Nat, N0 <= n -> forall i : Fin n,
          abs (hamiltonianPrimeDegree n i - 1) <= D / Real.log (n : Real) ^ m)) := by
  choose D hD A hA hRaw using hamiltonian_prime_raw_degree_uniform m
  choose B hB hDom using hamiltonian_log_power_dominated_uniform
    1 (by norm_num) (m + 1) 1 (by norm_num)
  let N0 := max A B
  refine Exists.intro (D + 1) (And.intro (by positivity)
    (Exists.intro N0 (And.intro (hA.trans (le_max_left _ _)) ?_)))
  intro n hn i
  have hnA : A <= n := (le_max_left A B).trans hn
  have hnB : B <= n := (le_max_right A B).trans hn
  have hn256 : 256 <= n := hA.trans hnA
  have hnPos : 0 < n := by omega
  letI : NeZero n := NeZero.mk (Nat.ne_of_gt hnPos)
  have hn0 : 0 < (n : Real) := by exact_mod_cast hnPos
  have hn1 : (1 : Real) < (n : Real) := by exact_mod_cast (show 1 < n by omega)
  let L := Real.log (2 * (n : Real))
  have hLogN : 0 < Real.log (n : Real) := Real.log_pos hn1
  have hDen : 0 < Real.log (n : Real) ^ m := pow_pos hLogN m
  have hL : 0 <= L := Real.log_nonneg (by
    have h : (1 : Real) <= (n : Real) := by exact_mod_cast hnPos
    linarith only [h])
  have hLogCompare : Real.log (n : Real) <= L := by
    exact Real.log_le_log hn0 (by linarith only [hn0])
  have hPower := wick_nonnegative_power_le _ _ hLogN.le hLogCompare m
  have hDomN := hDom n hnB
  simp only [one_mul, Real.rpow_one] at hDomN
  change L ^ (m + 1) <= (n : Real) at hDomN
  have hCross : L * Real.log (n : Real) ^ m <= (n : Real) := by
    have h := mul_le_mul_of_nonneg_left hPower hL
    exact h.trans (by simpa only [pow_succ, mul_comm] using hDomN)
  have hLoopScale : L / (n : Real) <= 1 / Real.log (n : Real) ^ m := by
    calc
      _ = ((L * Real.log (n : Real) ^ m) / (n : Real)) /
          Real.log (n : Real) ^ m := by field_simp
      _ <= ((n : Real) / (n : Real)) / Real.log (n : Real) ^ m :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hCross hn0.le) hDen.le
      _ = _ := by field_simp
  let z := hamiltonianPrimeValue ((i.val + 1) + (i.val + 1)) / (n : Real)
  have hz0 : 0 <= z := div_nonneg (hamiltonian_prime_value_nonnegative _) (Nat.cast_nonneg n)
  have hz : z <= L / (n : Real) := by
    have h := hamiltonian_prime_raw_entry_bound i i
    unfold hamiltonianPrimeRawMatrix at h
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hamiltonian_prime_value_nonnegative _), Complex.norm_natCast] at h
    exact h
  have hExact : hamiltonianPrimeDegree n i - 1 =
      (hamiltonianPrimeRawDegree n i - 1) - z := by
    dsimp [hamiltonianPrimeDegree, z]
    ring
  rw [hExact]
  calc
    _ <= abs (hamiltonianPrimeRawDegree n i - 1) + abs z := abs_sub _ _
    _ = abs (hamiltonianPrimeRawDegree n i - 1) + z := by rw [abs_of_nonneg hz0]
    _ <= D / Real.log (n : Real) ^ m + 1 / Real.log (n : Real) ^ m :=
      add_le_add (hRaw n hnA i) (hz.trans hLoopScale)
    _ = _ := by ring

end PrimeFactorOscillations.LPF
