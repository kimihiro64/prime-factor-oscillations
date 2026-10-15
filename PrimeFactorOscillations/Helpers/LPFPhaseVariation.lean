/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFAdditivePrefix
import PrimeFactorOscillations.Mathlib.Analysis.Complex.AbelBound

/-!
# Prime-interval phase bounds

Keep the already centered prime-prefix packet in summation by parts.
The exponential phase uses radians: exp(i * beta * n). Its increment bound
requires abs beta <= 1 and gives the 1 + 2 * length * abs beta cost.
The full prime-interval theorem retains its exact principal residue average.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem norm_sum_range_mul_le_of_variation
    (w f : Nat -> Complex) (N : Nat) (M : Real)
    (hPrefix : forall n, n <= N -> norm (Finset.sum (Finset.range n) f) <= M) :
    norm (Finset.sum (Finset.range N) (fun i => w i * f i)) <=
      (norm (w (N - 1)) + Finset.sum (Finset.range (N - 1))
        (fun i => norm (w (i + 1) - w i))) * M := by
  have hM : 0 <= M := by simpa using hPrefix 0 (Nat.zero_le N)
  cases N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero, Nat.zero_sub, add_zero]
    exact mul_nonneg (norm_nonneg _) hM
  | succ n =>
    have hLast : norm (w n * Finset.sum (Finset.range (n + 1)) f) <= norm (w n) * M := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hPrefix (n + 1) le_rfl) (norm_nonneg _)
    have hTerm (i : Nat) (hi : Membership.mem (Finset.range n) i) :
        norm ((w (i + 1) - w i) * Finset.sum (Finset.range (i + 1)) f) <=
          norm (w (i + 1) - w i) * M := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (hPrefix (i + 1) ((Nat.succ_le_of_lt (Finset.mem_range.mp hi)).trans (Nat.le_succ n)))
        (norm_nonneg _)
    change norm (Finset.sum (Finset.range (n + 1))
      (fun i => HSMul.hSMul (w i) (f i))) <= _
    rw [Finset.sum_range_by_parts]
    simp only [Nat.add_sub_cancel, smul_eq_mul]
    calc
      _ <= norm (w n * Finset.sum (Finset.range (n + 1)) f) +
          norm (Finset.sum (Finset.range n)
            (fun i => (w (i + 1) - w i) * Finset.sum (Finset.range (i + 1)) f)) :=
        norm_sub_le _ _
      _ <= norm (w n) * M + Finset.sum (Finset.range n)
          (fun i => norm (w (i + 1) - w i) * M) :=
        add_le_add hLast ((norm_sum_le _ _).trans (Finset.sum_le_sum hTerm))
      _ = _ := by rw [<- Finset.sum_mul]; ring

noncomputable def lpfPhase (beta : Real) (n : Nat) : Complex :=
  Complex.exp (((beta * (n : Real) : Real) : Complex) * Complex.I)

theorem norm_lpfPhase (beta : Real) (n : Nat) : norm (lpfPhase beta n) = 1 := by
  simp [lpfPhase, Complex.norm_exp, Complex.mul_re]

theorem norm_lpfPhase_succ_sub_le (beta : Real) (n : Nat) (hBeta : abs beta <= 1) :
    norm (lpfPhase beta (n + 1) - lpfPhase beta n) <= 2 * abs beta := by
  have hStep : lpfPhase beta (n + 1) =
      lpfPhase beta n * Complex.exp ((beta : Complex) * Complex.I) := by
    unfold lpfPhase
    rw [<- Complex.exp_add]
    congr 1
    push_cast
    ring
  have hNorm : norm ((beta : Complex) * Complex.I) <= 1 := by
    simpa only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      using hBeta
  have hExp := Complex.norm_exp_sub_one_le hNorm
  rw [hStep, <- mul_sub_one, norm_mul, norm_lpfPhase, one_mul]
  simpa only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] using hExp

theorem norm_sum_range_phase_mul_le
    (f : Nat -> Complex) (a N : Nat) (beta M : Real) (hBeta : abs beta <= 1)
    (hPrefix : forall n, n <= N -> norm (Finset.sum (Finset.range n) f) <= M) :
    norm (Finset.sum (Finset.range N) (fun i => lpfPhase beta (a + i) * f i)) <=
      (1 + 2 * (N : Real) * abs beta) * M := by
  have hM : 0 <= M := by simpa using hPrefix 0 (Nat.zero_le N)
  have h := norm_sum_range_mul_le_of_variation (fun i => lpfPhase beta (a + i)) f N M hPrefix
  simp only [norm_lpfPhase] at h
  have hTerm (i : Nat) :
      norm (lpfPhase beta (a + (i + 1)) - lpfPhase beta (a + i)) <= 2 * abs beta := by
    simpa only [Nat.add_assoc] using norm_lpfPhase_succ_sub_le beta (a + i) hBeta
  have hSum := Finset.sum_le_sum
    (fun i (_ : Membership.mem (Finset.range (N - 1)) i) => hTerm i)
  have hCard : ((N - 1 : Nat) : Real) <= (N : Real) := by exact_mod_cast Nat.sub_le N 1
  have hVar : Finset.sum (Finset.range (N - 1)) (fun i =>
      norm (lpfPhase beta (a + (i + 1)) - lpfPhase beta (a + i))) <=
        2 * (N : Real) * abs beta := by
    calc
      _ <= Finset.sum (Finset.range (N - 1)) (fun _ => 2 * abs beta) := hSum
      _ = ((N - 1 : Nat) : Real) * (2 * abs beta) := by simp
      _ <= (N : Real) * (2 * abs beta) :=
        mul_le_mul_of_nonneg_right hCard (by positivity)
      _ = _ := by ring
  exact h.trans (mul_le_mul_of_nonneg_right (add_le_add (le_refl 1) hVar) hM)

noncomputable def lpfPhaseAllowance (A : Real) (q x : Nat) : Real :=
  A * Real.sqrt (q.totient : Real) * (x : Real) ^ (15 / 16 : Real) *
    (1 + Real.log q + Real.log ((x : Real) + 2)) ^ 2 +
    Real.log q * Real.log (x : Real) / Real.log (2 : Real)

theorem lpfPhaseAllowance_mono (A : Real) (q a b : Nat)
    (hA : 0 <= A) (hq : 1 <= q) (ha : 1 <= a) (hab : a <= b) :
    lpfPhaseAllowance A q a <= lpfPhaseAllowance A q b := by
  have hAR : (1 : Real) <= (a : Real) := by exact_mod_cast ha
  have hAB : (a : Real) <= (b : Real) := by exact_mod_cast hab
  have hQR : (1 : Real) <= (q : Real) := by exact_mod_cast hq
  have hLogQ : 0 <= Real.log q := Real.log_nonneg hQR
  have hLogA : 0 <= Real.log (a : Real) := Real.log_nonneg hAR
  have hLogAB : Real.log (a : Real) <= Real.log (b : Real) :=
    Real.log_le_log (zero_lt_one.trans_le hAR) hAB
  have hFactor : 1 + Real.log q + Real.log ((a : Real) + 2) <=
      1 + Real.log q + Real.log ((b : Real) + 2) := by
    have h := Real.log_le_log (by positivity : 0 < (a : Real) + 2)
      (add_le_add hAB (le_refl 2))
    linarith only [h]
  have hFactorA : 0 <= 1 + Real.log q + Real.log ((a : Real) + 2) := by
    have hLog := Real.log_nonneg (by linarith : (1 : Real) <= (a : Real) + 2)
    linarith only [hLogQ, hLog]
  have hFactorB : 0 <= 1 + Real.log q + Real.log ((b : Real) + 2) := hFactorA.trans hFactor
  have hSquare : (1 + Real.log q + Real.log ((a : Real) + 2)) ^ 2 <=
      (1 + Real.log q + Real.log ((b : Real) + 2)) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hFactor hFactor hFactorA hFactorB
  have hPower : (a : Real) ^ (15 / 16 : Real) <= (b : Real) ^ (15 / 16 : Real) :=
    Real.rpow_le_rpow (by positivity) hAB (by norm_num)
  have hPowerA : 0 <= (a : Real) ^ (15 / 16 : Real) := Real.rpow_nonneg (by positivity) _
  have hCoeff : 0 <= A * Real.sqrt (q.totient : Real) := by positivity
  have hMain := mul_le_mul
    (mul_le_mul_of_nonneg_left hPower hCoeff) hSquare (sq_nonneg _)
    (mul_nonneg hCoeff (Real.rpow_nonneg (by positivity : 0 <= (b : Real)) _))
  have hCorrection := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hLogAB hLogQ)
    (Real.log_pos (by norm_num : (1 : Real) < 2)).le
  exact add_le_add hMain hCorrection

private theorem sum_range_primeWeight_eq_Icc {q : Nat} [NeZero q]
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

private theorem sum_range_shift_center (F : Nat -> Complex) (rho : Complex) (a k : Nat) :
    Finset.sum (Finset.range k) (fun i => F (a + i) - rho) =
      (Finset.sum (Finset.range (a + k)) F - ((a + k : Nat) : Complex) * rho) -
      (Finset.sum (Finset.range a) F - (a : Complex) * rho) := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Finset.sum_range_add]
  simp only [Nat.cast_add]
  ring

theorem exists_primeInterval_phase_power_bound :
    exists A : Real, And (0 < A)
      (forall {q : Nat} [NeZero q] (g : ZMod q -> Complex),
        (forall z, norm (g z) <= 1) -> forall (a N : Nat) (beta : Real),
          65536 <= a -> abs beta <= 1 ->
          norm (Finset.sum (Finset.range N) (fun i =>
            (ArithmeticFunction.vonMangoldt (a + 1 + i) : Complex) *
              g ((a + 1 + i : Nat) : ZMod q) * lpfPhase beta (a + 1 + i)) -
            (unitFourierCoefficient g 1 / (q.totient : Complex)) *
              Finset.sum (Finset.range N) (fun i => lpfPhase beta (a + 1 + i))) <=
            2 * (1 + 2 * (N : Real) * abs beta) * lpfPhaseAllowance A q (a + N)) := by
  classical
  choose A hA hSource using exists_primePrefix_phase_power_bound
  refine Exists.intro A (And.intro hA ?_)
  intro q inst g hg a N beta ha hBeta
  let rho : Complex := unitFourierCoefficient g 1 / (q.totient : Complex)
  let F (n : Nat) : Complex := (ArithmeticFunction.vonMangoldt (n + 1) : Complex) *
    g ((n + 1 : Nat) : ZMod q)
  let B : Real := lpfPhaseAllowance A q (a + N)
  have hCenter (x : Nat) : (x : Complex) * rho =
      (x : Complex) / (q.totient : Complex) * unitFourierCoefficient g 1 := by
    dsimp [rho]
    ring
  have hCut (k : Nat) (hk : k <= N) :
      norm (Finset.sum (Finset.range (a + k)) F - ((a + k : Nat) : Complex) * rho) <= B := by
    have hSrc := hSource g hg (by omega : 65536 <= a + k)
    change norm (Finset.sum (Finset.range (a + k)) (fun n =>
      (ArithmeticFunction.vonMangoldt (n + 1) : Complex) * g ((n + 1 : Nat) : ZMod q)) -
        ((a + k : Nat) : Complex) * rho) <= _
    rw [sum_range_primeWeight_eq_Icc, hCenter]
    exact hSrc.trans (lpfPhaseAllowance_mono A q (a + k) (a + N) hA.le
      (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) (by omega) (Nat.add_le_add_left hk a))
  have hPrefix (k : Nat) (hk : k <= N) :
      norm (Finset.sum (Finset.range k) (fun i => F (a + i) - rho)) <= 2 * B := by
    have hIdentity : Finset.sum (Finset.range k) (fun i => F (a + i) - rho) =
        (Finset.sum (Finset.range (a + k)) F - ((a + k : Nat) : Complex) * rho) -
        (Finset.sum (Finset.range a) F - (a : Complex) * rho) := by
      exact sum_range_shift_center F rho a k
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

end PrimeFactorOscillations.LPF
