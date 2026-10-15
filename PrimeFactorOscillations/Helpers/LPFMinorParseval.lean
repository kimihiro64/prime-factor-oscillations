/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFWarmCutoffs

/-!
# Complete fixed-interval minor-frequency mean square

The actual von Mangoldt transform, including every prime power, has exact
Parseval energy under input non-wrap. The minor mask retains the whole
squared transform. A uniform constant precedes every scale, grid, interval
and target set; the grid size cancels from the complete bound. This does
not assert a mean-square theorem for target-dependent input windows.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem lpf_grid_interval_weight_energy_bound {N : Nat} [NeZero N]
    (s L H : Nat) (hH : 1 <= H) (hTop : s + L <= H) (hInput : s + L < N) :
    Finset.sum Finset.univ (fun x : ZMod N => Complex.normSq (lpfGridIntervalWeight N s L x)) <=
      (N : Real) * (L : Real) * Real.log (H : Real) ^ 2 := by
  have hInj : Set.InjOn (fun n : Nat => (n : ZMod N)) ((lpfGridIntervalInputs s L) : Set Nat) := by
    intro n hn m hm hEq
    have hnN := (lpfGridIntervalInputs_le s L n hn).trans_lt hInput
    have hmN := (lpfGridIntervalInputs_le s L m hm).trans_lt hInput
    have h := congrArg (fun x : ZMod N => x.val) hEq
    simpa only [ZMod.val_natCast_of_lt hnN, ZMod.val_natCast_of_lt hmN] using h
  have hLog : 0 <= Real.log (H : Real) := Real.log_nonneg (by exact_mod_cast hH)
  have hWeight (n : Nat) (hn : Membership.mem (lpfGridIntervalInputs s L) n) :
      Complex.normSq (ArithmeticFunction.vonMangoldt n : Complex) <= Real.log (H : Real) ^ 2 := by
    have hnH := (lpfGridIntervalInputs_le s L n hn).trans hTop
    have hnPos : 0 < n := by
      choose i hi hEq using Finset.mem_image.mp hn
      omega
    have hnPosR : (0 : Real) < (n : Real) := by exact_mod_cast hnPos
    have hLambda : ArithmeticFunction.vonMangoldt n <= Real.log (H : Real) :=
      ArithmeticFunction.vonMangoldt_le_log.trans
        (Real.log_le_log hnPosR (by exact_mod_cast hnH))
    have hNonneg : 0 <= ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    have hSq := mul_le_mul hLambda hLambda hNonneg hLog
    simpa only [Complex.normSq_ofReal, pow_two] using hSq
  have hSum : Finset.sum (lpfGridIntervalInputs s L)
      (fun n => Complex.normSq (ArithmeticFunction.vonMangoldt n : Complex)) <=
      (L : Real) * Real.log (H : Real) ^ 2 := by
    calc
      _ <= Finset.sum (lpfGridIntervalInputs s L) (fun _ => Real.log (H : Real) ^ 2) :=
        Finset.sum_le_sum hWeight
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, lpfGridIntervalInputs_card]
  simp_rw [lpfGridIntervalWeight_eq_transform]
  rw [lpfFiniteTransform_parseval (lpfGridIntervalInputs s L) (fun n => (n : ZMod N))
    (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) hInj]
  calc
    _ <= (N : Real) * ((L : Real) * Real.log (H : Real) ^ 2) :=
      mul_le_mul_of_nonneg_left hSum (by positivity)
    _ = _ := by ring

theorem lpf_cyclic_minor_meanSquare_of_pointwise {N : Nat} [NeZero N]
    (S : ZMod N -> Complex) (G T : Finset (ZMod N)) (Q : Real) (hQ : 0 <= Q)
    (hBound : forall x, Not (Membership.mem G x) -> norm (S x) ^ 2 <= Q) :
    Finset.sum T (fun t => Complex.normSq (lpfCyclicInverse
      (fun x => if Membership.mem G x then 0 else S x ^ 2) t)) <=
      (N : Real) ^ (-1 : Int) * Q * Finset.sum Finset.univ (fun x => Complex.normSq (S x)) := by
  classical
  have hPoint (x : ZMod N) :
      Complex.normSq (if Membership.mem G x then 0 else S x ^ 2) <= Q * Complex.normSq (S x) := by
    by_cases hMajor : Membership.mem G x
    case pos =>
      rw [ite_eq_left hMajor, Complex.normSq_zero]
      exact mul_nonneg hQ (Complex.normSq_nonneg _)
    case neg =>
      rw [ite_eq_right hMajor, pow_two, Complex.normSq_mul]
      have h := hBound x hMajor
      rw [Complex.sq_norm] at h
      exact mul_le_mul_of_nonneg_right h (Complex.normSq_nonneg _)
  calc
    _ <= (N : Real) ^ (-1 : Int) * Finset.sum Finset.univ
        (fun x => Complex.normSq (if Membership.mem G x then 0 else S x ^ 2)) :=
      lpfCyclicInverse_bessel _ T
    _ <= (N : Real) ^ (-1 : Int) * Finset.sum Finset.univ
        (fun x => Q * Complex.normSq (S x)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun x _ => hPoint x)) (by positivity)
    _ = _ := by rw [<- Finset.mul_sum]; ring

theorem lpf_grid_interval_minor_meanSquare_of_pointwise {N : Nat} [NeZero N]
    (s L H : Nat) (hH : 1 <= H) (hTop : s + L <= H) (hInput : s + L < N)
    (G T : Finset (ZMod N)) (Q : Real) (hQ : 0 <= Q)
    (hBound : forall x, Not (Membership.mem G x) -> norm (lpfGridIntervalWeight N s L x) ^ 2 <= Q) :
    Finset.sum T (fun t => Complex.normSq (lpfCyclicInverse
      (fun x => if Membership.mem G x then 0 else lpfGridIntervalWeight N s L x ^ 2) t)) <=
      Q * (L : Real) * Real.log (H : Real) ^ 2 := by
  have hFirst := lpf_cyclic_minor_meanSquare_of_pointwise
    (fun x => lpfGridIntervalWeight N s L x) G T Q hQ hBound
  have hEnergy := lpf_grid_interval_weight_energy_bound s L H hH hTop hInput
  have hNPos : (0 : Real) < (N : Real) := by exact_mod_cast (NeZero.pos N)
  calc
    _ <= _ := hFirst
    _ <= (N : Real) ^ (-1 : Int) * Q *
        ((N : Real) * (L : Real) * Real.log (H : Real) ^ 2) :=
      mul_le_mul_of_nonneg_left hEnergy (by positivity)
    _ = _ := by rw [zpow_neg_one]; field_simp

theorem lpf_grid_minor_meanSquare_bound :
    exists C : Real, And (0 < C)
      (forall {N : Nat} [NeZero N] (M P s L : Nat),
        2 ^ 18 <= M -> 0 < P ->
        (P : Real) <= (M : Real) ^ ((1 : Real) / 40) ->
        Dvd.dvd M N -> (forall q, 0 < q -> q <= P -> Dvd.dvd q N) ->
        (M : Real) / 4 <= (s : Real) -> s + L <= 2 * M -> L <= M -> s + L < N ->
        forall T : Finset (ZMod N),
        Finset.sum T (fun t => Complex.normSq (lpfCyclicInverse
          (fun x => if Membership.mem (lpfRationalGrid N P ((N / M) * P)) x then 0
            else lpfGridIntervalWeight N s L x ^ 2) t)) <=
          C * (M : Real) ^ ((1 : Real) / 160) *
            ((M : Real) ^ 3 / (P : Real) + (M : Real) ^ (13 / 5 : Real)) *
            (1 + Real.log (2 * (M : Real))) ^ 9) := by
  classical
  choose C hC hPoint using lpf_grid_minor_uniform_squared_bound
  refine Exists.intro C (And.intro hC ?_)
  intro N instN M P s L hM hP hPPower hDivM hDiv hStart hTop hL hInput T
  have hOne : 1 <= M := (by decide : 1 <= 2 ^ 18).trans hM
  have hMPos : (0 : Real) < (M : Real) := by exact_mod_cast (by omega : 0 < M)
  have hMR : (1 : Real) <= (M : Real) := by exact_mod_cast hOne
  have hLog : 0 <= Real.log (2 * (M : Real)) := Real.log_nonneg (by linarith only [hMR])
  let ell : Real := 1 + Real.log (2 * (M : Real))
  let Q : Real := C * (M : Real) ^ ((1 : Real) / 160) *
    ((M : Real) ^ 2 / (P : Real) + (M : Real) ^ (8 / 5 : Real)) * ell ^ 7
  have hQ : 0 <= Q := by dsimp [Q, ell]; positivity
  have hAll (x : ZMod N)
      (hx : Not (Membership.mem (lpfRationalGrid N P ((N / M) * P)) x)) :
      norm (lpfGridIntervalWeight N s L x) ^ 2 <= Q := by
    have hxInt : Not (Membership.mem (lpfRationalGrid N P ((N / M) * P)) ((x.val : Int) : ZMod N)) := by
      simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hx
    have h := hPoint (N := N) M P s L hM hP hPPower hDivM hDiv hStart hTop (x.val : Int) hxInt
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using h
  have hMean := lpf_grid_interval_minor_meanSquare_of_pointwise s L (2 * M)
    (by omega) hTop hInput (lpfRationalGrid N P ((N / M) * P)) T Q hQ hAll
  have hHCast : ((2 * M : Nat) : Real) = 2 * (M : Real) := by push_cast; rfl
  rw [hHCast] at hMean
  have hLogSq : Real.log (2 * (M : Real)) ^ 2 <= ell ^ 2 := by
    have hLe : Real.log (2 * (M : Real)) <= ell := by dsimp [ell]; linarith only
    simpa only [pow_two] using mul_le_mul hLe hLe hLog (by dsimp [ell]; positivity)
  have hPow : (M : Real) ^ (8 / 5 : Real) * (M : Real) = (M : Real) ^ (13 / 5 : Real) := by
    calc
      _ = (M : Real) ^ (8 / 5 : Real) * (M : Real) ^ (1 : Real) := by rw [Real.rpow_one]
      _ = (M : Real) ^ ((8 / 5 : Real) + 1) := (Real.rpow_add hMPos _ _).symm
      _ = _ := by norm_num
  calc
    _ <= Q * (L : Real) * Real.log (2 * (M : Real)) ^ 2 := hMean
    _ <= Q * (M : Real) * ell ^ 2 := by gcongr
    _ = C * (M : Real) ^ ((1 : Real) / 160) *
        ((M : Real) ^ 3 / (P : Real) + (M : Real) ^ (8 / 5 : Real) * (M : Real)) * ell ^ 9 := by
      dsimp [Q]
      ring
    _ = _ := by rw [hPow]

end PrimeFactorOscillations.LPF
