/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeSignedCharacter
import PrimeFactorOscillations.Helpers.NativePrimeSignedCycleKernel

/-! # Full physical signed native character moments

All coefficients and finite row supports remain fixed before the independent
field-prime scale. The complete product numerator keeps its modulus and sign.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter IntegerQuadraticCharacter
open FiniteFieldIntegerWindowTransfer

def nativeSignedRowMoment (A B : Finset (Prod Nat Nat)) (Y X : Nat) : Real :=
  ((Finset.Ico Y X).filter Nat.Prime).sum (fun ell =>
    (1 / (ell : Real)) *
      (A.prod (fun e => (numeratorKernel (nativeSignedLowerCoefficient e) ell).re) *
        B.prod (fun e => (numeratorKernel (nativeSignedUpperCoefficient e) ell).re)))

theorem real_kernel_finset_product {I : Type*} (S : Finset I) (f : I -> Int)
    (ell : Nat) (hodd : Odd ell) :
    (numeratorKernel (S.prod f) ell).re =
      S.prod (fun i => (numeratorKernel (f i) ell).re) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [numeratorKernel, hodd]
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi, real_kernel_mul, ih, Finset.prod_insert hi]

theorem native_trace_eq_signed_rows (p q ell : Nat) (hpq : p < q) :
    nativeTrace p (q - p) ell =
      (numeratorKernel (nativeSignedLowerCoefficient (p, q)) ell).re +
        (numeratorKernel (nativeSignedUpperCoefficient (p, q)) ell).re := by
  have hq : p + (q - p) = q := Nat.add_sub_of_le hpq.le
  have hl : -(((q - p : Nat) : Int) * (p : Int)) =
      nativeSignedLowerCoefficient (p, q) := by
    simp only [nativeSignedLowerCoefficient, Nat.cast_mul]
    ring
  have hu : ((q - p : Nat) : Int) * ((p + (q - p) : Nat) : Int) =
      nativeSignedUpperCoefficient (p, q) := by
    rw [hq]
    simp only [nativeSignedUpperCoefficient, Nat.cast_mul]
    ring
  unfold nativeTrace
  rw [hl, hu]

theorem native_signed_row_moment_eq_correlation (A B : Finset (Prod Nat Nat))
    (Y X : Nat) (hY : 2 < Y) :
    nativeSignedRowMoment A B Y X = primeCorrelation (nativeSignedRowProduct A B) Y X := by
  unfold nativeSignedRowMoment primeCorrelation
  apply Finset.sum_congr rfl
  intro ell hell
  have hh := Finset.mem_filter.mp hell
  have hband := Finset.mem_Ico.mp hh.1
  have hodd : Odd ell := hh.2.odd_of_ne_two (by omega)
  rw [nativeSignedRowProduct, real_kernel_mul,
    real_kernel_finset_product A nativeSignedLowerCoefficient ell hodd,
    real_kernel_finset_product B nativeSignedUpperCoefficient ell hodd]

theorem native_prime_band_ratio_tendsto_of_centered (F : Nat -> Real) (c : Real)
    (hlim : Tendsto (fun U : Nat => F U - c *
      reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
        atTop (nhds 0)) :
    Tendsto (fun U : Nat => F U /
      reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
        atTop (nhds c) := by
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  let eta : Real := eps * Real.log 2 / 4
  have heta : 0 < eta := by dsimp [eta]; positivity
  have he := Metric.tendsto_nhds.mp hlim eta heta
  have hm := precise_core_tendsto_atTop.eventually eventually_reciprocal_square_band_positive
  filter_upwards [he, hm] with U hsmall hMass
  let M : Real := reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1)
  have hM : 0 < M := (show 0 < Real.log 2 / 2 by positivity).trans_le hMass
  have hid : F U / M - c = (F U - c * M) / M := by
    field_simp [ne_of_gt hM]
  change dist (F U / M) c < eps
  rw [Real.dist_eq, hid, abs_div, abs_of_pos hM]
  have hsmall' : abs (F U - c * M) < eta := by
    simpa only [Real.dist_eq, sub_zero] using hsmall
  have hscale := mul_le_mul_of_nonneg_left hMass heps.le
  have hpos : 0 < eps * Real.log 2 := mul_pos heps (by positivity)
  dsimp only [eta] at hsmall'
  have hbound : abs (F U - c * M) < eps * M := by
    linarith only [hsmall', hscale, hpos]
  have hdiv := div_lt_div_of_pos_right hbound hM
  have hcancel : eps * M / M = eps := by field_simp [ne_of_gt hM]
  rwa [hcancel] at hdiv

theorem native_signed_cycle_moment_centered_tendsto_zero (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (hind : nativePrimeVertexGapIndependent P) (A B : Finset (Prod Nat Nat))
    (hA : A <= nativePrimeVertexEdges P) (hB : B <= nativePrimeVertexEdges P) :
    Tendsto (fun U : Nat =>
      nativeSignedRowMoment A B (preciseCore U + 1) (preciseCore U * preciseCore U + 1) -
        (if And (A = B) (And (forall p : Nat, Membership.mem P p ->
          nativePrimeVertexCycleDegree A p % 2 = 0) (A.card % 2 = 0))
          then (1 : Real) else 0) *
            reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds 0) := by
  classical
  have hpos : 0 < A.prod (fun e => e.1 * (e.2 - e.1)) *
      B.prod (fun e => e.2 * (e.2 - e.1)) := by
    rw [native_gap_row_product_powers P A B hA hB]
    apply Finset.prod_pos
    intro x hx
    exact pow_pos (native_gap_basis_value_positive P hP x hx) _
  have hnz : Not (nativeSignedRowProduct A B = 0) := by
    rw [native_signed_row_product_factorization]
    apply mul_ne_zero
    . exact pow_ne_zero _ (by decide : Not ((-1 : Int) = 0))
    . exact_mod_cast (Nat.ne_of_gt hpos)
  have hlim := prime_correlation_centered_int_square_tendsto_zero
    (nativeSignedRowProduct A B) hnz
  have htail := precise_core_tendsto_atTop.eventually_ge_atTop 3
  have hresponse : Tendsto (fun U : Nat =>
      primeCorrelation (nativeSignedRowProduct A B) (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) -
        (if And (A = B) (And (forall p : Nat, Membership.mem P p ->
          nativePrimeVertexCycleDegree A p % 2 = 0) (A.card % 2 = 0))
          then (1 : Real) else 0) *
            reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds 0) := by
    simpa only [native_signed_row_product_isSquare_iff P hP hind A B hA hB] using hlim
  apply hresponse.congr'
  filter_upwards [htail] with U hU
  rw [native_signed_row_moment_eq_correlation A B _ _ (by omega)]

theorem native_signed_cycle_moment_ratio_tendsto (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (hind : nativePrimeVertexGapIndependent P) (A B : Finset (Prod Nat Nat))
    (hA : A <= nativePrimeVertexEdges P) (hB : B <= nativePrimeVertexEdges P) :
    Tendsto (fun U : Nat =>
      nativeSignedRowMoment A B (preciseCore U + 1) (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (if And (A = B) (And (forall p : Nat, Membership.mem P p ->
        nativePrimeVertexCycleDegree A p % 2 = 0) (A.card % 2 = 0))
          then (1 : Real) else 0)) := by
  classical
  exact native_prime_band_ratio_tendsto_of_centered _ _
    (native_signed_cycle_moment_centered_tendsto_zero P hP hind A B hA hB)

end PrimeFactorOscillations.FiniteFieldIntegerSignature
