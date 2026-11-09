/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimeCountingLocation
import PrimeFactorOscillations.Helpers.QRHPrimeSquareSpectrum

/-! # Fixed-coordinate prime sampling limits

The existing prime-counting theorem normalizes the complete finite signed
comparison. Every limit is taken with the finite coordinate set fixed, and
the eventual cutoff is uniform over all signed real vertex weights.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
open Filter Asymptotics
namespace PrimeFactorOscillations.QRH

private theorem primesBelow_card_eq_primeCounting (X : Nat) :
    (Nat.primesBelow (X + 1)).card = Nat.primeCounting X := by
  simp only [Nat.primesBelow, Nat.primeCounting, Nat.primeCounting',
    Nat.count_eq_card_filter_range]

private theorem oddPrimeVertices_card_add_one (X : Nat) (hX : 2 <= X) :
    (oddPrimeVertices X).card + 1 = Nat.primeCounting X := by
  have h2 : Membership.mem (Nat.primesBelow (X + 1)) 2 :=
    Nat.mem_primesBelow.mpr (And.intro (by omega) Nat.prime_two)
  calc
    _ = (Nat.primesBelow (X + 1)).card := Finset.card_erase_add_one h2
    _ = _ := primesBelow_card_eq_primeCounting X

private theorem oddPrimeVertices_card_pos (X : Nat) (hX : 3 <= X) :
    0 < (oddPrimeVertices X).card := by
  apply Finset.card_pos.mpr
  refine Exists.intro 3 ?_
  apply Finset.mem_erase.mpr
  exact And.intro (by decide)
    (Nat.mem_primesBelow.mpr (And.intro (by omega) Nat.prime_three))

private theorem log_pow_div_rpow_tendsto (k : Nat) {u : Real} (hu : 0 < u) :
    Tendsto (fun x : Real => Real.log x ^ (k + 1) / x ^ u)
      atTop (nhds (0 : Real)) := by
  have hk : (0 : Real) < (k : Real) + 1 := by positivity
  have h := (isLittleO_log_rpow_atTop (div_pos hu hk)).pow
    (n := k + 1) (by omega)
  have heq : Filter.EventuallyEq atTop
      (fun x : Real => (x ^ (u / ((k : Real) + 1))) ^ (k + 1))
      (fun x : Real => x ^ u) := by
    filter_upwards [eventually_gt_atTop (0 : Real)] with x hx
    rw [<- Real.rpow_natCast, <- Real.rpow_mul hx.le]
    congr 1
    push_cast
    field_simp [ne_of_gt hk]
  exact (h.congr' Filter.EventuallyEq.rfl heq).tendsto_div_nhds_zero

theorem tendsto_oddPrimeVertices_count_div_mainTerm :
    Tendsto (fun X : Nat => ((oddPrimeVertices X).card : Real) /
      ((X : Real) / Real.log (X : Real))) atTop (nhds (1 : Real)) := by
  have hrecip := (isLittleO_log_rpow_atTop
    (show (0 : Real) < 1 by norm_num)).tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun X : Nat => (X : Real)) atTop atTop)
  have hrecip' : Tendsto (fun X : Nat => 1 /
      ((X : Real) / Real.log (X : Real))) atTop (nhds (0 : Real)) := by
    simpa only [Real.rpow_one, one_div_div, Function.comp_def] using hrecip
  have hsub : Tendsto (fun X : Nat =>
      (Nat.primeCounting X : Real) / ((X : Real) / Real.log (X : Real)) -
        1 / ((X : Real) / Real.log (X : Real))) atTop (nhds (1 : Real)) := by
    simpa only [sub_zero] using
      PrimeFactorOscillations.tendsto_primeCounting_div_mainTerm.sub hrecip'
  apply hsub.congr'
  filter_upwards [eventually_ge_atTop (2 : Nat)] with X hX
  have hcard : (Nat.primeCounting X : Real) =
      ((oddPrimeVertices X).card : Real) + 1 := by
    exact_mod_cast (oddPrimeVertices_card_add_one X hX).symm
  rw [hcard]
  ring1

private theorem tendsto_rpow_logshift_pow_div_main (r A : Real)
    (hr : r < 1) (hA : 0 <= A) (k : Nat) :
    Tendsto (fun x : Real => x ^ r * (A + Real.log (x + 2)) ^ k /
      (x / Real.log x)) atTop (nhds (0 : Real)) := by
  let B := A + Real.log 2 + 1
  have hlog2 : 0 <= Real.log (2 : Real) := Real.log_nonneg (by norm_num)
  have hB : 0 <= B := by dsimp only [B]; positivity
  have hsmall := (log_pow_div_rpow_tendsto k (sub_pos.mpr hr)).const_mul (B ^ k)
  apply squeeze_zero' ?_ ?_ (by simpa only [mul_zero] using hsmall)
  { filter_upwards [eventually_ge_atTop (2 : Real)] with x hx
    have hx0 : 0 < x := by linarith
    have hlog : 0 < Real.log x := Real.log_pos (by linarith)
    have hshift : 0 <= Real.log (x + 2) := Real.log_nonneg (by linarith)
    exact div_nonneg
      (mul_nonneg (Real.rpow_nonneg hx0.le _) (pow_nonneg (add_nonneg hA hshift) k))
      (div_nonneg hx0.le hlog.le) }
  { have hLogEventually : Filter.Eventually
        (fun x : Real => 1 <= Real.log x) atTop :=
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : Real))
    filter_upwards [eventually_ge_atTop (2 : Real), hLogEventually] with x hx hlogOne
    have hx0 : 0 < x := by linarith
    have hlog : 0 < Real.log x := by linarith
    have hshift0 : 0 <= Real.log (x + 2) := Real.log_nonneg (by linarith)
    have hL0 : 0 <= A + Real.log (x + 2) := add_nonneg hA hshift0
    have hShift : Real.log (x + 2) <= Real.log 2 + Real.log x := by
      calc
        _ <= Real.log (2 * x) := Real.log_le_log (by linarith) (by linarith)
        _ = _ := Real.log_mul (by norm_num) hx0.ne'
    have hBound : A + Real.log (x + 2) <= B * Real.log x := by
      have h := mul_nonneg (add_nonneg hA hlog2) (sub_nonneg.mpr hlogOne)
      dsimp only [B]
      nlinarith only [hShift, h]
    have hPow : (A + Real.log (x + 2)) ^ k <= (B * Real.log x) ^ k := by
      gcongr
    have hNum : (A + Real.log (x + 2)) ^ k * Real.log x <=
        B ^ k * Real.log x ^ (k + 1) := by
      calc
        _ <= (B * Real.log x) ^ k * Real.log x :=
          mul_le_mul_of_nonneg_right hPow hlog.le
        _ = _ := by rw [mul_pow, pow_succ]; ring1
    have hPower : x ^ r * x ^ (1 - r) = x := by
      rw [<- Real.rpow_add hx0]
      have hExp : r + (1 - r) = 1 := by ring1
      rw [hExp, Real.rpow_one]
    have hIdentity : x ^ r * (A + Real.log (x + 2)) ^ k / (x / Real.log x) =
        (A + Real.log (x + 2)) ^ k * Real.log x / x ^ (1 - r) := by
      have hEq := congrArg
        (fun z : Real => z * (A + Real.log (x + 2)) ^ k) hPower
      field_simp [hx0.ne', hlog.ne', (Real.rpow_pos_of_pos hx0 (1 - r)).ne']
      nlinarith only [hEq]
    rw [hIdentity]
    simpa only [mul_div_assoc] using
      div_le_div_of_nonneg_right hNum (Real.rpow_nonneg hx0.le (1 - r)) }

theorem tendsto_rpow_logshift_pow_div_oddPrimeCount (r A : Real)
    (hr : r < 1) (hA : 0 <= A) (k : Nat) :
    Tendsto (fun X : Nat => (X : Real) ^ r *
      (A + Real.log ((X : Real) + 2)) ^ k /
      ((oddPrimeVertices X).card : Real)) atTop (nhds (0 : Real)) := by
  have hmain := (tendsto_rpow_logshift_pow_div_main r A hr hA k).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun X : Nat => (X : Real)) atTop atTop)
  have hdiv : Tendsto (fun X : Nat =>
      ((X : Real) ^ r * (A + Real.log ((X : Real) + 2)) ^ k /
        ((X : Real) / Real.log (X : Real))) /
      (((oddPrimeVertices X).card : Real) /
        ((X : Real) / Real.log (X : Real)))) atTop (nhds (0 : Real)) := by
    convert hmain.div tendsto_oddPrimeVertices_count_div_mainTerm
      (by norm_num) using 1
    { ext X
      rfl }
    { norm_num }
  apply hdiv.congr'
  filter_upwards [eventually_ge_atTop (3 : Nat)] with X hX
  have hx0 : (0 : Real) < X := by exact_mod_cast (show 0 < X by omega)
  have hlog : Not (Real.log (X : Real) = 0) :=
    (Real.log_pos (by exact_mod_cast (show 1 < X by omega))).ne'
  have hn : Not (((oddPrimeVertices X).card : Real) = 0) := by
    exact_mod_cast Nat.ne_of_gt (oddPrimeVertices_card_pos X hX)
  field_simp [hx0.ne', hlog, hn]

/-- The fixed finite cutoff comparison, uniform over all signed real weights.
The finite coordinate set precedes the eventual cutoff; no simultaneous
growing-coordinate limit is asserted. -/
theorem eventually_prime_square_spectral_gap (S : Finset Nat)
    (hS : forall p, Membership.mem S p -> Nat.Prime p)
    (h3 : forall p, Membership.mem S p -> 3 <= p)
    {eps : Real} (heps : 0 < eps) :
    Filter.Eventually (fun X : Nat => forall f : Nat -> Real,
      let D := Nat.primeSquareUnitDensity (fun p : S => p.val)
      let n : Real := ((oddPrimeVertices X).card : Real)
      let a := (oddPrimeVertices X).sum f / n
      let b := (oddPrimeVertices X).sum (fun q => primeResidueSign q * f q) / n
      let e := (oddPrimeVertices X).sum (fun q => (f q) ^ 2) / n
      abs (Finset.kernelBilinear (oddPrimeVertices X) (primeSquareCutoffKernel S) f f /
        n ^ 2 - D * (a ^ 2 - b ^ 2)) <=
        D / 5 * (e - a ^ 2 - b ^ 2) + eps * e) atTop := by
  choose C hC hBound using exists_finite_prime_square_spectral_gap
  let N := (insert 2 S : Finset Nat).prod (fun p => p ^ 2)
  let M := (insert 2 S : Finset Nat).prod (fun p => p * (p - 1))
  let D := Nat.primeSquareUnitDensity (fun p : S => p.val)
  let A : Real := 1 + Real.log (N : Real)
  let n (X : Nat) : Real := ((oddPrimeVertices X).card : Real)
  let delta (X : Nat) := (1 + (M : Real) *
    (C * (X : Real) ^ (7 / 8 : Real) *
      (A + Real.log ((X : Real) + 2)) ^ 2)) / n X
  let tau (X : Nat) := Real.sqrt ((S.card : Real) / n X)
  have hN : 0 < N := by
    apply Finset.prod_pos
    intro p hp
    cases Finset.mem_insert.mp hp with
    | inl h => rw [h]; norm_num
    | inr h => exact pow_pos (hS p h).pos 2
  have hA : 0 <= A := add_nonneg (by norm_num)
    (Real.log_nonneg (by exact_mod_cast hN))
  have hInv : Tendsto (fun X : Nat => 1 / n X) atTop (nhds (0 : Real)) := by
    simpa only [Real.rpow_zero, pow_zero, one_mul, n] using
      tendsto_rpow_logshift_pow_div_oddPrimeCount 0 0 (by norm_num) (by norm_num) 0
  have hErr : Tendsto (fun X : Nat => C * (X : Real) ^ (7 / 8 : Real) *
      (A + Real.log ((X : Real) + 2)) ^ 2 / n X) atTop (nhds (0 : Real)) := by
    have h := (tendsto_rpow_logshift_pow_div_oddPrimeCount (7 / 8) A
      (by norm_num) hA 2).const_mul C
    apply (show Tendsto (fun X : Nat => C * ((X : Real) ^ (7 / 8 : Real) *
        (A + Real.log ((X : Real) + 2)) ^ 2 / ((oddPrimeVertices X).card : Real)))
        atTop (nhds (0 : Real)) from by simpa only [mul_zero] using h).congr'
    filter_upwards [] with X
    dsimp only [n]
    ring1
  have hDelta : Tendsto delta atTop (nhds (0 : Real)) := by
    have h := hInv.add (hErr.const_mul (M : Real))
    apply (show Tendsto (fun X : Nat => 1 / n X +
        (M : Real) * (C * (X : Real) ^ (7 / 8 : Real) *
          (A + Real.log ((X : Real) + 2)) ^ 2 / n X))
        atTop (nhds (0 : Real)) from by simpa only [mul_zero, zero_add] using h).congr'
    filter_upwards [] with X
    dsimp only [delta]
    ring1
  have hRatio : Tendsto (fun X : Nat => (S.card : Real) / n X)
      atTop (nhds (0 : Real)) := by
    apply (show Tendsto (fun X : Nat => (S.card : Real) * (1 / n X))
        atTop (nhds (0 : Real)) from by
      simpa only [mul_zero] using hInv.const_mul (S.card : Real)).congr'
    filter_upwards [] with X
    ring1
  have hTau : Tendsto tau atTop (nhds (0 : Real)) := by
    simpa only [tau, Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto (0 : Real)).comp hRatio
  have hEta : Tendsto (fun X : Nat =>
      D * delta X / 5 + (4 * D + 2) * tau X + tau X ^ 2)
      atTop (nhds (0 : Real)) := by
    simpa using
      (((hDelta.const_mul D).div_const 5).add
        (hTau.const_mul (4 * D + 2))).add (hTau.pow 2)
  have hSmallError := hEta.eventually (gt_mem_nhds heps)
  filter_upwards [eventually_ge_atTop (3 : Nat), hSmallError] with X hX hError
  intro f
  have hnNat := oddPrimeVertices_card_pos X hX
  have hn : 0 < n X := by
    dsimp only [n]
    exact_mod_cast hnNat
  have hSparse : (S.card : Real) <= tau X ^ 2 * n X := by
    have hRatio0 : 0 <= (S.card : Real) / n X :=
      div_nonneg (Nat.cast_nonneg _) hn.le
    have heq : tau X ^ 2 * n X = (S.card : Real) := by
      dsimp only [tau]
      rw [Real.sq_sqrt hRatio0]
      field_simp [ne_of_gt hn]
    exact le_of_eq heq.symm
  have hBase := hBound S hS h3 X (tau X) hnNat (Real.sqrt_nonneg _) hSparse f
  let e := (oddPrimeVertices X).sum (fun q => (f q) ^ 2) / n X
  have he : 0 <= e :=
    div_nonneg (Finset.sum_nonneg (fun q hq => sq_nonneg (f q))) hn.le
  have hErrorMul : (D * delta X / 5 + (4 * D + 2) * tau X + tau X ^ 2) * e <=
      eps * e := mul_le_mul_of_nonneg_right hError.le he
  dsimp only at hBase
  dsimp only
  dsimp only [D, delta, N, M, A, n, tau, e] at hErrorMul
  dsimp only [tau, n] at hBase
  linarith only [hBase, hErrorMul]

end PrimeFactorOscillations.QRH
