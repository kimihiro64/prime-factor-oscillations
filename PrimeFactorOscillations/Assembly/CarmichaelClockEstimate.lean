/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelAscentEstimate

/-!
# Full signed native clock estimate

The existing unconditional coefficient comparison is applied to the actual
native profile packet. Positive and negative Nicolas terms remain coupled;
only the proved profile remainder and finite-grid error are bounded.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.CarmichaelAscentEstimate

open Filter PrimeFactorUnimodality Robin1984

def sampledClock (i : Nat) : Real :=
  Real.eulerMascheroniConstant +
    Real.log (Real.log (Chebyshev.theta ((primeAt i - 1 : Nat) : Real)))

def sampledNicolas (i : Nat) : Real :=
  nicolasLogMertensOscillation ((primeAt i - 1 : Nat) : Real)

def clockMain (H : Nat) (m : Nat -> Nat)
    (a : (X : Nat) -> Fin (m X) -> Nat) (q : Nat -> Nat)
    [forall X, NeZero (q X)] (S : Nat -> Finset Nat.Primes) (X : Nat) : Real :=
  Finset.univ.sum (fun i : Fin (m X) =>
    carmichaelPrimeWeight (q X) (S X) (primeAt (a X i)) *
      ((localTiltRank H X : Real) / (sampledClock (a X i)) ^ 2) *
        sampledNicolas (a X i))

def clockError (H : Nat) (m : Nat -> Nat)
    (a : (X : Nat) -> Fin (m X) -> Nat) (q : Nat -> Nat)
    [forall X, NeZero (q X)] (S : Nat -> Finset Nat.Primes) (K : Real) (X : Nat) : Real :=
  K * Finset.univ.sum (fun i : Fin (m X) =>
    carmichaelPrimeWeight (q X) (S X) (primeAt (a X i)) *
      (abs (sampledNicolas (a X i)) / (sampledClock (a X i)) ^ 2 +
        1 / ((localTiltRank H X : Real) * ((primeAt (a X i) - 1 : Nat) : Real))))

theorem exists_eventually_signed_clock_error
    (H : Nat) (m : Nat -> Nat)
    (a : (X : Nat) -> Fin (m X) -> Nat) (hs : LocalAscentSampling H m a)
    (q : Nat -> Nat) [forall X, NeZero (q X)] (S : Nat -> Finset Nat.Primes)
    (hDiv : forall X, forall p : S X,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod (q X)))))
    (hOdd : forall X, forall p : S X, Not ((p.val : Nat) = 2)) :
    exists K : Real, 0 <= K /\ Filter.Eventually (fun X : Nat =>
      abs (profileExcess H m a q S X - clockMain H m a q S X) <=
        clockError H m a q S K X) atTop := by
  let alpha : Real := (H : Real) + 2
  have ha : 0 < alpha := by dsimp [alpha]; positivity
  choose r0 K hr0 hK hApprox using
    exists_eventually_densityRatio_real_thetaClock_linearization (2 * alpha) (by positivity)
  have hCast : Tendsto (fun n : Nat => (n : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hBands := hCast.eventually (eventually_primeProfile_fixed_window_bands alpha ha)
  choose Y hY using eventually_atTop.mp hApprox
  have hRank : Filter.Eventually (fun X : Nat => r0 <= localTiltRank H X) atTop := by
    have hLarge := tendsto_primeProfile_thetaClock_atTop.eventually_ge_atTop
      ((r0 : Real) / alpha)
    filter_upwards [hLarge] with X hX
    apply Nat.le_floor
    have hMul := mul_le_mul_of_nonneg_right hX ha.le
    have hCancel : (r0 : Real) / alpha * alpha = r0 := by field_simp [ha.ne']
    rw [hCancel] at hMul
    simpa only [mul_comm] using hMul
  refine Exists.intro K (And.intro hK ?_)
  filter_upwards [hs.2, hBands, hRank, hCast.eventually (eventually_ge_atTop Y),
    eventually_ge_atTop (1 : Nat)] with X hc hb hr hxY hx
  have hx1 : (1 : Real) <= X := by exact_mod_cast hx
  have hp : (X : Real) ^ (3 / 4 : Real) <= X := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx1
      (by norm_num : (3 / 4 : Real) <= 1)
  have hError (i : Fin (m X)) :
      abs (profileDifference H X (a X i) -
        ((localTiltRank H X : Real) / (sampledClock (a X i)) ^ 2) *
          sampledNicolas (a X i)) <=
      K * (abs (sampledNicolas (a X i)) / (sampledClock (a X i)) ^ 2 +
        1 / ((localTiltRank H X : Real) * ((primeAt (a X i) - 1 : Nat) : Real))) := by
    have hPair := hc.2 i
    let y : Real := ((primeAt (a X i) - 1 : Nat) : Real)
    have hy : (X : Real) <= y := hPair.2.2.1
    have hB := hb.2 y hy (by dsimp [y]; linarith [hPair.2.2.2])
    have hL := (hY y (hxY.trans hy)).2.2 (localTiltRank H X) hr hB.2.1
    have hCut : Nat.floor y + 1 = primeAt (a X i) := by
      dsimp [y]
      rw [Nat.floor_natCast, Nat.sub_add_cancel (prime_primeAt (a X i)).one_lt.le]
    rw [hCut] at hL
    exact hL.2.2
  have hW (i : Fin (m X)) :
      0 <= carmichaelPrimeWeight (q X) (S X) (primeAt (a X i)) :=
    carmichaelPrimeWeight_nonneg (q X) (S X) (hDiv X) (hOdd X) _
  unfold profileExcess clockMain clockError
  rw [<- Finset.sum_sub_distrib, Finset.mul_sum]
  calc
    _ <= Finset.univ.sum (fun i : Fin (m X) =>
        abs (carmichaelPrimeWeight (q X) (S X) (primeAt (a X i)) *
              profileDifference H X (a X i) -
          carmichaelPrimeWeight (q X) (S X) (primeAt (a X i)) *
            ((localTiltRank H X : Real) / (sampledClock (a X i)) ^ 2) *
              sampledNicolas (a X i))) := Finset.abs_sum_le_sum_abs _ _
    _ <= _ := by
      apply Finset.sum_le_sum
      intro i hi
      have hFactor :
          carmichaelPrimeWeight (q X) (S X) (primeAt (a X i)) *
              profileDifference H X (a X i) -
            carmichaelPrimeWeight (q X) (S X) (primeAt (a X i)) *
              ((localTiltRank H X : Real) / (sampledClock (a X i)) ^ 2) *
                sampledNicolas (a X i) =
          carmichaelPrimeWeight (q X) (S X) (primeAt (a X i)) *
            (profileDifference H X (a X i) -
              ((localTiltRank H X : Real) / (sampledClock (a X i)) ^ 2) *
                sampledNicolas (a X i)) := by ring
      rw [hFactor, abs_mul, abs_of_nonneg (hW i)]
      exact (mul_le_mul_of_nonneg_left (hError i) (hW i)).trans_eq (by ring)

def signedClockUpper (H : Nat) (m : Nat -> Nat)
    (a : (X : Nat) -> Fin (m X) -> Nat) (q : Nat -> Nat)
    [forall X, NeZero (q X)] (S : Nat -> Finset Nat.Primes) (K : Real) (X : Nat) : Real :=
  Finset.univ.sum (fun i : Fin (m X) =>
    carmichaelPrimeWeight (q X) (S X) (primeAt (a X i)) *
      (((if 0 <= sampledNicolas (a X i) then (localTiltRank H X : Real) + K
          else (localTiltRank H X : Real) - K) *
          sampledNicolas (a X i) / (sampledClock (a X i)) ^ 2) +
        K / ((localTiltRank H X : Real) * ((primeAt (a X i) - 1 : Nat) : Real))))

theorem exists_eventually_profile_signed_upper
    (H : Nat) (m : Nat -> Nat)
    (a : (X : Nat) -> Fin (m X) -> Nat) (hs : LocalAscentSampling H m a)
    (q : Nat -> Nat) [forall X, NeZero (q X)] (S : Nat -> Finset Nat.Primes)
    (hDiv : forall X, forall p : S X,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod (q X)))))
    (hOdd : forall X, forall p : S X, Not ((p.val : Nat) = 2)) :
    exists K : Real, 0 <= K /\ Filter.Eventually (fun X : Nat =>
      profileExcess H m a q S X <= signedClockUpper H m a q S K X) atTop := by
  choose K hK hError using exists_eventually_signed_clock_error H m a hs q S hDiv hOdd
  have hEq (X : Nat) :
      clockMain H m a q S X + clockError H m a q S K X =
        signedClockUpper H m a q S K X := by
    unfold clockMain clockError signedClockUpper
    rw [Finset.mul_sum, <- Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hF : 0 <= sampledNicolas (a X i)
    . rw [ite_eq_left hF, abs_of_nonneg hF]
      ring
    . rw [ite_eq_right hF, abs_of_neg (lt_of_not_ge hF)]
      ring
  refine Exists.intro K (And.intro hK ?_)
  filter_upwards [hError] with X hX
  have hUpper := (abs_le.mp hX).2
  rw [<- hEq]
  linarith

theorem exists_eventually_packet_signed_upper
    (H : Nat) (m : Nat -> Nat)
    (a : (X : Nat) -> Fin (m X) -> Nat) (hs : LocalAscentSampling H m a)
    (q : Nat -> Nat) [forall X, NeZero (q X)] (S : Nat -> Finset Nat.Primes)
    (hDiv : forall X, forall p : S X,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod (q X)))))
    (hOdd : forall X, forall p : S X, Not ((p.val : Nat) = 2)) :
    exists K : Real, 0 <= K /\ Filter.Eventually (fun X : Nat =>
      2 * K <= (localTiltRank H X : Real) /\
      CarmichaelAscentSpectrum.normalizedExcess H m a q S X <=
        (localTiltMesh X : Real) * signedClockUpper H m a q S K X +
          Finset.univ.sum (fun i : Fin (m X) =>
            carmichaelPrimeWeight (q X) (S X) (primeAt (a X i)))) atTop := by
  choose K hK hUpper using exists_eventually_profile_signed_upper H m a hs q S hDiv hOdd
  let alpha : Real := (H : Real) + 2
  have ha : 0 < alpha := by dsimp [alpha]; positivity
  have hRank : Filter.Eventually (fun X : Nat =>
      2 * K <= (localTiltRank H X : Real)) atTop := by
    have hLarge := tendsto_primeProfile_thetaClock_atTop.eventually_ge_atTop
      ((2 * K + 1) / alpha)
    filter_upwards [hLarge] with X hX
    have hMul := mul_le_mul_of_nonneg_right hX ha.le
    have hCancel : (2 * K + 1) / alpha * alpha = 2 * K + 1 := by
      field_simp [ha.ne']
    rw [hCancel] at hMul
    have hFloor := Nat.lt_floor_add_one
      (alpha * (Real.eulerMascheroniConstant +
        Real.log (Real.log (Chebyshev.theta (X : Real)))))
    change 2 * K <= (Nat.floor (alpha * (Real.eulerMascheroniConstant +
      Real.log (Real.log (Chebyshev.theta (X : Real))))) : Real)
    nlinarith only [hMul, hFloor]
  have hGrid := eventually_signed_profile_error H m a hs q S hDiv hOdd
  refine Exists.intro K (And.intro hK ?_)
  filter_upwards [hUpper, hGrid, hRank] with X hV hJ hr
  refine And.intro hr ?_
  have hOne := (abs_le.mp hJ).2
  have hTwo := mul_le_mul_of_nonneg_left hV
    (Nat.cast_nonneg (localTiltMesh X) : (0 : Real) <= localTiltMesh X)
  linarith

end PrimeFactorOscillations.CarmichaelAscentEstimate
