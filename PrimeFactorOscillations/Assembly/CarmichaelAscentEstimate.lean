/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelAscentSpectrum

/-!
# Signed native ascent estimate

The actual nonlinear probability profile is retained as the signed main term.
Only the finite-grid rounding remainder is bounded in absolute value.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.CarmichaelAscentEstimate

open Filter PrimeFactorUnimodality CarmichaelAscentSpectrum
open CarmichaelIntegralSpectrum CarmichaelPermutationKernel

def profileDifference (H X i : Nat) : Real :=
  (densityRatio (primesBelow (primeAt i)) (localTiltRank H X) : Real) -
    localTiltReference H X i

def profileExcess (H : Nat) (m : Nat -> Nat)
    (a : (X : Nat) -> Fin (m X) -> Nat) (q : Nat -> Nat)
    [forall X, NeZero (q X)] (S : Nat -> Finset Nat.Primes) (X : Nat) : Real :=
  Finset.univ.sum (fun i : Fin (m X) =>
    carmichaelPrimeWeight (q X) (S X) (primeAt (a X i)) *
      profileDifference H X (a X i))

theorem scaled_profile_eq_character_rows
    (H : Nat) (m : Nat -> Nat)
    (a : (X : Nat) -> Fin (m X) -> Nat) (q : Nat -> Nat)
    [forall X, NeZero (q X)] (S : Nat -> Finset Nat.Primes) (X : Nat)
    (hDiv : forall p : S X,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod (q X))))) :
    (normalization (G := Units (ZMod (q X))) (S X) : Complex) *
        (profileExcess H m a q S X : Complex) =
      Finset.univ.sum (fun chi : DirichletCharacter Complex (q X) =>
        (multiplicity (S X) chi : Complex) *
          Finset.univ.sum (fun i : Fin (m X) =>
            chi (primeAt (a X i) : ZMod (q X)) *
              (profileDifference H X (a X i) : Complex))) := by
  classical
  unfold profileExcess
  simp only [Complex.ofReal_sum, Complex.ofReal_mul]
  rw [Finset.mul_sum]
  calc
    _ = Finset.univ.sum (fun i : Fin (m X) =>
        Finset.univ.sum (fun chi : DirichletCharacter Complex (q X) =>
          (multiplicity (S X) chi : Complex) *
            chi (primeAt (a X i) : ZMod (q X))) *
          (profileDifference H X (a X i) : Complex)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [<- mul_assoc, natural_character_expansion (S X) hDiv (primeAt (a X i))]
    _ = _ := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro chi hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact mul_assoc _ _ _

theorem eventually_signed_profile_error
    (H : Nat) (m : Nat -> Nat)
    (a : (X : Nat) -> Fin (m X) -> Nat) (hs : LocalAscentSampling H m a)
    (q : Nat -> Nat) [forall X, NeZero (q X)] (S : Nat -> Finset Nat.Primes)
    (hDiv : forall X, forall p : S X,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod (q X)))))
    (hOdd : forall X, forall p : S X, Not ((p.val : Nat) = 2)) :
    Filter.Eventually (fun X : Nat =>
      abs (normalizedExcess H m a q S X -
        (localTiltMesh X : Real) * profileExcess H m a q S X) <=
      Finset.univ.sum (fun i : Fin (m X) =>
        carmichaelPrimeWeight (q X) (S X) (primeAt (a X i)))) atTop := by
  rw [normalizedExcess_eq_original H m a q S hDiv]
  let alpha : Real := (H : Real) + 2
  have ha : 0 < alpha := by dsimp [alpha]; positivity
  have hCast : Tendsto (fun n : Nat => (n : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hBands := hCast.eventually (eventually_primeProfile_fixed_window_bands alpha ha)
  filter_upwards [hs.2, hBands, eventually_ge_atTop (1 : Nat)] with X hc hb hx
  have hx1 : (1 : Real) <= X := by exact_mod_cast hx
  have hp : (X : Real) ^ (3 / 4 : Real) <= X := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx1
      (by norm_num : (3 / 4 : Real) <= 1)
  have hM : 0 < localTiltMesh X := by
    have hPow : (0 : Real) < (X : Real) ^ (1 / 2 : Real) :=
      Real.rpow_pos_of_pos (by linarith) _
    have hCeil : (X : Real) ^ (1 / 2 : Real) <= (localTiltMesh X : Real) :=
      Nat.le_ceil _
    exact_mod_cast lt_of_lt_of_le hPow hCeil
  have hError (i : Fin (m X)) :
      abs (localAscentPairExcess H X (a X i) -
        (localTiltMesh X : Real) * profileDifference H X (a X i)) < 1 := by
    have hPair := hc.2 i
    let y : Real := ((primeAt (a X i) - 1 : Nat) : Real)
    have hy : (X : Real) <= y := hPair.2.2.1
    have hB := hb.2 y hy (by dsimp [y]; linarith [hPair.2.2.2])
    have hCut : Nat.floor y + 1 = primeAt (a X i) := by
      dsimp [y]
      rw [Nat.floor_natCast, Nat.sub_add_cancel (prime_primeAt (a X i)).one_lt.le]
    rw [hCut] at hB
    let R : Real := densityRatio (primesBelow (primeAt (a X i))) (localTiltRank H X)
    let U : Real := localTiltReference H X (a X i)
    let g : Real := primeGap (a X i)
    have hG : (2 : Real) <= g := by dsimp [g]; exact_mod_cast hPair.1
    have hGH : g <= H := by dsimp [g]; exact_mod_cast hPair.2.1
    have hRNear : -(1 / 2 : Real) <= R - alpha /\ R - alpha <= 1 / 2 :=
      abs_le.mp hB.2.2.2.2
    have hUNear : -(1 / 2 : Real) <= U - alpha /\ U - alpha <= 1 / 2 :=
      abs_le.mp hB.2.2.2.1
    dsimp only [alpha] at hRNear hUNear
    have hActual := localTiltAscentSet_eq_scalar H (localTiltMesh X) (localTiltRank H X)
      (a X i) hb.1 (weightEsymm_positive_degree_supported _ _ hB.2.2.1)
    unfold localAscentPairExcess profileDifference
    rw [hActual]
    exact tiltAscentSet_signed_error_lt_one H (localTiltMesh X) hM R U g
      (by linarith) (by linarith) (by linarith) (by linarith)
  have hW (i : Fin (m X)) :
      0 <= carmichaelPrimeWeight (q X) (S X) (primeAt (a X i)) :=
    carmichaelPrimeWeight_nonneg (q X) (S X) (hDiv X) (hOdd X) _
  unfold carmichaelLocalAscentExcess weightedLocalAscentExcess
    carmichaelLocalAscentWeight profileExcess
  rw [Finset.mul_sum, <- Finset.sum_sub_distrib]
  calc
    _ <= Finset.univ.sum (fun i : Fin (m X) =>
        abs (carmichaelPrimeWeight (q X) (S X) (primeAt (a X i)) *
          localAscentPairExcess H X (a X i) -
          (localTiltMesh X : Real) *
            (carmichaelPrimeWeight (q X) (S X) (primeAt (a X i)) *
              profileDifference H X (a X i)))) := Finset.abs_sum_le_sum_abs _ _
    _ <= _ := by
      apply Finset.sum_le_sum
      intro i hi
      have hFactor :
          carmichaelPrimeWeight (q X) (S X) (primeAt (a X i)) *
              localAscentPairExcess H X (a X i) -
            (localTiltMesh X : Real) *
              (carmichaelPrimeWeight (q X) (S X) (primeAt (a X i)) *
                profileDifference H X (a X i)) =
          carmichaelPrimeWeight (q X) (S X) (primeAt (a X i)) *
            (localAscentPairExcess H X (a X i) -
              (localTiltMesh X : Real) * profileDifference H X (a X i)) := by ring
      rw [hFactor, abs_mul, abs_of_nonneg (hW i)]
      exact (mul_le_mul_of_nonneg_left (hError i).le (hW i)).trans_eq (mul_one _)

end PrimeFactorOscillations.CarmichaelAscentEstimate
