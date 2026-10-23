/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Proof.PrimeClassDeletion.GreedyPrimeRHCriterion

/-!
# Root-scale headroom preserves the cofinal prime-class zero criterion

A retained prime class may exceed the diagonal by a buffer. Its complement
mass plus the complete prefix buffer still dominates the old regulator.
The finite comparison charges every logarithmic count-to-mass loss.
No sparse deletion estimate is assumed to have been proved.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter
open PrimeFactorUnimodality
open PrimeFactorOscillations.PrimeClassSampling

namespace PrimeFactorOscillations.PrimeClassDeletion

theorem primeClassTheta_mono_cutoff (P : Set Nat) (X Y : Nat) (hXY : X <= Y) :
    primeClassTheta P X <= primeClassTheta P Y := by
  classical
  unfold primeClassTheta
  apply Finset.sum_le_sum_of_subset_of_nonneg
  case h =>
    intro p hp
    have hmem := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    exact And.intro (Finset.mem_Icc.mpr (And.intro
      (Finset.mem_Icc.mp hmem.1).1 ((Finset.mem_Icc.mp hmem.1).2.trans hXY))) hmem.2
  case hf =>
    intro p hp _
    have hPrime := primeClassPrefix_prime P Y p hp
    exact Real.log_nonneg (by exact_mod_cast hPrime.one_le)

theorem primeClassTheta_le_count_mul_log (P : Set Nat) (X : Nat) :
    primeClassTheta P X <=
      ((primeClassPrefix P X).card : Real) * Real.log (X : Real) := by
  classical
  unfold primeClassTheta
  calc
    _ <= (primeClassPrefix P X).sum (fun _ => Real.log (X : Real)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hmem := Finset.mem_filter.mp hp
      have hpX : p <= X := (Finset.mem_Icc.mp hmem.1).2
      have hPrime := primeClassPrefix_prime P X p hp
      exact Real.log_le_log (Nat.cast_pos.mpr hPrime.pos) (Nat.cast_le.mpr hpX)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

theorem bufferedPrimeClass_complementMass_dominates_record
    (P : Set Nat) (X : Nat) (B : Real) (hB : 0 <= B)
    (hCap : forall t : Nat, 2 <= t -> t <= X ->
      primeClassTheta P t <= (t : Real) + B) :
    greedyPrimeRegulator X <=
      primeClassTheta (fun p => Not (Membership.mem P p)) X + B := by
  have hMass : 0 <= primeClassTheta (fun p => Not (Membership.mem P p)) X := by
    unfold primeClassTheta
    apply Finset.sum_nonneg
    intro p hp
    have hPrime := primeClassPrefix_prime (fun p => Not (Membership.mem P p)) X p hp
    exact Real.log_nonneg (by exact_mod_cast hPrime.one_le)
  apply (greedyPrimeRegulator_le_iff X _).mpr
  refine And.intro (add_nonneg hMass hB) ?_
  intro p hp hpX
  have hTotal := primeClassTheta_complement_sum P p
  have hMono := primeClassTheta_mono_cutoff
    (fun p => Not (Membership.mem P p)) p X hpX
  have hLocal := hCap p hp.two_le hpX
  linarith only [hTotal, hMono, hLocal]

theorem greedyDeletedPrimeClass_mass_le_buffered_complement
    (P : Set Nat) (X : Nat) (hX : 2 <= X) (B : Real) (hB : 0 <= B)
    (hCap : forall t : Nat, 2 <= t -> t <= X ->
      primeClassTheta P t <= (t : Real) + B) :
    primeClassTheta greedyDeletedPrimeClass X <=
      primeClassTheta (fun p => Not (Membership.mem P p)) X + B +
        Real.log (X : Real) := by
  have hRecord := bufferedPrimeClass_complementMass_dominates_record P X B hB hCap
  have hMass := (greedyDeletedPrimeClass_record_bounds X hX).2
  linarith only [hRecord, hMass]

theorem greedyDeletedPrimeClass_count_le_buffered_complement
    (P : Set Nat) (X : Nat) (hX : 2 <= X) (B : Real) (hB : 0 <= B)
    (hCap : forall t : Nat, 2 <= t -> t <= X ->
      primeClassTheta P t <= (t : Real) + B) :
    ((primeClassPrefix greedyDeletedPrimeClass X).card : Real) * Real.log 2 <=
      ((primeClassPrefix (fun p => Not (Membership.mem P p)) X).card : Real) *
        Real.log (X : Real) + B + Real.log (X : Real) := by
  have hLower := primeClassPrefix_count_mul_log_two_le_theta greedyDeletedPrimeClass X
  have hMass := greedyDeletedPrimeClass_mass_le_buffered_complement P X hX B hB hCap
  have hUpper := primeClassTheta_le_count_mul_log
    (fun p => Not (Membership.mem P p)) X
  linarith only [hLower, hMass, hUpper]

theorem bufferedPrimeClass_cofinal_power_count_transfer
    (P : Set Nat) (eta : Real) (hEta : 0 <= eta)
    (hCap : forall delta : Real, 0 < delta ->
      Exists fun C : Real => And (0 <= C) (forall t : Nat, 2 <= t ->
        primeClassTheta P t <= (t : Real) + C * (t : Real) ^ (eta + delta)))
    (hSparse : forall epsilon : Real, 0 < epsilon -> forall N : Nat,
      Exists fun n : Nat => And (max N 2 <= n)
        (((primeClassPrefix (fun p => Not (Membership.mem P p)) n).card : Real) <=
          (n : Real) ^ (eta + epsilon))) :
    forall epsilon : Real, 0 < epsilon -> forall N : Nat,
      Exists fun n : Nat => And (max N 2 <= n)
        (((primeClassPrefix greedyDeletedPrimeClass n).card : Real) <=
          (n : Real) ^ (eta + epsilon)) := by
  intro epsilon he N
  let delta : Real := epsilon / 2
  let a : Real := eta + delta
  let b : Real := eta + epsilon
  have hd : 0 < delta := by dsimp only [delta]; linarith only [he]
  have ha : 0 <= a := by dsimp only [a]; linarith only [hEta, hd]
  have hb : 0 < b := by dsimp only [b]; linarith only [hEta, he]
  have hab : a < b := by dsimp only [a, b, delta]; linarith only [he]
  choose C hC hCapC using hCap delta hd
  have hFirst : Tendsto (fun x : Real => x ^ a * Real.log x / x ^ b)
      atTop (nhds 0) := gaussian_power_log_ratio_tendsto a b hab
  have hSecond : Tendsto (fun x : Real => x ^ a / x ^ b)
      atTop (nhds 0) := gaussian_power_ratio_tendsto a b hab
  have hLast : Tendsto (fun x : Real => Real.log x / x ^ b)
      atTop (nhds 0) := by
    simpa only [Real.rpow_zero, one_mul] using gaussian_power_log_ratio_tendsto 0 b hb
  have hSum : Tendsto (fun x : Real =>
      x ^ a * Real.log x / x ^ b + C * (x ^ a / x ^ b) +
        Real.log x / x ^ b) atTop (nhds 0) := by
    simpa only [mul_zero, zero_add, add_zero] using
      (hFirst.add (hSecond.const_mul C)).add hLast
  have hTotal : Tendsto (fun x : Real =>
      (x ^ a * Real.log x + C * x ^ a + Real.log x) / x ^ b)
      atTop (nhds 0) := by
    apply hSum.congr'
    exact Filter.Eventually.of_forall (fun x => by ring)
  have hNat : Tendsto (fun n : Nat =>
      ((n : Real) ^ a * Real.log (n : Real) + C * (n : Real) ^ a +
        Real.log (n : Real)) / (n : Real) ^ b) atTop (nhds 0) :=
    hTotal.comp tendsto_natCast_atTop_atTop
  have hLogTwo : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  choose K hK using Filter.eventually_atTop.mp
    (hNat.eventually (eventually_lt_nhds hLogTwo))
  choose n hn using hSparse delta hd (max N K)
  have hN : max N 2 <= n := by omega
  have hKn : K <= n := by omega
  have hnTwo : 2 <= n := (le_max_right N 2).trans hN
  have hnPos : (0 : Real) < (n : Real) := by exact_mod_cast (by omega : 0 < n)
  have hBuffer : 0 <= C * (n : Real) ^ a :=
    mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg n) a)
  have hPrefix : forall t : Nat, 2 <= t -> t <= n ->
      primeClassTheta P t <= (t : Real) + C * (n : Real) ^ a := by
    intro t ht htn
    have hPower : (t : Real) ^ a <= (n : Real) ^ a :=
      Real.rpow_le_rpow (Nat.cast_nonneg t) (Nat.cast_le.mpr htn) ha
    have hScale := mul_le_mul_of_nonneg_left hPower hC
    have hLocal := hCapC t ht
    change primeClassTheta P t <= (t : Real) + C * (t : Real) ^ a at hLocal
    linarith only [hScale, hLocal]
  have hFinite := greedyDeletedPrimeClass_count_le_buffered_complement
    P n hnTwo (C * (n : Real) ^ a) hBuffer hPrefix
  have hLog : 0 <= Real.log (n : Real) :=
    Real.log_nonneg (by exact_mod_cast (show 1 <= n by omega))
  have hCountScale := mul_le_mul_of_nonneg_right hn.2 hLog
  have hBound :
      ((primeClassPrefix greedyDeletedPrimeClass n).card : Real) * Real.log 2 <=
        (n : Real) ^ a * Real.log (n : Real) + C * (n : Real) ^ a +
          Real.log (n : Real) := by
    change _ <= (n : Real) ^ a * Real.log (n : Real) at hCountScale
    linarith only [hFinite, hCountScale]
  have hPower : 0 < (n : Real) ^ b := Real.rpow_pos_of_pos hnPos b
  have hSmall := mul_lt_mul_of_pos_right (hK n hKn) hPower
  have hCancel : (((n : Real) ^ a * Real.log (n : Real) + C * (n : Real) ^ a +
      Real.log (n : Real)) / (n : Real) ^ b) * (n : Real) ^ b =
        (n : Real) ^ a * Real.log (n : Real) + C * (n : Real) ^ a +
          Real.log (n : Real) := by field_simp [hPower.ne']
  rw [hCancel] at hSmall
  refine Exists.intro n (And.intro hN ?_)
  by_contra hFail
  have hWrong := mul_le_mul_of_nonneg_right
    (le_of_lt (lt_of_not_ge hFail)) hLogTwo.le
  change (n : Real) ^ b * Real.log 2 <=
    ((primeClassPrefix greedyDeletedPrimeClass n).card : Real) * Real.log 2 at hWrong
  linarith only [hWrong, hBound, hSmall]

theorem bufferedPrimeClass_zero_strip_of_sparse_power_count
    (P : Set Nat) (eta : Real) (hEta : (1 / 2 : Real) <= eta)
    (hCap : forall delta : Real, 0 < delta ->
      Exists fun C : Real => And (0 <= C) (forall t : Nat, 2 <= t ->
        primeClassTheta P t <= (t : Real) + C * (t : Real) ^ (eta + delta)))
    (hSparse : forall epsilon : Real, 0 < epsilon -> forall N : Nat,
      Exists fun n : Nat => And (max N 2 <= n)
        (((primeClassPrefix (fun p => Not (Membership.mem P p)) n).card : Real) <=
          (n : Real) ^ (eta + epsilon))) :
    forall rho : Complex, riemannZeta rho = 0 ->
      And (0 < rho.re) (rho.re < 1) -> rho.re <= eta := by
  have hNonneg : 0 <= eta := by linarith only [hEta]
  exact greedyDeletedPrimeClass_zero_strip_of_sparse_power_count eta hEta
    (bufferedPrimeClass_cofinal_power_count_transfer P eta hNonneg hCap hSparse)

theorem riemannHypothesis_of_sqrt_buffered_primeClass
    (P : Set Nat)
    (hCap : forall t : Nat, 2 <= t ->
      primeClassTheta P t <= (t : Real) + Real.sqrt (t : Real))
    (hSparse : forall epsilon : Real, 0 < epsilon -> forall N : Nat,
      Exists fun n : Nat => And (max N 2 <= n)
        (((primeClassPrefix (fun p => Not (Membership.mem P p)) n).card : Real) <=
          (n : Real) ^ ((1 / 2 : Real) + epsilon))) :
    RiemannHypothesis := by
  have hPowerCap : forall delta : Real, 0 < delta ->
      Exists fun C : Real => And (0 <= C) (forall t : Nat, 2 <= t ->
        primeClassTheta P t <= (t : Real) +
          C * (t : Real) ^ ((1 / 2 : Real) + delta)) := by
    intro delta hd
    refine Exists.intro 1 (And.intro (by norm_num) ?_)
    intro t ht
    have htOne : (1 : Real) <= (t : Real) := by
      exact_mod_cast (show 1 <= t by omega)
    have hExponent : (1 / 2 : Real) <= (1 / 2 : Real) + delta := by
      linarith only [hd]
    have hPower := Real.rpow_le_rpow_of_exponent_le htOne hExponent
    rw [<- Real.sqrt_eq_rpow] at hPower
    have hLocal := hCap t ht
    simp only [one_mul]
    linarith only [hPower, hLocal]
  exact riemannHypothesis_of_sparse_greedyDeletedPrimeClass_count
    (bufferedPrimeClass_cofinal_power_count_transfer P (1 / 2 : Real)
      (by norm_num) hPowerCap hSparse)

end PrimeFactorOscillations.PrimeClassDeletion
