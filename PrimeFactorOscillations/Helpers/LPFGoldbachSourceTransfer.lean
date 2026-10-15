/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFMinorBilinear
import PrimeFactorOscillations.Helpers.LPFMinorDyadic
import PrimeFactorOscillations.Helpers.LPFMinorPower
import PrimeFactorOscillations.Helpers.LPFMinorResidueMean
import PrimeFactorOscillations.Helpers.LPFMinorTypeI
import PrimeFactorOscillations.Helpers.LPFMinorTypeILog
import PrimeFactorOscillations.Helpers.LPFMinorWeightedPacket
import PrimeFactorOscillations.Helpers.LPFPositiveSupply

/-!
# Complete finite transfer of the positive Goldbach mean-square source

The source windows, singular factors, exceptional-set cardinality and
normalized prime-pair supply retain explicit c and K. The two analytic
mean-square inequalities remain hypotheses; no such input is an axiom.
-/

set_option Elab.async false

namespace PrimeFactorOscillations.LPF

noncomputable def goldbachWindowWeight (M t : Nat) : Real :=
  goldbachMangoldtWeight (goldbachWindowInputs M t) t

noncomputable def goldbachWindowError (M : Nat) (c : Real) (t : Nat) : Real :=
  goldbachWindowWeight M t - 4 * ((M / 64 : Nat) : Real) * c * singularDivisorProduct t

noncomputable def goldbachSourceErrorSum (M : Nat) (c : Real) : Real :=
  Finset.sum (Union.union (goldbachEvenTargets (M / 2)) (goldbachEvenTargets M))
    (fun t => goldbachWindowError M c t ^ 2)

noncomputable def goldbachBadPrimeTargets (M : Nat) (c : Real) : Finset Nat := by
  classical
  exact (nextPrimeWindow M).filter (fun r => goldbachWindowWeight M (primeTargetSum r) <
    2 * ((M / 64 : Nat) : Real) * c * singularDivisorProduct (primeTargetSum r))

/-- No multiplicity is lost when bad prime targets enter the complete squared-error sum. -/
theorem goldbachBadPrimeTargets_energy (M : Nat) (c : Real) (hM : 128 <= M) (hc : 0 < c) :
    4 * ((M / 64 : Nat) : Real) ^ 2 * c ^ 2 * ((goldbachBadPrimeTargets M c).card : Real) <=
      goldbachSourceErrorSum M c := by
  classical
  let Z := goldbachBadPrimeTargets M c
  let D := Union.union (goldbachEvenTargets (M / 2)) (goldbachEvenTargets M)
  let u : Real := ((M / 64 : Nat) : Real)
  have hu : 0 < u := by dsimp [u]; exact_mod_cast (by omega : 0 < M / 64)
  have hInj : Set.InjOn primeTargetSum (Z : Set Nat) := by
    intro r hr s hs hEq
    have hR := nextPrimeWindow_spec M r (Finset.mem_filter.mp hr).1
    have hS := nextPrimeWindow_spec M s (Finset.mem_filter.mp hs).1
    exact primeTarget_injective_window M r s (by omega) hR.1 hS.1 hR.2 hS.2 hEq
  have hImage : Z.image primeTargetSum <= D := by
    intro t ht
    choose r hr hEq using Finset.mem_image.mp ht
    rw [<- hEq]
    have hSource := primeTarget_goldbach_source_interval M r (by omega) (Finset.mem_filter.mp hr).1
    by_cases hBranch : r % 4 = 1
    next =>
      simp [hBranch] at hSource
      exact Finset.mem_union_right _ hSource
    next =>
      simp [hBranch] at hSource
      exact Finset.mem_union_left _ hSource
  have hBad (r : Nat) (hr : Membership.mem Z r) :
      4 * u ^ 2 * c ^ 2 <= goldbachWindowError M c (primeTargetSum r) ^ 2 := by
    have hW := (Finset.mem_filter.mp hr).2
    change goldbachWindowWeight M (primeTargetSum r) <
      2 * u * c * singularDivisorProduct (primeTargetSum r) at hW
    have hG := mul_le_mul_of_nonneg_left (sieve_singularDivisorProduct_one_le (primeTargetSum r))
      (by positivity : 0 <= 2 * u * c)
    have hNeg : 2 * u * c <= -goldbachWindowError M c (primeTargetSum r) := by
      dsimp [goldbachWindowError]
      change 2 * u * c <= -(goldbachWindowWeight M (primeTargetSum r) -
        4 * u * c * singularDivisorProduct (primeTargetSum r))
      nlinarith only [hW, hG]
    have hNonneg : 0 <= 2 * u * c := by positivity
    have hSq := mul_le_mul hNeg hNeg hNonneg (hNonneg.trans hNeg)
    convert hSq using 1 <;> ring
  change 4 * u ^ 2 * c ^ 2 * (Z.card : Real) <=
    Finset.sum D (fun t => goldbachWindowError M c t ^ 2)
  calc
    _ = Finset.sum Z (fun _ => 4 * u ^ 2 * c ^ 2) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ <= Finset.sum Z (fun r => goldbachWindowError M c (primeTargetSum r) ^ 2) :=
      Finset.sum_le_sum hBad
    _ = Finset.sum (Z.image primeTargetSum) (fun t => goldbachWindowError M c t ^ 2) :=
      (Finset.sum_image (f := fun t => goldbachWindowError M c t ^ 2) hInj).symm
    _ <= _ := Finset.sum_le_sum_of_subset_of_nonneg hImage (fun t _ _ => sq_nonneg _)

theorem goldbachBadPrimeTargets_card_bound (M : Nat) (c K : Real) (hM : 128 <= M)
    (hc : 0 < c)
    (hBudget : goldbachSourceErrorSum M c <=
      K * (M : Real) * ((M / 64 : Nat) : Real) ^ 2 / Real.log (M : Real) ^ 4) :
    ((goldbachBadPrimeTargets M c).card : Real) <=
      (K / (4 * c ^ 2)) * ((M : Real) / Real.log (M : Real) ^ 4) := by
  let u : Real := ((M / 64 : Nat) : Real)
  have hu : 0 < u := by dsimp [u]; exact_mod_cast (by omega : 0 < M / 64)
  have hLog : 0 < Real.log (M : Real) := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have h := (goldbachBadPrimeTargets_energy M c hM hc).trans hBudget
  apply (mul_le_mul_iff_of_pos_right (by positivity : 0 < 4 * u ^ 2 * c ^ 2)).mp
  have hRight : ((K / (4 * c ^ 2)) * ((M : Real) / Real.log (M : Real) ^ 4)) *
      (4 * u ^ 2 * c ^ 2) = K * (M : Real) * u ^ 2 / Real.log (M : Real) ^ 4 := by
    field_simp [ne_of_gt hc, ne_of_gt hLog]
  rw [hRight]
  convert h using 1
  ring

theorem goldbach_good_primeTarget_weight (M r : Nat) (c : Real) (hM : 128 <= M)
    (hc : 0 < c)
    (hr : Membership.mem (SDiff.sdiff (nextPrimeWindow M) (goldbachBadPrimeTargets M c)) r) :
    (c / 64) * (M : Real) * singularDivisorProduct (primeTargetSum r) <=
      goldbachWindowWeight M (primeTargetSum r) := by
  classical
  have hR := Finset.mem_sdiff.mp hr
  have hGood : 2 * ((M / 64 : Nat) : Real) * c * singularDivisorProduct (primeTargetSum r) <=
      goldbachWindowWeight M (primeTargetSum r) := by
    apply le_of_not_gt
    intro hBad
    exact hR.2 (Finset.mem_filter.mpr (And.intro hR.1 hBad))
  have hWidthNat : M <= 128 * (M / 64) := by omega
  have hWidth : (M : Real) <= 128 * ((M / 64 : Nat) : Real) := by exact_mod_cast hWidthNat
  have hG : 0 <= singularDivisorProduct (primeTargetSum r) :=
    zero_le_one.trans (sieve_singularDivisorProduct_one_le _)
  have hScaled := mul_le_mul_of_nonneg_right hWidth (mul_nonneg hc.le hG)
  nlinarith only [hGood, hScaled]

/-- The two source estimates combine with a proved constant nine. -/
theorem goldbach_source_errorSum_le_nine (M : Nat) (c K : Real) (hM : 16 <= M) (hK : 0 <= K)
    (hHalf : Finset.sum (goldbachEvenTargets (M / 2)) (fun t => goldbachWindowError M c t ^ 2) <=
      K * ((M / 2 : Nat) : Real) * ((M / 64 : Nat) : Real) ^ 2 /
        Real.log ((M / 2 : Nat) : Real) ^ 4)
    (hFull : Finset.sum (goldbachEvenTargets M) (fun t => goldbachWindowError M c t ^ 2) <=
      K * (M : Real) * ((M / 64 : Nat) : Real) ^ 2 / Real.log (M : Real) ^ 4) :
    goldbachSourceErrorSum M c <=
      9 * K * (M : Real) * ((M / 64 : Nat) : Real) ^ 2 / Real.log (M : Real) ^ 4 := by
  classical
  have hDisjoint : Disjoint (goldbachEvenTargets (M / 2)) (goldbachEvenTargets M) := by
    apply Finset.disjoint_left.mpr
    intro t hHalfT hFullT
    have h1 := Finset.mem_Ioo.mp (Finset.mem_filter.mp hHalfT).1
    have h2 := Finset.mem_Ioo.mp (Finset.mem_filter.mp hFullT).1
    omega
  let X : Real := (M : Real)
  let Y : Real := ((M / 2 : Nat) : Real)
  let u : Real := ((M / 64 : Nat) : Real)
  have hX : 0 < X := by dsimp [X]; exact_mod_cast (by omega : 0 < M)
  have hY : 0 < Y := by dsimp [Y]; exact_mod_cast (by omega : 0 < M / 2)
  have hLogX : 0 < Real.log X := Real.log_pos (by dsimp [X]; exact_mod_cast (by omega : 1 < M))
  have hLogY : 0 < Real.log Y := Real.log_pos (by dsimp [Y]; exact_mod_cast (by omega : 1 < M / 2))
  have hXY : X <= Y ^ 2 := by
    have hNat : M <= (M / 2) ^ 2 := by
      have hDiv : M <= 2 * (M / 2) + 1 := by omega
      have hEight : 8 <= M / 2 := by omega
      nlinarith only [hDiv, hEight]
    dsimp [X, Y]
    exact_mod_cast hNat
  have hYHalf : 2 * Y <= X := by
    dsimp [X, Y]
    exact_mod_cast (by omega : 2 * (M / 2) <= M)
  have hLogXY : Real.log X <= 2 * Real.log Y := by
    have h := Real.log_le_log hX hXY
    rw [Real.log_pow] at h
    simpa using h
  have hPow2 : Real.log X ^ 2 <= (2 * Real.log Y) ^ 2 := by
    have h := mul_le_mul hLogXY hLogXY hLogX.le (by positivity)
    simpa only [pow_two] using h
  have hPow4 : Real.log X ^ 4 <= (2 * Real.log Y) ^ 4 := by
    have h := mul_le_mul hPow2 hPow2 (sq_nonneg _) (sq_nonneg _)
    convert h using 1 <;> ring
  have hHalfScale : K * Y * u ^ 2 / Real.log Y ^ 4 <=
      8 * K * X * u ^ 2 / Real.log X ^ 4 := by
    apply (mul_le_mul_iff_of_pos_right (mul_pos (pow_pos hLogX 4) (pow_pos hLogY 4))).mp
    have hRaw := mul_le_mul hYHalf hPow4 (by positivity : 0 <= Real.log X ^ 4) (by positivity : 0 <= X)
    have hScaled := mul_le_mul_of_nonneg_left hRaw (by positivity : 0 <= K * u ^ 2)
    have hnX : Not (Real.log X = 0) := ne_of_gt hLogX
    have hnY : Not (Real.log Y = 0) := ne_of_gt hLogY
    field_simp
    nlinarith only [hScaled]
  unfold goldbachSourceErrorSum
  rw [Finset.sum_union hDisjoint]
  have hHalf' : Finset.sum (goldbachEvenTargets (M / 2)) (fun t => goldbachWindowError M c t ^ 2) <=
      8 * K * X * u ^ 2 / Real.log X ^ 4 := hHalf.trans hHalfScale
  change Finset.sum (goldbachEvenTargets M) (fun t => goldbachWindowError M c t ^ 2) <=
    K * X * u ^ 2 / Real.log X ^ 4 at hFull
  change _ <= 9 * K * X * u ^ 2 / Real.log X ^ 4
  calc
    _ <= 8 * K * X * u ^ 2 / Real.log X ^ 4 + K * X * u ^ 2 / Real.log X ^ 4 :=
      add_le_add hHalf' hFull
    _ = _ := by ring

/-- All finite source adapters are proved. The two analytic mean-square estimates
remain explicit premises, with c and K fixed before the cutoffs. -/
theorem exists_primeTarget_supply_of_goldbach_meanSquare (c K : Real) (hc : 0 < c) (hK : 0 <= K)
    (hMeanSquare : Filter.Eventually (fun M : Nat => And
      (Finset.sum (goldbachEvenTargets (M / 2)) (fun t => goldbachWindowError M c t ^ 2) <=
        K * ((M / 2 : Nat) : Real) * ((M / 64 : Nat) : Real) ^ 2 /
          Real.log ((M / 2 : Nat) : Real) ^ 4)
      (Finset.sum (goldbachEvenTargets M) (fun t => goldbachWindowError M c t ^ 2) <=
        K * (M : Real) * ((M / 64 : Nat) : Real) ^ 2 / Real.log (M : Real) ^ 4)) Filter.atTop) :
    exists a : Real, exists C : Real, And (0 < a) (And (0 <= C)
      (Filter.Eventually (fun M : Nat =>
        exists Z : Finset Nat, And ((Z.card : Real) <= C * ((M : Real) / Real.log (M : Real) ^ 4))
          (forall r, Membership.mem (SDiff.sdiff (nextPrimeWindow M) Z) r ->
            a * ((M : Real) / Real.log (M : Real) ^ 2) <=
              (1 / singularDivisorProduct (primeTargetSum r)) *
                ((Finset.sumPartners (inputPrimePrefix M) (primeTargetSum r)).card : Real))) Filter.atTop)) := by
  classical
  refine Exists.intro (c / 128) (Exists.intro (9 * K / (4 * c ^ 2))
    (And.intro (by positivity) (And.intro (by positivity) ?_)))
  filter_upwards [hMeanSquare, Filter.eventually_ge_atTop (128 : Nat),
    eventually_goldbachMangoldt_to_sumPartners (c / 64) (by positivity)] with M hMean hM hConvert
  refine Exists.intro (goldbachBadPrimeTargets M c) (And.intro ?_ ?_)
  next =>
    exact goldbachBadPrimeTargets_card_bound M c (9 * K) hM hc
      (goldbach_source_errorSum_le_nine M c K (by omega) hK hMean.1 hMean.2)
  next =>
    intro r hr
    have hR := (Finset.mem_sdiff.mp hr).1
    have hSupply := goldbach_good_primeTarget_weight M r c hM hc hr
    have hRep := hConvert (goldbachWindowInputs M (primeTargetSum r)) (primeTargetSum r)
      (fun p hp => (primeTarget_goldbach_input_bounds M r hM hR p hp).1)
      (fun p hp => (primeTarget_goldbach_input_bounds M r hM hR p hp).2) hSupply
    have hConstant : c / 64 / 2 = c / 128 := by ring
    rw [hConstant] at hRep
    exact hRep

end PrimeFactorOscillations.LPF
