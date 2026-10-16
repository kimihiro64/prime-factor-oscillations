import PrimeFactorOscillations.Helpers.PeakDensityModel
import PrimeFactorOscillations.Helpers.PeakEulerProduct

/-!
# Full product limits and terminal ratios for reciprocal prime laws

Full product limits and terminal ratios for reciprocal prime laws for the peak-height comparison of regular prime Bernoulli laws.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter Topology

namespace PrimeFactorOscillations

noncomputable def primeComparisonEulerConstant
    (P : Nat) (eta1 eta2 : Nat -> Real) (nu b1 b2 : Real) : Real :=
  let theta := nu * (b2 - b1)
  Real.exp ((tsum (fun p : Nat => if Nat.Prime p /\ P < p then
    Real.log (eta1 p) - Real.log (eta2 p) +
      theta * Real.log (1 - 1 / (p : Real)) else 0)) +
    theta * (Real.eulerMascheroniConstant +
      (P + 1).primesBelow.sum (fun p => Real.log (1 - 1 / (p : Real)))))

theorem regularPrimeLaws_tendsto_growing_product_sequence
    (P : Nat) (eta1 eta2 : Nat -> Real) (nu b1 b2 C1 C2 alpha beta : Real)
    (hnu : 0 < nu) (hC1 : 0 <= C1) (hC2 : 0 <= C2)
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (h1 : forall p, Nat.Prime p -> P < p -> 0 < eta1 p)
    (h2 : forall p, Nat.Prime p -> P < p -> 0 < eta2 p)
    (herr1 : forall p, Nat.Prime p -> P < p ->
      abs (1 / eta1 p - (p : Real) / nu - b1) <= C1 / (p : Real))
    (herr2 : forall p, Nat.Prime p -> P < p ->
      abs (1 / eta2 p - (p : Real) / nu - b2) <= C2 / (p : Real))
    (hscale1 : forall p, Nat.Prime p -> P < p ->
      2 * (nu * (abs b1 + C1)) <= (p : Real))
    (hscale2 : forall p, Nat.Prime p -> P < p ->
      2 * (nu * (abs b2 + C2)) <= (p : Real))
    (n : Nat -> Nat)
    (hband : Filter.Eventually (fun k : Nat => k ^ 2 <= n k /\
      alpha * Real.log (k : Real) <= Real.log (Real.log (n k : Real)) /\
        Real.log (Real.log (n k : Real)) <= beta * Real.log (k : Real)) atTop) :
    let theta := nu * (b2 - b1)
    let C := primeComparisonEulerConstant P eta1 eta2 nu b1 b2
    let z := fun k : Nat => (k : Real) / (nu * Real.log (Real.log (n k : Real)))
    0 < C /\ Tendsto (fun k : Nat =>
      (((n k + 1).primesBelow \ (P + 1).primesBelow).prod
        (fun p => (1 + (z k - 1) * eta1 p) / (1 + (z k - 1) * eta2 p))) /
          (C * Real.rpow (Real.log (z k)) theta)) atTop (nhds 1) := by
  let C := primeComparisonEulerConstant P eta1 eta2 nu b1 b2
  let z := fun k : Nat => (k : Real) / (nu * Real.log (Real.log (n k : Real)))
  have hp := regularPrimeLaws_uniform_growing_product_ratio P eta1 eta2 nu b1 b2 C1 C2
    hnu hC1 hC2 h1 h2 herr1 herr2 hscale1 hscale2
  have ht := Real.primeTilt_sequence_atTop_and_cutoff nu alpha beta hnu halpha hbeta n hband
  refine And.intro hp.1 ?_
  apply Metric.tendsto_nhds.2
  intro e he
  choose Z hZ using hp.2 (e / 2) (half_pos he)
  filter_upwards [ht.1.eventually (eventually_ge_atTop Z), ht.2] with k hk hn
  change abs (((((n k + 1).primesBelow \ (P + 1).primesBelow).prod
    (fun p => (1 + (z k - 1) * eta1 p) / (1 + (z k - 1) * eta2 p))) /
      (C * Real.rpow (Real.log (z k)) (nu * (b2 - b1)))) - 1) < e
  exact (hZ.2 (z k) hk (n k) hn.2).trans_lt (half_lt_self he)

end PrimeFactorOscillations
namespace PrimeFactorOscillations

noncomputable def primeBernoulliProduct (eta : Nat -> Real) (n : Nat) (z : Real) : Real :=
  (n + 1).primesBelow.prod (fun p => 1 - eta p + eta p * z)

theorem primeBernoulliProduct_pos (eta : Nat -> Real) (n : Nat) (z : Real)
    (hunit : forall p, Nat.Prime p -> 0 <= eta p /\ eta p <= 1) (hz : 0 < z) :
    0 < primeBernoulliProduct eta n z := by
  apply Finset.prod_pos
  intro p hp
  have hh := hunit p (Nat.mem_primesBelow.mp hp).2
  exact List.bernoulliFactor_pos (eta p) z hh.1 hh.2 hz

theorem primeBernoulliProduct_split (P n : Nat) (eta : Nat -> Real) (z : Real) (hPn : P <= n) :
    primeBernoulliProduct eta n z =
      primeBernoulliProduct eta P z *
        ((n + 1).primesBelow \ (P + 1).primesBelow).prod
          (fun p => 1 - eta p + eta p * z) := by
  have hsub : forall p, Membership.mem (P + 1).primesBelow p ->
      Membership.mem (n + 1).primesBelow p := by
    intro p hp
    have hh := Nat.mem_primesBelow.mp hp
    exact Nat.mem_primesBelow.mpr (And.intro (by omega) hh.2)
  have hh :
      (((n + 1).primesBelow \ (P + 1).primesBelow).prod
        (fun p => 1 - eta p + eta p * z)) *
          (P + 1).primesBelow.prod (fun p => 1 - eta p + eta p * z) =
            (n + 1).primesBelow.prod (fun p => 1 - eta p + eta p * z) :=
    Finset.prod_sdiff hsub
  exact hh.symm.trans (mul_comm _ _)

theorem primeTail_product_ratio_eq (P n : Nat) (eta1 eta2 : Nat -> Real) (z : Real) :
    ((n + 1).primesBelow \ (P + 1).primesBelow).prod
      (fun p => (1 + (z - 1) * eta1 p) / (1 + (z - 1) * eta2 p)) =
    (((n + 1).primesBelow \ (P + 1).primesBelow).prod
      (fun p => 1 - eta1 p + eta1 p * z)) /
    (((n + 1).primesBelow \ (P + 1).primesBelow).prod
      (fun p => 1 - eta2 p + eta2 p * z)) := by
  rw [<- Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have h1 : 1 + (z - 1) * eta1 p = 1 - eta1 p + eta1 p * z := by ring
  have h2 : 1 + (z - 1) * eta2 p = 1 - eta2 p + eta2 p * z := by ring
  rw [h1, h2]

theorem regularPrimeLaws_tendsto_full_product_sequence
    (P : Nat) (eta1 eta2 : Nat -> Real) (nu b1 b2 C1 C2 alpha beta : Real)
    (hnu : 0 < nu) (hC1 : 0 <= C1) (hC2 : 0 <= C2)
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hunit1 : forall p, Nat.Prime p -> 0 <= eta1 p /\ eta1 p <= 1)
    (hunit2 : forall p, Nat.Prime p -> 0 <= eta2 p /\ eta2 p <= 1)
    (h1 : forall p, Nat.Prime p -> P < p -> 0 < eta1 p)
    (h2 : forall p, Nat.Prime p -> P < p -> 0 < eta2 p)
    (herr1 : forall p, Nat.Prime p -> P < p ->
      abs (1 / eta1 p - (p : Real) / nu - b1) <= C1 / (p : Real))
    (herr2 : forall p, Nat.Prime p -> P < p ->
      abs (1 / eta2 p - (p : Real) / nu - b2) <= C2 / (p : Real))
    (hscale1 : forall p, Nat.Prime p -> P < p ->
      2 * (nu * (abs b1 + C1)) <= (p : Real))
    (hscale2 : forall p, Nat.Prime p -> P < p ->
      2 * (nu * (abs b2 + C2)) <= (p : Real))
    (n : Nat -> Nat)
    (hband : Filter.Eventually (fun k : Nat => k ^ 2 <= n k /\
      alpha * Real.log (k : Real) <= Real.log (Real.log (n k : Real)) /\
        Real.log (Real.log (n k : Real)) <= beta * Real.log (k : Real)) atTop) :
    let z := fun k : Nat => (k : Real) / (nu * Real.log (Real.log (n k : Real)))
    let s1 := (smallPrimePositiveFront P eta1).length
    let s2 := (smallPrimePositiveFront P eta2).length
    let A1 := (smallPrimePositiveFront P eta1).prod
    let A2 := (smallPrimePositiveFront P eta2).prod
    let C := primeComparisonEulerConstant P eta1 eta2 nu b1 b2
    0 < A1 / A2 * C /\
      Tendsto (fun k : Nat =>
        ((primeBernoulliProduct eta1 (n k) (z k) / (z k) ^ s1) /
          (primeBernoulliProduct eta2 (n k) (z k) / (z k) ^ s2)) /
            Real.rpow (Real.log (z k)) (nu * (b2 - b1))) atTop (nhds (A1 / A2 * C)) := by
  classical
  let z := fun k : Nat => (k : Real) / (nu * Real.log (Real.log (n k : Real)))
  let raw1 := (P + 1).primesBelow.toList.map eta1
  let raw2 := (P + 1).primesBelow.toList.map eta2
  let s1 := (smallPrimePositiveFront P eta1).length
  let s2 := (smallPrimePositiveFront P eta2).length
  let A1 := (smallPrimePositiveFront P eta1).prod
  let A2 := (smallPrimePositiveFront P eta2).prod
  let C := primeComparisonEulerConstant P eta1 eta2 nu b1 b2
  have hraw2 : forall a, List.Mem a raw2 -> 0 <= a := by
    intro a ha
    have hh := List.mem_map.mp ha
    choose p hp using hh
    rw [<- hp.2]
    exact (hunit2 p (Nat.mem_primesBelow.mp (Finset.mem_toList.mp hp.1)).2).1
  have ht := Real.primeTilt_sequence_atTop_and_cutoff nu alpha beta hnu halpha hbeta n hband
  have hp := regularPrimeLaws_tendsto_growing_product_sequence P eta1 eta2 nu b1 b2 C1 C2
    alpha beta hnu hC1 hC2 halpha hbeta h1 h2 herr1 herr2 hscale1 hscale2 n hband
  have hsmall := (List.tendsto_bernoulliProduct_normalized_ratio raw1 raw2 hraw2).comp ht.1
  have hsmall' : Tendsto (fun k : Nat =>
      (primeBernoulliProduct eta1 P (z k) / (z k) ^ s1) /
        (primeBernoulliProduct eta2 P (z k) / (z k) ^ s2)) atTop (nhds (A1 / A2)) := by
    simpa [raw1, raw2, s1, s2, A1, A2, z, smallPrimePositiveFront,
      primeBernoulliProduct, List.map_map, Function.comp_def] using hsmall
  have hA1 : 0 < A1 := (smallPrimePositiveFront_properties P eta1 hunit1).2
  have hA2 : 0 < A2 := (smallPrimePositiveFront_properties P eta2 hunit2).2
  have hC : 0 < C := hp.1
  refine And.intro (mul_pos (div_pos hA1 hA2) hC) ?_
  have hc : Tendsto (fun _ : Nat => C) atTop (nhds C) := tendsto_const_nhds
  have hm := (hsmall'.mul hp.2).mul hc
  have hm' : Tendsto (fun k : Nat =>
      ((primeBernoulliProduct eta1 P (z k) / (z k) ^ s1) /
        (primeBernoulliProduct eta2 P (z k) / (z k) ^ s2)) *
      ((((n k + 1).primesBelow \ (P + 1).primesBelow).prod
        (fun p => (1 + (z k - 1) * eta1 p) / (1 + (z k - 1) * eta2 p))) /
          (C * Real.rpow (Real.log (z k)) (nu * (b2 - b1)))) * C)
        atTop (nhds (A1 / A2 * C)) := by
    simpa only [mul_one] using hm
  apply hm'.congr'
  filter_upwards [ht.1.eventually (eventually_gt_atTop (1 : Real)), hband,
      eventually_ge_atTop (P + 2)] with k hz hk hPk
  have hzp : 0 < z k := zero_lt_one.trans hz
  have hPn : P <= n k := by
    have hk2 : 2 <= k := by omega
    have hkk : k <= k ^ 2 := by nlinarith only [hk2]
    omega
  let T := (n k + 1).primesBelow \ (P + 1).primesBelow
  let T2 := T.prod (fun p => 1 - eta2 p + eta2 p * z k)
  have hS2 : Not (primeBernoulliProduct eta2 P (z k) = 0) :=
    ne_of_gt (primeBernoulliProduct_pos eta2 P (z k) hunit2 hzp)
  have hT2 : Not (T2 = 0) := by
    apply ne_of_gt
    apply Finset.prod_pos
    intro p hp
    have hpp := (Nat.mem_primesBelow.mp (Finset.mem_sdiff.mp hp).1).2
    exact List.bernoulliFactor_pos (eta2 p) (z k) (hunit2 p hpp).1 (hunit2 p hpp).2 hzp
  have hZ1 : Not ((z k) ^ s1 = 0) := pow_ne_zero _ (ne_of_gt hzp)
  have hZ2 : Not ((z k) ^ s2 = 0) := pow_ne_zero _ (ne_of_gt hzp)
  have hR : Not (Real.rpow (Real.log (z k)) (nu * (b2 - b1)) = 0) :=
    ne_of_gt (Real.rpow_pos_of_pos (Real.log_pos hz) _)
  rw [primeTail_product_ratio_eq P (n k) eta1 eta2 (z k),
    primeBernoulliProduct_split P (n k) eta1 (z k) hPn,
    primeBernoulliProduct_split P (n k) eta2 (z k) hPn]
  change
    ((primeBernoulliProduct eta1 P (z k) / (z k) ^ s1) /
      (primeBernoulliProduct eta2 P (z k) / (z k) ^ s2)) *
      ((T.prod (fun p => 1 - eta1 p + eta1 p * z k) / T2) /
        (C * Real.rpow (Real.log (z k)) (nu * (b2 - b1)))) * C =
    (((primeBernoulliProduct eta1 P (z k) *
        T.prod (fun p => 1 - eta1 p + eta1 p * z k)) / (z k) ^ s1) /
      ((primeBernoulliProduct eta2 P (z k) * T2) / (z k) ^ s2)) /
        Real.rpow (Real.log (z k)) (nu * (b2 - b1))
  field_simp [hS2, hT2, hZ1, hZ2, hR, ne_of_gt hC]
  ring_nf
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  ring

end PrimeFactorOscillations
namespace PrimeFactorOscillations

theorem regularPrimeLaw_tendsto_normalized_inverse
    (P : Nat) (eta : Nat -> Real) (nu b C : Real)
    (hnu : 0 < nu) (hC : 0 <= C)
    (herr : forall p, Nat.Prime p -> P < p ->
      abs (1 / eta p - (p : Real) / nu - b) <= C / (p : Real))
    (p : Nat -> Nat) (hp : Tendsto p atTop atTop)
    (hprime : Filter.Eventually (fun k : Nat => Nat.Prime (p k)) atTop) :
    Tendsto (fun k : Nat => (nu / (p k : Real)) * (1 / eta (p k)))
      atTop (nhds 1) := by
  let D := nu * (abs b + C)
  have hD : 0 <= D := mul_nonneg hnu.le (add_nonneg (abs_nonneg _) hC)
  have hpc := (tendsto_natCast_atTop_atTop (R := Real)).comp hp
  have hinv := tendsto_inv_atTop_zero.comp hpc
  have hc : Tendsto (fun _ : Nat => D) atTop (nhds D) := tendsto_const_nhds
  have hz : Tendsto (fun k : Nat => D / (p k : Real)) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using hc.mul hinv
  apply Metric.tendsto_nhds.2
  intro e he
  have hsmall := (Metric.tendsto_nhds.1 hz) e he
  filter_upwards [hsmall, hprime, hp.eventually (eventually_ge_atTop (P + 2))] with
    k hk hpk hPk
  have hx : (1 : Real) <= (p k : Real) := by exact_mod_cast (show 1 <= p k by omega)
  have hbound := Real.normalized_reciprocal_error_bound (p k : Real) nu
    (1 / eta (p k)) b C hx hnu hC (herr (p k) hpk (by omega))
  have hnonneg : 0 <= D / (p k : Real) := div_nonneg hD (Nat.cast_nonneg _)
  have hless : D / (p k : Real) < e := by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using hk
  change abs ((nu / (p k : Real)) * (1 / eta (p k)) - 1) < e
  exact hbound.trans_lt hless

theorem regularPrimeLaws_tendsto_terminal_ratio
    (P : Nat) (eta1 eta2 : Nat -> Real) (nu b1 b2 C1 C2 : Real)
    (hnu : 0 < nu) (hC1 : 0 <= C1) (hC2 : 0 <= C2)
    (h1 : forall p, Nat.Prime p -> P < p -> 0 < eta1 p)
    (h2 : forall p, Nat.Prime p -> P < p -> 0 < eta2 p)
    (herr1 : forall p, Nat.Prime p -> P < p ->
      abs (1 / eta1 p - (p : Real) / nu - b1) <= C1 / (p : Real))
    (herr2 : forall p, Nat.Prime p -> P < p ->
      abs (1 / eta2 p - (p : Real) / nu - b2) <= C2 / (p : Real))
    (p : Nat -> Nat) (hp : Tendsto p atTop atTop)
    (hprime : Filter.Eventually (fun k : Nat => Nat.Prime (p k)) atTop) :
    Tendsto (fun k : Nat => eta1 (p k) / eta2 (p k)) atTop (nhds 1) := by
  have ht1 := regularPrimeLaw_tendsto_normalized_inverse P eta1 nu b1 C1 hnu hC1
    herr1 p hp hprime
  have ht2 := regularPrimeLaw_tendsto_normalized_inverse P eta2 nu b2 C2 hnu hC2
    herr2 p hp hprime
  have hh := ht2.div ht1 (by norm_num : Not ((1 : Real) = 0))
  have hh' : Tendsto (fun k : Nat =>
      ((nu / (p k : Real)) * (1 / eta2 (p k))) /
        ((nu / (p k : Real)) * (1 / eta1 (p k)))) atTop (nhds 1) := by
    change Tendsto (fun k : Nat =>
      ((nu / (p k : Real)) * (1 / eta2 (p k))) /
        ((nu / (p k : Real)) * (1 / eta1 (p k)))) atTop (nhds ((1 : Real) / 1)) at hh
    simpa only [div_one] using hh
  apply hh'.congr'
  filter_upwards [hprime, hp.eventually (eventually_ge_atTop (P + 2))] with k hk hPk
  have hn : 0 < (p k : Real) := by exact_mod_cast (show 0 < p k by omega)
  have hne1 : Not (eta1 (p k) = 0) := ne_of_gt (h1 (p k) hk (by omega))
  have hne2 : Not (eta2 (p k) = 0) := ne_of_gt (h2 (p k) hk (by omega))
  field_simp [ne_of_gt hnu, ne_of_gt hn, hne1, hne2]

end PrimeFactorOscillations

