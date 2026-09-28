import PrimeFactorOscillations.Proof.AffinePairs.NormalizedProgressions

/-! # Prime probabilities in every residue class of a fixed modulus -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

open scoped Classical

theorem nonunit_prime_progression_count_le
    (q : Nat) (hq : 1 <= q) (a : ZMod q) (ha : Not (IsUnit a)) (N : Nat) :
    Real.primeCountingZMod (N : Real) q a <= q + 1 := by
  classical
  unfold Real.primeCountingZMod
  calc
    _ <= ((Finset.range (q + 1) : Finset Nat) : Set Nat).ncard := by
      apply Set.ncard_le_ncard _ (Finset.finite_toSet _)
      intro r hr
      have hd : Dvd.dvd r q := by
        by_contra hn
        have hu := ZMod.isUnit_prime_of_not_dvd hr.1 hn
        rw [hr.2.1] at hu
        exact ha hu
      have hle := Nat.le_of_dvd (show 0 < q by omega) hd
      exact Finset.mem_range.mpr (by omega)
    _ = q + 1 := by simp only [Set.ncard_coe_finset, Finset.card_range]

theorem tendsto_nonunit_prime_progression_probability
    (q : Nat) (hq : 1 <= q) (a : ZMod q) (ha : Not (IsUnit a)) :
    Filter.Tendsto (fun N : Nat =>
      (Real.primeCountingZMod (N : Real) q a : Real) / (Nat.primeCounting N : Real))
      Filter.atTop (nhds 0) := by
  apply Metric.tendsto_atTop.mpr
  intro epsilon he
  have hpi : Filter.Tendsto (fun N : Nat => (Nat.primeCounting N : Real))
      Filter.atTop Filter.atTop := tendsto_natCast_atTop_atTop.comp Nat.tendsto_primeCounting
  have hev := hpi.eventually
    (Filter.eventually_ge_atTop (((q + 1 : Nat) : Real) / epsilon + 1))
  choose K hK using Filter.eventually_atTop.mp hev
  refine Exists.intro K ?_
  intro N hN
  have hb : (((q + 1 : Nat) : Real) / epsilon) < (Nat.primeCounting N : Real) :=
    (lt_add_one _).trans_le (hK N hN)
  have hn : 0 < (Nat.primeCounting N : Real) :=
    (div_nonneg (by positivity) he.le).trans_lt hb
  have hc : (Real.primeCountingZMod (N : Real) q a : Real) <= (q + 1 : Nat) := by
    exact_mod_cast nonunit_prime_progression_count_le q hq a ha N
  have hratio : (Real.primeCountingZMod (N : Real) q a : Real) /
      (Nat.primeCounting N : Real) < epsilon := by
    have hbound := mul_lt_mul_of_pos_right hb he
    have hec : (((q + 1 : Nat) : Real) / epsilon) * epsilon = (q + 1 : Nat) := by
      field_simp [ne_of_gt he]
    rw [hec] at hbound
    have hnc : ((Real.primeCountingZMod (N : Real) q a : Real) /
        (Nat.primeCounting N : Real)) * (Nat.primeCounting N : Real) =
        (Real.primeCountingZMod (N : Real) q a : Real) := by
      field_simp [ne_of_gt hn]
    by_contra hnot
    have hmul := mul_le_mul_of_nonneg_right (le_of_not_gt hnot) hn.le
    rw [hnc] at hmul
    nlinarith only [hc, hbound, hmul]
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity :
    0 <= (Real.primeCountingZMod (N : Real) q a : Real) /
      (Nat.primeCounting N : Real))] using hratio

theorem tendsto_all_prime_progression_probabilities
    (q : Nat) (hq : 1 <= q) (a : ZMod q) :
    Filter.Tendsto (fun N : Nat =>
      (Real.primeCountingZMod (N : Real) q a : Real) / (Nat.primeCounting N : Real))
      Filter.atTop (nhds (if IsUnit a then 1 / (q.totient : Real) else 0)) := by
  classical
  by_cases ha : IsUnit a
  case pos =>
    rw [ite_eq_left ha]
    choose u hu using ha
    rw [<- hu]
    exact tendsto_prime_progression_probability q hq u
  case neg =>
    rw [ite_eq_right ha]
    exact tendsto_nonunit_prime_progression_probability q hq a ha

end PrimeFactorOscillations
