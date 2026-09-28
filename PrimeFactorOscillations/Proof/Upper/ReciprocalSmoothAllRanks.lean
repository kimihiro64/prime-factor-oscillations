import PrimeFactorOscillations.Helpers.PrimeConsecutive
import PrimeFactorOscillations.Helpers.ReciprocalSmoothFixedRanks
import PrimeFactorOscillations.Helpers.ReciprocalSmoothSteps
import PrimeFactorOscillations.Proof.Upper.FiniteMaximum

/-! # Eventual weak descent and finite reversal maxima at every fixed rank -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.ReciprocalSmoothLaw
open scoped Classical

theorem eventually_rank_density_nonincreasing (law : ReciprocalSmoothLaw) (k : Nat) :
    exists T : Nat, forall i : Nat, T <= i ->
      law.rankDensity k (i + 1) <= law.rankDensity k i := by
  have mass_nonneg (s : List Real)
      (hs : forall a, List.Mem a s -> 0 <= a /\ a <= 1) (r : Nat) :
      0 <= List.bernoulliMass s r := by
    induction s generalizing r with
    | nil => cases r <;> simp [List.bernoulliMass]
    | cons a s ih =>
        have ha := hs a (List.Mem.head _)
        have ht : forall b, List.Mem b s -> 0 <= b /\ b <= 1 :=
          fun b hb => hs b (List.Mem.tail _ hb)
        cases r with
        | zero =>
            exact mul_nonneg (sub_nonneg.mpr ha.2) (ih ht 0)
        | succ r =>
            exact add_nonneg (mul_nonneg (sub_nonneg.mpr ha.2) (ih ht (r + 1)))
              (mul_nonneg ha.1 (ih ht r))
  have hmass (p r : Nat) : 0 <= law.prefixMass p r :=
    mass_nonneg (law.prefixProbabilities p) (law.prime_prefix_probability_bounds p) r
  choose P0 hP0 using law.eventually_gap_threshold_bounds (1 / 2) (by norm_num)
  choose P1 hP1 using law.eventually_probability_interior
  have hmasses : exists P : Nat, forall p : Nat, P <= p -> 2 <= k ->
      law.prefixMass p (k - 2) <= (1 / 2 : Real) * law.prefixMass p (k - 1) := by
    by_cases hk : 2 <= k
    next =>
      choose P hP using law.eventually_prefix_previous_le_half (k - 1) (by omega)
      refine Exists.intro P ?_
      intro p hp _
      have hid : k - 1 - 1 = k - 2 := by omega
      simpa only [hid] using hP p hp
    next =>
      exact Exists.intro 0 (fun p _ h => (hk h).elim)
  choose P2 hP2 using hmasses
  refine Exists.intro (max P0 (max P1 P2)) ?_
  intro i hi
  let p := PrimeFactorUnimodality.primeAt i
  let q := PrimeFactorUnimodality.primeAt (i + 1)
  have hp := PrimeFactorUnimodality.prime_primeAt i
  have hq := PrimeFactorUnimodality.prime_primeAt (i + 1)
  have hpq : p < q := PrimeFactorUnimodality.primeAt_strictMono (Nat.lt_succ_self i)
  have hip : i + 2 <= p := Nat.add_two_le_nth_prime i
  have hp0 : P0 <= p := by omega
  have hp1 : P1 <= p := by omega
  have hp2 : P2 <= p := by omega
  have ha := (hP1 p hp1 hp).1
  have hb := (hP1 q (hp1.trans hpq.le) hq).1
  have hthreshold : (1 / 2 : Real) <= 1 / law.eta q - 1 / law.eta p + 1 := by
    have h := (hP0 p q hp0 hpq.le hp hq).1
    have hg : (0 : Real) <= ((q - p : Nat) : Real) / law.nu :=
      div_nonneg (Nat.cast_nonneg _) law.nu_pos.le
    linarith only [h, hg]
  have hgap : forall t : Nat, p < t -> t < q -> Not (Nat.Prime t) :=
    fun t htlo hthi => no_prime_between_consecutive_indexed i t htlo hthi
  change law.rankDensityAt k q <= law.rankDensityAt k p
  by_cases hk : 2 <= k
  next =>
    have hhalf := hP2 p hp2 hk
    have hinside : law.prefixMass p (k - 2) -
        (1 / law.eta q - 1 / law.eta p + 1) * law.prefixMass p (k - 1) <= 0 := by
      nlinarith only [hhalf, hthreshold, hmass p (k - 1)]
    have hmain := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ha.le hb.le) hinside
    have hindex : k - 2 + 1 = k - 1 := by omega
    have hstep : law.prefixMass q (k - 1) =
        (1 - law.eta p) * law.prefixMass p (k - 1) +
          law.eta p * law.prefixMass p (k - 2) := by
      rw [law.prefix_mass_at_next_prime p q (k - 1) hp hpq hgap, <- hindex,
        List.bernoulliMass]
      rfl
    have hid : law.rankDensityAt k q - law.rankDensityAt k p =
        (law.eta p * law.eta q) * (law.prefixMass p (k - 2) -
          (1 / law.eta q - 1 / law.eta p + 1) * law.prefixMass p (k - 1)) := by
      unfold rankDensityAt
      rw [hstep]
      field_simp [ne_of_gt ha, ne_of_gt hb]
      ring
    linarith only [hid, hmain]
  next =>
    have hindex : k - 1 = 0 := by omega
    have hscale : 0 <= law.eta p * law.eta q *
        (1 / law.eta q - 1 / law.eta p + 1) :=
      mul_nonneg (mul_nonneg ha.le hb.le) (by linarith only [hthreshold])
    have hid : law.eta p * law.eta q *
        (1 / law.eta q - 1 / law.eta p + 1) =
        law.eta p - law.eta q + law.eta p * law.eta q := by
      field_simp [ne_of_gt ha, ne_of_gt hb]
    have hcoeff : law.eta q * (1 - law.eta p) <= law.eta p := by
      rw [hid] at hscale
      nlinarith only [hscale]
    unfold rankDensityAt
    rw [hindex, law.prefix_mass_at_next_prime p q 0 hp hpq hgap, List.bernoulliMass]
    simpa only [prefixMass, mul_assoc] using
      mul_le_mul_of_nonneg_right hcoeff (hmass p 0)

theorem exists_reversal_number_all_ranks (law : ReciprocalSmoothLaw) (k : Nat) :
    exists N : Nat, HasReversalNumber (law.rankDensity k) N := by
  choose T hT using law.eventually_rank_density_nonincreasing k
  choose N hN using PrimeFactorOscillations.exists_reversalNumber_of_tail
    (law.rankDensity k) T hT
  exact Exists.intro N hN.1

end PrimeFactorOscillations.ReciprocalSmoothLaw
