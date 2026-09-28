import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Definitions.ReciprocalSmoothLaw

/-! # Reciprocal-smooth laws: actual odds estimates -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.ReciprocalSmoothLaw

private theorem reciprocal_perturbation_bounds (a t D : Real)
    (ha : 0 < a) (hD : 0 <= D) (herror : abs (t - a) <= D)
    (hlarge : 2 * D <= a) :
    0 < t /\ 0 < 1 / t /\ 1 / t <= 2 / a /\
      abs (1 / t - 1 / a) <= 2 * D / a ^ 2 := by
  have he := abs_le.mp herror
  have hhalf : a / 2 <= t := by linarith only [he.1, hlarge]
  have ht : 0 < t := (half_pos ha).trans_le hhalf
  refine And.intro ht (And.intro (one_div_pos.mpr ht) (And.intro ?_ ?_))
  next =>
    have h := div_le_div_of_nonneg_left (by norm_num : (0 : Real) <= 1)
      (half_pos ha) hhalf
    have hc : 1 / (a / 2) = 2 / a := by field_simp
    simpa only [hc] using h
  next =>
    have hidentity : 1 / t - 1 / a = (a - t) / (t * a) := by
      field_simp
    have hprod : 0 < t * a := mul_pos ht ha
    have hnum : abs (a - t) <= D := by simpa only [abs_sub_comm] using herror
    calc
      abs (1 / t - 1 / a) = abs (a - t) / (t * a) := by
        rw [hidentity, abs_div, abs_of_pos hprod]
      _ <= D / (t * a) := div_le_div_of_nonneg_right hnum hprod.le
      _ <= D / ((a / 2) * a) :=
        div_le_div_of_nonneg_left hD (mul_pos (half_pos ha) ha)
          (mul_le_mul_of_nonneg_right hhalf ha.le)
      _ = 2 * D / a ^ 2 := by field_simp

/-- The odds themselves, not an assumed auxiliary weight, have a uniform
inverse-prime upper bound and a summable inverse-square error on the prime tail. -/
theorem eventually_odds_bounds (law : ReciprocalSmoothLaw) :
    exists D : Real, 0 < D /\ exists P : Nat,
      forall p : Nat, P <= p -> Nat.Prime p ->
        0 < law.eta p / (1 - law.eta p) /\
        law.eta p / (1 - law.eta p) <= 2 * law.nu / p /\
        abs (law.eta p / (1 - law.eta p) - law.nu / p) <=
          D / (p : Real) ^ 2 := by
  let M := abs (law.offset - 1) + 1
  have hM : 0 < M := by dsimp [M]; positivity
  choose P0 hP0 using law.reciprocal_control 1 (by norm_num)
  choose P1 hP1 using law.eventually_probability_interior
  choose P2 hP2 using exists_nat_gt (2 * law.nu * M)
  refine Exists.intro (2 * law.nu ^ 2 * M)
    (And.intro (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos law.nu_pos)) hM)
    (Exists.intro (max P0 (max P1 P2)) ?_))
  intro p hp hprime
  have hp0 := (le_max_left P0 (max P1 P2)).trans hp
  have hp1 := (le_max_left P1 P2).trans ((le_max_right P0 (max P1 P2)).trans hp)
  have hp2 := (le_max_right P1 P2).trans ((le_max_right P0 (max P1 P2)).trans hp)
  have hi := hP1 p hp1 hprime
  have hpR : 0 < (p : Real) := by exact_mod_cast hprime.pos
  have happrox := abs_le.mp (hP0 p hp0 hprime)
  have hscale : 2 * M <= (p : Real) / law.nu := by
    have hp2R : (P2 : Real) <= p := by exact_mod_cast hp2
    have hc : ((p : Real) / law.nu) * law.nu = p := by
      field_simp [ne_of_gt law.nu_pos]
    nlinarith only [hP2, hp2R, hc, law.nu_pos]
  have herr : abs ((1 / law.eta p - 1) - (p : Real) / law.nu) <= M := by
    apply abs_le.mpr
    have hlo := neg_abs_le (law.offset - 1)
    have hhi := le_abs_self (law.offset - 1)
    dsimp [M]
    constructor <;> linarith only [happrox.1, happrox.2, hlo, hhi]
  have h := reciprocal_perturbation_bounds ((p : Real) / law.nu)
    (1 / law.eta p - 1) M (div_pos hpR law.nu_pos) hM.le herr hscale
  have hw : law.eta p / (1 - law.eta p) = 1 / (1 / law.eta p - 1) := by
    field_simp [ne_of_gt hi.1, ne_of_gt (sub_pos.mpr hi.2)]
  have hnu : 1 / ((p : Real) / law.nu) = law.nu / p := by field_simp
  have htwo : 2 / ((p : Real) / law.nu) = 2 * law.nu / p := by field_simp
  have herror : 2 * M / ((p : Real) / law.nu) ^ 2 =
      (2 * law.nu ^ 2 * M) / (p : Real) ^ 2 := by field_simp
  rw [hw]
  exact And.intro h.2.1 (And.intro (by simpa only [htwo] using h.2.2.1)
    (by simpa only [hnu, herror] using h.2.2.2))

/-- All non-forced prime odds admit one fixed inverse-prime majorant.
No uniform bound over the class of laws is asserted. -/
theorem odds_global_majorant (law : ReciprocalSmoothLaw) :
    exists C : Real, 0 < C /\ forall p : Nat, Nat.Prime p ->
      law.eta p < 1 ->
      0 <= law.eta p / (1 - law.eta p) /\
      law.eta p / (1 - law.eta p) <= C / p := by
  choose D hD P hP using law.eventually_odds_bounds
  let w := fun p : Nat => law.eta p / (1 - law.eta p)
  let B := (Finset.range P).sum (fun p => abs ((p : Real) * w p))
  have hB : 0 <= B := Finset.sum_nonneg (fun p _ => abs_nonneg _)
  let C := 2 * law.nu + B
  have hC : 0 < C := by dsimp [C]; linarith only [law.nu_pos, hB]
  refine Exists.intro C (And.intro hC ?_)
  intro p hprime heta
  have hp : 0 < (p : Real) := by exact_mod_cast hprime.pos
  refine And.intro
    (div_nonneg (law.probability p hprime).1 (sub_pos.mpr heta).le) ?_
  change w p <= C / (p : Real)
  by_cases hlarge : P <= p
  next =>
    have htail := (hP p hlarge hprime).2.1
    have hnum : 2 * law.nu <= C := by dsimp [C]; linarith only [hB]
    exact htail.trans (div_le_div_of_nonneg_right hnum hp.le)
  next =>
    have hmem : p < P := lt_of_not_ge hlarge
    have hterm : abs ((p : Real) * w p) <= B :=
      Finset.single_le_sum (fun (q : Nat) _ => abs_nonneg ((q : Real) * w q))
        (Finset.mem_range.mpr hmem)
    have hbound : (p : Real) * w p <= C := by
      have h := le_abs_self ((p : Real) * w p)
      dsimp [C]
      linarith only [h, hterm, law.nu_pos]
    have hc : (C / (p : Real)) * p = C := by field_simp
    nlinarith only [hbound, hc, hp]

/-- The reciprocal-smooth law has one global inverse-square error constant.
At forced primes the field-valued odds are zero; the finite head absorbs their
error, and they must still be removed with an exact rank shift in a density. -/
theorem odds_global_error (law : ReciprocalSmoothLaw) :
    exists D : Real, 0 < D /\ forall p : Nat, Nat.Prime p ->
      abs (law.eta p / (1 - law.eta p) - law.nu / p) <= D / (p : Real) ^ 2 := by
  choose D hD P hP using law.eventually_odds_bounds
  let e := fun p : Nat => law.eta p / (1 - law.eta p) - law.nu / p
  let B := (Finset.range P).sum (fun p => (p : Real) ^ 2 * abs (e p))
  have hB : 0 <= B :=
    Finset.sum_nonneg (fun p _ => mul_nonneg (sq_nonneg (p : Real)) (abs_nonneg _))
  let C := D + B
  have hC : 0 < C := by dsimp [C]; linarith only [hD, hB]
  refine Exists.intro C (And.intro hC ?_)
  intro p hprime
  have hp : 0 < (p : Real) := by exact_mod_cast hprime.pos
  change abs (e p) <= C / (p : Real) ^ 2
  by_cases hlarge : P <= p
  next =>
    have htail := (hP p hlarge hprime).2.2
    have hnum : D <= C := by dsimp [C]; linarith only [hB]
    exact htail.trans (div_le_div_of_nonneg_right hnum (sq_nonneg (p : Real)))
  next =>
    have hmem : p < P := lt_of_not_ge hlarge
    have hterm : (p : Real) ^ 2 * abs (e p) <= B :=
      Finset.single_le_sum
        (fun (q : Nat) _ => mul_nonneg (sq_nonneg (q : Real)) (abs_nonneg (e q)))
        (Finset.mem_range.mpr hmem)
    have hbound : (p : Real) ^ 2 * abs (e p) <= C := by
      dsimp [C]
      linarith only [hterm, hD]
    have hc : (C / (p : Real) ^ 2) * (p : Real) ^ 2 = C := by field_simp
    have hsq : 0 < (p : Real) ^ 2 := sq_pos_of_pos hp
    nlinarith only [hbound, hc, hsq]

end PrimeFactorOscillations.ReciprocalSmoothLaw
