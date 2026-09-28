import PrimeFactorOscillations.Helpers.ReciprocalSmoothPrefixes
import PrimeFactorOscillations.Helpers.ReciprocalSmoothSteps

/-! # Sharp broad-band signs and tail cutoffs for reciprocal-smooth densities -/

set_option autoImplicit false
set_option Elab.async false

open Filter

namespace PrimeFactorOscillations.ReciprocalSmoothLaw

private theorem normalized_ratio_band (nu u v L k R delta : Real)
    (hnu : 0 < nu) (hu : 0 < u) (hk : 0 < k)
    (hlo : u * k <= L) (hhi : L <= v * k)
    (hd : delta < 1)
    (hnear : abs (nu * L * R / k - 1) <= delta) :
    0 < R /\ 1 - delta <= nu * v * R /\ nu * u * R <= 1 + delta := by
  have hL : 0 < L := (mul_pos hu hk).trans_le hlo
  have hb := abs_le.mp hnear
  have hc : (nu * L * R / k) * k = nu * L * R := by field_simp
  have hlow := mul_le_mul_of_nonneg_right hb.1 hk.le
  have hhigh := mul_le_mul_of_nonneg_right hb.2 hk.le
  have hm : (nu * L * R / k - 1) * k = nu * L * R - k := by
    rw [sub_mul, hc, one_mul]
  rw [hm] at hlow hhigh
  have hp : 0 < R := by
    by_contra hn
    have hnon := mul_nonpos_of_nonneg_of_nonpos (mul_pos hnu hL).le (le_of_not_gt hn)
    have hstrict := mul_pos (by linarith only [hd] : 0 < 1 - delta) hk
    nlinarith only [hlow, hnon, hstrict]
  have hscalehi := mul_le_mul_of_nonneg_left hhi (mul_pos hnu hp).le
  have hscalelo := mul_le_mul_of_nonneg_left hlo (mul_pos hnu hp).le
  refine And.intro hp (And.intro ?_ ?_)
  next =>
    by_contra hn
    have h := mul_lt_mul_of_pos_right (lt_of_not_ge hn) hk
    nlinarith only [hlow, hscalehi, h]
  next =>
    by_contra hn
    have h := mul_lt_mul_of_pos_right (lt_of_not_ge hn) hk
    nlinarith only [hhigh, hscalelo, h]

/-- Short gaps force ascent throughout every fixed band below 1/(H+nu).
An independently chosen long-gap threshold forces descent on the same band.
All finite exceptional primes are retained behind one fixed cutoff P. -/
theorem rank_density_gap_signs_on_broad_band
    (law : ReciprocalSmoothLaw) (H D : Nat) (u v : Real)
    (hu : 0 < u) (hv : 0 < v)
    (hmargin : ((H : Real) + law.nu) * v < 1)
    (hD : 2 / u < (D : Real)) :
    exists P : Nat, Filter.Eventually (fun k : Nat => forall p q : Nat,
      3 <= p -> P <= p -> Nat.Prime p -> Nat.Prime q -> p < q ->
      (forall t : Nat, p < t -> t < q -> Not (Nat.Prime t)) ->
      u * k <= Real.log (Real.log (p - 1 : Nat)) ->
      Real.log (Real.log (p - 1 : Nat)) <= v * k ->
      (q <= p + H -> law.rankDensityAt k p < law.rankDensityAt k q) /\
      (p + D <= q -> law.rankDensityAt k q < law.rankDensityAt k p)) Filter.atTop := by
  let M := 1 - ((H : Real) + law.nu) * v
  let delta := M / 4
  let epsilon := min (1 / 2) (M / (4 * law.nu * v))
  have hM : 0 < M := by dsimp [M]; linarith only [hmargin]
  have hM1 : M <= 1 := by
    have h := mul_nonneg (add_nonneg (Nat.cast_nonneg H) law.nu_pos.le) hv.le
    dsimp [M]
    linarith only [h]
  have hdpos : 0 < delta := div_pos hM (by norm_num)
  have hdquarter : delta <= 1 / 4 := by dsimp [delta]; linarith only [hM1]
  have hepos : 0 < epsilon := lt_min (by norm_num)
    (div_pos hM (mul_pos (mul_pos (by norm_num) law.nu_pos) hv))
  have hehalf : epsilon <= 1 / 2 := min_le_left _ _
  have hesmall : epsilon <= M / (4 * law.nu * v) := min_le_right _ _
  choose P0 hP0 using law.eventually_probability_interior
  choose P1 hP1 using law.eventually_gap_threshold_bounds epsilon hepos
  refine Exists.intro (max P0 P1) ?_
  have hr := law.prime_prefix_uniform_normalized_ratio u hu delta hdpos
  filter_upwards [hr, Filter.eventually_ge_atTop 2] with k hk hk2
  intro p q hp3 hpP hpp hqp hpq hgap hlow hhigh
  have hp0 : P0 <= p := (le_max_left P0 P1).trans hpP
  have hp1 : P1 <= p := (le_max_right P0 P1).trans hpP
  have ha := (hP0 p hp0 hpp).1
  have hb := (hP0 q (hp0.trans hpq.le) hqp).1
  have hthreshold := hP1 p q hp1 hpq.le hpp hqp
  have hcut : p - 1 + 1 = p := by omega
  have hratio := hk (p - 1) (by omega) hlow
  rw [hcut] at hratio
  change 0 < law.prefixMass p (k - 1) /\
    abs (law.nu * Real.log (Real.log (p - 1 : Nat)) *
      (law.prefixMass p (k - 2) / law.prefixMass p (k - 1)) / (k : Real) - 1)
      <= delta at hratio
  let R := law.prefixMass p (k - 2) / law.prefixMass p (k - 1)
  have hkR : (0 : Real) < k := by exact_mod_cast (show 0 < k by omega)
  have hband := normalized_ratio_band law.nu u v
    (Real.log (Real.log (p - 1 : Nat))) k R delta law.nu_pos hu hkR hlow hhigh
    (by linarith only [hdquarter]) hratio.2
  have hnu : Not (law.nu = 0) := ne_of_gt law.nu_pos
  have hv0 : Not (v = 0) := ne_of_gt hv
  have hsmall := mul_le_mul_of_nonneg_right hesmall (mul_pos law.nu_pos hv).le
  have hecancel : (M / (4 * law.nu * v)) * (law.nu * v) = M / 4 := by
    field_simp
  rw [hecancel] at hsmall
  have htarget : law.nu * v * ((H : Real) / law.nu + 1 + epsilon) < 1 - delta := by
    have hcancel : law.nu * v * ((H : Real) / law.nu + 1 + epsilon) =
        ((H : Real) + law.nu) * v + epsilon * (law.nu * v) := by
      field_simp
    rw [hcancel]
    dsimp [M, delta] at hsmall hM
    dsimp [delta, M]
    linarith only [hsmall, hM]
  have hshortR : (H : Real) / law.nu + 1 + epsilon < R := by
    by_contra hn
    have h := mul_le_mul_of_nonneg_left (le_of_not_gt hn) (mul_pos law.nu_pos hv).le
    exact not_lt_of_ge (hband.2.1.trans h) htarget
  have hupper : law.nu * u * R < 2 := by linarith only [hband.2.2, hdquarter]
  have hDmul := mul_lt_mul_of_pos_right hD hu
  have hDcancel : (2 / u) * u = (2 : Real) := by field_simp
  rw [hDcancel] at hDmul
  have hlongR : R < (D : Real) / law.nu := by
    by_contra hn
    have h := mul_le_mul_of_nonneg_left (le_of_not_gt hn) (mul_pos law.nu_pos hu).le
    have hc : law.nu * u * ((D : Real) / law.nu) = (D : Real) * u := by field_simp
    rw [hc] at h
    linarith only [h, hupper, hDmul]
  constructor
  next =>
    intro hshort
    apply (law.rank_density_ascent_iff k p q hk2 hpp hpq hgap ha hb hratio.1).mpr
    have hg : ((q - p : Nat) : Real) <= H := by exact_mod_cast (show q - p <= H by omega)
    have hdiv := div_le_div_of_nonneg_right hg law.nu_pos.le
    have ht : 1 / law.eta q - 1 / law.eta p + 1 <=
        (H : Real) / law.nu + 1 + epsilon := by
      linarith only [hthreshold.2, hdiv]
    exact ht.trans_lt hshortR
  next =>
    intro hlong
    apply (law.rank_density_descent_iff k p q hk2 hpp hpq hgap ha hb hratio.1).mpr
    have hg : (D : Real) <= ((q - p : Nat) : Real) := by
      exact_mod_cast (show D <= q - p by omega)
    have hdiv := div_le_div_of_nonneg_right hg law.nu_pos.le
    exact hlongR.trans_le (by linarith only [hthreshold.1, hdiv, hehalf])

/-- Every gap of size at least H forces descent beyond any fixed rank scale
a strictly greater than 1/(H+nu). This is uniform in both prime endpoints,
without an upper restriction on their size. -/
theorem rank_density_descent_beyond_gap_scale
    (law : ReciprocalSmoothLaw) (H : Nat) (a : Real) (ha : 0 < a)
    (hmargin : 1 < ((H : Real) + law.nu) * a) :
    exists P : Nat, Filter.Eventually (fun k : Nat => forall p q : Nat,
      3 <= p -> P <= p -> Nat.Prime p -> Nat.Prime q -> p < q ->
      (forall t : Nat, p < t -> t < q -> Not (Nat.Prime t)) ->
      p + H <= q ->
      a * k <= Real.log (Real.log (p - 1 : Nat)) ->
      law.rankDensityAt k q < law.rankDensityAt k p) Filter.atTop := by
  let M := ((H : Real) + law.nu) * a - 1
  let delta := min (1 / 2) (M / 4)
  let epsilon := min (1 / 2) (M / (4 * law.nu * a))
  have hM : 0 < M := by dsimp [M]; linarith only [hmargin]
  have hdpos : 0 < delta := lt_min (by norm_num) (div_pos hM (by norm_num))
  have hdhalf : delta <= 1 / 2 := min_le_left _ _
  have hdsmall : delta <= M / 4 := min_le_right _ _
  have hepos : 0 < epsilon := lt_min (by norm_num)
    (div_pos hM (mul_pos (mul_pos (by norm_num) law.nu_pos) ha))
  have hesmall : epsilon <= M / (4 * law.nu * a) := min_le_right _ _
  choose P0 hP0 using law.eventually_probability_interior
  choose P1 hP1 using law.eventually_gap_threshold_bounds epsilon hepos
  refine Exists.intro (max P0 P1) ?_
  have hr := law.prime_prefix_uniform_normalized_ratio a ha delta hdpos
  filter_upwards [hr, Filter.eventually_ge_atTop 2] with k hk hk2
  intro p q hp3 hpP hpp hqp hpq hgap hH hlow
  have hp0 : P0 <= p := (le_max_left P0 P1).trans hpP
  have hp1 : P1 <= p := (le_max_right P0 P1).trans hpP
  have hpa := (hP0 p hp0 hpp).1
  have hqa := (hP0 q (hp0.trans hpq.le) hqp).1
  have hthreshold := (hP1 p q hp1 hpq.le hpp hqp).1
  have hcut : p - 1 + 1 = p := by omega
  have hratio := hk (p - 1) (by omega) hlow
  rw [hcut] at hratio
  change 0 < law.prefixMass p (k - 1) /\
    abs (law.nu * Real.log (Real.log (p - 1 : Nat)) *
      (law.prefixMass p (k - 2) / law.prefixMass p (k - 1)) / (k : Real) - 1)
      <= delta at hratio
  let R := law.prefixMass p (k - 2) / law.prefixMass p (k - 1)
  let L := Real.log (Real.log (p - 1 : Nat))
  have hkR : (0 : Real) < k := by exact_mod_cast (show 0 < k by omega)
  have hhi : L <= (L / (k : Real)) * k := by
    have hc : (L / (k : Real)) * k = L := by field_simp
    rw [hc]
  have hband := normalized_ratio_band law.nu a (L / (k : Real))
    L k R delta law.nu_pos ha hkR hlow hhi
    (by linarith only [hdhalf]) hratio.2
  have hnu : Not (law.nu = 0) := ne_of_gt law.nu_pos
  have ha0 : Not (a = 0) := ne_of_gt ha
  have hsmall := mul_le_mul_of_nonneg_right hesmall (mul_pos law.nu_pos ha).le
  have hecancel : (M / (4 * law.nu * a)) * (law.nu * a) = M / 4 := by
    field_simp
  rw [hecancel] at hsmall
  have htarget : 1 + delta < law.nu * a * ((H : Real) / law.nu + 1 - epsilon) := by
    have hc : law.nu * a * ((H : Real) / law.nu + 1 - epsilon) =
        ((H : Real) + law.nu) * a - epsilon * (law.nu * a) := by field_simp
    rw [hc]
    dsimp [M] at hsmall hdsmall hM
    linarith only [hsmall, hdsmall, hM]
  have hR : R < (H : Real) / law.nu + 1 - epsilon := by
    by_contra hn
    have h := mul_le_mul_of_nonneg_left (le_of_not_gt hn) (mul_pos law.nu_pos ha).le
    exact not_lt_of_ge (h.trans hband.2.2) htarget
  apply (law.rank_density_descent_iff k p q hk2 hpp hpq hgap hpa hqa hratio.1).mpr
  have hg : (H : Real) <= ((q - p : Nat) : Real) := by
    exact_mod_cast (show H <= q - p by omega)
  have hdiv := div_le_div_of_nonneg_right hg law.nu_pos.le
  exact hR.trans_le (by linarith only [hthreshold, hdiv])

end PrimeFactorOscillations.ReciprocalSmoothLaw
