import PrimeFactorOscillations.Helpers.GapSpectrum

/-! # Finite phase reduction of the actual prime-gap spectrum -/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations

private theorem gap_ratio_le_full_class (H J : Nat) (nu : Real)
    (hnu : 0 < nu) (hJH : J <= H) :
    primeGapFrequencyExponent H / ((H : Real) + nu) <=
      1 / ((J : Real) + nu) := by
  have hHpos : 0 < (H : Real) + nu := by positivity
  have hJpos : 0 < (J : Real) + nu := by positivity
  have hgamma := primeGapFrequencyExponent_bounds H
  have hratio : 0 <= primeGapFrequencyExponent H / ((H : Real) + nu) :=
    div_nonneg hgamma.1 hHpos.le
  have hc : (primeGapFrequencyExponent H / ((H : Real) + nu)) *
      ((H : Real) + nu) = primeGapFrequencyExponent H := by
    field_simp [ne_of_gt hHpos]
  have hinv : (1 / ((J : Real) + nu)) * ((J : Real) + nu) = (1 : Real) := by
    field_simp [ne_of_gt hJpos]
  have hdiff : (0 : Real) <= (H : Real) - J := by
    exact sub_nonneg.mpr (by exact_mod_cast hJH)
  have hcost := mul_nonneg hratio hdiff
  by_contra hn
  have hm := mul_lt_mul_of_pos_right (lt_of_not_ge hn) hJpos
  rw [hinv] at hm
  nlinarith only [hm, hcost, hc, hgamma.2]

/-- Any full-frequency gap class cuts the infinite spectrum down to a finite
attained maximum, simultaneously for every positive dimension. -/
theorem primeGapSpectrum_finite_maximum
    (J : Nat) (hJ : 2 <= J) (hfull : primeGapFrequencyExponent J = 1)
    (nu : Real) (hnu : 0 < nu) :
    exists H : Nat, 2 <= H /\ H <= J /\
      primeGapSpectrum nu = primeGapFrequencyExponent H / ((H : Real) + nu) := by
  classical
  let f := fun H : Nat => primeGapFrequencyExponent H / ((H : Real) + nu)
  choose H hH using Finset.exists_max_image (Finset.Icc 2 J) f
    (Finset.nonempty_Icc.mpr hJ)
  have hbounds := Finset.mem_Icc.mp hH.1
  refine Exists.intro H (And.intro hbounds.1 (And.intro hbounds.2 ?_))
  apply le_antisymm
  next =>
    change sSup (Set.range (fun j : Nat =>
      primeGapFrequencyExponent (j + 2) / ((j : Real) + 2 + nu))) <= f H
    apply csSup_le (Set.range_nonempty _)
    intro x hx
    choose j hj using hx
    rw [<- hj]
    have hterm : primeGapFrequencyExponent (j + 2) / (((j + 2 : Nat) : Real) + nu) <= f H := by
      by_cases hle : j + 2 <= J
      next => exact hH.2 (j + 2) (Finset.mem_Icc.mpr (And.intro (by omega) hle))
      next =>
        have htail := gap_ratio_le_full_class (j + 2) J nu hnu (by omega)
        have hJmax := hH.2 J (Finset.mem_Icc.mpr (And.intro hJ (le_refl J)))
        dsimp only [f] at hJmax
        rw [hfull] at hJmax
        exact htail.trans hJmax
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hterm
  next => exact primeGapFrequency_ratio_le_spectrum H nu hnu

/-- Once every smaller class has exponent strictly below one, the least full
class dominates at every sufficiently large fixed dimension. -/
theorem primeGapSpectrum_eventually_full_class
    (J : Nat) (hJ : 2 <= J) (hfull : primeGapFrequencyExponent J = 1)
    (hminimal : forall H : Nat, 2 <= H -> H < J -> primeGapFrequencyExponent H < 1) :
    exists V : Nat, forall nu : Real, 0 < nu -> (V : Real) <= nu ->
      primeGapSpectrum nu = 1 / ((J : Real) + nu) := by
  classical
  have hcuts : forall H : Nat, exists V : Nat, forall nu : Real,
      0 < nu -> (V : Real) <= nu -> 2 <= H -> H < J ->
      primeGapFrequencyExponent H * ((J : Real) + nu) <= (H : Real) + nu := by
    intro H
    by_cases hgood : 2 <= H /\ H < J
    next =>
      have hg := hminimal H hgood.1 hgood.2
      have hd : 0 < 1 - primeGapFrequencyExponent H := by linarith
      choose V hV using exists_nat_gt
        ((primeGapFrequencyExponent H * J - H) / (1 - primeGapFrequencyExponent H))
      refine Exists.intro V ?_
      intro nu _ hVnu _ _
      have hm := mul_le_mul_of_nonneg_right (hV.le.trans hVnu) hd.le
      have hc : ((primeGapFrequencyExponent H * J - H) /
          (1 - primeGapFrequencyExponent H)) * (1 - primeGapFrequencyExponent H) =
          primeGapFrequencyExponent H * J - H := by field_simp [ne_of_gt hd]
      rw [hc] at hm
      nlinarith only [hm]
    next =>
      refine Exists.intro 0 ?_
      intro nu _ _ htwo hsmall
      exact False.elim (hgood (And.intro htwo hsmall))
  choose Vs hVs using hcuts
  let V := (Finset.range J).sup Vs
  refine Exists.intro V ?_
  intro nu hnu hVnu
  have hlo := primeGapFrequency_ratio_le_spectrum J nu hnu
  rw [hfull] at hlo
  apply le_antisymm ?_ hlo
  choose H hH using primeGapSpectrum_finite_maximum J hJ hfull nu hnu
  rw [hH.2.2]
  by_cases heq : H = J
  next => rw [heq, hfull]
  next =>
    have hHJ : H < J := by omega
    have hv : (Vs H : Real) <= nu := by
      have hvNat : Vs H <= V := Finset.le_sup (f := Vs) (Finset.mem_range.mpr hHJ)
      exact (by exact_mod_cast hvNat : (Vs H : Real) <= V).trans hVnu
    have hcomp := hVs H nu hnu hv hH.1 hHJ
    have hdH : 0 < (H : Real) + nu := by positivity
    have hdJ : 0 < (J : Real) + nu := by positivity
    have hcH : (primeGapFrequencyExponent H / ((H : Real) + nu)) *
        ((H : Real) + nu) = primeGapFrequencyExponent H := by
      field_simp [ne_of_gt hdH]
    have hcJ : (1 / ((J : Real) + nu)) * ((J : Real) + nu) = (1 : Real) := by
      field_simp [ne_of_gt hdJ]
    by_contra hn
    have hm := mul_lt_mul_of_pos_right (lt_of_not_ge hn) (mul_pos hdH hdJ)
    have hcancelH : (primeGapFrequencyExponent H / ((H : Real) + nu)) *
        (((H : Real) + nu) * ((J : Real) + nu)) =
        primeGapFrequencyExponent H * ((J : Real) + nu) := by
      rw [<- mul_assoc, hcH]
    have hcancelJ : (1 / ((J : Real) + nu)) *
        (((H : Real) + nu) * ((J : Real) + nu)) = (H : Real) + nu := by
      calc
        _ = ((H : Real) + nu) * ((1 / ((J : Real) + nu)) * ((J : Real) + nu)) := by ring
        _ = _ := by rw [hcJ, mul_one]
    rw [hcancelH, hcancelJ] at hm
    exact (not_lt_of_ge hcomp) hm

end PrimeFactorOscillations
