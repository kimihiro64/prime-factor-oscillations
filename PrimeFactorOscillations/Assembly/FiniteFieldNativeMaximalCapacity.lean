/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeFullCapacity
import PrimeFactorOscillations.Assembly.FiniteFieldNativeMaximalPacking

/-!
# Uniform capacity of maximal native selections

The sharp finite deficit comparison upgrades the existential density-one
packing theorem to every square-row dominating selection. In particular,
every inclusion-maximal flat selection has sharp full-height capacity.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter
open scoped Classical Topology

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

/-- A flat selection that admits no further single-label insertion
dominates the complete ambient support in the two native square rows. -/
theorem native_insertion_maximal_flat_selection_dominates
    (S G : Finset (Prod Nat Nat))
    (hGeometry : forall a : Prod Nat Nat, Membership.mem S a ->
      Nat.Prime a.1 /\ Nat.Prime (a.1 + a.2) /\ 0 < a.2)
    (hGS : G <= S)
    (hFlat : forall a : Prod Nat Nat, Membership.mem G a ->
      forall b : Prod Nat Nat, Membership.mem G b -> Not (a = b) ->
        nativeAgreementRate a.1 a.2 b.1 b.2 = 3 / 8)
    (hMax : forall a : Prod Nat Nat, Membership.mem S a ->
      (forall u : Prod Nat Nat, Membership.mem (insert a G) u ->
        forall v : Prod Nat Nat, Membership.mem (insert a G) v -> Not (u = v) ->
          nativeAgreementRate u.1 u.2 v.1 v.2 = 3 / 8) -> Membership.mem G a) :
    forall a : Prod Nat Nat, Membership.mem S a -> Not (Membership.mem G a) ->
      exists g : Prod Nat Nat, Membership.mem G g /\
        Or (IsSquare ((a.2 * a.1) * (g.2 * g.1)))
          (IsSquare ((a.2 * (a.1 + a.2)) * (g.2 * (g.1 + g.2)))) := by
  classical
  intro a ha haNot
  by_contra hNo
  have hCompatible (g : Prod Nat Nat) (hg : Membership.mem G g) (hneq : Not (a = g)) :
      nativeAgreementRate a.1 a.2 g.1 g.2 = 3 / 8 := by
    have ga := hGeometry a ha
    have gg := hGeometry g (hGS hg)
    have hPair : Not (And (a.1 = g.1) (a.2 = g.2)) := by
      intro he
      exact hneq (Prod.ext he.1 he.2)
    apply (native_agreement_arithmetic_classification
      a.1 a.2 g.1 g.2 ga.1 ga.2.1 gg.1 gg.2.1 ga.2.2 gg.2.2 hPair).2.mpr
    refine And.intro ?_ ?_
    . intro hs
      apply hNo
      refine Exists.intro g (And.intro hg (Or.inl ?_))
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hs
    . intro hs
      apply hNo
      refine Exists.intro g (And.intro hg (Or.inr ?_))
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hs
  apply haNot
  apply hMax a ha
  intro u hu v hv hne
  rcases Finset.mem_insert.mp hu with huEq | huG
  . subst u
    rcases Finset.mem_insert.mp hv with hvEq | hvG
    . subst v
      exact False.elim (hne rfl)
    . exact hCompatible v hvG hne
  . rcases Finset.mem_insert.mp hv with hvEq | hvG
    . subst v
      have hRev : nativeAgreementRate u.1 u.2 a.1 a.2 =
          nativeAgreementRate a.1 a.2 u.1 u.2 := by
        simp only [nativeAgreementRate, mul_assoc, mul_comm, mul_left_comm]
      exact hRev.trans (hCompatible u huG (fun he => hne he.symm))
    . exact hFlat u huG v hvG hne

/-- Every dominating selection retains density one, uniformly over all
choices at the same sufficiently large full height. Flatness of the
dominating selection is not needed for this cardinal conclusion. -/
theorem eventually_native_full_dominating_density_one
    (eps : Real) (heps : 0 < eps) :
    Filter.Eventually (fun Y : Nat =>
      forall G : Finset (Prod Nat Nat), G <= nativeFullPrimePairGapSet Y ->
        (forall a : Prod Nat Nat, Membership.mem (nativeFullPrimePairGapSet Y) a ->
          Not (Membership.mem G a) ->
          exists g : Prod Nat Nat, Membership.mem G g /\
            Or (IsSquare ((a.2 * a.1) * (g.2 * g.1)))
              (IsSquare ((a.2 * (a.1 + a.2)) * (g.2 * (g.1 + g.2))))) ->
        (1 - eps) * ((nativeFullPrimePairGapSet Y).card : Real) <= (G.card : Real))
      atTop := by
  classical
  filter_upwards [eventually_native_full_prime_pair_density_one (eps / 2) (by positivity)]
    with Y hRet
  choose M hMS hCount hMGeometry hFlat using hRet
  intro G hGS hDom
  let S := nativeFullPrimePairGapSet Y
  have hGeometry (a : Prod Nat Nat) (ha : Membership.mem S a) :
      Nat.Prime a.1 /\ Nat.Prime (a.1 + a.2) /\ 0 < a.2 := by
    have hh := (mem_nativeFullPrimePairGapSet_iff Y a.1 a.2).mp ha
    exact And.intro hh.1 (And.intro hh.2.1 hh.2.2.1)
  have hDefNat := native_dominating_selection_flat_deficit S G M hGeometry hGS hMS hFlat hDom
  have hDef : ((S \ G).card : Real) <= 2 * ((S \ M).card : Real) := by
    exact_mod_cast hDefNat
  have hG : ((S \ G).card : Real) + (G.card : Real) = (S.card : Real) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hGS
  have hM : ((S \ M).card : Real) + (M.card : Real) = (S.card : Real) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hMS
  change (1 - eps) * (S.card : Real) <= (G.card : Real)
  nlinarith only [hDef, hG, hM, hCount]

/-- The full-height leading capacity one half holds uniformly for every
dominating selection, not only for an optimized existential choice. -/
theorem eventually_native_full_dominating_sharp_capacity
    (eps : Real) (heps : 0 < eps) :
    Filter.Eventually (fun Y : Nat =>
      forall G : Finset (Prod Nat Nat), G <= nativeFullPrimePairGapSet Y ->
        (forall a : Prod Nat Nat, Membership.mem (nativeFullPrimePairGapSet Y) a ->
          Not (Membership.mem G a) ->
          exists g : Prod Nat Nat, Membership.mem G g /\
            Or (IsSquare ((a.2 * a.1) * (g.2 * g.1)))
              (IsSquare ((a.2 * (a.1 + a.2)) * (g.2 * (g.1 + g.2))))) ->
        (1 - eps) * ((nativeFullPrimePairGapSet Y).card : Real) <= (G.card : Real) /\
        (1 / 2 - eps) * ((Y : Real) ^ 2 / Real.log (Y : Real) ^ 2) <= (G.card : Real) /\
        (G.card : Real) <=
          (1 / 2 + eps) * ((Y : Real) ^ 2 / Real.log (Y : Real) ^ 2)) atTop := by
  classical
  let delta : Real := eps / 4
  have hd : 0 < delta := by dsimp only [delta]; positivity
  filter_upwards [eventually_native_full_pair_sharp_capacity delta hd,
    eventually_native_full_dominating_density_one eps heps] with Y hCapacity hDensity
  intro G hGS hDom
  let S := nativeFullPrimePairGapSet Y
  let D : Real := (Y : Real) ^ 2 / Real.log (Y : Real) ^ 2
  choose M hMS hRet hLow hTwo hFlat hPhysical using hCapacity.2
  have hGeometry (a : Prod Nat Nat) (ha : Membership.mem S a) :
      Nat.Prime a.1 /\ Nat.Prime (a.1 + a.2) /\ 0 < a.2 := by
    have hh := (mem_nativeFullPrimePairGapSet_iff Y a.1 a.2).mp ha
    exact And.intro hh.1 (And.intro hh.2.1 hh.2.2.1)
  have hDefNat := native_dominating_selection_flat_deficit S G M hGeometry hGS hMS hFlat hDom
  have hDef : ((S \ G).card : Real) <= 2 * ((S \ M).card : Real) := by
    exact_mod_cast hDefNat
  have hG : ((S \ G).card : Real) + (G.card : Real) = (S.card : Real) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hGS
  have hM : ((S \ M).card : Real) + (M.card : Real) = (S.card : Real) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hMS
  have hSUp : (S.card : Real) <= (1 / 2 + delta) * D := hCapacity.1 S (le_refl S)
  have hD : 0 <= D := by dsimp only [D]; positivity
  have hAbsolute : (1 / 2 - eps) * D <= (G.card : Real) := by
    have he : eps = 4 * delta := by dsimp only [delta]; ring
    change (1 / 2 - delta) * D <= (M.card : Real) at hLow
    nlinarith only [hDef, hG, hM, hLow, hSUp, mul_nonneg hd.le hD, he]
  refine And.intro (hDensity G hGS hDom) (And.intro hAbsolute ?_)
  have hUp : (G.card : Real) <= (1 / 2 + delta) * D := hCapacity.1 G hGS
  have hCoeff : delta <= eps := by dsimp only [delta]; linarith only [heps]
  exact hUp.trans (mul_le_mul_of_nonneg_right (by linarith) hD)


/-- Every insertion-maximal full-height flat family has density one,
sharp capacity, at least two members, and the same exact signed physical
limit with optimal lower stability constant five eighths. -/
theorem eventually_native_full_maximal_physical_capacity
    (eps : Real) (heps : 0 < eps) :
    Filter.Eventually (fun Y : Nat =>
      forall G : Finset (Prod Nat Nat), G <= nativeFullPrimePairGapSet Y ->
        (forall a : Prod Nat Nat, Membership.mem G a ->
          forall b : Prod Nat Nat, Membership.mem G b -> Not (a = b) ->
            nativeAgreementRate a.1 a.2 b.1 b.2 = 3 / 8) ->
        (forall a : Prod Nat Nat, Membership.mem (nativeFullPrimePairGapSet Y) a ->
          (forall u : Prod Nat Nat, Membership.mem (insert a G) u ->
            forall v : Prod Nat Nat, Membership.mem (insert a G) v -> Not (u = v) ->
              nativeAgreementRate u.1 u.2 v.1 v.2 = 3 / 8) -> Membership.mem G a) ->
        (1 - eps) * ((nativeFullPrimePairGapSet Y).card : Real) <= (G.card : Real) /\
        (1 / 2 - eps) * ((Y : Real) ^ 2 / Real.log (Y : Real) ^ 2) <= (G.card : Real) /\
        (G.card : Real) <=
          (1 / 2 + eps) * ((Y : Real) ^ 2 / Real.log (Y : Real) ^ 2) /\
        2 <= G.card /\
        let n : G -> Nat := fun a => a.val.1
        let h : G -> Nat := fun a => a.val.2
        (forall c : G -> Real,
          Tendsto (nativeAgreementMassForm n h c) atTop
            (nhds ((3 / 8 : Real) * (Finset.univ.sum c) ^ 2 +
              (5 / 8 : Real) * Finset.univ.sum (fun i => (c i) ^ 2)))) /\
        (forall kappa : Real,
          (forall c : G -> Real,
            kappa * Finset.univ.sum (fun i => (c i) ^ 2) <=
              nativeAgreementForm n h c) <-> kappa <= 5 / 8)) atTop := by
  classical
  have hEighth := eventually_native_full_dominating_sharp_capacity
    (1 / 8) (by norm_num)
  have hGrow := Real.eventually_const_mul_log_natpow_le_rpow
    (8 : Real) 2 (s := (2 : Real)) (by norm_num)
  filter_upwards [eventually_native_full_dominating_sharp_capacity eps heps,
    hEighth, hGrow, eventually_ge_atTop (2 : Nat)] with Y hMain hSmall hGrowth hY
  intro G hGS hFlat hMax
  let S := nativeFullPrimePairGapSet Y
  let D : Real := (Y : Real) ^ 2 / Real.log (Y : Real) ^ 2
  have hGeometry (a : Prod Nat Nat) (ha : Membership.mem S a) :
      Nat.Prime a.1 /\ Nat.Prime (a.1 + a.2) /\ 0 < a.2 := by
    have hh := (mem_nativeFullPrimePairGapSet_iff Y a.1 a.2).mp ha
    exact And.intro hh.1 (And.intro hh.2.1 hh.2.2.1)
  have hDom := native_insertion_maximal_flat_selection_dominates
    S G hGeometry hGS hFlat hMax
  have hBounds := hMain G hGS hDom
  have hSmallBound := (hSmall G hGS hDom).2.1
  have hy1 : (1 : Real) < Y := by exact_mod_cast (show 1 < Y by omega)
  have hl0 : Not (Real.log (Y : Real) = 0) := ne_of_gt (Real.log_pos hy1)
  have hGrowthNat : 8 * Real.log (Y : Real) ^ 2 <= (Y : Real) ^ 2 := by
    norm_num [Real.rpow_natCast] at hGrowth
    exact hGrowth
  have hD8 : (8 : Real) <= D := by
    have hh := div_nonneg (sub_nonneg.mpr hGrowthNat)
      (sq_nonneg (Real.log (Y : Real)))
    have he : ((Y : Real) ^ 2 - 8 * Real.log (Y : Real) ^ 2) /
        Real.log (Y : Real) ^ 2 = D - 8 := by
      dsimp only [D]
      field_simp [hl0]
    rw [he] at hh
    linarith only [hh]
  have hTwo : 2 <= G.card := by
    have hr : (2 : Real) <= (G.card : Real) := by
      change (1 / 2 - 1 / 8 : Real) * D <= (G.card : Real) at hSmallBound
      nlinarith only [hSmallBound, hD8]
    exact_mod_cast hr
  refine And.intro hBounds.1 (And.intro hBounds.2.1
    (And.intro hBounds.2.2 (And.intro hTwo ?_)))
  let n : G -> Nat := fun a => a.val.1
  let h : G -> Nat := fun a => a.val.2
  have hn (a : G) : Nat.Prime (n a) := (hGeometry a.val (hGS a.property)).1
  have hnh (a : G) : Nat.Prime (n a + h a) := (hGeometry a.val (hGS a.property)).2.1
  have hh (a : G) : 0 < h a := (hGeometry a.val (hGS a.property)).2.2
  have hinj : Function.Injective (fun a : G => Prod.mk (n a) (h a)) := by
    intro a b he
    apply Subtype.ext
    exact he
  have hflat (a b : G) (hab : Not (a = b)) :
      nativeAgreementRate (n a) (h a) (n b) (h b) = 3 / 8 := by
    apply hFlat a.val a.property b.val b.property
    intro he
    exact hab (Subtype.ext he)
  refine And.intro ?_ ?_
  . intro c
    exact native_flat_agreement_mass_form_tendsto n h hn hnh hh hinj hflat c
  . intro kappa
    apply Iff.intro
    . intro hBound
      choose a ha b hb hab using Finset.one_lt_card.mp (show 1 < G.card by omega)
      let i : G := Subtype.mk a ha
      let j : G := Subtype.mk b hb
      have hij : Not (i = j) := by
        intro he
        exact hab (congrArg (fun v : G => v.val) he)
      exact native_flat_agreement_stability_optimal n h hflat i j hij kappa hBound
    . intro hk c
      have hs : 0 <= Finset.univ.sum (fun i : G => (c i) ^ 2) :=
        Finset.sum_nonneg (fun i hi => sq_nonneg (c i))
      exact (mul_le_mul_of_nonneg_right hk hs).trans
        (native_flat_agreement_stability n h hflat c)

end PrimeFactorOscillations.FiniteFieldIntegerSignature
