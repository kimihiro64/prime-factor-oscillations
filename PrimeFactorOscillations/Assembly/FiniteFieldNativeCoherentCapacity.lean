/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeGreedyPacking

/-!
# One computable density-one infinite native family

A single persistent decidable family retains almost every actual
positive prime pair at every sufficiently large natural height.
Its cardinality has sharp leading constant one half. All choices are
made by the computable greedy construction, not by a fresh existence
argument at each height.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter
open scoped Classical Topology

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

/-- Every label in the one global computable class is an actual
positive-gap pair of integer primes. -/
theorem nativePrimePairGreedyClass_geometry (a : Prod Nat Nat)
    (ha : Membership.mem nativePrimePairGreedyClass a) :
    Nat.Prime a.1 /\ Nat.Prime (a.1 + a.2) /\ 0 < a.2 := by
  have hBirth : Membership.mem (nativePrimePairGreedyPrefix (a.1 + a.2)) a := ha
  have hg := nativePrimePairGreedyPrefix_geometry (a.1 + a.2) a hBirth
  exact And.intro hg.1 (And.intro hg.2.1 hg.2.2.1)

/-- All distinct labels of the same infinite class have native
agreement rate exactly three eighths. -/
theorem nativePrimePairGreedyClass_agreement (a : Prod Nat Nat)
    (ha : Membership.mem nativePrimePairGreedyClass a)
    (b : Prod Nat Nat) (hb : Membership.mem nativePrimePairGreedyClass b)
    (hne : Not (a = b)) :
    nativeAgreementRate a.1 a.2 b.1 b.2 = 3 / 8 := by
  let Y := max (a.1 + a.2) (b.1 + b.2)
  have hA : Membership.mem (nativePrimePairGreedyPrefix Y) a :=
    nativePrimePairGreedyPrefix_mono (a.1 + a.2) Y (le_max_left _ _) ha
  have hB : Membership.mem (nativePrimePairGreedyPrefix Y) b :=
    nativePrimePairGreedyPrefix_mono (b.1 + b.2) Y (le_max_right _ _) hb
  exact nativePrimePairGreedyPrefix_agreement Y a hA b hB hne

/-- The persistent computable family has density one and the sharp
capacity bracket at every sufficiently large natural height. -/
theorem eventually_nativePrimePairGreedyPrefix_capacity (eps : Real) (heps : 0 < eps) :
    Filter.Eventually (fun Y : Nat =>
      (1 - eps) * ((nativeFullPrimePairGapSet Y).card : Real) <=
        ((nativePrimePairGreedyPrefix Y).card : Real) /\
      (1 / 2 - eps) * ((Y : Real) ^ 2 / Real.log (Y : Real) ^ 2) <=
        ((nativePrimePairGreedyPrefix Y).card : Real) /\
      ((nativePrimePairGreedyPrefix Y).card : Real) <=
        (1 / 2 + eps) * ((Y : Real) ^ 2 / Real.log (Y : Real) ^ 2)) atTop := by
  filter_upwards [eventually_native_full_dominating_sharp_capacity eps heps] with Y hY
  have hSub : nativePrimePairGreedyPrefix Y <= nativeFullPrimePairGapSet Y := by
    intro a ha
    exact (mem_nativeFullPrimePairGapSet_iff Y a.1 a.2).mpr
      (nativePrimePairGreedyPrefix_geometry Y a ha)
  exact hY (nativePrimePairGreedyPrefix Y) hSub (nativePrimePairGreedyPrefix_dominates Y)

/-- Greedy prefix sizes eventually exceed every prescribed natural
cardinality; no effective height is asserted. -/
theorem eventually_nativePrimePairGreedyPrefix_card_ge (N : Nat) :
    Filter.Eventually (fun Y : Nat => N <= (nativePrimePairGreedyPrefix Y).card) atTop := by
  have hGrow := Real.eventually_const_mul_log_natpow_le_rpow
    (4 * (N : Real)) 2 (s := (2 : Real)) (by norm_num)
  filter_upwards [eventually_nativePrimePairGreedyPrefix_capacity (1 / 4) (by norm_num),
    hGrow, eventually_ge_atTop (2 : Nat)] with Y hCapacity hGrowth hY
  let D : Real := (Y : Real) ^ 2 / Real.log (Y : Real) ^ 2
  have hy1 : (1 : Real) < Y := by exact_mod_cast (show 1 < Y by omega)
  have hl0 : Not (Real.log (Y : Real) = 0) := ne_of_gt (Real.log_pos hy1)
  have hGrowthNat : 4 * (N : Real) * Real.log (Y : Real) ^ 2 <= (Y : Real) ^ 2 := by
    norm_num [Real.rpow_natCast] at hGrowth
    exact hGrowth
  have hD : 4 * (N : Real) <= D := by
    have hh := div_nonneg (sub_nonneg.mpr hGrowthNat)
      (sq_nonneg (Real.log (Y : Real)))
    have he : ((Y : Real) ^ 2 - 4 * (N : Real) * Real.log (Y : Real) ^ 2) /
        Real.log (Y : Real) ^ 2 = D - 4 * (N : Real) := by
      dsimp only [D]
      field_simp [hl0]
    rw [he] at hh
    linarith only [hh]
  have hLow : (1 / 2 - 1 / 4 : Real) * D <=
      ((nativePrimePairGreedyPrefix Y).card : Real) := hCapacity.2.1
  have hN : (N : Real) <= ((nativePrimePairGreedyPrefix Y).card : Real) := by
    nlinarith only [hD, hLow]
  exact_mod_cast hN

/-- The single decidable prime-pair class is infinite. -/
theorem nativePrimePairGreedyClass_infinite : Set.Infinite nativePrimePairGreedyClass := by
  classical
  intro hFinite
  let F := hFinite.toFinset
  choose Y hLarge using
    (eventually_nativePrimePairGreedyPrefix_card_ge (F.card + 1)).exists
  have hSub : nativePrimePairGreedyPrefix Y <= F := by
    intro a ha
    apply hFinite.mem_toFinset.mpr
    exact (nativePrimePairGreedyPrefix_mem_iff Y a).mp ha |>.1
  have hLe := Finset.card_le_card hSub
  omega

/-- The sharp normalized size of this one persistent family tends to
one half along all natural heights. -/
theorem tendsto_nativePrimePairGreedyPrefix_count_ratio :
    Tendsto (fun Y : Nat => ((nativePrimePairGreedyPrefix Y).card : Real) /
      ((Y : Real) ^ 2 / Real.log (Y : Real) ^ 2)) atTop (nhds (1 / 2)) := by
  apply tendsto_order.mpr
  refine And.intro ?_ ?_
  . intro b hb
    let eps : Real := (1 / 2 - b) / 2
    have heps : 0 < eps := by dsimp only [eps]; linarith only [hb]
    filter_upwards [eventually_nativePrimePairGreedyPrefix_capacity eps heps,
      eventually_ge_atTop (2 : Nat)] with Y hCapacity hY
    let D : Real := (Y : Real) ^ 2 / Real.log (Y : Real) ^ 2
    have hy1 : (1 : Real) < Y := by exact_mod_cast (show 1 < Y by omega)
    have hyPos : (0 : Real) < Y := zero_lt_one.trans hy1
    have hLog : 0 < Real.log (Y : Real) := Real.log_pos hy1
    have hD : 0 < D := by dsimp only [D]; positivity
    have hD0 : Not (D = 0) := ne_of_gt hD
    have hCancel : (((nativePrimePairGreedyPrefix Y).card : Real) / D) * D =
        ((nativePrimePairGreedyPrefix Y).card : Real) := by field_simp [hD0]
    have hCmp : (1 / 2 - eps) * D <=
        (((nativePrimePairGreedyPrefix Y).card : Real) / D) * D := by
      rw [hCancel]
      exact hCapacity.2.1
    have hRatio := le_of_mul_le_mul_right hCmp hD
    change b < ((nativePrimePairGreedyPrefix Y).card : Real) / D
    dsimp only [eps] at hRatio
    linarith only [hRatio, hb]
  . intro b hb
    let eps : Real := (b - 1 / 2) / 2
    have heps : 0 < eps := by dsimp only [eps]; linarith only [hb]
    filter_upwards [eventually_nativePrimePairGreedyPrefix_capacity eps heps,
      eventually_ge_atTop (2 : Nat)] with Y hCapacity hY
    let D : Real := (Y : Real) ^ 2 / Real.log (Y : Real) ^ 2
    have hy1 : (1 : Real) < Y := by exact_mod_cast (show 1 < Y by omega)
    have hyPos : (0 : Real) < Y := zero_lt_one.trans hy1
    have hLog : 0 < Real.log (Y : Real) := Real.log_pos hy1
    have hD : 0 < D := by dsimp only [D]; positivity
    have hD0 : Not (D = 0) := ne_of_gt hD
    have hCancel : (((nativePrimePairGreedyPrefix Y).card : Real) / D) * D =
        ((nativePrimePairGreedyPrefix Y).card : Real) := by field_simp [hD0]
    have hCmp : (((nativePrimePairGreedyPrefix Y).card : Real) / D) * D <=
        (1 / 2 + eps) * D := by
      rw [hCancel]
      exact hCapacity.2.2
    have hRatio := le_of_mul_le_mul_right hCmp hD
    change ((nativePrimePairGreedyPrefix Y).card : Real) / D < b
    dsimp only [eps] at hRatio
    linarith only [hRatio, hb]

/-- Density one means convergence of the actual retained fraction,
not only a separate existential family at each height. -/
theorem tendsto_nativePrimePairGreedyPrefix_retention_ratio :
    Tendsto (fun Y : Nat => ((nativePrimePairGreedyPrefix Y).card : Real) /
      ((nativeFullPrimePairGapSet Y).card : Real)) atTop (nhds 1) := by
  have hNonempty := eventually_nativePrimePairGreedyPrefix_card_ge 1
  have hSub (Y : Nat) : nativePrimePairGreedyPrefix Y <= nativeFullPrimePairGapSet Y := by
    intro a ha
    exact (mem_nativeFullPrimePairGapSet_iff Y a.1 a.2).mpr
      (nativePrimePairGreedyPrefix_geometry Y a ha)
  apply tendsto_order.mpr
  refine And.intro ?_ ?_
  . intro b hb
    let eps : Real := (1 - b) / 2
    have heps : 0 < eps := by dsimp only [eps]; linarith only [hb]
    filter_upwards [eventually_nativePrimePairGreedyPrefix_capacity eps heps, hNonempty]
      with Y hCapacity hOne
    let S := nativeFullPrimePairGapSet Y
    have hCount := Finset.card_le_card (hSub Y)
    have hSPosNat : 0 < S.card := by change 0 < (nativeFullPrimePairGapSet Y).card; omega
    have hSPos : (0 : Real) < (S.card : Real) := by exact_mod_cast hSPosNat
    have hS0 : Not ((S.card : Real) = 0) := ne_of_gt hSPos
    have hCancel : (((nativePrimePairGreedyPrefix Y).card : Real) / (S.card : Real)) *
        (S.card : Real) = ((nativePrimePairGreedyPrefix Y).card : Real) := by
      field_simp [hS0]
    have hCmp : (1 - eps) * (S.card : Real) <=
        (((nativePrimePairGreedyPrefix Y).card : Real) / (S.card : Real)) * (S.card : Real) := by
      rw [hCancel]
      exact hCapacity.1
    have hRatio := le_of_mul_le_mul_right hCmp hSPos
    change b < ((nativePrimePairGreedyPrefix Y).card : Real) / (S.card : Real)
    dsimp only [eps] at hRatio
    linarith only [hRatio, hb]
  . intro b hb
    filter_upwards [hNonempty] with Y hOne
    let S := nativeFullPrimePairGapSet Y
    have hCount := Finset.card_le_card (hSub Y)
    have hSPosNat : 0 < S.card := by change 0 < (nativeFullPrimePairGapSet Y).card; omega
    have hSPos : (0 : Real) < (S.card : Real) := by exact_mod_cast hSPosNat
    have hS0 : Not ((S.card : Real) = 0) := ne_of_gt hSPos
    have hCancel : (((nativePrimePairGreedyPrefix Y).card : Real) / (S.card : Real)) *
        (S.card : Real) = ((nativePrimePairGreedyPrefix Y).card : Real) := by
      field_simp [hS0]
    have hCountReal : ((nativePrimePairGreedyPrefix Y).card : Real) <= (S.card : Real) := by
      exact_mod_cast hCount
    have hCmp : (((nativePrimePairGreedyPrefix Y).card : Real) / (S.card : Real)) *
        (S.card : Real) <= 1 * (S.card : Real) := by
      rw [hCancel]
      simpa only [one_mul] using hCountReal
    have hRatio := le_of_mul_le_mul_right hCmp hSPos
    change ((nativePrimePairGreedyPrefix Y).card : Real) / (S.card : Real) < b
    linarith only [hRatio, hb]


/-- One explicit computable infinite family realizes full native
flatness, exact coherent truncations, density one, and sharp leading
capacity one half, all along every sufficiently large natural height. -/
theorem native_computable_density_one_flat_prime_pair_family :
    Set.Infinite nativePrimePairGreedyClass /\
    (forall a : Prod Nat Nat, Membership.mem nativePrimePairGreedyClass a ->
      Nat.Prime a.1 /\ Nat.Prime (a.1 + a.2) /\ 0 < a.2) /\
    (forall a : Prod Nat Nat, Membership.mem nativePrimePairGreedyClass a ->
      forall b : Prod Nat Nat, Membership.mem nativePrimePairGreedyClass b -> Not (a = b) ->
        nativeAgreementRate a.1 a.2 b.1 b.2 = 3 / 8) /\
    (forall Y : Nat, forall a : Prod Nat Nat,
      Membership.mem (nativePrimePairGreedyPrefix Y) a <->
        Membership.mem nativePrimePairGreedyClass a /\
          Membership.mem (nativeFullPrimePairGapSet Y) a) /\
    Tendsto (fun Y : Nat => ((nativePrimePairGreedyPrefix Y).card : Real) /
      ((nativeFullPrimePairGapSet Y).card : Real)) atTop (nhds 1) /\
    Tendsto (fun Y : Nat => ((nativePrimePairGreedyPrefix Y).card : Real) /
      ((Y : Real) ^ 2 / Real.log (Y : Real) ^ 2)) atTop (nhds (1 / 2)) := by
  exact And.intro nativePrimePairGreedyClass_infinite
    (And.intro nativePrimePairGreedyClass_geometry
      (And.intro nativePrimePairGreedyClass_agreement
        (And.intro nativePrimePairGreedyPrefix_mem_iff
          (And.intro tendsto_nativePrimePairGreedyPrefix_retention_ratio
            tendsto_nativePrimePairGreedyPrefix_count_ratio))))

end PrimeFactorOscillations.FiniteFieldIntegerSignature
