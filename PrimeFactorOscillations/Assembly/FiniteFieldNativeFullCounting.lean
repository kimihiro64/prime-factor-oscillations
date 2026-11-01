/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeFullHeightSupply
import PrimeFactorOscillations.Helpers.PrimeCountingLocation

/-!
# Exact full-height prime-pair count and its sharp asymptotic

The actual positive-gap labels are the strict upper triangle of the
complete prime-pair ensemble. Both endpoint triangles and the full
diagonal are retained in the exact counting identity.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter
open scoped Classical Topology

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

/-- The two strict endpoint triangles and the diagonal partition every
actual ordered prime pair, including the small empty cases. -/
theorem nativeFullPrimePairGapSet_card_twice (Y : Nat) :
    2 * (nativeFullPrimePairGapSet Y).card + Nat.primeCounting Y =
      (Nat.primeCounting Y) ^ 2 := by
  classical
  let P := primePairs Y
  let U := P.filter (fun z => z.1 < z.2)
  let V := P.filter (fun z => z.2 < z.1)
  let E := P.filter (fun z => z.1 = z.2)
  let N := P.filter (fun z => Not (z.1 < z.2))
  let swap : Prod Nat Nat -> Prod Nat Nat := fun z => Prod.mk z.2 z.1
  have hPmem (z : Prod Nat Nat) :
      Membership.mem P z <->
        Membership.mem (Nat.primesLE Y) z.1 /\
        Membership.mem (Nat.primesLE Y) z.2 := by
    change Membership.mem ((Nat.primesLE Y).product (Nat.primesLE Y)) z <-> _
    exact Finset.mem_product
  have hSwapMem (z : Prod Nat Nat) (hz : Membership.mem P z) :
      Membership.mem P (swap z) := by
    have hh := (hPmem z).mp hz
    exact (hPmem (swap z)).mpr (And.intro hh.2 hh.1)
  have hSwapInj : Function.Injective swap := by
    intro z w he
    have h1 := congrArg (fun t : Prod Nat Nat => t.2) he
    have h2 := congrArg (fun t : Prod Nat Nat => t.1) he
    exact Prod.ext h1 h2
  have hUV : U.card = V.card := by
    apply Nat.le_antisymm
    . apply Finset.card_le_card_of_injOn swap
      . intro z hz
        have hh := Finset.mem_filter.mp hz
        exact Finset.mem_filter.mpr (And.intro (hSwapMem z hh.1) hh.2)
      . exact fun _ _ _ _ he => hSwapInj he
    . apply Finset.card_le_card_of_injOn swap
      . intro z hz
        have hh := Finset.mem_filter.mp hz
        exact Finset.mem_filter.mpr (And.intro (hSwapMem z hh.1) hh.2)
      . exact fun _ _ _ _ he => hSwapInj he
  have hDiagLe : E.card <= (Nat.primesLE Y).card := by
    apply Finset.card_le_card_of_injOn (fun z : Prod Nat Nat => z.1)
    . intro z hz
      exact ((hPmem z).mp (Finset.mem_filter.mp hz).1).1
    . intro z hz w hw he
      have hzEq : z.1 = z.2 := (Finset.mem_filter.mp hz).2
      have hwEq : w.1 = w.2 := (Finset.mem_filter.mp hw).2
      have hn : z.1 = w.1 := he
      exact Prod.ext hn (by omega)
  have hDiagGe : (Nat.primesLE Y).card <= E.card := by
    apply Finset.card_le_card_of_injOn (fun p : Nat => Prod.mk p p)
    . intro p hp
      exact Finset.mem_filter.mpr
        (And.intro ((hPmem (Prod.mk p p)).mpr (And.intro hp hp)) rfl)
    . intro p hp q hq he
      exact congrArg (fun z : Prod Nat Nat => z.1) he
  have hDiag : E.card = Nat.primeCounting Y := by
    have hh := Nat.le_antisymm hDiagLe hDiagGe
    simpa only [Nat.primesLE_card_eq_primeCounting] using hh
  have hNE : N.filter (fun z => z.1 = z.2) = E := by
    apply Finset.ext
    intro z
    apply Iff.intro
    . intro hz
      have h1 := Finset.mem_filter.mp hz
      have h2 := Finset.mem_filter.mp h1.1
      exact Finset.mem_filter.mpr (And.intro h2.1 h1.2)
    . intro hz
      have h1 := Finset.mem_filter.mp hz
      have he : z.1 = z.2 := h1.2
      have hnot : Not (z.1 < z.2) := by omega
      exact Finset.mem_filter.mpr (And.intro
        (Finset.mem_filter.mpr (And.intro h1.1 hnot)) he)
  have hNV : N.filter (fun z => Not (z.1 = z.2)) = V := by
    apply Finset.ext
    intro z
    apply Iff.intro
    . intro hz
      have h1 := Finset.mem_filter.mp hz
      have h2 := Finset.mem_filter.mp h1.1
      have hnotlt : Not (z.1 < z.2) := h2.2
      have hnoteq : Not (z.1 = z.2) := h1.2
      have hlt : z.2 < z.1 := by omega
      exact Finset.mem_filter.mpr (And.intro h2.1 hlt)
    . intro hz
      have h1 := Finset.mem_filter.mp hz
      have hlt : z.2 < z.1 := h1.2
      have hnotlt : Not (z.1 < z.2) := by omega
      have hnoteq : Not (z.1 = z.2) := by omega
      exact Finset.mem_filter.mpr (And.intro
        (Finset.mem_filter.mpr (And.intro h1.1 hnotlt)) hnoteq)
  have hPartition : U.card + N.card = P.card :=
    Finset.card_filter_add_card_filter_not (s := P) (fun z => z.1 < z.2)
  have hNPartition := Finset.card_filter_add_card_filter_not
    (s := N) (fun z => z.1 = z.2)
  rw [hNE, hNV] at hNPartition
  have hGapCard : (nativeFullPrimePairGapSet Y).card = U.card := by
    change (U.image (fun z => Prod.mk z.1 (z.2 - z.1))).card = U.card
    apply Finset.card_image_of_injOn
    intro z hz w hw he
    have h1 := congrArg (fun t : Prod Nat Nat => t.1) he
    have h2 := congrArg (fun t : Prod Nat Nat => t.2) he
    have hn : z.1 = w.1 := h1
    have hd : z.2 - z.1 = w.2 - w.1 := h2
    have hzlt := (Finset.mem_filter.mp hz).2
    have hwlt := (Finset.mem_filter.mp hw).2
    exact Prod.ext hn (by omega)
  have hPCard : P.card = (Nat.primeCounting Y) ^ 2 := primePairs_card Y
  omega

/-- Exact full positive-gap candidate count; no large-height hypothesis. -/
theorem nativeFullPrimePairGapSet_card (Y : Nat) :
    (nativeFullPrimePairGapSet Y).card =
      ((Nat.primeCounting Y) ^ 2 - Nat.primeCounting Y) / 2 := by
  have hh := nativeFullPrimePairGapSet_card_twice Y
  omega

/-- The complete positive-gap candidate count has leading constant one half
on the natural height scale, with every diagonal correction retained. -/
theorem tendsto_native_full_pair_count_ratio :
    Tendsto (fun Y : Nat =>
      ((nativeFullPrimePairGapSet Y).card : Real) /
        ((Y : Real) ^ 2 / Real.log (Y : Real) ^ 2))
      atTop (nhds (1 / 2 : Real)) := by
  have hr := PrimeFactorOscillations.tendsto_primeCounting_div_mainTerm
  have ht : Tendsto (fun Y : Nat => Real.log (Y : Real) / (Y : Real))
      atTop (nhds (0 : Real)) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R := Real))
  have hhalf : Tendsto (fun _Y : Nat => (1 / 2 : Real))
      atTop (nhds (1 / 2 : Real)) := tendsto_const_nhds
  have hraw := hhalf.mul ((hr.pow 2).sub (hr.mul ht))
  have hlim : Tendsto (fun Y : Nat =>
      (1 / 2 : Real) *
        (((Nat.primeCounting Y : Real) /
            ((Y : Real) / Real.log (Y : Real))) ^ 2 -
          ((Nat.primeCounting Y : Real) /
            ((Y : Real) / Real.log (Y : Real))) *
            (Real.log (Y : Real) / (Y : Real))))
      atTop (nhds (1 / 2 : Real)) := by
    simpa only [one_pow, mul_zero, sub_zero, mul_one] using hraw
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (2 : Nat)] with Y hY
  have hy1 : (1 : Real) < Y := by exact_mod_cast (show 1 < Y by omega)
  have hy0 : Not ((Y : Real) = 0) := ne_of_gt (zero_lt_one.trans hy1)
  have hl0 : Not (Real.log (Y : Real) = 0) := ne_of_gt (Real.log_pos hy1)
  have hCount : (2 : Real) * ((nativeFullPrimePairGapSet Y).card : Real) +
      (Nat.primeCounting Y : Real) = (Nat.primeCounting Y : Real) ^ 2 := by
    exact_mod_cast nativeFullPrimePairGapSet_card_twice Y
  have hScalar : ((nativeFullPrimePairGapSet Y).card : Real) =
      ((Nat.primeCounting Y : Real) ^ 2 - (Nat.primeCounting Y : Real)) / 2 := by
    nlinarith only [hCount]
  rw [hScalar]
  field_simp [hy0, hl0]

end PrimeFactorOscillations.FiniteFieldIntegerSignature
