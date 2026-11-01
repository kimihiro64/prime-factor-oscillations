/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeCleanPacking
import PrimeFactorOscillations.Helpers.NativeHeightSquarefreeSupply

/-!
# Height-sized native prime-pair codebooks

The complete asymptotic squarefree supply produces actual short prime-pair
codebooks with three-eighths agreement between every pair of distinct entries.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

open Filter

/-- Large native codebooks indexed by actual short prime pairs below the height. -/
theorem eventually_native_prime_pair_height_packing :
    Filter.Eventually (fun Y : Nat => 24 <= Y /\ 1 <= Real.log (Y : Real) /\
      exists M : Finset (Prod Nat Nat),
        (forall a : Prod Nat Nat, Membership.mem M a ->
          Nat.Prime a.1 /\ Nat.Prime (a.1 + a.2) /\ 0 < a.2 /\
            a.2 < a.1 /\ a.1 + a.2 <= Y) /\
        (Y : Real) ^ 2 / (4096 * Real.log (Y : Real) ^ 2) <= (M.card : Real) /\
        forall a : Prod Nat Nat, Membership.mem M a ->
          forall b : Prod Nat Nat, Membership.mem M b -> Not (a = b) ->
            nativeAgreementRate a.1 a.2 b.1 b.2 = 3 / 8) Filter.atTop := by
  classical
  filter_upwards [QRH.eventually_squarefree_quarter_prime_pair_supply] with Y hY
  let N := Y / 4
  let S := QRH.squarefreePrimeBlockGapSet (2 * N) (3 * N) (4 * N)
  have hSF (a : Prod Nat Nat) (ha : Membership.mem S a) :
      Membership.mem (QRH.primeBlockGapSet (2 * N) (3 * N) (4 * N)) a /\
        forall u : Nat, 2 <= u -> Not (Dvd.dvd (u ^ 2) a.2) := by
    exact Finset.mem_filter.mp ha
  have hNY : 4 * N <= Y := by dsimp [N]; omega
  have hSpec (a : Prod Nat Nat) (ha : Membership.mem S a) :
      Nat.Prime a.1 /\ Nat.Prime (a.1 + a.2) /\ 0 < a.2 /\
        a.2 < a.1 /\ a.1 + a.2 <= Y := by
    have hImage := (hSF a ha).1
    unfold QRH.primeBlockGapSet at hImage
    choose z hz using Finset.mem_image.mp hImage
    have hLower := (QRH.mem_primeBlockSet_iff (2 * N) (3 * N) z.1).mp
      (Finset.mem_product.mp hz.1).1
    have hUpper := (QRH.mem_primeBlockSet_iff (3 * N) (4 * N) z.2).mp
      (Finset.mem_product.mp hz.1).2
    have he : Prod.mk z.1 (z.2 - z.1) = a := hz.2
    rw [<- he]
    dsimp only
    have hAdd : z.1 + (z.2 - z.1) = z.2 := by omega
    refine And.intro hLower.1 (And.intro ?_ (And.intro ?_ (And.intro ?_ ?_)))
    . simpa only [hAdd] using hUpper.1
    . omega
    . omega
    . omega
  have hPrime (a : Prod Nat Nat) (ha : Membership.mem S a) :
      Nat.Prime a.1 /\ Nat.Prime (a.1 + a.2) /\ 0 < a.2 /\ a.2 < a.1 := by
    have h := hSpec a ha
    exact And.intro h.1 (And.intro h.2.1 (And.intro h.2.2.1 h.2.2.2.1))
  have hClean (a : Prod Nat Nat) (ha : Membership.mem S a) :
      forall u : Nat, 2 <= u -> Not (Dvd.dvd (u ^ 2) a.2) := (hSF a ha).2
  choose M hM using native_clean_gap_packing S 2 hPrime hClean
  have hCard : (S.card : Real) <= 2 * (M.card : Real) := by
    have h := hM.2.1
    norm_num at h
    exact_mod_cast h
  let l := Real.log (Y : Real)
  let t := (Y : Real) ^ 2 / (4096 * l ^ 2)
  have hl : 1 <= l := hY.2.1
  have hlPos : 0 < l := by linarith
  have hl0 : Not (l = 0) := ne_of_gt hlPos
  have hLower : (Y : Real) ^ 2 / (2000 * l ^ 2) <= 2 * (M.card : Real) :=
    hY.2.2.trans hCard
  have hMultiply := mul_le_mul_of_nonneg_right hLower
    (by positivity : 0 <= 2000 * l ^ 2)
  have hCancel : ((Y : Real) ^ 2 / (2000 * l ^ 2)) * (2000 * l ^ 2) =
      (Y : Real) ^ 2 := by field_simp
  have hHeight : (Y : Real) ^ 2 <= 4000 * (M.card : Real) * l ^ 2 := by
    nlinarith only [hMultiply, hCancel]
  have ht : 4096 * t * l ^ 2 = (Y : Real) ^ 2 := by
    dsimp [t]
    field_simp
  have hNonneg : 0 <= (M.card : Real) * l ^ 2 :=
    mul_nonneg (Nat.cast_nonneg M.card) (sq_nonneg l)
  have hScale : t * l ^ 2 <= (M.card : Real) * l ^ 2 := by
    nlinarith only [hHeight, ht, hNonneg]
  have hCount : t <= (M.card : Real) :=
    le_of_mul_le_mul_right hScale (pow_pos hlPos 2)
  refine And.intro hY.1 (And.intro hY.2.1 (Exists.intro M ?_))
  exact And.intro (fun a ha => hSpec a (hM.1 a ha)) (And.intro hCount hM.2.2)

end PrimeFactorOscillations.FiniteFieldIntegerSignature
