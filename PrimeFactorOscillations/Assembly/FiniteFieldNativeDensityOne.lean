/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeFullHeightSupply
import PrimeFactorOscillations.Assembly.FiniteFieldNativeFullSparseConflicts
import PrimeFactorOscillations.Helpers.NativeHeightSquarefreeSupply
import PrimeFactorOscillations.Helpers.NativeSquarepartTail

/-!
# Density-one native prime-pair retention

The complete finite deletion lower bound is assembled with the actual PNT
blocks. The squarepart threshold and every weighted-prime family are fixed
before the height tends to infinity. The checked rounded-cutoff argument
is lifted to an arbitrary positive error budget.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter
open scoped Classical Topology

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

private theorem eventually_native_density_one_cutoff (J : Nat) (hJ : 0 < J)
    (C : Real) (hC : 0 <= C)
    (B : Real) (hB : 0 < B) :
    Filter.Eventually (fun Y : Nat =>
      let R := Nat.ceil ((Y : Real) ^ (1 / 8 : Real))
      24 <= Y /\ 1 <= Real.log (Y : Real) /\ 2 <= R /\
        R ^ 2 <= Y / J /\
        C * (R : Real) * (Y : Real) ^ (7 / 4 : Real) *
            (1 + 2 * Real.log ((Y : Real) + 2)) ^ 4 +
          (Y : Real) * ((Y / R : Nat) : Real) <=
            (Y : Real) ^ 2 / (B * Real.log (Y : Real) ^ 2)) Filter.atTop := by
  have hB0 : Not (B = 0) := ne_of_gt hB
  have hLog := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R := Real))).eventually
      (Filter.eventually_ge_atTop (1 : Real))
  have hPoly := Real.eventually_const_mul_log_natpow_le_rpow
    (B * (1250 * C + 1)) 6 (s := (1 / 8 : Real)) (by norm_num)
  have hRadius := Real.eventually_const_mul_log_natpow_le_rpow
    3 0 (s := (1 / 8 : Real)) (by norm_num)
  have hGeometry := Real.eventually_const_mul_log_natpow_le_rpow
    (8 * (J : Real)) 0 (s := (3 / 4 : Real)) (by norm_num)
  filter_upwards [Filter.eventually_ge_atTop (24 : Nat), hLog, hPoly,
      hRadius, hGeometry, Filter.eventually_ge_atTop (2 * J)]
    with Y hY hl hp hr hg hYJ
  let x : Real := Y
  let R := Nat.ceil (x ^ (1 / 8 : Real))
  let L := 1 + 2 * Real.log (x + 2)
  change 1 <= Real.log x at hl
  change (B * (1250 * C + 1)) * Real.log x ^ 6 <= x ^ (1 / 8 : Real) at hp
  simp only [pow_zero, mul_one] at hr hg
  have hx24 : (24 : Real) <= x := by
    dsimp [x]
    exact_mod_cast hY
  have hx : 0 < x := by linarith
  have hz : 0 < x ^ (1 / 8 : Real) := Real.rpow_pos_of_pos hx _
  have hz0 : Not (x ^ (1 / 8 : Real) = 0) := ne_of_gt hz
  have hLower : x ^ (1 / 8 : Real) <= (R : Real) := Nat.le_ceil _
  have hUpper : (R : Real) <= 2 * x ^ (1 / 8 : Real) := by
    have hc : (R : Real) < x ^ (1 / 8 : Real) + 1 := Nat.ceil_lt_add_one hz.le
    linarith
  have hR : 2 <= R := by
    have h : (2 : Real) <= R := by linarith
    exact_mod_cast h
  have hSquare : x ^ (1 / 8 : Real) * x ^ (1 / 8 : Real) =
      x ^ (1 / 4 : Real) := by
    rw [<- Real.rpow_add hx]
    norm_num
  have hRSquare : (R : Real) ^ 2 <= 4 * x ^ (1 / 4 : Real) := by
    have hs := mul_self_le_mul_self (Nat.cast_nonneg R) hUpper
    nlinarith only [hs, hSquare]
  have hGeometryProduct : (8 * (J : Real)) * x ^ (1 / 4 : Real) <= x := by
    calc
      (8 * (J : Real)) * x ^ (1 / 4 : Real) <=
          x ^ (3 / 4 : Real) * x ^ (1 / 4 : Real) :=
        mul_le_mul_of_nonneg_right hg (Real.rpow_nonneg hx.le _)
      _ = x := by
        rw [<- Real.rpow_add hx]
        norm_num
  have hDiv := Nat.div_add_mod Y J
  have hRem := Nat.mod_lt Y hJ
  have hq : 1 <= Y / J := by
    apply (Nat.le_div_iff_mul_le hJ).mpr
    omega
  have hqJ : J <= J * (Y / J) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left J hq
  have hNatGeometry : Y <= 2 * J * (Y / J) := by
    nlinarith only [hDiv, hRem, hqJ]
  have hCastGeometry : x <= 2 * (J : Real) * ((Y / J : Nat) : Real) := by
    dsimp only [x]
    exact_mod_cast hNatGeometry
  have hJReal : (0 : Real) < (J : Real) := by exact_mod_cast hJ
  have hQuarter : 4 * x ^ (1 / 4 : Real) <= ((Y / J : Nat) : Real) := by
    apply le_of_mul_le_mul_right ?_ hJReal
    nlinarith only [hGeometryProduct, hCastGeometry]
  have hRGeometry : R ^ 2 <= Y / J := by
    exact_mod_cast hRSquare.trans hQuarter
  have hLogAdd : Real.log (x + 2) <= 2 * Real.log x := by
    calc
      Real.log (x + 2) <= Real.log (x ^ 2) :=
        Real.log_le_log (by linarith) (by nlinarith)
      _ = 2 * Real.log x := by rw [Real.log_pow]; norm_num
  have hL0 : 0 <= L := by
    have h := Real.log_nonneg (by linarith : 1 <= x + 2)
    dsimp [L]
    linarith
  have hL : L <= 5 * Real.log x := by
    dsimp [L]
    linarith
  have hL4 : L ^ 4 <= 625 * Real.log x ^ 4 := by
    have h2 := mul_self_le_mul_self hL0 hL
    have h4 := mul_self_le_mul_self (mul_nonneg hL0 hL0) h2
    nlinarith only [h4]
  have hProduct : x ^ (1 / 8 : Real) * x ^ (7 / 4 : Real) =
      x ^ (15 / 8 : Real) := by
    rw [<- Real.rpow_add hx]
    norm_num
  have hPower7 : 0 <= x ^ (7 / 4 : Real) := Real.rpow_nonneg hx.le _
  have hPower15 : 0 <= x ^ (15 / 8 : Real) := Real.rpow_nonneg hx.le _
  have hLow : C * (R : Real) * x ^ (7 / 4 : Real) * L ^ 4 <=
      1250 * C * x ^ (15 / 8 : Real) * Real.log x ^ 4 := by
    calc
      C * (R : Real) * x ^ (7 / 4 : Real) * L ^ 4 <=
          C * (2 * x ^ (1 / 8 : Real)) * x ^ (7 / 4 : Real) * L ^ 4 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hUpper hC) hPower7) (pow_nonneg hL0 4)
      _ <= C * (2 * x ^ (1 / 8 : Real)) * x ^ (7 / 4 : Real) *
          (625 * Real.log x ^ 4) :=
        mul_le_mul_of_nonneg_left hL4
          (mul_nonneg (mul_nonneg hC (mul_nonneg (by norm_num) hz.le)) hPower7)
      _ = 1250 * C * x ^ (15 / 8 : Real) * Real.log x ^ 4 := by
        calc
          _ = 1250 * C * (x ^ (1 / 8 : Real) * x ^ (7 / 4 : Real)) *
              Real.log x ^ 4 := by ring
          _ = _ := by rw [hProduct]
  have hQuotient : x ^ 2 / x ^ (1 / 8 : Real) = x ^ (15 / 8 : Real) := by
    have he : x ^ (15 / 8 : Real) * x ^ (1 / 8 : Real) = x ^ 2 := by
      rw [<- Real.rpow_add hx]
      norm_num [Real.rpow_natCast]
    calc
      x ^ 2 / x ^ (1 / 8 : Real) =
          (x ^ (15 / 8 : Real) * x ^ (1 / 8 : Real)) /
            x ^ (1 / 8 : Real) := by rw [he]
      _ = x ^ (15 / 8 : Real) := by field_simp
  have hHigh : x * ((Y / R : Nat) : Real) <= x ^ (15 / 8 : Real) := by
    calc
      x * ((Y / R : Nat) : Real) <= x * (x / (R : Real)) :=
        mul_le_mul_of_nonneg_left Nat.cast_div_le hx.le
      _ = x ^ 2 / (R : Real) := by ring
      _ <= x ^ 2 / x ^ (1 / 8 : Real) :=
        div_le_div_of_nonneg_left (sq_nonneg x) hz hLower
      _ = x ^ (15 / 8 : Real) := hQuotient
  have hLog2 : 1 <= Real.log x ^ 2 := by nlinarith only [hl]
  have hLog4 : 1 <= Real.log x ^ 4 := by
    nlinarith only [hLog2, sq_nonneg (Real.log x ^ 2 - 1)]
  have hHighLog : x ^ (15 / 8 : Real) <=
      x ^ (15 / 8 : Real) * Real.log x ^ 4 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hLog4 hPower15
  let E := C * (R : Real) * x ^ (7 / 4 : Real) * L ^ 4 +
    x * ((Y / R : Nat) : Real)
  have hCombined : E <= (1250 * C + 1) * x ^ (15 / 8 : Real) *
      Real.log x ^ 4 := by
    dsimp [E]
    nlinarith only [hLow, hHigh, hHighLog]
  have hlPos : 0 < Real.log x := by linarith
  have hl0 : Not (Real.log x = 0) := ne_of_gt hlPos
  have hDen : 0 < B * Real.log x ^ 2 := by positivity
  have hFinal : E * (B * Real.log x ^ 2) <= x ^ 2 := by
    calc
      E * (B * Real.log x ^ 2) <=
          ((1250 * C + 1) * x ^ (15 / 8 : Real) * Real.log x ^ 4) *
            (B * Real.log x ^ 2) :=
        mul_le_mul_of_nonneg_right hCombined hDen.le
      _ = (B * (1250 * C + 1) * Real.log x ^ 6) *
          x ^ (15 / 8 : Real) := by ring
      _ <= x ^ (1 / 8 : Real) * x ^ (15 / 8 : Real) :=
        mul_le_mul_of_nonneg_right hp hPower15
      _ = x ^ 2 := by
        rw [<- Real.rpow_add hx]
        norm_num [Real.rpow_natCast]
  have hCancel : (x ^ 2 / (B * Real.log x ^ 2)) *
      (B * Real.log x ^ 2) = x ^ 2 := by field_simp
  refine And.intro hY (And.intro hl (And.intro hR (And.intro hRGeometry ?_)))
  change E <= x ^ 2 / (B * Real.log x ^ 2)
  exact le_of_mul_le_mul_right (hFinal.trans_eq hCancel.symm) hDen


open PrimeFactorOscillations.QRH

/-- Almost all actual quarter-block prime pairs can be retained in one
native codebook with every distinct agreement rate exactly three eighths. -/
theorem eventually_native_prime_pair_density_one
    (eps : Real) (heps : 0 < eps) :
    Filter.Eventually (fun Y : Nat =>
      exists M : Finset (Prod Nat Nat),
        M <= primeBlockGapSet (2 * (Y / 4)) (3 * (Y / 4)) (4 * (Y / 4)) /\
        (1 - eps) *
          ((primeBlockGapSet (2 * (Y / 4)) (3 * (Y / 4)) (4 * (Y / 4))).card : Real) <=
            (M.card : Real) /\
        (forall a : Prod Nat Nat, Membership.mem M a ->
          Nat.Prime a.1 /\ Nat.Prime (a.1 + a.2) /\ 0 < a.2 /\
            a.2 < a.1 /\ a.1 + a.2 <= Y) /\
        (forall a : Prod Nat Nat, Membership.mem M a ->
          forall b : Prod Nat Nat, Membership.mem M b -> Not (a = b) ->
            nativeAgreementRate a.1 a.2 b.1 b.2 = 3 / 8)) atTop := by
  classical
  have heps0 : Not (eps = 0) := ne_of_gt heps
  choose C hC hTail using exists_primeBlock_largeSquarepart_small_allowance
  choose T hT hTailT using hTail (eps / 3) (by positivity)
  have hError := eventually_native_density_one_cutoff 4 (by decide) C hC.le
    (243 / eps) (by positivity)
  have hProb := (tendsto_native_weighted_endpoint_output_probability_zero T).eventually
    (gt_mem_nhds (show (0 : Real) < eps / 972 by positivity))
  have hPnt := PrimeFactorOscillations.eventually_thetaPrefix_and_primeCounting_bounds
    (1 : Real) (by norm_num)
  choose N0 hN0 using eventually_primeQuarterBlock_supply.exists_forall_of_atTop
  filter_upwards [hError, hProb, hPnt, eventually_ge_atTop (4 * N0 + 24)]
    with Y hErr hPr hPi hY
  let N := Y / 4
  let a := 2 * N
  let b := 3 * N
  let c := 4 * N
  let A := primeBlockSet a b
  let B := primeBlockSet b c
  let f : Prod Nat Nat -> Prod Nat Nat := fun z => Prod.mk z.1 (z.2 - z.1)
  let S := (A.product B).image f
  let Bad := S.filter (fun z => exists u : Nat, T <= u /\ Dvd.dvd (u ^ 2) z.2)
  let V := S.filter (fun z => Not (exists u : Nat, T <= u /\ Dvd.dvd (u ^ 2) z.2))
  let R := Nat.ceil ((Y : Real) ^ (1 / 8 : Real))
  let x : Real := Y
  let l := Real.log x
  let K : Real := (A.card : Real) * (B.card : Real)
  let D : Real := x ^ 2 / l ^ 2
  let Error : Real := C * (R : Real) * x ^ (7 / 4 : Real) *
    (1 + 2 * Real.log (x + 2)) ^ 4 + x * ((Y / R : Nat) : Real)
  let W := ((primePairs Y).filter
    (fun pq => nativeWeightedEndpointPrimeOutput T pq.1 pq.2)).card
  have hNbase : N0 <= N := by dsimp [N]; omega
  have hNY : 4 * N <= Y := by dsimp [N]; omega
  have hNrel : 2 * Y <= 9 * N := by dsimp [N]; omega
  have hcY : c <= Y := hNY
  have hLog : 1 <= l := hErr.2.1
  have hlPos : 0 < l := by linarith
  have hl0 : Not (l = 0) := ne_of_gt hlPos
  have hl2 : 0 < l ^ 2 := pow_pos hlPos 2
  have hR : 2 <= R := hErr.2.2.1
  have hRA : R ^ 2 <= a := by
    have hh : R ^ 2 <= Y / 4 := hErr.2.2.2.1
    dsimp only [a, N]
    omega
  have hK : 0 <= K := by dsimp [K]; positivity
  have hSupply := (hN0 N hNbase).2 Y hNY
  have hA : (N : Real) <= 2 * (A.card : Real) * l := hSupply.1
  have hB : (N : Real) <= 2 * (B.card : Real) * l := hSupply.2
  have hProduct : (N : Real) ^ 2 <= 4 * K * l ^ 2 := by
    have hh := mul_le_mul hA hB (Nat.cast_nonneg N)
      (by positivity : 0 <= 2 * (A.card : Real) * l)
    dsimp only [K]
    nlinarith only [hh]
  have hGeometry : 2 * x <= 9 * (N : Real) := by
    dsimp only [x]
    exact_mod_cast hNrel
  have hGeometrySq := mul_self_le_mul_self
    (by positivity : 0 <= 2 * x) hGeometry
  have hScale : D <= 81 * K := by
    have hn : x ^ 2 <= (81 * K) * l ^ 2 := by
      nlinarith only [hProduct, hGeometrySq]
    have he : D * l ^ 2 = x ^ 2 := by dsimp only [D]; field_simp
    apply le_of_mul_le_mul_right ?_ hl2
    rw [he]
    exact hn
  have hSmall : eps / 243 * D <= eps / 3 * K := by
    have hh := mul_le_mul_of_nonneg_left hScale
      (show 0 <= eps / 243 by positivity)
    nlinarith only [hh]
  have hErrorBound : Error <= eps / 243 * D := by
    have hh : Error <= x ^ 2 / ((243 / eps) * l ^ 2) := hErr.2.2.2.2
    calc
      Error <= x ^ 2 / ((243 / eps) * l ^ 2) := hh
      _ = eps / 243 * D := by
        dsimp only [D]
        field_simp [heps0, hl0]
  have hPiScalar : (Nat.primeCounting Y : Real) <= 2 * x / l := by
    simpa only [one_add_one_eq_two] using hPi.2.2
  have hPiSq : (Nat.primeCounting Y : Real) ^ 2 <= 4 * D := by
    have hh := mul_self_le_mul_self (Nat.cast_nonneg (Nat.primeCounting Y)) hPiScalar
    calc
      (Nat.primeCounting Y : Real) ^ 2 =
          (Nat.primeCounting Y : Real) * (Nat.primeCounting Y : Real) := by ring
      _ <= (2 * x / l) * (2 * x / l) := hh
      _ = 4 * D := by dsimp only [D]; ring
  have hPiPosNat : 0 < Nat.primeCounting Y := by
    rw [<- Nat.primesLE_card_eq_primeCounting]
    exact Finset.card_pos.mpr (Exists.intro 2
      (Nat.mem_primesLE.mpr (And.intro (by omega) Nat.prime_two)))
  have hPiPos : (0 : Real) < (Nat.primeCounting Y : Real) := by exact_mod_cast hPiPosNat
  have hMass : (W : Real) = primePairProbability Y
      (fun pq => nativeWeightedEndpointPrimeOutput T pq.1 pq.2) *
        (Nat.primeCounting Y : Real) ^ 2 := by
    change (W : Real) = ((W : Real) / (Nat.primeCounting Y : Real) ^ 2) *
      (Nat.primeCounting Y : Real) ^ 2
    field_simp [ne_of_gt hPiPos]
  have hW : (W : Real) <= eps / 243 * D := by
    calc
      (W : Real) = primePairProbability Y
          (fun pq => nativeWeightedEndpointPrimeOutput T pq.1 pq.2) *
            (Nat.primeCounting Y : Real) ^ 2 := hMass
      _ <= (eps / 972) * (Nat.primeCounting Y : Real) ^ 2 :=
        mul_le_mul_of_nonneg_right hPr.le (sq_nonneg _)
      _ <= (eps / 972) * (4 * D) :=
        mul_le_mul_of_nonneg_left hPiSq (by positivity)
      _ = eps / 243 * D := by ring
  have hcoords (z : Prod Nat Nat) (hz : Membership.mem S z) :
      Membership.mem A z.1 /\ Membership.mem B (z.1 + z.2) /\
        0 < z.2 /\ z.2 <= Y := by
    choose w hw he using Finset.mem_image.mp hz
    have hwAB := Finset.mem_product.mp hw
    have ha := (mem_primeBlockSet_iff a b w.1).mp hwAB.1
    have hb := (mem_primeBlockSet_iff b c w.2).mp hwAB.2
    have he1 : w.1 = z.1 := by
      have hp := congrArg (fun t : Prod Nat Nat => t.1) he
      exact hp
    have he2 : w.2 - w.1 = z.2 := by
      have hp := congrArg (fun t : Prod Nat Nat => t.2) he
      exact hp
    have hsum : z.1 + z.2 = w.2 := by omega
    have hzA : Membership.mem A z.1 := by rw [<- he1]; exact hwAB.1
    have hzB : Membership.mem B (z.1 + z.2) := by rw [hsum]; exact hwAB.2
    exact And.intro hzA (And.intro hzB (And.intro (by omega) (by omega)))
  have hshort (z : Prod Nat Nat) (hz : Membership.mem S z) :
      Nat.Prime z.1 /\ Nat.Prime (z.1 + z.2) /\ 0 < z.2 /\
        z.2 < z.1 /\ z.1 + z.2 <= Y := by
    have hh := hcoords z hz
    have hp := (mem_primeBlockSet_iff a b z.1).mp hh.1
    have hq := (mem_primeBlockSet_iff b c (z.1 + z.2)).mp hh.2.1
    dsimp only [a, b, c] at hp hq
    exact And.intro hp.1 (And.intro hq.1
      (And.intro hh.2.2.1 (And.intro (by omega) (by omega))))
  have hinj : Set.InjOn f (fun z => Membership.mem (A.product B) z) := by
    intro x hx y hy he
    have hxAB := Finset.mem_product.mp hx
    have hyAB := Finset.mem_product.mp hy
    have hxA := (mem_primeBlockSet_iff a b x.1).mp hxAB.1
    have hxB := (mem_primeBlockSet_iff b c x.2).mp hxAB.2
    have hyA := (mem_primeBlockSet_iff a b y.1).mp hyAB.1
    have hyB := (mem_primeBlockSet_iff b c y.2).mp hyAB.2
    have he1 : x.1 = y.1 := by
      have hp := congrArg (fun t : Prod Nat Nat => t.1) he
      exact hp
    have he2 : x.2 - x.1 = y.2 - y.1 := by
      have hp := congrArg (fun t : Prod Nat Nat => t.2) he
      exact hp
    exact Prod.ext he1 (by omega)
  have hcard : S.card = A.card * B.card := by
    dsimp only [S]
    rw [Finset.card_image_iff.mpr hinj]
    exact Finset.card_product A B
  have hKcast : (S.card : Real) = K := by
    dsimp only [K]
    exact_mod_cast hcard
  have hAcard : A.card <= Y := by
    have hh : A <= Finset.Icc 1 Y := by
      intro p hp
      have hm := (mem_primeBlockSet_iff a b p).mp hp
      exact Finset.mem_Icc.mpr (And.intro hm.1.pos (by dsimp [b] at hm; omega))
    have hc := Finset.card_le_card hh
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hc
  have hHigh : (A.card : Real) * ((Y / R : Nat) : Real) <=
      x * ((Y / R : Nat) : Real) :=
    mul_le_mul_of_nonneg_right (by dsimp only [x]; exact_mod_cast hAcard) (Nat.cast_nonneg _)
  have hBad : (Bad.card : Real) <= eps / 3 * K + Error := by
    have hh := hTailT a b c Y R hR hRA
      (by dsimp [a, b]; omega) (by dsimp [b, c]; omega) hcY
    change (Bad.card : Real) <=
      (eps / 3) * (A.card : Real) * (B.card : Real) +
        C * (R : Real) * x ^ (7 / 4 : Real) *
          (1 + 2 * Real.log (x + 2)) ^ 4 +
        (A.card : Real) * ((Y / R : Nat) : Real) at hh
    dsimp only [K, Error]
    nlinarith only [hh, hHigh]
  have hV : V <= S := Finset.filter_subset _ _
  have hVprime (z : Prod Nat Nat) (hz : Membership.mem V z) :=
    hshort z (hV hz)
  have hVclean (z : Prod Nat Nat) (hz : Membership.mem V z)
      (u : Nat) (hu : T <= u) : Not (Dvd.dvd (u ^ 2) z.2) := by
    intro hd
    exact (Finset.mem_filter.mp hz).2 (Exists.intro u (And.intro hu hd))
  choose M hM hPack hFlat using native_clean_sparse_collision_packing V T Y hVprime hVclean
  have hcover : S <= Union.union V Bad := by
    intro z hz
    by_cases hb : exists u : Nat, T <= u /\ Dvd.dvd (u ^ 2) z.2
    . exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr (And.intro hz hb)))
    . exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr (And.intro hz hb)))
  have hSV : S.card <= V.card + Bad.card :=
    (Finset.card_le_card hcover).trans (Finset.card_union_le V Bad)
  have hPack' : V.card <= M.card + W := hPack
  have hFullNat : S.card <= M.card + Bad.card + W := by omega
  have hFull : (S.card : Real) <= (M.card : Real) + (Bad.card : Real) + (W : Real) := by
    exact_mod_cast hFullNat
  refine Exists.intro M (And.intro (fun z hz => hV (hM hz)) (And.intro ?_
    (And.intro (fun z hz => hshort z (hV (hM hz))) hFlat)))
  change (1 - eps) * (S.card : Real) <= (M.card : Real)
  rw [hKcast]
  have hEB := hErrorBound.trans hSmall
  have hWB := hW.trans hSmall
  nlinarith only [hFull, hKcast, hBad, hEB, hWB]

/-- Almost all actual positive-gap prime pairs up to the full height can be
retained with distinct native agreement rates exactly three eighths. -/
theorem eventually_native_full_prime_pair_density_one
    (eps : Real) (heps : 0 < eps) :
    Filter.Eventually (fun Y : Nat =>
      exists M : Finset (Prod Nat Nat),
        M <= nativeFullPrimePairGapSet Y /\
        (1 - eps) * ((nativeFullPrimePairGapSet Y).card : Real) <= (M.card : Real) /\
        (forall z : Prod Nat Nat, Membership.mem M z ->
          Nat.Prime z.1 /\ Nat.Prime (z.1 + z.2) /\ 0 < z.2 /\ z.1 + z.2 <= Y) /\
        (forall z : Prod Nat Nat, Membership.mem M z ->
          forall w : Prod Nat Nat, Membership.mem M w -> Not (z = w) ->
            nativeAgreementRate z.1 z.2 w.1 w.2 = 3 / 8)) atTop := by
  classical
  have heps0 : Not (eps = 0) := ne_of_gt heps
  let J := Nat.ceil (2592 / eps) + 4
  have hJ : 0 < J := by dsimp only [J]; omega
  have hjPos : (0 : Real) < (J : Real) := by exact_mod_cast hJ
  have hj0 : Not ((J : Real) = 0) := ne_of_gt hjPos
  have hJceil : (2592 / eps : Real) <= (J : Real) := by
    have hl := Nat.le_ceil (2592 / eps)
    have hg : (Nat.ceil (2592 / eps) : Real) <= (J : Real) := by
      dsimp only [J]
      exact_mod_cast (show Nat.ceil (2592 / eps) <= Nat.ceil (2592 / eps) + 4 by omega)
    exact hl.trans hg
  have hBudget : (2592 : Real) <= eps * (J : Real) := by
    have hh := mul_le_mul_of_nonneg_right hJceil heps.le
    have hc : (2592 / eps : Real) * eps = 2592 := by field_simp [heps0]
    nlinarith only [hh, hc]
  have hCoeff : (8 / (J : Real)) <= eps / 324 := by
    apply le_of_mul_le_mul_right ?_ hjPos
    have he : (8 / (J : Real)) * (J : Real) = 8 := by field_simp [hj0]
    rw [he]
    nlinarith only [hBudget]
  choose C hC hTail using exists_primeBlocksSupport_largeSquarepart_small_allowance
  choose T hT hTailT using hTail (eps / 1296) (by positivity)
  have hError := eventually_native_density_one_cutoff J hJ C hC.le
    (324 / eps) (by positivity)
  have hSupplies := eventually_native_full_pair_supplies J hJ
  have hRoot := (tendsto_native_weighted_endpoint_output_probability_zero T).eventually
    (gt_mem_nhds (show (0 : Real) < eps / 2592 by positivity))
  have hCross := (tendsto_native_cross_endpoint_output_probability_zero J).eventually
    (gt_mem_nhds (show (0 : Real) < eps / 2592 by positivity))
  filter_upwards [hError, hSupplies, hRoot, hCross] with Y hErr hSup hEr hWr
  let S := nativeFullPrimePairGapSet Y
  let a := Y / J
  let A := primeBlockSet a Y
  let U := S.filter (fun z => a < z.1)
  let Low := S.filter (fun z => z.1 <= a)
  let Bad := U.filter (fun z => exists u : Nat, T <= u /\ Dvd.dvd (u ^ 2) z.2)
  let V := U.filter (fun z => Not (exists u : Nat, T <= u /\ Dvd.dvd (u ^ 2) z.2))
  let R := Nat.ceil ((Y : Real) ^ (1 / 8 : Real))
  let x : Real := Y
  let l := Real.log x
  let D : Real := x ^ 2 / l ^ 2
  let Error : Real := C * (R : Real) * x ^ (7 / 4 : Real) *
    (1 + 2 * Real.log (x + 2)) ^ 4 + x * ((Y / R : Nat) : Real)
  let E := ((primePairs Y).filter
    (fun pq => nativeWeightedEndpointPrimeOutput T pq.1 pq.2)).card
  let W := ((primePairs Y).filter
    (fun pq => nativeCrossEndpointPrimeOutput J pq.1 pq.2)).card
  have hLog : 1 <= l := hErr.2.1
  have hlPos : 0 < l := by linarith
  have hl0 : Not (l = 0) := ne_of_gt hlPos
  have hD0 : 0 <= D := by dsimp only [D]; positivity
  have hR : 2 <= R := hErr.2.2.1
  have hRA : R ^ 2 <= a := hErr.2.2.2.1
  have haY : a <= Y := Nat.div_le_self Y J
  have hScale : D <= 81 * (S.card : Real) := hSup.2.2.1
  have hPiSq : (Nat.primeCounting Y : Real) ^ 2 <= 4 * D := hSup.2.2.2.1
  have hPrefix : (Nat.primeCounting a : Real) * (Nat.primeCounting Y : Real) <=
      (8 / (J : Real)) * D := hSup.2.2.2.2
  have hSmall : eps / 324 * D <= eps / 4 * (S.card : Real) := by
    have hh := mul_le_mul_of_nonneg_left hScale
      (show (0 : Real) <= eps / 324 by positivity)
    nlinarith only [hh]
  have hErrorBound : Error <= eps / 324 * D := by
    have hh : Error <= x ^ 2 / ((324 / eps) * l ^ 2) := hErr.2.2.2.2
    calc
      Error <= x ^ 2 / ((324 / eps) * l ^ 2) := hh
      _ = eps / 324 * D := by dsimp only [D]; field_simp [heps0, hl0]
  have hScoords (z : Prod Nat Nat) (hz : Membership.mem S z) :
      Nat.Prime z.1 /\ Nat.Prime (z.1 + z.2) /\ 0 < z.2 /\ z.1 + z.2 <= Y :=
    (mem_nativeFullPrimePairGapSet_iff Y z.1 z.2).mp hz
  have hU : U <= S := Finset.filter_subset _ _
  have hLowCard : Low.card <= Nat.primeCounting a * Nat.primeCounting Y := by
    have hh : Low.card <= ((Nat.primesLE a).product (Nat.primesLE Y)).card := by
      apply Finset.card_le_card_of_injOn (fun z : Prod Nat Nat => Prod.mk z.1 (z.1 + z.2))
      . intro z hz
        have hp := hScoords z (Finset.mem_filter.mp hz).1
        exact Finset.mem_product.mpr (And.intro
          (Nat.mem_primesLE.mpr (And.intro (Finset.mem_filter.mp hz).2 hp.1))
          (Nat.mem_primesLE.mpr (And.intro hp.2.2.2 hp.2.1)))
      . intro z hz w hw he
        have hp1 := congrArg (fun t : Prod Nat Nat => t.1) he
        have hp2 := congrArg (fun t : Prod Nat Nat => t.2) he
        have hn : z.1 = w.1 := hp1
        have hq : z.1 + z.2 = w.1 + w.2 := hp2
        exact Prod.ext hn (by omega)
    have hc : ((Nat.primesLE a).product (Nat.primesLE Y)).card =
        Nat.primeCounting a * Nat.primeCounting Y := by
      calc
        _ = (Nat.primesLE a).card * (Nat.primesLE Y).card :=
          Finset.card_product (Nat.primesLE a) (Nat.primesLE Y)
        _ = Nat.primeCounting a * Nat.primeCounting Y := by
          simp only [Nat.primesLE_card_eq_primeCounting]
    exact hh.trans_eq hc
  have hLow : (Low.card : Real) <= eps / 324 * D := by
    calc
      (Low.card : Real) <=
          (Nat.primeCounting a : Real) * (Nat.primeCounting Y : Real) := by
        exact_mod_cast hLowCard
      _ <= (8 / (J : Real)) * D := hPrefix
      _ <= eps / 324 * D := mul_le_mul_of_nonneg_right hCoeff hD0
  have hAPi : A.card <= Nat.primeCounting Y := by
    have hs : A <= Nat.primesLE Y := by
      intro p hp
      have hh := (mem_primeBlockSet_iff a Y p).mp hp
      exact Nat.mem_primesLE.mpr (And.intro hh.2.2 hh.1)
    have hc := Finset.card_le_card hs
    simpa only [Nat.primesLE_card_eq_primeCounting] using hc
  have hAcard : A.card <= Y := by
    have hs : A <= Finset.Icc 1 Y := by
      intro p hp
      have hh := (mem_primeBlockSet_iff a Y p).mp hp
      exact Finset.mem_Icc.mpr (And.intro hh.1.pos hh.2.2)
    have hc := Finset.card_le_card hs
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hc
  have hAPiSq : (A.card : Real) ^ 2 <= (Nat.primeCounting Y : Real) ^ 2 := by
    have hh := mul_self_le_mul_self (Nat.cast_nonneg A.card)
      (show (A.card : Real) <= Nat.primeCounting Y by exact_mod_cast hAPi)
    nlinarith only [hh]
  have hUcoords (z : Prod Nat Nat) (hz : Membership.mem U z) :
      Membership.mem A z.1 /\ Membership.mem A (z.1 + z.2) /\
        0 < z.2 /\ z.2 <= Y := by
    have hp := hScoords z (hU hz)
    have hcut := (Finset.mem_filter.mp hz).2
    have hlo : Membership.mem A z.1 :=
      (mem_primeBlockSet_iff a Y z.1).mpr
        (And.intro hp.1 (And.intro hcut (by omega)))
    have hup : Membership.mem A (z.1 + z.2) :=
      (mem_primeBlockSet_iff a Y (z.1 + z.2)).mpr
        (And.intro hp.2.1 (And.intro (by have hh := hp.2.2.1; omega) hp.2.2.2))
    exact And.intro hlo (And.intro hup (And.intro hp.2.2.1 (by omega)))
  have hHigh : (A.card : Real) * ((Y / R : Nat) : Real) <=
      x * ((Y / R : Nat) : Real) :=
    mul_le_mul_of_nonneg_right (by dsimp only [x]; exact_mod_cast hAcard) (Nat.cast_nonneg _)
  have hPrincipal : (eps / 1296) * (A.card : Real) * (A.card : Real) <=
      eps / 324 * D := by
    have hh := mul_le_mul_of_nonneg_left (hAPiSq.trans hPiSq)
      (show (0 : Real) <= eps / 1296 by positivity)
    nlinarith only [hh]
  have hBad : (Bad.card : Real) <= eps / 324 * D + Error := by
    have hh := hTailT a Y a Y Y R U hR hRA hRA haY haY (le_refl Y) (le_refl Y) hUcoords
    change (Bad.card : Real) <=
      (eps / 1296) * (A.card : Real) * (A.card : Real) +
        C * (R : Real) * x ^ (7 / 4 : Real) *
          (1 + 2 * Real.log (x + 2)) ^ 4 +
        (A.card : Real) * ((Y / R : Nat) : Real) at hh
    dsimp only [Error]
    nlinarith only [hh, hHigh, hPrincipal]
  have hPiPosNat : 0 < Nat.primeCounting Y := by
    rw [<- Nat.primesLE_card_eq_primeCounting]
    exact Finset.card_pos.mpr (Exists.intro 2
      (Nat.mem_primesLE.mpr (And.intro (by have hy := hErr.1; omega) Nat.prime_two)))
  have hPiPos : (0 : Real) < (Nat.primeCounting Y : Real) := by exact_mod_cast hPiPosNat
  have hEventBound (P : Prod Nat Nat -> Prop)
      (hP : primePairProbability Y P <= eps / 2592) :
      (((primePairs Y).filter P).card : Real) <= eps / 648 * D := by
    have he : (((primePairs Y).filter P).card : Real) =
        primePairProbability Y P * (Nat.primeCounting Y : Real) ^ 2 := by
      unfold primePairProbability
      field_simp [ne_of_gt hPiPos]
    calc
      (((primePairs Y).filter P).card : Real) =
          primePairProbability Y P * (Nat.primeCounting Y : Real) ^ 2 := he
      _ <= (eps / 2592) * (Nat.primeCounting Y : Real) ^ 2 :=
        mul_le_mul_of_nonneg_right hP (sq_nonneg _)
      _ <= (eps / 2592) * (4 * D) :=
        mul_le_mul_of_nonneg_left hPiSq (by positivity)
      _ = eps / 648 * D := by ring
  have hEW : (E : Real) + (W : Real) <= eps / 324 * D := by
    have he := hEventBound
      (fun pq => nativeWeightedEndpointPrimeOutput T pq.1 pq.2) hEr.le
    have hw := hEventBound
      (fun pq => nativeCrossEndpointPrimeOutput J pq.1 pq.2) hWr.le
    change (E : Real) <= eps / 648 * D at he
    change (W : Real) <= eps / 648 * D at hw
    nlinarith only [he, hw]
  have hV : V <= U := Finset.filter_subset _ _
  have haFour : 4 <= a := by
    have hh := Nat.pow_le_pow_left hR 2
    norm_num at hh
    omega
  have hVprime (z : Prod Nat Nat) (hz : Membership.mem V z) :
      Nat.Prime z.1 /\ Nat.Prime (z.1 + z.2) /\ 0 < z.2 /\
        2 < z.1 /\ z.1 + z.2 <= Y /\ Y < J * z.1 := by
    have hp := hScoords z (hU (hV hz))
    have hcut : a < z.1 := (Finset.mem_filter.mp (hV hz)).2
    have hdiv : Y < z.1 * J :=
      (Nat.div_lt_iff_lt_mul hJ).mp (show Y / J < z.1 from hcut)
    have hJn : Y < J * z.1 := by simpa only [Nat.mul_comm] using hdiv
    exact And.intro hp.1 (And.intro hp.2.1 (And.intro hp.2.2.1
      (And.intro (by omega) (And.intro hp.2.2.2 hJn))))
  have hVclean (z : Prod Nat Nat) (hz : Membership.mem V z)
      (u : Nat) (hu : T <= u) : Not (Dvd.dvd (u ^ 2) z.2) := by
    intro hd
    exact (Finset.mem_filter.mp hz).2 (Exists.intro u (And.intro hu hd))
  choose M hM hPack hFlat using
    native_unrestricted_clean_sparse_collision_packing V T J Y hVprime hVclean
  have hLowCover : S <= Union.union Low U := by
    intro z hz
    by_cases hcut : z.1 <= a
    . exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr (And.intro hz hcut)))
    . exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_filter.mpr (And.intro hz (by omega))))
  have hCleanCover : U <= Union.union V Bad := by
    intro z hz
    by_cases hb : exists u : Nat, T <= u /\ Dvd.dvd (u ^ 2) z.2
    . exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr (And.intro hz hb)))
    . exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr (And.intro hz hb)))
  have hSLow : S.card <= Low.card + U.card :=
    (Finset.card_le_card hLowCover).trans (Finset.card_union_le Low U)
  have hUV : U.card <= V.card + Bad.card :=
    (Finset.card_le_card hCleanCover).trans (Finset.card_union_le V Bad)
  have hPack' : V.card <= M.card + E + W := hPack
  have hWholeNat : S.card <= M.card + Low.card + Bad.card + E + W := by omega
  have hWhole : (S.card : Real) <=
      (M.card : Real) + (Low.card : Real) + (Bad.card : Real) + (E : Real) + (W : Real) := by
    exact_mod_cast hWholeNat
  have hLoss : (Low.card : Real) + (Bad.card : Real) + (E : Real) + (W : Real) <=
      eps * (S.card : Real) := by
    nlinarith only [hLow, hBad, hErrorBound, hEW, hSmall]
  have hKeep : (1 - eps) * (S.card : Real) <= (M.card : Real) := by
    nlinarith only [hWhole, hLoss]
  refine Exists.intro M (And.intro (fun z hz => hU (hV (hM hz)))
    (And.intro hKeep (And.intro ?_ hFlat)))
  intro z hz
  exact hScoords z (hU (hV (hM hz)))

end PrimeFactorOscillations.FiniteFieldIntegerSignature
