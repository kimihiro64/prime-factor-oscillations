/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Definitions.PrimePairEnsemble
import PrimeFactorOscillations.Helpers.PrimeBlockPackingSupply

/-!
# Actual full-height prime-pair supply and prefix loss

The full positive-gap universe contains the actual quarter-block product.
For every fixed positive J, the low-endpoint prefix has a uniform PNT upper
allowance 8/J times the same height scale. No short gaps are imposed.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter
open scoped Classical Topology

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

open PrimeFactorOscillations.QRH

noncomputable def nativeFullPrimePairGapSet (Y : Nat) : Finset (Prod Nat Nat) := by
  classical
  exact ((primePairs Y).filter (fun pq => pq.1 < pq.2)).image
    (fun pq => Prod.mk pq.1 (pq.2 - pq.1))

theorem mem_nativeFullPrimePairGapSet_iff (Y n h : Nat) :
    Membership.mem (nativeFullPrimePairGapSet Y) (Prod.mk n h) <->
      Nat.Prime n /\ Nat.Prime (n + h) /\ 0 < h /\ n + h <= Y := by
  classical
  constructor
  . intro hz
    choose w hw he using Finset.mem_image.mp hz
    have hwf := Finset.mem_filter.mp hw
    have hinput : Membership.mem
        ((Nat.primesLE Y).product (Nat.primesLE Y)) w := hwf.1
    have hwAB := Finset.mem_product.mp hinput
    have hp := Nat.mem_primesLE.mp hwAB.1
    have hq := Nat.mem_primesLE.mp hwAB.2
    have hp1 := congrArg (fun z : Prod Nat Nat => z.1) he
    have hp2 := congrArg (fun z : Prod Nat Nat => z.2) he
    have hn : w.1 = n := hp1
    have hh : w.2 - w.1 = h := hp2
    have hsum : n + h = w.2 := by omega
    exact And.intro (by rw [<- hn]; exact hp.2)
      (And.intro (by rw [hsum]; exact hq.2) (And.intro (by omega) (by omega)))
  . intro hz
    apply Finset.mem_image.mpr
    refine Exists.intro (Prod.mk n (n + h)) (And.intro ?_ ?_)
    . apply Finset.mem_filter.mpr
      refine And.intro ?_ (by have hh := hz.2.2.1; omega)
      change Membership.mem ((Nat.primesLE Y).product (Nat.primesLE Y))
        (Prod.mk n (n + h))
      exact Finset.mem_product.mpr (And.intro
        (Nat.mem_primesLE.mpr (And.intro (by have hy := hz.2.2.2; omega) hz.1))
        (Nat.mem_primesLE.mpr (And.intro hz.2.2.2 hz.2.1)))
    . exact Prod.ext rfl (by omega)

theorem eventually_native_full_pair_supplies (J : Nat) (hJ : 0 < J) :
    Filter.Eventually (fun Y : Nat =>
      24 <= Y /\ 1 <= Real.log (Y : Real) /\
      (Y : Real) ^ 2 / Real.log (Y : Real) ^ 2 <=
        81 * ((nativeFullPrimePairGapSet Y).card : Real) /\
      (Nat.primeCounting Y : Real) ^ 2 <=
        4 * ((Y : Real) ^ 2 / Real.log (Y : Real) ^ 2) /\
      (Nat.primeCounting (Y / J) : Real) * (Nat.primeCounting Y : Real) <=
        (8 / (J : Real)) * ((Y : Real) ^ 2 / Real.log (Y : Real) ^ 2)) atTop := by
  classical
  have hPnt := PrimeFactorOscillations.eventually_thetaPrefix_and_primeCounting_bounds
    (1 : Real) (by norm_num)
  choose K hK using hPnt.exists_forall_of_atTop
  choose Q hQ using eventually_primeQuarterBlock_supply.exists_forall_of_atTop
  have hLog := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R := Real))).eventually
      (eventually_ge_atTop (1 : Real))
  filter_upwards [eventually_ge_atTop
      (4 * Q + 24 + K + 2 * J + J * (K + 1) + 4 * J ^ 2), hLog]
    with Y hY hl
  let x : Real := Y
  let l := Real.log x
  let a := Y / J
  let N := Y / 4
  let A := primeBlockSet (2 * N) (3 * N)
  let B := primeBlockSet (3 * N) (4 * N)
  let P : Real := Nat.primeCounting Y
  let Pa : Real := Nat.primeCounting a
  let D : Real := x ^ 2 / l ^ 2
  let F : Real := (A.card : Real) * (B.card : Real)
  have hY24 : 24 <= Y := by omega
  have hx : 0 < x := by dsimp [x]; exact_mod_cast (by omega : 0 < Y)
  have hl1 : 1 <= l := hl
  have hlPos : 0 < l := by linarith
  have hl0 : Not (l = 0) := ne_of_gt hlPos
  have hl2 : 0 < l ^ 2 := pow_pos hlPos 2
  have hjPos : (0 : Real) < (J : Real) := by exact_mod_cast hJ
  have hj0 : Not ((J : Real) = 0) := ne_of_gt hjPos
  have haK : K <= a := by
    apply (Nat.le_div_iff_mul_le hJ).mpr
    have hmul := Nat.mul_le_mul_left J (show K <= K + 1 by omega)
    have hcomm : K * J = J * K := Nat.mul_comm K J
    omega
  have hKY : K <= Y := by omega
  have hNbase : Q <= N := by dsimp [N]; omega
  have hNY : 4 * N <= Y := by dsimp [N]; omega
  have hNrel : 2 * Y <= 9 * N := by dsimp [N]; omega
  have hSupply := (hQ N hNbase).2 Y hNY
  have hA : (N : Real) <= 2 * (A.card : Real) * l := hSupply.1
  have hB : (N : Real) <= 2 * (B.card : Real) * l := hSupply.2
  have hProduct : (N : Real) ^ 2 <= 4 * F * l ^ 2 := by
    have hh := mul_le_mul hA hB (Nat.cast_nonneg N)
      (by positivity : 0 <= 2 * (A.card : Real) * l)
    dsimp only [F]
    nlinarith only [hh]
  have hGeometry : 2 * x <= 9 * (N : Real) := by
    dsimp only [x]
    exact_mod_cast hNrel
  have hGeometrySq := mul_self_le_mul_self (by positivity : 0 <= 2 * x) hGeometry
  have hScale : D <= 81 * F := by
    have hn : x ^ 2 <= (81 * F) * l ^ 2 := by
      nlinarith only [hProduct, hGeometrySq]
    have he : D * l ^ 2 = x ^ 2 := by dsimp only [D]; field_simp
    apply le_of_mul_le_mul_right ?_ hl2
    rw [he]
    exact hn
  have hFullCard : A.card * B.card <= (nativeFullPrimePairGapSet Y).card := by
    rw [<- Finset.card_product]
    let f : Prod Nat Nat -> Prod Nat Nat := fun z => Prod.mk z.1 (z.2 - z.1)
    apply Finset.card_le_card_of_injOn f
    . intro z hz
      have hh := Finset.mem_product.mp hz
      have hp := (mem_primeBlockSet_iff (2 * N) (3 * N) z.1).mp hh.1
      have hq := (mem_primeBlockSet_iff (3 * N) (4 * N) z.2).mp hh.2
      apply (mem_nativeFullPrimePairGapSet_iff Y z.1 (z.2 - z.1)).mpr
      have hsum : z.1 + (z.2 - z.1) = z.2 := by omega
      exact And.intro hp.1 (And.intro (by rw [hsum]; exact hq.1)
        (And.intro (by omega) (by omega)))
    . intro z hz w hw he
      have hzAB := Finset.mem_product.mp hz
      have hwAB := Finset.mem_product.mp hw
      have hp := (mem_primeBlockSet_iff (2 * N) (3 * N) z.1).mp hzAB.1
      have hq := (mem_primeBlockSet_iff (3 * N) (4 * N) z.2).mp hzAB.2
      have hr := (mem_primeBlockSet_iff (2 * N) (3 * N) w.1).mp hwAB.1
      have hs := (mem_primeBlockSet_iff (3 * N) (4 * N) w.2).mp hwAB.2
      have hp1 := congrArg (fun t : Prod Nat Nat => t.1) he
      have hp2 := congrArg (fun t : Prod Nat Nat => t.2) he
      have hn : z.1 = w.1 := hp1
      have hh : z.2 - z.1 = w.2 - w.1 := hp2
      exact Prod.ext hn (by omega)
  have hF : F <= ((nativeFullPrimePairGapSet Y).card : Real) := by
    dsimp only [F]
    exact_mod_cast hFullCard
  have hActualSupply : D <= 81 * ((nativeFullPrimePairGapSet Y).card : Real) :=
    hScale.trans (mul_le_mul_of_nonneg_left hF (by norm_num))
  have hPi : P <= 2 * x / l := by
    simpa only [one_add_one_eq_two] using (hK Y hKY).2.2
  have hPiSq : P ^ 2 <= 4 * D := by
    have hh := mul_self_le_mul_self (Nat.cast_nonneg (Nat.primeCounting Y)) hPi
    calc
      P ^ 2 = P * P := by ring
      _ <= (2 * x / l) * (2 * x / l) := hh
      _ = 4 * D := by dsimp only [D]; ring
  have hPiA : Pa <= 2 * (a : Real) / Real.log (a : Real) := by
    simpa only [one_add_one_eq_two] using (hK a haK).2.2
  have ha1 : 1 <= a := by
    apply (Nat.le_div_iff_mul_le hJ).mpr
    omega
  have hDiv := Nat.div_add_mod Y J
  have hRem := Nat.mod_lt Y hJ
  have hJA : J <= J * a := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left J ha1
  have hNatGeometry : Y <= 2 * J * a := by
    dsimp only [a]
    dsimp only [a] at hJA
    nlinarith only [hDiv, hRem, hJA]
  have hCastGeometry : x <= 2 * (J : Real) * (a : Real) := by
    dsimp only [x, a]
    exact_mod_cast hNatGeometry
  have hBig : 4 * (J : Real) ^ 2 <= x := by
    dsimp only [x]
    exact_mod_cast (show 4 * J ^ 2 <= Y by omega)
  have haTwo : 2 * (J : Real) <= (a : Real) := by
    apply le_of_mul_le_mul_right ?_ hjPos
    nlinarith only [hBig, hCastGeometry]
  have hxSq : x <= (a : Real) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right haTwo (Nat.cast_nonneg a)
    nlinarith only [hCastGeometry, hh]
  have hLogA : l <= 2 * Real.log (a : Real) := by
    calc
      l <= Real.log ((a : Real) ^ 2) := Real.log_le_log hx hxSq
      _ = 2 * Real.log (a : Real) := by rw [Real.log_pow]; norm_num
  have hLogAPos : 0 < Real.log (a : Real) := by linarith
  have hLogA0 : Not (Real.log (a : Real) = 0) := ne_of_gt hLogAPos
  have hPiAMul : Pa * Real.log (a : Real) <= 2 * (a : Real) := by
    have hh := mul_le_mul_of_nonneg_right hPiA hLogAPos.le
    have he : (2 * (a : Real) / Real.log (a : Real)) *
        Real.log (a : Real) = 2 * (a : Real) := by field_simp [hLogA0]
    exact hh.trans_eq he
  have hPiYMul : P * l <= 2 * x := by
    have hh := mul_le_mul_of_nonneg_right hPi hlPos.le
    have he : (2 * x / l) * l = 2 * x := by field_simp [hl0]
    exact hh.trans_eq he
  have haMul : (a : Real) * (J : Real) <= x := by
    dsimp only [x, a]
    exact_mod_cast Nat.div_mul_le_self Y J
  have hPrefixMul : Pa * l * (J : Real) <= 4 * x := by
    have hh := mul_le_mul_of_nonneg_left hLogA
      (Nat.cast_nonneg (Nat.primeCounting a))
    have hg : Pa * l <= 4 * (a : Real) := by nlinarith only [hh, hPiAMul]
    have hm := mul_le_mul_of_nonneg_right hg hjPos.le
    nlinarith only [hm, haMul]
  have hJoint : (Pa * P) * ((J : Real) * l ^ 2) <= 8 * x ^ 2 := by
    have hh := mul_le_mul hPrefixMul hPiYMul
      (mul_nonneg (Nat.cast_nonneg (Nat.primeCounting Y)) hlPos.le)
      (by positivity : 0 <= 4 * x)
    nlinarith only [hh]
  have hCancel : ((8 / (J : Real)) * D) * ((J : Real) * l ^ 2) = 8 * x ^ 2 := by
    dsimp only [D]
    field_simp [hj0, hl0]
  have hPrefix : Pa * P <= (8 / (J : Real)) * D := by
    exact le_of_mul_le_mul_right (hJoint.trans_eq hCancel.symm) (by positivity)
  exact And.intro hY24 (And.intro hl1
    (And.intro hActualSupply (And.intro hPiSq hPrefix)))

end PrimeFactorOscillations.FiniteFieldIntegerSignature
