/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import PrimeFactorOscillations.Helpers.LPFTotientTail
import PrimeFactorOscillations.Helpers.QRHSquarefreePrimePairs

/-!
# Large squarepart deletion in actual prime blocks

The full supported square-divisor union is retained. Its low-divisor
principal allowance has a summable totient-square tail; the high divisors
are controlled by the exact natural-quotient bound.
-/

set_option autoImplicit false
set_option Elab.async false

open Filter
open scoped Classical Topology

namespace PrimeFactorOscillations.QRH

private noncomputable def squarepartWeight (u : Nat) : Real :=
  1 / ((u ^ 2).totient : Real)

private theorem squarepartWeight_nonneg (u : Nat) :
    0 <= squarepartWeight u := by
  exact div_nonneg (by norm_num) (Nat.cast_nonneg _)

private theorem squarepartWeight_summable : Summable squarepartWeight := by
  have hp : Summable (fun u : Nat => 1 / (u : Real) ^ (3 / 2 : Real)) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  apply Summable.of_nonneg_of_le squarepartWeight_nonneg ?_ (hp.mul_left 4)
  intro u
  by_cases hu : u = 0
  . simp [hu, squarepartWeight]
  have hu0 : 0 < u := Nat.pos_of_ne_zero hu
  have hphi : (0 : Real) < (u.totient : Real) := by
    exact_mod_cast Nat.totient_pos.mpr hu0
  have hmul := Nat.totient_super_multiplicative u u
  have hsq : (u.totient : Real) ^ 2 <= ((u ^ 2).totient : Real) := by
    exact_mod_cast (show u.totient ^ 2 <= (u ^ 2).totient by
      simpa only [pow_two] using hmul)
  have hfirst : squarepartWeight u <= 1 / (u.totient : Real) ^ 2 :=
    one_div_le_one_div_of_le (pow_pos hphi 2) hsq
  calc
    squarepartWeight u <= 1 / (u.totient : Real) ^ 2 := hfirst
    _ <= 4 / (u : Real) ^ (3 / 2 : Real) :=
      LPF.lpf_totient_inverse_sq_power_bound u hu0
    _ = 4 * (1 / (u : Real) ^ (3 / 2 : Real)) := by ring

private noncomputable def squarepartAllowance (T : Nat) : Real :=
  (tsum squarepartWeight) - (Finset.range T).sum squarepartWeight

private theorem squarepartAllowance_tendsto :
    Tendsto squarepartAllowance atTop (nhds (0 : Real)) := by
  have h : Tendsto (fun T : Nat =>
      (tsum squarepartWeight) - (Finset.range T).sum squarepartWeight) atTop
      (nhds ((tsum squarepartWeight) - (tsum squarepartWeight))) :=
    tendsto_const_nhds.sub squarepartWeight_summable.hasSum.tendsto_sum_nat
  change Tendsto (fun T : Nat =>
    (tsum squarepartWeight) - (Finset.range T).sum squarepartWeight) atTop (nhds (0 : Real))
  simpa only [sub_self] using h

private theorem squarepart_sum_le_allowance (S : Finset Nat) (T : Nat)
    (hS : forall u : Nat, Membership.mem S u -> T <= u) :
    S.sum squarepartWeight <= squarepartAllowance T := by
  have hd : Disjoint (Finset.range T) S := by
    apply Finset.disjoint_left.mpr
    intro u hu hsu
    have hl := Finset.mem_range.mp hu
    have hg := hS u hsu
    omega
  have hu := Summable.sum_le_tsum (Union.union (Finset.range T) S)
    (fun u _ => squarepartWeight_nonneg u) squarepartWeight_summable
  rw [Finset.sum_union hd] at hu
  dsimp only [squarepartAllowance]
  linarith


/-- All large square-divisor deletions have arbitrarily small principal mass,
with the complete low-character and high-divisor errors retained. -/
theorem exists_primeBlocksSupport_largeSquarepart_small_allowance :
    exists C : Real, 0 < C /\
      forall eps : Real, 0 < eps ->
        exists T : Nat, 2 <= T /\
          forall (a b c d Y R : Nat) (S : Finset (Prod Nat Nat)),
            2 <= R -> R ^ 2 <= a -> R ^ 2 <= c ->
            a <= b -> c <= d -> b <= Y -> d <= Y ->
            (forall z : Prod Nat Nat, Membership.mem S z ->
              Membership.mem (primeBlockSet a b) z.1 /\
              Membership.mem (primeBlockSet c d) (z.1 + z.2) /\
              0 < z.2 /\ z.2 <= Y) ->
              ((S.filter (fun z =>
                exists u : Nat, T <= u /\ Dvd.dvd (u ^ 2) z.2)).card : Real) <=
                eps * (primeBlockSet a b).card * (primeBlockSet c d).card +
                  C * (R : Real) * (Y : Real) ^ (7 / 4 : Real) *
                    (1 + 2 * Real.log ((Y : Real) + 2)) ^ 4 +
                  (primeBlockSet a b).card * ((Y / R : Nat) : Real) := by
  classical
  choose C0 hC0 hCollision using exists_primeBlocksCollisionCount_le_seven_fourths
  refine Exists.intro C0 (And.intro hC0 ?_)
  intro eps heps
  have hev : Filter.Eventually (fun T => squarepartAllowance T < eps) atTop :=
    squarepartAllowance_tendsto.eventually (gt_mem_nhds heps)
  choose T hTail hT using (hev.and (eventually_ge_atTop 2)).exists
  refine Exists.intro T (And.intro hT ?_)
  intro a b c d Y R S hR hR2a hR2c hab hcd hbY hdY hcoords
  let A := primeBlockSet a b
  let B := primeBlockSet c d
  let P := Finset.Icc T R
  let Q : Nat -> Finset (Prod Nat Nat) := fun u =>
    S.filter (fun z => Dvd.dvd (u ^ 2) z.2)
  let D := S.filter (fun z => exists u : Nat, R + 1 <= u /\ Dvd.dvd (u ^ 2) z.2)
  let Bad := S.filter (fun z => exists u : Nat, T <= u /\ Dvd.dvd (u ^ 2) z.2)
  let K : Real := (A.card : Real) * (B.card : Real)
  let L : Real := 1 + 2 * Real.log ((Y : Real) + 2)
  let E : Real := C0 * (Y : Real) ^ (7 / 4 : Real) * L ^ 4
  have hK : 0 <= K := by dsimp [K]; positivity
  have hE : 0 <= E := by dsimp [E]; positivity
  have hQcard (p : Nat) :
      (Q p).card <= primeBlocksCollisionCount (p ^ 2) a b c d := by
    let g : Prod Nat Nat -> Prod Nat Nat := fun z => Prod.mk z.1 (z.1 + z.2)
    change (Q p).card <=
      ((A.product B).filter (fun z => (z.1 : ZMod (p ^ 2)) = (z.2 : ZMod (p ^ 2)))).card
    apply Finset.card_le_card_of_injOn g
    . intro z hz
      have hzS := (Finset.mem_filter.mp hz).1
      have hzC := hcoords z hzS
      have hd := (Finset.mem_filter.mp hz).2
      choose k hk using hd
      have hzero : (z.2 : ZMod (p ^ 2)) = 0 := by
        rw [hk, Nat.cast_mul, ZMod.natCast_self, zero_mul]
      apply Finset.mem_filter.mpr
      refine And.intro (Finset.mem_product.mpr (And.intro hzC.1 hzC.2.1)) ?_
      change (z.1 : ZMod (p ^ 2)) = ((z.1 + z.2 : Nat) : ZMod (p ^ 2))
      rw [Nat.cast_add, hzero, add_zero]
    . intro x hx y hy he
      have he1 : x.1 = y.1 := by
        have hp := congrArg (fun t : Prod Nat Nat => t.1) he
        exact hp
      have he2 : x.1 + x.2 = y.1 + y.2 := by
        have hp := congrArg (fun t : Prod Nat Nat => t.2) he
        exact hp
      exact Prod.ext he1 (by omega)
  have hQreal (p : Nat) (hp : Membership.mem P p) :
      ((Q p).card : Real) <=
        K * squarepartWeight p + E := by
    have hpI := Finset.mem_Icc.mp hp
    have hpR : p <= R := hpI.2
    have hpPos : 0 < p := by omega
    have hpSq : 0 < p ^ 2 := pow_pos hpPos 2
    have hInst : NeZero (p ^ 2) := by
      constructor
      exact Nat.ne_of_gt hpSq
    have hNa : p ^ 2 <= a := (Nat.pow_le_pow_left hpR 2).trans hR2a
    have hNc : p ^ 2 <= c := (Nat.pow_le_pow_left hpR 2).trans hR2c
    have hNY : p ^ 2 <= Y := hNa.trans (hab.trans hbY)
    have hLogN : 0 <= Real.log ((p ^ 2 : Nat) : Real) :=
      Real.log_nonneg (by exact_mod_cast (show 1 <= p ^ 2 by omega))
    have hLogY : 0 <= Real.log ((Y : Real) + 2) := Real.log_nonneg (by
      have hY0 : (0 : Real) <= Y := Nat.cast_nonneg Y
      linarith)
    have hLogNY : Real.log ((p ^ 2 : Nat) : Real) <= Real.log ((Y : Real) + 2) :=
      Real.log_le_log (by exact_mod_cast hpSq) (by
        have hh : ((p ^ 2 : Nat) : Real) <= Y := by exact_mod_cast hNY
        linarith)
    let V : Real := 1 + Real.log ((p ^ 2 : Nat) : Real) + Real.log ((Y : Real) + 2)
    have hV : 0 <= V := by dsimp [V]; linarith
    have hVL : V <= L := by dsimp [V, L]; linarith
    have hfour : V ^ 4 <= L ^ 4 := by
      have hsq := mul_self_le_mul_self hV hVL
      have hh := mul_self_le_mul_self (mul_nonneg hV hV) hsq
      nlinarith only [hh]
    have hError : C0 * (Y : Real) ^ (7 / 4 : Real) * V ^ 4 <= E := by
      dsimp only [E]
      exact mul_le_mul_of_nonneg_left hfour
        (mul_nonneg hC0.le (Real.rpow_nonneg (Nat.cast_nonneg Y) _))
    have hBound := @hCollision (p ^ 2) hInst a b c d Y hNa hNc hab hcd hbY hdY
    change abs ((primeBlocksCollisionCount (p ^ 2) a b c d : Real) -
      K / ((p ^ 2).totient : Real)) <=
        C0 * (Y : Real) ^ (7 / 4 : Real) * V ^ 4 at hBound
    have hUpper := (le_abs_self
      ((primeBlocksCollisionCount (p ^ 2) a b c d : Real) -
        K / ((p ^ 2).totient : Real))).trans hBound
    have hCast : ((Q p).card : Real) <= primeBlocksCollisionCount (p ^ 2) a b c d := by
      exact_mod_cast hQcard p
    calc
      ((Q p).card : Real) <= K / ((p ^ 2).totient : Real) + E := by linarith
      _ = K * squarepartWeight p + E := by
        simp only [squarepartWeight, div_eq_mul_inv, one_mul]
  have hPcard : P.card <= R := by
    have hs : P <= Finset.Icc 1 R := by
      intro p hp
      have hi := Finset.mem_Icc.mp hp
      exact Finset.mem_Icc.mpr (And.intro (by omega) hi.2)
    have hh := Finset.card_le_card hs
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hh
  have hrecip : P.sum squarepartWeight <= eps :=
    (squarepart_sum_le_allowance P T (fun u hu => (Finset.mem_Icc.mp hu).1)).trans hTail.le
  have hsumQ : ((P.sum (fun p => (Q p).card) : Nat) : Real) <=
      K * eps + (R : Real) * E := by
    rw [Nat.cast_sum]
    calc
      P.sum (fun p => ((Q p).card : Real)) <=
          P.sum (fun p => K * squarepartWeight p + E) :=
        Finset.sum_le_sum hQreal
      _ = K * P.sum squarepartWeight + (P.card : Real) * E := by
        rw [Finset.sum_add_distrib, <- Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      _ <= K * eps + (R : Real) * E :=
        add_le_add (mul_le_mul_of_nonneg_left hrecip hK)
          (mul_le_mul_of_nonneg_right (by exact_mod_cast hPcard) hE)
  have hD : D.card <= A.card * (Y / R) := by
    have hsmall (z : Prod Nat Nat) (hz : Membership.mem S z) :
        Membership.mem A z.1 /\ 0 < z.2 /\ z.2 <= Y :=
      And.intro (hcoords z hz).1 (hcoords z hz).2.2
    simpa only [Nat.add_sub_cancel] using
      Finset.card_filter_exists_sq_dvd_le S A Y (R + 1) (by omega) hsmall
  have hcover : Bad <= Union.union (P.biUnion Q) D := by
    intro z hz
    have hzS := (Finset.mem_filter.mp hz).1
    choose u hu hd using (Finset.mem_filter.mp hz).2
    apply Finset.mem_union.mpr
    by_cases hlow : u <= R
    . exact Or.inl (Finset.mem_biUnion.mpr (Exists.intro u
        (And.intro (Finset.mem_Icc.mpr (And.intro hu hlow))
          (Finset.mem_filter.mpr (And.intro hzS hd)))))
    . exact Or.inr (Finset.mem_filter.mpr (And.intro hzS
        (Exists.intro u (And.intro (by omega) hd))))
  have hcard : Bad.card <= P.sum (fun p => (Q p).card) + A.card * (Y / R) := by
    calc
      Bad.card <= (Union.union (P.biUnion Q) D).card := Finset.card_le_card hcover
      _ <= (P.biUnion Q).card + D.card := Finset.card_union_le _ _
      _ <= P.sum (fun p => (Q p).card) + A.card * (Y / R) :=
        Nat.add_le_add Finset.card_biUnion_le hD
  have hcast : (Bad.card : Real) <=
      ((P.sum (fun p => (Q p).card) : Nat) : Real) + (A.card : Real) * (Y / R : Nat) := by
    exact_mod_cast hcard
  have hfinal : (Bad.card : Real) <= K * eps + (R : Real) * E +
      (A.card : Real) * (Y / R : Nat) := by linarith
  change (Bad.card : Real) <= _
  convert hfinal using 1
  dsimp only [K, E, L, A, B]
  ring

theorem exists_primeBlock_largeSquarepart_small_allowance :
    exists C : Real, 0 < C /\
      forall eps : Real, 0 < eps ->
        exists T : Nat, 2 <= T /\
          forall a b c Y R : Nat, 2 <= R -> R ^ 2 <= a ->
            a <= b -> b <= c -> c <= Y ->
              (((primeBlockGapSet a b c).filter (fun z =>
                exists u : Nat, T <= u /\ Dvd.dvd (u ^ 2) z.2)).card : Real) <=
                eps * (primeBlockSet a b).card * (primeBlockSet b c).card +
                  C * (R : Real) * (Y : Real) ^ (7 / 4 : Real) *
                    (1 + 2 * Real.log ((Y : Real) + 2)) ^ 4 +
                  (primeBlockSet a b).card * ((Y / R : Nat) : Real) := by
  choose C hC hAll using exists_primeBlocksSupport_largeSquarepart_small_allowance
  refine Exists.intro C (And.intro hC ?_)
  intro eps heps
  choose T hT hBound using hAll eps heps
  refine Exists.intro T (And.intro hT ?_)
  intro a b c Y R hR hR2 hab hbc hcY
  let A := primeBlockSet a b
  let B := primeBlockSet b c
  let f : Prod Nat Nat -> Prod Nat Nat := fun z => Prod.mk z.1 (z.2 - z.1)
  let S := (A.product B).image f
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
  exact hBound a b b c Y R S hR hR2 (hR2.trans hab)
    hab hbc (hbc.trans hcY) hcY hcoords

end PrimeFactorOscillations.QRH
