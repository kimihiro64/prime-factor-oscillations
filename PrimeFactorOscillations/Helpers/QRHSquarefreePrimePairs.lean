/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.QRHPrimeBlockCollision
import PrimeFactorOscillations.Mathlib.Data.Finset.ReciprocalGapSum
import PrimeFactorOscillations.Mathlib.Data.Finset.SquareDivisorCount

/-!
# A positive squarefree-gap supply between actual prime blocks

The principal product supply is retained. All low prime-square collisions
and the complete high square-divisor union occur in the same inequality.
The constant is chosen before the height, block endpoints and divisor cutoff.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QRH

theorem mem_primeBlockSet_iff (a b p : Nat) :
    Membership.mem (primeBlockSet a b) p <-> Nat.Prime p /\ a < p /\ p <= b := by
  constructor
  . intro hp
    have h := Finset.mem_sdiff.mp hp
    have hb := Nat.mem_primesBelow.mp h.1
    refine And.intro hb.2 (And.intro ?_ (by omega))
    by_contra hn
    exact h.2 (Nat.mem_primesBelow.mpr (And.intro (by omega) hb.2))
  . intro hp
    apply Finset.mem_sdiff.mpr
    refine And.intro (Nat.mem_primesBelow.mpr (And.intro (by omega) hp.1)) ?_
    intro hn
    have h := Nat.mem_primesBelow.mp hn
    omega

def primeBlockGapSet (a b c : Nat) : Finset (Prod Nat Nat) :=
  ((primeBlockSet a b).product (primeBlockSet b c)).image
    (fun (z : Prod Nat Nat) => Prod.mk z.1 (z.2 - z.1))

noncomputable def squarefreePrimeBlockGapSet (a b c : Nat) : Finset (Prod Nat Nat) := by
  classical
  exact (primeBlockGapSet a b c).filter (fun (z : Prod Nat Nat) =>
    forall u : Nat, 2 <= u -> Not (Dvd.dvd (u ^ 2) z.2))

/-- A full finite lower bound, with both deletion costs retained. -/
theorem exists_squarefreePrimeBlockGapSet_lower :
    exists C : Real, 0 < C /\
      forall a b c Y R : Nat, 2 <= R -> R ^ 2 <= a ->
        a <= b -> b <= c -> c <= Y ->
          (primeBlockSet a b).card * (primeBlockSet b c).card / (12 : Real) <=
            (squarefreePrimeBlockGapSet a b c).card +
              C * (R : Real) * (Y : Real) ^ (7 / 4 : Real) *
                (1 + 2 * Real.log ((Y : Real) + 2)) ^ 4 +
              (primeBlockSet a b).card * ((Y / R : Nat) : Real) := by
  classical
  choose C0 hC0 hCollision using exists_primeBlockCollisionCount_le_seven_fourths
  refine Exists.intro C0 (And.intro hC0 ?_)
  intro a b c Y R hR hR2 hab hbc hcY
  let A := primeBlockSet a b
  let B := primeBlockSet b c
  let f : Prod Nat Nat -> Prod Nat Nat := fun z => Prod.mk z.1 (z.2 - z.1)
  let S := (A.product B).image f
  let Clean := S.filter (fun (z : Prod Nat Nat) =>
    forall u : Nat, 2 <= u -> Not (Dvd.dvd (u ^ 2) z.2))
  let P := Nat.primesBelow (R + 1)
  let Q : Nat -> Finset (Prod Nat Nat) := fun p =>
    S.filter (fun (z : Prod Nat Nat) => Dvd.dvd (p ^ 2) z.2)
  let D := S.filter (fun (z : Prod Nat Nat) =>
    exists u : Nat, R + 1 <= u /\ Dvd.dvd (u ^ 2) z.2)
  let K : Real := (A.card : Real) * (B.card : Real)
  let L : Real := 1 + 2 * Real.log ((Y : Real) + 2)
  let E : Real := C0 * (Y : Real) ^ (7 / 4 : Real) * L ^ 4
  have hK : 0 <= K := by dsimp [K]; positivity
  have hE : 0 <= E := by dsimp [E]; positivity
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
  have hQcard (p : Nat) :
      (Q p).card <= primeBlockCollisionCount (p ^ 2) a b c := by
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
        K * (1 / ((p : Real) * ((p : Real) - 1))) + E := by
    have hpP := Nat.mem_primesBelow.mp hp
    have hpR : p <= R := by omega
    have hpSq : 0 < p ^ 2 := pow_pos hpP.2.pos 2
    have hInst : NeZero (p ^ 2) := by
      constructor
      exact Nat.ne_of_gt hpSq
    have hNa : p ^ 2 <= a := (Nat.pow_le_pow_left hpR 2).trans hR2
    have hNY : p ^ 2 <= Y := hNa.trans (hab.trans (hbc.trans hcY))
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
    have hphi : (p ^ 2).totient = p * (p - 1) := by
      rw [Nat.totient_prime_pow hpP.2 (by norm_num : 0 < (2 : Nat))]
      norm_num
    have hphiReal : ((p ^ 2).totient : Real) = (p : Real) * ((p : Real) - 1) := by
      rw [hphi, Nat.cast_mul, Nat.cast_sub hpP.2.one_le, Nat.cast_one]
    have hBound := @hCollision (p ^ 2) hInst a b c Y hNa hab hbc hcY
    change abs ((primeBlockCollisionCount (p ^ 2) a b c : Real) -
      K / ((p ^ 2).totient : Real)) <=
        C0 * (Y : Real) ^ (7 / 4 : Real) * V ^ 4 at hBound
    have hUpper := (le_abs_self
      ((primeBlockCollisionCount (p ^ 2) a b c : Real) -
        K / ((p ^ 2).totient : Real))).trans hBound
    have hCast : ((Q p).card : Real) <= primeBlockCollisionCount (p ^ 2) a b c := by
      exact_mod_cast hQcard p
    calc
      ((Q p).card : Real) <= K / ((p ^ 2).totient : Real) + E := by linarith
      _ = K * (1 / ((p : Real) * ((p : Real) - 1))) + E := by
        rw [hphiReal]
        simp only [div_eq_mul_inv, one_mul]
  have hPcard : P.card <= R := by
    have hsub : forall p : Nat, Membership.mem P p -> Membership.mem (Finset.Icc 1 R) p := by
      intro p hp
      have h := Nat.mem_primesBelow.mp hp
      exact Finset.mem_Icc.mpr (And.intro h.2.pos (by omega))
    have hh := Finset.card_le_card hsub
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hh
  have hrecip : Finset.sum P (fun p => 1 / ((p : Real) * ((p : Real) - 1))) <= 11 / 12 := by
    apply Finset.sum_inv_mul_pred_le_of_four_notMem P
    . intro p hp
      exact (Nat.mem_primesBelow.mp hp).2.two_le
    . intro hfour
      have hp := (Nat.mem_primesBelow.mp hfour).2
      exact (by decide : Not (Nat.Prime 4)) hp
  have hsumQ : ((Finset.sum P (fun p => (Q p).card) : Nat) : Real) <=
      K * (11 / 12) + (R : Real) * E := by
    rw [Nat.cast_sum]
    calc
      Finset.sum P (fun p => ((Q p).card : Real)) <=
          Finset.sum P (fun p => K * (1 / ((p : Real) * ((p : Real) - 1))) + E) :=
        Finset.sum_le_sum hQreal
      _ = K * Finset.sum P (fun p => 1 / ((p : Real) * ((p : Real) - 1))) +
          (P.card : Real) * E := by
        rw [Finset.sum_add_distrib, <- Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      _ <= K * (11 / 12) + (R : Real) * E :=
        add_le_add (mul_le_mul_of_nonneg_left hrecip hK)
          (mul_le_mul_of_nonneg_right (by exact_mod_cast hPcard) hE)
  have hD : D.card <= A.card * (Y / R) := by
    have hsmall (z : Prod Nat Nat) (hz : Membership.mem S z) :
        Membership.mem A z.1 /\ 0 < z.2 /\ z.2 <= Y :=
      And.intro (hcoords z hz).1 (hcoords z hz).2.2
    simpa only [Nat.add_sub_cancel] using
      Finset.card_filter_exists_sq_dvd_le S A Y (R + 1) (by omega) hsmall
  let Low := P.biUnion Q
  have hcover : forall z : Prod Nat Nat, Membership.mem S z ->
      Membership.mem (Union.union Clean (Union.union Low D)) z := by
    intro z hz
    by_cases hg : forall u : Nat, 2 <= u -> Not (Dvd.dvd (u ^ 2) z.2)
    . exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_filter.mpr (And.intro hz hg)))
    . have hex : exists u : Nat, 2 <= u /\ Dvd.dvd (u ^ 2) z.2 := by
        by_contra hn
        apply hg
        intro u hu hd
        exact hn (Exists.intro u (And.intro hu hd))
      choose u hu hd using hex
      choose p hp hpu using Nat.exists_prime_and_dvd (by omega : Not (u = 1))
      choose k hk using hpu
      have hpSq : Dvd.dvd (p ^ 2) (u ^ 2) := by
        refine Exists.intro (k ^ 2) ?_
        rw [hk, mul_pow]
      have hpD : Dvd.dvd (p ^ 2) z.2 := dvd_trans hpSq hd
      apply Finset.mem_union.mpr
      apply Or.inr
      apply Finset.mem_union.mpr
      by_cases hpR : p <= R
      . apply Or.inl
        apply Finset.mem_biUnion.mpr
        refine Exists.intro p (And.intro ?_ ?_)
        . exact Nat.mem_primesBelow.mpr (And.intro (by omega) hp)
        . exact Finset.mem_filter.mpr (And.intro hz hpD)
      . apply Or.inr
        exact Finset.mem_filter.mpr (And.intro hz
          (Exists.intro p (And.intro (by omega) hpD)))
  have hLow : Low.card <= Finset.sum P (fun p => (Q p).card) := Finset.card_biUnion_le
  have hsplit : S.card <= Clean.card + Finset.sum P (fun p => (Q p).card) + D.card := by
    have h1 := Finset.card_le_card hcover
    have h2 := Finset.card_union_le Clean (Union.union Low D)
    have h3 := Finset.card_union_le Low D
    omega
  have hsplitReal : K <= (Clean.card : Real) +
      ((Finset.sum P (fun p => (Q p).card) : Nat) : Real) + (D.card : Real) := by
    rw [hcard] at hsplit
    dsimp only [K]
    exact_mod_cast hsplit
  have hDReal : (D.card : Real) <= (A.card : Real) * ((Y / R : Nat) : Real) := by
    exact_mod_cast hD
  have hfinal : K / 12 <= (Clean.card : Real) + (R : Real) * E +
      (A.card : Real) * ((Y / R : Nat) : Real) := by linarith
  change K / 12 <= (Clean.card : Real) +
    C0 * (R : Real) * (Y : Real) ^ (7 / 4 : Real) * L ^ 4 +
      (A.card : Real) * ((Y / R : Nat) : Real)
  dsimp only [E] at hfinal
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hfinal

end PrimeFactorOscillations.QRH
