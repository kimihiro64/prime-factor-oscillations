/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.QRHPrimePrefix
import PrimeFactorOscillations.Mathlib.NumberTheory.DirichletCharacter.ResidueCount

/-!
# Uniform paired congruence counts on actual prime blocks

The principal mass is the product of the actual block cardinalities.
The same-character product is estimated before applying residue reconstruction,
so there is no additional totient or residue-class counting loss.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.QRH

def primeBlockSet (a b : Nat) : Finset Nat :=
  SDiff.sdiff (Nat.primesBelow (b + 1)) (Nat.primesBelow (a + 1))

noncomputable def primeBlockCollisionCount (N a b c : Nat) : Nat := by
  classical
  exact (((primeBlockSet a b).product (primeBlockSet b c)).filter
    (fun z => (z.1 : ZMod N) = (z.2 : ZMod N))).card

theorem exists_primeBlockCollisionCount_le_seven_fourths :
    exists C : Real, 0 < C /\
      forall {N : Nat} [NeZero N] (a b c Y : Nat),
        N <= a -> a <= b -> b <= c -> c <= Y ->
          abs ((primeBlockCollisionCount N a b c : Real) -
            (primeBlockSet a b).card * (primeBlockSet b c).card / (N.totient : Real)) <=
              C * (Y : Real) ^ (7 / 4 : Real) *
                (1 + Real.log N + Real.log ((Y : Real) + 2)) ^ 4 := by
  classical
  choose B0 hB0 hPrefix0 using exists_primeCharacterSum_le_seven_eighths
  refine Exists.intro (4 * B0 ^ 2) (And.intro (by positivity) ?_)
  intro N inst a b c Y hNa hab hbc hcY
  let A := primeBlockSet a b
  let B := primeBlockSet b c
  let S := A.product B
  let f : Prod Nat Nat -> ZMod N := fun z => Ring.inverse (z.1 : ZMod N) * (z.2 : ZMod N)
  let L : Real := 1 + Real.log N + Real.log ((Y : Real) + 2)
  let E0 : Real := B0 * (Y : Real) ^ (7 / 8 : Real) * L ^ 2
  let E : Real := 2 * E0
  have hE0 : 0 <= E0 := by dsimp [E0]; positivity
  have hE : 0 <= E := by dsimp [E]; positivity
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hLogN : 0 <= Real.log (N : Real) :=
    Real.log_nonneg (by exact_mod_cast hNpos)
  have hPrefix (chi : DirichletCharacter Complex N) (hchi : Not (chi = 1))
      (t : Nat) (ht : t <= Y) :
      norm (Finset.sum (Nat.primesBelow (t + 1)) (fun p => chi (p : ZMod N))) <= E0 := by
    have hLogt : 0 <= Real.log ((t : Real) + 2) := Real.log_nonneg (by
      have ht0 : (0 : Real) <= t := Nat.cast_nonneg t
      linarith)
    have hLogY : 0 <= Real.log ((Y : Real) + 2) := Real.log_nonneg (by
      have hY0 : (0 : Real) <= Y := Nat.cast_nonneg Y
      linarith)
    have hLogs : Real.log ((t : Real) + 2) <= Real.log ((Y : Real) + 2) :=
      Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right ht 2)
    have hSq : (1 + Real.log N + Real.log ((t : Real) + 2)) ^ 2 <= L ^ 2 := by
      dsimp [L]
      nlinarith
    have hPow : (t : Real) ^ (7 / 8 : Real) <= (Y : Real) ^ (7 / 8 : Real) :=
      Real.rpow_le_rpow (Nat.cast_nonneg t) (Nat.cast_le.mpr ht) (by norm_num)
    exact (hPrefix0 chi hchi t).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hPow hB0.le) hSq
        (sq_nonneg _) (mul_nonneg hB0.le (Real.rpow_nonneg (Nat.cast_nonneg Y) _)))
  have hBlock (chi : DirichletCharacter Complex N) (hchi : Not (chi = 1))
      (x y : Nat) (hxy : x <= y) (hy : y <= Y) :
      norm (Finset.sum (primeBlockSet x y) (fun p => chi (p : ZMod N))) <= E := by
    have hsub : forall p : Nat, Membership.mem (Nat.primesBelow (x + 1)) p ->
        Membership.mem (Nat.primesBelow (y + 1)) p := by
      intro p hp
      have h := Nat.mem_primesBelow.mp hp
      exact Nat.mem_primesBelow.mpr (And.intro (by omega) h.2)
    have hSum : Finset.sum (primeBlockSet x y) (fun p => chi (p : ZMod N)) =
        Finset.sum (Nat.primesBelow (y + 1)) (fun p => chi (p : ZMod N)) -
          Finset.sum (Nat.primesBelow (x + 1)) (fun p => chi (p : ZMod N)) := by
      apply eq_sub_iff_add_eq.mpr
      exact Finset.sum_sdiff hsub
    rw [hSum]
    exact (norm_sub_le _ _).trans
      (by simpa only [E, two_mul] using
        add_le_add (hPrefix chi hchi y hy) (hPrefix chi hchi x (hxy.trans hy)))
  have hUnit (x y p : Nat) (hNx : N <= x) (hp : Membership.mem (primeBlockSet x y) p) :
      IsUnit (p : ZMod N) := by
    have hm := Finset.mem_sdiff.mp hp
    have hprime := (Nat.mem_primesBelow.mp hm.1).2
    have hxp : x < p := by
      by_contra hn
      exact hm.2 (Nat.mem_primesBelow.mpr (And.intro (by omega) hprime))
    exact (ZMod.isUnit_iff_coprime p N).mpr
      (hprime.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hNpos (hNx.trans_lt hxp)))
  have hBound (chi : DirichletCharacter Complex N) (hchi : Not (chi = 1)) :
      norm (Finset.sum S (fun z => chi (f z))) <= E * E := by
    have hFactor : Finset.sum S (fun z => chi (f z)) =
        Finset.sum A (fun p => (Inv.inv chi) (p : ZMod N)) *
          Finset.sum B (fun q => chi (q : ZMod N)) := by
      calc
        _ = Finset.sum A (fun p => Finset.sum B
            (fun q => chi (Ring.inverse (p : ZMod N) * (q : ZMod N)))) :=
          Finset.sum_product A B _
        _ = _ := by
          simp only [map_mul, <- MulChar.inv_apply, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
    rw [hFactor, norm_mul]
    exact mul_le_mul
      (hBlock (Inv.inv chi) (inv_ne_one.mpr hchi) a b hab (hbc.trans hcY))
      (hBlock chi hchi b c hbc hcY) (norm_nonneg _) hE
  have hUnitF (z : Prod Nat Nat) (hz : Membership.mem S z) : IsUnit (f z) := by
    have hm := Finset.mem_product.mp hz
    have hn := hUnit a b z.1 hNa hm.1
    have hq := hUnit b c z.2 (hNa.trans hab) hm.2
    dsimp [f]
    rw [<- hn.unit_spec, <- hq.unit_spec, Ring.inverse_unit]
    exact (Units.isUnit _).mul (Units.isUnit _)
  have hRatio (z : Prod Nat Nat) (hz : Membership.mem S z) :
      f z = 1 <-> (z.1 : ZMod N) = (z.2 : ZMod N) := by
    have hm := Finset.mem_product.mp hz
    have hn := hUnit a b z.1 hNa hm.1
    have hLeft := Ring.mul_inverse_cancel (z.1 : ZMod N) hn
    have hRight := Ring.inverse_mul_cancel (z.1 : ZMod N) hn
    constructor
    . intro h
      have hp := congrArg (fun v : ZMod N => (z.1 : ZMod N) * v) h
      dsimp only [f] at hp
      rw [<- mul_assoc, hLeft, one_mul, mul_one] at hp
      exact hp.symm
    . intro h
      dsimp only [f]
      rw [<- h]
      exact hRight
  have hFilter : S.filter (fun z => f z = 1) =
      S.filter (fun z => (z.1 : ZMod N) = (z.2 : ZMod N)) :=
    Finset.filter_congr hRatio
  have hCount : (S.filter (fun z => f z = 1)).card = primeBlockCollisionCount N a b c := by
    rw [hFilter]
    rfl
  have hUnitFilter : S.filter (fun z => IsUnit (f z)) = S :=
    Finset.filter_eq_self.mpr hUnitF
  have hCard : S.card = A.card * B.card := Finset.card_product A B
  have hRes := DirichletCharacter.abs_residue_count_sub_unit_mean_le
    S f (1 : Units (ZMod N)) (E * E) (mul_nonneg hE hE) hBound
  change abs (((S.filter (fun z => f z = 1)).card : Real) -
    ((S.filter (fun z => IsUnit (f z))).card : Real) / (N.totient : Real)) <= E * E at hRes
  rw [hCount, hUnitFilter, hCard, Nat.cast_mul] at hRes
  have hPow : ((Y : Real) ^ (7 / 8 : Real)) ^ 2 = (Y : Real) ^ (7 / 4 : Real) := by
    rw [<- Real.rpow_natCast, <- Real.rpow_mul (Nat.cast_nonneg Y)]
    norm_num
  have hError : E * E = 4 * B0 ^ 2 * (Y : Real) ^ (7 / 4 : Real) * L ^ 4 := by
    calc
      _ = 4 * B0 ^ 2 * ((Y : Real) ^ (7 / 8 : Real)) ^ 2 * L ^ 4 := by
        dsimp [E, E0]
        ring
      _ = _ := by rw [hPow]
  exact hRes.trans_eq hError

end PrimeFactorOscillations.QRH
