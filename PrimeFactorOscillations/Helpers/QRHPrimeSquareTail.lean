/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.QRHPrimePrefix
import PrimeFactorOscillations.Mathlib.Data.Finset.SquareDivisorCount
import PrimeFactorOscillations.Mathlib.NumberTheory.DirichletCharacter.ResidueCount

/-!
Uniform square-divisor tails at every moving prime vertex.
This is the arithmetic input to the admitted signed spectral theorem,
not a bound on zero multiplicities or an improved zero-free exponent.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

namespace PrimeFactorOscillations.QRH

theorem exists_prime_reduced_residue_count_upper :
    exists C : Real, 0 < C /\
      forall {N : Nat} [NeZero N] (a : ZMod N), IsUnit a ->
        forall X : Nat,
          (((Nat.primesBelow (X + 1)).filter
            (fun q : Nat => (q : ZMod N) = a)).card : Real) <=
            ((Nat.primesBelow (X + 1)).card : Real) / (N.totient : Real) +
              C * (X : Real) ^ (7 / 8 : Real) *
                (1 + Real.log N + Real.log ((X : Real) + 2)) ^ 2 := by
  classical
  choose C hC hBound using exists_primeCharacterSum_le_seven_eighths
  refine Exists.intro C (And.intro hC ?_)
  intro N inst a ha X
  let S := Nat.primesBelow (X + 1)
  let E : Real := C * (X : Real) ^ (7 / 8 : Real) *
    (1 + Real.log N + Real.log ((X : Real) + 2)) ^ 2
  have hE : 0 <= E := by dsimp [E]; positivity
  have h := DirichletCharacter.abs_residue_count_sub_unit_mean_le
    S (fun q : Nat => (q : ZMod N)) ha.unit E hE (fun chi hchi => hBound chi hchi X)
  rw [ha.unit_spec] at h
  have hCard : (((S.filter (fun q : Nat => IsUnit (q : ZMod N))).card : Nat) : Real) <=
      (S.card : Real) := by
    exact_mod_cast Finset.card_filter_le S (fun q : Nat => IsUnit (q : ZMod N))
  have hMean := div_le_div_of_nonneg_right hCard (Nat.cast_nonneg N.totient)
  have hUpper := (le_abs_self
    ((((S.filter (fun q : Nat => (q : ZMod N) = a)).card : Nat) : Real) -
      (((S.filter (fun q : Nat => IsUnit (q : ZMod N))).card : Nat) : Real) /
        (N.totient : Real))).trans h
  change (((S.filter (fun q : Nat => (q : ZMod N) = a)).card : Nat) : Real) <=
    (S.card : Real) / (N.totient : Real) + E
  linarith

noncomputable def primeSquareCollisionCount (p ell X : Nat) : Nat := by
  classical
  exact ((Nat.primesBelow (X + 1)).filter (fun q : Nat =>
    Not (q = p) /\ (q : ZMod (ell ^ 2)) = (p : ZMod (ell ^ 2)))).card

theorem prime_square_residue_isUnit (p ell : Nat)
    (hp : Nat.Prime p) (hl : Nat.Prime ell) (hne : Not (p = ell)) :
    IsUnit (p : ZMod (ell ^ 2)) := by
  have hnot : Not (Dvd.dvd ell p) := by
    intro hd
    exact hne ((hp.dvd_iff_eq hl.ne_one).mp hd)
  have hcop : Nat.Coprime p ell := (hl.coprime_iff_not_dvd.mpr hnot).symm
  exact (ZMod.isUnit_iff_coprime p (ell ^ 2)).mpr (Nat.Coprime.pow_right 2 hcop)

theorem prime_square_self_collision_zero (p X : Nat) (hp : Nat.Prime p) :
    primeSquareCollisionCount p p X = 0 := by
  classical
  unfold primeSquareCollisionCount
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have hqP := (Nat.mem_primesBelow.mp (Finset.mem_filter.mp hq).1).2
  have hne := (Finset.mem_filter.mp hq).2.1
  have heq := (Finset.mem_filter.mp hq).2.2
  have hqUnit : IsUnit (q : ZMod (p ^ 2)) :=
    prime_square_residue_isUnit q p hqP hp hne
  rw [heq] at hqUnit
  have hcop := (ZMod.isUnit_iff_coprime p (p ^ 2)).mp hqUnit
  have hnot := hp.coprime_iff_not_dvd.mp hcop
  apply hnot
  refine Exists.intro p ?_
  simp only [pow_two]

theorem exists_prime_square_collision_upper :
    exists C : Real, 0 < C /\
      forall p ell X : Nat, Nat.Prime p -> Nat.Prime ell ->
        (primeSquareCollisionCount p ell X : Real) <=
          ((Nat.primesBelow (X + 1)).card : Real) /
            ((ell : Real) * ((ell : Real) - 1)) +
          C * (X : Real) ^ (7 / 8 : Real) *
            (1 + Real.log (ell ^ 2 : Nat) + Real.log ((X : Real) + 2)) ^ 2 := by
  classical
  choose C hC hBound using exists_prime_reduced_residue_count_upper
  refine Exists.intro C (And.intro hC ?_)
  intro p ell X hp hl
  have hPos : 0 < ell ^ 2 := pow_pos hl.pos 2
  have hInst : NeZero (ell ^ 2) := by
    constructor
    exact Nat.ne_of_gt hPos
  have hPhi : (ell ^ 2).totient = ell * (ell - 1) := by
    rw [Nat.totient_prime_pow hl (by norm_num : 0 < (2 : Nat))]
    norm_num
  have hPhiR : ((ell ^ 2).totient : Real) = (ell : Real) * ((ell : Real) - 1) := by
    rw [hPhi, Nat.cast_mul, Nat.cast_sub hl.one_le, Nat.cast_one]
  have hEllR : (1 : Real) <= ell := by exact_mod_cast hl.one_le
  have hDen : 0 <= (ell : Real) * ((ell : Real) - 1) :=
    mul_nonneg (Nat.cast_nonneg ell) (sub_nonneg.mpr hEllR)
  by_cases heq : p = ell
  . subst p
    rw [prime_square_self_collision_zero ell X hl]
    norm_num only [Nat.cast_zero]
    exact add_nonneg (div_nonneg (Nat.cast_nonneg _) hDen) (by positivity)
  . have hUnit := prime_square_residue_isUnit p ell hp hl heq
    have h := @hBound (ell ^ 2) hInst (p : ZMod (ell ^ 2)) hUnit X
    have hSub : forall q : Nat,
        Membership.mem ((Nat.primesBelow (X + 1)).filter (fun q : Nat =>
          Not (q = p) /\ (q : ZMod (ell ^ 2)) = (p : ZMod (ell ^ 2)))) q ->
        Membership.mem ((Nat.primesBelow (X + 1)).filter
          (fun q : Nat => (q : ZMod (ell ^ 2)) = (p : ZMod (ell ^ 2)))) q := by
      intro q hq
      exact Finset.mem_filter.mpr (And.intro (Finset.mem_filter.mp hq).1
        (Finset.mem_filter.mp hq).2.2)
    have hCard := Finset.card_le_card hSub
    have hCardR : (primeSquareCollisionCount p ell X : Real) <=
        (((Nat.primesBelow (X + 1)).filter
          (fun q : Nat => (q : ZMod (ell ^ 2)) = (p : ZMod (ell ^ 2)))).card : Real) := by
      exact_mod_cast hCard
    rw [hPhiR] at h
    exact hCardR.trans h


theorem card_filter_square_congruence_tail_le
    (S : Finset Nat) (p X T : Nat) (hpX : p <= X) (hT : 2 <= T)
    (hS : forall q : Nat, Membership.mem S q -> q <= X) :
    (S.filter (fun q : Nat => Not (q = p) /\
      exists u : Nat, T <= u /\ (q : ZMod (u ^ 2)) = (p : ZMod (u ^ 2)))).card <=
        2 * (X / (T - 1)) := by
  classical
  let g : Nat -> Prod Nat Nat := fun q =>
    if p < q then Prod.mk 0 (q - p) else Prod.mk 1 (p - q)
  let A : Finset Nat := Insert.insert 0 (Singleton.singleton 1)
  let B := S.filter (fun q : Nat => Not (q = p))
  let V := B.image g
  have hInj : Function.Injective g := by
    intro x y heq
    have h1 := congrArg (fun z : Prod Nat Nat => z.1) heq
    have h2 := congrArg (fun z : Prod Nat Nat => z.2) heq
    by_cases hx : p < x
    . by_cases hy : p < y
      . simp only [g, ite_eq_left hx, ite_eq_left hy] at h2
        omega
      . simp only [g, ite_eq_left hx, ite_eq_right hy] at h1
        omega
    . by_cases hy : p < y
      . simp only [g, ite_eq_right hx, ite_eq_left hy] at h1
        omega
      . simp only [g, ite_eq_right hx, ite_eq_right hy] at h2
        omega
  have hCoords (z : Prod Nat Nat) (hz : Membership.mem V z) :
      Membership.mem A z.1 /\ 0 < z.2 /\ z.2 <= X := by
    choose q hq heq using Finset.mem_image.mp hz
    have hqS := (Finset.mem_filter.mp hq).1
    have hne := (Finset.mem_filter.mp hq).2
    have hqX := hS q hqS
    rw [<- heq]
    by_cases hpq : p < q
    . simp only [g, ite_eq_left hpq]
      exact And.intro (by simp [A]) (And.intro (by omega) (by omega))
    . simp only [g, ite_eq_right hpq]
      exact And.intro (by simp [A]) (And.intro (by omega) (by omega))
  have hDiv (q u : Nat)
      (heq : (q : ZMod (u ^ 2)) = (p : ZMod (u ^ 2))) :
      Dvd.dvd (u ^ 2) (g q).2 := by
    have hm := (ZMod.natCast_eq_natCast_iff q p (u ^ 2)).mp heq
    have hd : Dvd.dvd ((u ^ 2 : Nat) : Int) ((p : Int) - (q : Int)) := hm.dvd
    by_cases hpq : p < q
    . simp only [g, ite_eq_left hpq]
      have hneg : Dvd.dvd ((u ^ 2 : Nat) : Int) ((q : Int) - (p : Int)) := by
        simpa only [neg_sub] using dvd_neg.mpr hd
      have hcast : ((q - p : Nat) : Int) = (q : Int) - (p : Int) :=
        Nat.cast_sub (by omega : p <= q)
      rw [<- hcast] at hneg
      exact_mod_cast hneg
    . simp only [g, ite_eq_right hpq]
      have hcast : ((p - q : Nat) : Int) = (p : Int) - (q : Int) :=
        Nat.cast_sub (by omega : q <= p)
      rw [<- hcast] at hd
      exact_mod_cast hd
  let D := V.filter (fun z : Prod Nat Nat =>
    exists u : Nat, T <= u /\ Dvd.dvd (u ^ 2) z.2)
  have hCard : (S.filter (fun q : Nat => Not (q = p) /\
      exists u : Nat, T <= u /\ (q : ZMod (u ^ 2)) = (p : ZMod (u ^ 2)))).card <=
        D.card := by
    apply Finset.card_le_card_of_injOn g
    . intro q hq
      have hqS := (Finset.mem_filter.mp hq).1
      have hne := (Finset.mem_filter.mp hq).2.1
      choose u hu heq using (Finset.mem_filter.mp hq).2.2
      apply Finset.mem_filter.mpr
      refine And.intro ?_ (Exists.intro u (And.intro hu (hDiv q u heq)))
      exact Finset.mem_image.mpr (Exists.intro q
        (And.intro (Finset.mem_filter.mpr (And.intro hqS hne)) rfl))
    . intro x hx y hy heq
      exact hInj heq
  have hTail := Finset.card_filter_exists_sq_dvd_le V A X T hT hCoords
  have hA : A.card = 2 := by simp [A]
  change D.card <= A.card * (X / (T - 1)) at hTail
  rw [hA] at hTail
  exact hCard.trans hTail

theorem reciprocal_square_tail_sum_le
    (S : Finset Nat) (R T : Nat) (hR : 2 <= R) (hRT : R <= T)
    (hS : forall n : Nat, Membership.mem S n -> R < n /\ n <= T) :
    Finset.sum S (fun n => 1 / ((n : Real) * ((n : Real) - 1))) <= 1 / (R : Real) := by
  let f : Nat -> Real := fun n => 1 / ((n : Real) * ((n : Real) - 1))
  let F : Nat -> Real := fun n => -(1 / ((n : Real) - 1))
  have hSub : forall n : Nat, Membership.mem S n ->
      Membership.mem (Finset.Ico (R + 1) (T + 1)) n := by
    intro n hn
    have hh := hS n hn
    exact Finset.mem_Ico.mpr (And.intro (by omega) (by omega))
  have hNonneg (n : Nat) (hn : Membership.mem (Finset.Ico (R + 1) (T + 1)) n) :
      0 <= f n := by
    have hnN : 2 <= n := by have hh := (Finset.mem_Ico.mp hn).1; omega
    have hnR : (2 : Real) <= n := by exact_mod_cast hnN
    dsimp [f]
    exact div_nonneg (by norm_num)
      (mul_nonneg (Nat.cast_nonneg n) (by linarith))
  have hStep (n : Nat) (hn : Membership.mem (Finset.Ico (R + 1) (T + 1)) n) :
      f n = F (n + 1) - F n := by
    have hnN : 2 <= n := by have hh := (Finset.mem_Ico.mp hn).1; omega
    have hnR : (2 : Real) <= n := by exact_mod_cast hnN
    have hn0 : Not ((n : Real) = 0) := by linarith
    have hn1 : Not ((n : Real) - 1 = 0) := by linarith
    dsimp [f, F]
    rw [Nat.cast_add, Nat.cast_one, show (n : Real) + 1 - 1 = n by ring]
    field_simp
    ring
  have hTel := Finset.sum_Ico_sub F (m := R + 1) (n := T + 1) (by omega)
  have hSum := Finset.sum_le_sum_of_subset_of_nonneg hSub
    (fun n hn _ => hNonneg n hn)
  change Finset.sum S f <= 1 / (R : Real)
  calc
    _ <= Finset.sum (Finset.Ico (R + 1) (T + 1)) f := hSum
    _ = Finset.sum (Finset.Ico (R + 1) (T + 1)) (fun n => F (n + 1) - F n) :=
      Finset.sum_congr rfl hStep
    _ = F (T + 1) - F (R + 1) := hTel
    _ = 1 / (R : Real) - 1 / (T : Real) := by
      dsimp [F]
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    _ <= 1 / (R : Real) := by
      have hInv : (0 : Real) <= 1 / (T : Real) :=
        div_nonneg (by norm_num) (Nat.cast_nonneg T)
      linarith

noncomputable def primeSquareLowTailCount (p X R T : Nat) : Nat := by
  classical
  exact ((Nat.primesBelow (X + 1)).filter (fun q : Nat =>
    Not (q = p) /\ exists ell : Nat,
      Nat.Prime ell /\ R < ell /\ ell <= T /\
        (q : ZMod (ell ^ 2)) = (p : ZMod (ell ^ 2)))).card

theorem exists_prime_square_low_tail_upper :
    exists C : Real, 0 < C /\
      forall p X R T : Nat, Nat.Prime p -> 2 <= R -> R <= T ->
        (primeSquareLowTailCount p X R T : Real) <=
          ((Nat.primesBelow (X + 1)).card : Real) / (R : Real) +
          C * (T : Real) * (X : Real) ^ (7 / 8 : Real) *
            (1 + Real.log (T ^ 2 : Nat) + Real.log ((X : Real) + 2)) ^ 2 := by
  classical
  choose C hC hBound using exists_prime_square_collision_upper
  refine Exists.intro C (And.intro hC ?_)
  intro p X R T hp hR hRT
  let S := Nat.primesBelow (X + 1)
  let P := (Nat.primesBelow (T + 1)).filter (fun ell : Nat => R < ell)
  let Q : Nat -> Finset Nat := fun ell => S.filter (fun q : Nat =>
    Not (q = p) /\ (q : ZMod (ell ^ 2)) = (p : ZMod (ell ^ 2)))
  let L : Real := 1 + Real.log (T ^ 2 : Nat) + Real.log ((X : Real) + 2)
  let E : Real := C * (X : Real) ^ (7 / 8 : Real) * L ^ 2
  have hE : 0 <= E := by dsimp [E]; positivity
  have hP (ell : Nat) (hl : Membership.mem P ell) :
      Nat.Prime ell /\ R < ell /\ ell <= T := by
    have hm := Finset.mem_filter.mp hl
    have hh := Nat.mem_primesBelow.mp hm.1
    exact And.intro hh.2 (And.intro hm.2 (by omega))
  have hCover : forall q : Nat,
      Membership.mem (S.filter (fun q : Nat => Not (q = p) /\
        exists ell : Nat, Nat.Prime ell /\ R < ell /\ ell <= T /\
          (q : ZMod (ell ^ 2)) = (p : ZMod (ell ^ 2)))) q ->
      Membership.mem (P.biUnion Q) q := by
    intro q hq
    have hqS := (Finset.mem_filter.mp hq).1
    have hne := (Finset.mem_filter.mp hq).2.1
    choose ell hl hRl hlT heq using (Finset.mem_filter.mp hq).2.2
    apply Finset.mem_biUnion.mpr
    refine Exists.intro ell (And.intro ?_ ?_)
    . exact Finset.mem_filter.mpr (And.intro
        (Nat.mem_primesBelow.mpr (And.intro (by omega) hl)) hRl)
    . exact Finset.mem_filter.mpr (And.intro hqS (And.intro hne heq))
  have hCard : primeSquareLowTailCount p X R T <=
      Finset.sum P (fun ell => primeSquareCollisionCount p ell X) :=
    (Finset.card_le_card hCover).trans Finset.card_biUnion_le
  have hCardR : (primeSquareLowTailCount p X R T : Real) <=
      Finset.sum P (fun ell => (primeSquareCollisionCount p ell X : Real)) := by
    exact_mod_cast hCard
  have hPcard : P.card <= T := by
    have hSub : forall ell : Nat, Membership.mem P ell ->
        Membership.mem (Finset.Icc 1 T) ell := by
      intro ell hl
      have hh := hP ell hl
      exact Finset.mem_Icc.mpr (And.intro hh.1.pos hh.2.2)
    have hh := Finset.card_le_card hSub
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hh
  have hRecip := reciprocal_square_tail_sum_le P R T hR hRT
    (fun ell hl => (hP ell hl).2)
  have hEach (ell : Nat) (hl : Membership.mem P ell) :
      (primeSquareCollisionCount p ell X : Real) <=
        (S.card : Real) * (1 / ((ell : Real) * ((ell : Real) - 1))) + E := by
    have hh := hP ell hl
    have hEllPos : 0 < ell ^ 2 := pow_pos hh.1.pos 2
    have hLog : Real.log (ell ^ 2 : Nat) <= Real.log (T ^ 2 : Nat) :=
      Real.log_le_log (by exact_mod_cast hEllPos)
        (by exact_mod_cast Nat.pow_le_pow_left hh.2.2 2)
    have hLogEll : 0 <= Real.log (ell ^ 2 : Nat) :=
      Real.log_nonneg (by exact_mod_cast (show 1 <= ell ^ 2 by omega))
    have hLogX : 0 <= Real.log ((X : Real) + 2) :=
      Real.log_nonneg (by have hx : (0 : Real) <= X := Nat.cast_nonneg X; linarith)
    have hSq : (1 + Real.log (ell ^ 2 : Nat) + Real.log ((X : Real) + 2)) ^ 2 <=
        L ^ 2 := by
      dsimp [L]
      nlinarith
    have hErr : C * (X : Real) ^ (7 / 8 : Real) *
        (1 + Real.log (ell ^ 2 : Nat) + Real.log ((X : Real) + 2)) ^ 2 <= E :=
      mul_le_mul_of_nonneg_left hSq (by positivity)
    have h := hBound p ell X hp hh.1
    change (primeSquareCollisionCount p ell X : Real) <=
      (S.card : Real) / ((ell : Real) * ((ell : Real) - 1)) + _ at h
    rw [mul_one_div]
    linarith
  have hSum : Finset.sum P (fun ell => (primeSquareCollisionCount p ell X : Real)) <=
      (S.card : Real) / (R : Real) + (T : Real) * E := by
    calc
      _ <= Finset.sum P (fun ell =>
          (S.card : Real) * (1 / ((ell : Real) * ((ell : Real) - 1))) + E) :=
        Finset.sum_le_sum hEach
      _ = (S.card : Real) *
          Finset.sum P (fun ell => 1 / ((ell : Real) * ((ell : Real) - 1))) +
            (P.card : Real) * E := by
        rw [Finset.sum_add_distrib, <- Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      _ <= (S.card : Real) * (1 / (R : Real)) + (T : Real) * E :=
        add_le_add (mul_le_mul_of_nonneg_left hRecip (Nat.cast_nonneg S.card))
          (mul_le_mul_of_nonneg_right (by exact_mod_cast hPcard) hE)
      _ = _ := by ring
  change (primeSquareLowTailCount p X R T : Real) <=
    (S.card : Real) / (R : Real) +
      C * (T : Real) * (X : Real) ^ (7 / 8 : Real) * L ^ 2
  have hFinal := hCardR.trans hSum
  dsimp only [E] at hFinal
  nlinarith

noncomputable def primeSquareTailCount (p X R : Nat) : Nat := by
  classical
  exact ((Nat.primesBelow (X + 1)).filter (fun q : Nat => Not (q = p) /\
    exists ell : Nat, Nat.Prime ell /\ R < ell /\
      (q : ZMod (ell ^ 2)) = (p : ZMod (ell ^ 2)))).card

theorem exists_uniform_prime_square_tail_upper :
    exists C : Real, 0 < C /\
      forall p X R T : Nat, Nat.Prime p -> p <= X -> 2 <= R -> R <= T ->
        (primeSquareTailCount p X R : Real) <=
          ((Nat.primesBelow (X + 1)).card : Real) / (R : Real) +
          C * (T : Real) * (X : Real) ^ (7 / 8 : Real) *
            (1 + Real.log (T ^ 2 : Nat) + Real.log ((X : Real) + 2)) ^ 2 +
          2 * ((X / T : Nat) : Real) := by
  classical
  choose C hC hLow using exists_prime_square_low_tail_upper
  refine Exists.intro C (And.intro hC ?_)
  intro p X R T hp hpX hR hRT
  let S := Nat.primesBelow (X + 1)
  let L := S.filter (fun q : Nat => Not (q = p) /\
    exists ell : Nat, Nat.Prime ell /\ R < ell /\ ell <= T /\
      (q : ZMod (ell ^ 2)) = (p : ZMod (ell ^ 2)))
  let H := S.filter (fun q : Nat => Not (q = p) /\
    exists u : Nat, T + 1 <= u /\
      (q : ZMod (u ^ 2)) = (p : ZMod (u ^ 2)))
  have hCover : forall q : Nat, Membership.mem (S.filter (fun q : Nat =>
      Not (q = p) /\ exists ell : Nat, Nat.Prime ell /\ R < ell /\
        (q : ZMod (ell ^ 2)) = (p : ZMod (ell ^ 2)))) q ->
      Membership.mem (Union.union L H) q := by
    intro q hq
    have hqS := (Finset.mem_filter.mp hq).1
    have hne := (Finset.mem_filter.mp hq).2.1
    choose ell hl hRl heq using (Finset.mem_filter.mp hq).2.2
    by_cases hlT : ell <= T
    . apply Finset.mem_union.mpr
      apply Or.inl
      exact Finset.mem_filter.mpr (And.intro hqS (And.intro hne
        (Exists.intro ell (And.intro hl (And.intro hRl (And.intro hlT heq))))))
    . apply Finset.mem_union.mpr
      apply Or.inr
      exact Finset.mem_filter.mpr (And.intro hqS (And.intro hne
        (Exists.intro ell (And.intro (by omega) heq))))
  have hCard : primeSquareTailCount p X R <= L.card + H.card :=
    (Finset.card_le_card hCover).trans (Finset.card_union_le L H)
  have hHigh : H.card <= 2 * (X / T) := by
    have h := card_filter_square_congruence_tail_le S p X (T + 1)
      hpX (by omega) (fun q hq => by
        have hh := Nat.mem_primesBelow.mp hq
        omega)
    simpa only [Nat.add_sub_cancel] using h
  have hCardR : (primeSquareTailCount p X R : Real) <=
      (L.card : Real) + (H.card : Real) := by exact_mod_cast hCard
  have hHighR : (H.card : Real) <= 2 * ((X / T : Nat) : Real) := by
    exact_mod_cast hHigh
  have hLowNow := hLow p X R T hp hR hRT
  change (L.card : Real) <= _ at hLowNow
  linarith

end PrimeFactorOscillations.QRH
