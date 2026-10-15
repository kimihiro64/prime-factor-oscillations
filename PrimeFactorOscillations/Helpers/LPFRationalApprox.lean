/-
Copyright (c) 2022 Michael Stoll; 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Geisser, Michael Stoll, Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFVaughanMinor

/-!
# Reduced unit approximations from cached primitives

The finite-bin argument ports Mathlib's classical Dirichlet proof at revision
5ed2965256430c3649e86755f9576b54eca72435, Basic.lean lines 95-158. The
uncached source module is not imported or rebuilt. Positive reduced
denominators and unit numerators are obtained without additional assumptions.
The strict upper integer cutoff supplies the physical denominator/error bounds.
LPFMajorSelection consumes these bounds and excludes small denominators
outside the exact major grid.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem lpf_abs_le_inv_of_scaled_bound (x t : Real) (ht : 0 < t)
    (h : abs (x * t) <= 1) : abs x <= 1 / t := by
  have hInv : t * t ^ (-1 : Int) = 1 := by field_simp [ne_of_gt ht]
  have hMul : abs x * t <= 1 := by simpa only [abs_mul, abs_of_pos ht] using h
  calc
    abs x = (abs x * t) * t ^ (-1 : Int) := by rw [mul_assoc, hInv, mul_one]
    _ <= 1 * t ^ (-1 : Int) := mul_le_mul_of_nonneg_right hMul (by positivity)
    _ = 1 / t := by simp

theorem lpf_exists_integer_dirichlet_approximation (x : Real) (Q : Nat) (hQ : 0 < Q) :
    exists a b : Int, And (0 < b) (And (b <= (Q : Int))
      (abs ((b : Real) * x - (a : Real)) <= 1 / ((Q : Real) + 1))) := by
  classical
  let t : Real := (Q : Real) + 1
  let f : Int -> Int := fun m => Int.floor (Int.fract (x * (m : Real)) * t)
  let D : Finset Int := Finset.Icc 0 (Q : Int)
  have ht : 0 < t := by dsimp [t]; positivity
  have hFrac (m : Int) : Int.fract (x * (m : Real)) * t < t :=
    mul_lt_of_lt_one_left ht (Int.fract_lt_one _)
  by_cases hEdge : exists m, And (Membership.mem D m) (f m = (Q : Int))
  . let m := Classical.choose hEdge
    have hm : Membership.mem D m := (Classical.choose_spec hEdge).1
    have hf : f m = (Q : Int) := (Classical.choose_spec hEdge).2
    have hmLow : 0 <= m := (Finset.mem_Icc.mp hm).1
    have hmNe : Not (m = 0) := by
      intro hmZero
      have hfZero : f 0 = 0 := by simp [f]
      have hQZero : (Q : Int) = 0 := by rw [hmZero, hfZero] at hf; exact hf.symm
      have hQNat : Q = 0 := by exact_mod_cast hQZero
      omega
    have hmPos : 0 < m := by omega
    have hFloor : (Q : Real) <= Int.fract (x * (m : Real)) * t := by
      have h := Int.floor_le (Int.fract (x * (m : Real)) * t)
      change ((f m : Int) : Real) <= Int.fract (x * (m : Real)) * t at h
      simpa only [hf, Int.cast_natCast] using h
    refine Exists.intro (Int.floor (x * (m : Real)) + 1)
      (Exists.intro m (And.intro hmPos (And.intro (Finset.mem_Icc.mp hm).2 ?_)))
    have hIdentity : (m : Real) * x - ((Int.floor (x * (m : Real)) + 1 : Int) : Real) =
        Int.fract (x * (m : Real)) - 1 := by
      simp only [Int.fract, Int.cast_add, Int.cast_one]
      ring
    rw [hIdentity]
    apply lpf_abs_le_inv_of_scaled_bound _ t ht
    apply abs_le.mpr
    refine And.intro ?_ ?_
    . dsimp [t] at hFloor
      dsimp [t]
      nlinarith only [hFloor]
    . nlinarith only [(hFrac m).le]
  . have hCard : (Finset.Ico (0 : Int) (Q : Int)).card < D.card := by
      dsimp [D]
      rw [Int.card_Icc, Int.card_Ico]
      exact Nat.lt_succ_self Q
    have hMap : Set.MapsTo f (D : Set Int) ((Finset.Ico 0 (Q : Int)) : Set Int) := by
      intro m hm
      have hLow : 0 <= f m := Int.floor_nonneg.mpr
        (mul_nonneg (Int.fract_nonneg _) ht.le)
      have hTop : f m < (Q : Int) + 1 := by
        apply Int.floor_lt.mpr
        simpa only [t, Int.cast_add, Int.cast_natCast, Int.cast_one] using hFrac m
      have hNe : Not (f m = (Q : Int)) := by
        intro h
        exact hEdge (Exists.intro m (And.intro hm h))
      exact Finset.mem_Ico.mpr (And.intro hLow (by omega))
    have hPair := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hCard hMap
    let a := Classical.choose hPair
    have ha := (Classical.choose_spec hPair).1
    let b := Classical.choose (Classical.choose_spec hPair).2
    have hb := (Classical.choose_spec (Classical.choose_spec hPair).2).1
    have hNe := (Classical.choose_spec (Classical.choose_spec hPair).2).2.1
    have hEq := (Classical.choose_spec (Classical.choose_spec hPair).2).2.2
    have hWitness (a b : Int) (ha : Membership.mem D a) (hb : Membership.mem D b)
        (hAB : a < b) (hEq : f a = f b) :
        exists j k : Int, And (0 < k) (And (k <= (Q : Int))
          (abs ((k : Real) * x - (j : Real)) <= 1 / ((Q : Real) + 1))) := by
      refine Exists.intro (Int.floor (x * (b : Real)) - Int.floor (x * (a : Real)))
        (Exists.intro (b - a) (And.intro (sub_pos.mpr hAB) (And.intro ?_ ?_)))
      . have haLow := (Finset.mem_Icc.mp ha).1
        have hbTop := (Finset.mem_Icc.mp hb).2
        omega
      . apply lpf_abs_le_inv_of_scaled_bound _ t ht
        have hPhase : (((b - a : Int) : Real) * x -
            ((Int.floor (x * (b : Real)) - Int.floor (x * (a : Real)) : Int) : Real)) * t =
            Int.fract (x * (b : Real)) * t - Int.fract (x * (a : Real)) * t := by
          push_cast
          simp only [Int.fract]
          ring
        rw [hPhase]
        exact (Int.abs_sub_lt_one_of_floor_eq_floor hEq.symm).le
    by_cases hAB : a < b
    . exact hWitness a b ha hb hAB hEq
    . exact hWitness b a hb ha (by omega) hEq.symm

theorem lpf_exists_reduced_rat_approximation (x : Real) (Q : Nat) (hQ : 0 < Q) :
    exists r : Rat, And (abs (x - (r : Real)) <= 1 / (((Q : Real) + 1) * (r.den : Real)))
      (r.den <= Q) := by
  have h := lpf_exists_integer_dirichlet_approximation x Q hQ
  let a := Classical.choose h
  let b := Classical.choose (Classical.choose_spec h)
  have hbPos := (Classical.choose_spec (Classical.choose_spec h)).1
  have hbTop := (Classical.choose_spec (Classical.choose_spec h)).2.1
  have hApprox := (Classical.choose_spec (Classical.choose_spec h)).2.2
  let r : Rat := (a : Rat) / (b : Rat)
  have hbReal : (0 : Real) < (b : Real) := Int.cast_pos.mpr hbPos
  have hDen : (r.den : Int) <= b := by
    dsimp [r]
    rw [Rat.intCast_div_eq_divInt]
    exact Int.le_of_dvd hbPos (Rat.den_dvd a b)
  have hDenTop : r.den <= Q := by exact_mod_cast hDen.trans hbTop
  have hDenReal : (r.den : Real) <= (b : Real) := by exact_mod_cast hDen
  have hDenPos : (0 : Real) < (r.den : Real) := Nat.cast_pos.mpr (Rat.pos r)
  let t : Real := (Q : Real) + 1
  have ht : 0 < t := by dsimp [t]; positivity
  have hIdentity : (x - (r : Real)) * (b : Real) = (b : Real) * x - (a : Real) := by
    dsimp [r]
    rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_intCast]
    field_simp [ne_of_gt hbReal]
  have hScaled : abs (x - (r : Real)) * (b : Real) <= 1 / t := by
    have h := hApprox
    rw [<- hIdentity, abs_mul, abs_of_pos hbReal] at h
    exact h
  refine Exists.intro r (And.intro ?_ hDenTop)
  apply lpf_abs_le_inv_of_scaled_bound _ (t * (r.den : Real)) (mul_pos ht hDenPos)
  rw [abs_mul, abs_of_pos (mul_pos ht hDenPos)]
  calc
    _ = (abs (x - (r : Real)) * (r.den : Real)) * t := by ring
    _ <= (abs (x - (r : Real)) * (b : Real)) * t :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDenReal (abs_nonneg _)) ht.le
    _ <= (1 / t) * t := mul_le_mul_of_nonneg_right hScaled ht.le
    _ = 1 := by field_simp [ne_of_gt ht]

theorem lpf_intCast_isUnit_of_natAbs_coprime (a : Int) (q : Nat)
    (h : a.natAbs.Coprime q) : IsUnit (a : ZMod q) := by
  cases a with
  | ofNat n =>
    change IsUnit ((n : Int) : ZMod q)
    rw [Int.cast_natCast]
    exact (ZMod.isUnit_iff_coprime n q).mpr h
  | negSucc n =>
    rw [Int.cast_negSucc]
    simpa only [Nat.cast_add, Nat.cast_one] using
      ((ZMod.isUnit_iff_coprime (n + 1) q).mpr h).neg

theorem lpf_exists_reduced_unit_approximation (x : Real) (Q : Nat) (hQ : 0 < Q) :
    exists a : Int, exists q : Nat, exists u : Units (ZMod q), exists beta : Real,
      And (0 < q) (And (q <= Q) (And ((a : ZMod q) = (u : ZMod q))
        (And (x = (a : Real) / (q : Real) + beta)
          (abs beta <= 1 / (((Q : Real) + 1) * (q : Real)))))) := by
  have h := lpf_exists_reduced_rat_approximation x Q hQ
  let r := Classical.choose h
  have hApprox := (Classical.choose_spec h).1
  have hDen := (Classical.choose_spec h).2
  have hUnit := lpf_intCast_isUnit_of_natAbs_coprime r.num r.den (Rat.reduced r)
  let beta : Real := x - (r : Real)
  refine Exists.intro r.num (Exists.intro r.den (Exists.intro hUnit.unit
    (Exists.intro beta (And.intro (Rat.pos r) (And.intro hDen
      (And.intro hUnit.unit_spec.symm (And.intro ?_ hApprox)))))))
  dsimp [beta]
  rw [Rat.cast_def]
  ring

theorem lpf_dirichlet_cutoff_lower (M P : Nat) (hP : 0 < P) :
    (M : Real) < (P : Real) * ((M / P + 1 : Nat) : Real) := by
  have hIdentity := Nat.div_add_mod M P
  have hRem := Nat.mod_lt M hP
  have hNat : M < P * (M / P + 1) := by nlinarith only [hIdentity, hRem]
  exact_mod_cast hNat

theorem lpf_dirichlet_cutoff_upper (M P : Nat) (hP : 0 < P) (hPM : P <= M) :
    ((M / P + 1 : Nat) : Real) <= 2 * (M : Real) / (P : Real) := by
  have hPR : (0 : Real) < (P : Real) := Nat.cast_pos.mpr hP
  have hPMR : (P : Real) <= (M : Real) := Nat.cast_le.mpr hPM
  have hRatio := div_le_div_of_nonneg_right hPMR hPR.le
  have hSelf : (P : Real) / (P : Real) = 1 := by field_simp [ne_of_gt hPR]
  rw [hSelf] at hRatio
  have hFloor := lpf_nat_div_cast_le M P hP
  calc
    _ = ((M / P : Nat) : Real) + 1 := by simp only [Nat.cast_add, Nat.cast_one]
    _ <= (M : Real) / (P : Real) + 1 := add_le_add hFloor (le_refl 1)
    _ <= 2 * ((M : Real) / (P : Real)) := by linarith only [hRatio]
    _ = _ := by ring

theorem lpf_exists_physical_unit_approximation (x : Real) (M P : Nat)
    (hP : 0 < P) (hPM : P <= M) :
    exists a : Int, exists q : Nat, exists u : Units (ZMod q), exists beta : Real,
      And (0 < q) (And (q <= 2 * M)
        (And ((q : Real) <= 2 * (M : Real) / (P : Real))
          (And ((a : ZMod q) = (u : ZMod q))
            (And (x = (a : Real) / (q : Real) + beta)
              (abs beta <= (P : Real) / ((M : Real) * (q : Real))))))) := by
  let Q := M / P + 1
  have hQ : 0 < Q := by dsimp [Q]; exact Nat.succ_pos _
  choose a q u beta hq hqQ hu hAlpha hBeta using
    lpf_exists_reduced_unit_approximation x Q hQ
  have hM : 0 < M := hP.trans_le hPM
  have hMR : (0 : Real) < (M : Real) := Nat.cast_pos.mpr hM
  have hqR : (0 : Real) < (q : Real) := Nat.cast_pos.mpr hq
  have hQR : (0 : Real) < (Q : Real) + 1 := by positivity
  have hScale : (M : Real) <= (P : Real) * ((Q : Real) + 1) := by
    have h := lpf_dirichlet_cutoff_lower M P hP
    change (M : Real) < (P : Real) * (Q : Real) at h
    nlinarith only [h, (show (0 : Real) <= (P : Real) from Nat.cast_nonneg P)]
  have hCompare : 1 / (((Q : Real) + 1) * (q : Real)) <=
      (P : Real) / ((M : Real) * (q : Real)) := by
    have h := div_le_div_of_nonneg_right hScale
      (by positivity : 0 <= (M : Real) * (q : Real) * ((Q : Real) + 1))
    convert h using 1 <;> field_simp [ne_of_gt hMR, ne_of_gt hqR, ne_of_gt hQR] <;> ring
  have hqNat : q <= 2 * M := by
    have hDiv : M / P <= M := Nat.div_le_self M P
    dsimp [Q] at hqQ
    omega
  have hqTop : (q : Real) <= 2 * (M : Real) / (P : Real) :=
    (Nat.cast_le.mpr hqQ).trans (lpf_dirichlet_cutoff_upper M P hP hPM)
  exact Exists.intro a (Exists.intro q (Exists.intro u (Exists.intro beta
    (And.intro hq (And.intro hqNat (And.intro hqTop
      (And.intro hu (And.intro hAlpha (hBeta.trans hCompare)))))))))
end PrimeFactorOscillations.LPF
