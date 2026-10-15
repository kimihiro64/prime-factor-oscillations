/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFMinorBilinear
import PrimeFactorOscillations.Helpers.LPFMinorResidueMean

/-!
# Complete finite weighted Type II packet bound

The paired geometric cancellation is retained on its exact product window.
Every affine residue and diagonal pair contributes to the same finite bound:
A2*B2*Qn*(floor(Qn/q)+1)*(Qm+2*q*(1+log q)). A2 bounds the outer
second moment, and B2 bounds each inner coefficient square. The rational
frequency and perturbation hypotheses are explicit. Physical-scale and
full minor-arc assembly remain separate obligations.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem lpf_bilinear_window_minor_point_bound {N q : Nat} [NeZero N] [NeZero q]
    (k a : Int) (u : Units (ZMod q)) (hU : (a : ZMod q) = (u : ZMod q))
    (beta : Real) (A B C D s L n1 n2 : Nat)
    (hn1 : Membership.mem (Finset.Ioc C D) n1) (hn2 : Membership.mem (Finset.Ioc C D) n2)
    (hAlpha : (k : Real) / (N : Real) = (a : Real) / (q : Real) + beta)
    (hBeta : abs beta * ((D - C : Nat) : Real) <= 1 / (4 * (q : Real))) :
    norm (Finset.sum (Finset.Ioc (max (max A (s / n1)) (s / n2))
      (min (min B ((s + L) / n1)) ((s + L) / n2))) (fun m =>
        ZMod.stdAddChar (N := N)
          ((k : ZMod N) * (m : ZMod N) * ((n1 : ZMod N) - (n2 : ZMod N))))) <=
      lpfMinorResidueAllowance q ((B - A : Nat) : Real)
        (((u : ZMod q) * ((n1 : ZMod q) - (n2 : ZMod q))).val) := by
  let d : Int := (n1 : Int) - (n2 : Int)
  let lo := max (max A (s / n1)) (s / n2)
  let hi := min (min B ((s + L) / n1)) ((s + L) / n2)
  have h1 := Finset.mem_Ioc.mp hn1
  have h2 := Finset.mem_Ioc.mp hn2
  have hCD : C <= D := by omega
  have hDiffCast : (d : Real) = (n1 : Real) - (n2 : Real) := by
    dsimp [d]
    simp only [Int.cast_sub, Int.cast_natCast]
  have hDiff : abs (d : Real) <= ((D - C : Nat) : Real) := by
    have hC1 : (C : Real) < (n1 : Real) := Nat.cast_lt.mpr h1.1
    have hC2 : (C : Real) < (n2 : Real) := Nat.cast_lt.mpr h2.1
    have hD1 : (n1 : Real) <= (D : Real) := Nat.cast_le.mpr h1.2
    have hD2 : (n2 : Real) <= (D : Real) := Nat.cast_le.mpr h2.2
    rw [hDiffCast, Nat.cast_sub hCD]
    apply abs_le.mpr
    constructor <;> linarith
  have hError : abs (beta * (d : Real)) <= 1 / (4 * (q : Real)) := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hDiff (abs_nonneg beta)).trans hBeta
  have hCastN : (d : ZMod N) = (n1 : ZMod N) - (n2 : ZMod N) := by
    dsimp [d]
    simp only [Int.cast_sub, Int.cast_natCast]
  have hCastQ : ((a * d : Int) : ZMod q) =
      (u : ZMod q) * ((n1 : ZMod q) - (n2 : ZMod q)) := by
    dsimp [d]
    simp only [Int.cast_mul, Int.cast_sub, Int.cast_natCast, hU]
  rw [<- hCastN, <- hCastQ]
  change norm (Finset.sum (Finset.Ioc lo hi) (fun m =>
    ZMod.stdAddChar (N := N) ((k : ZMod N) * (m : ZMod N) * (d : ZMod N)))) <=
      lpfMinorResidueAllowance q ((B - A : Nat) : Real) (((a * d : Int) : ZMod q).val)
  by_cases hZero : (((a * d : Int) : ZMod q).val) = 0
  . rw [lpfMinorResidueAllowance, ite_eq_left hZero]
    have hLo : A <= lo :=
      (le_max_left A (s / n1)).trans (le_max_left (max A (s / n1)) (s / n2))
    have hHi : hi <= B :=
      (min_le_left (min B ((s + L) / n1)) ((s + L) / n2)).trans (min_le_left B ((s + L) / n1))
    have hWidth : hi - lo <= B - A := by omega
    exact (norm_lpf_grid_pair_interval_le_length k d lo hi).trans (Nat.cast_le.mpr hWidth)
  . rw [lpfMinorResidueAllowance, ite_eq_right hZero]
    have h := lpf_grid_pair_interval_minor_bound k a d beta lo hi hAlpha
      (Nat.pos_of_ne_zero hZero) hError
    have h' := h.trans (min_le_right _ _)
    simpa only [div_eq_mul_inv, one_mul] using h'

theorem lpf_typeII_weighted_packet_bound {N q : Nat} [NeZero N] [NeZero q]
    (k a : Int) (u : Units (ZMod q)) (hU : (a : ZMod q) = (u : ZMod q))
    (beta : Real) (A B C D s L : Nat) (outer inner : Nat -> Complex) (A2 B2 : Real)
    (hAlpha : (k : Real) / (N : Real) = (a : Real) / (q : Real) + beta)
    (hBeta : abs beta * ((D - C : Nat) : Real) <= 1 / (4 * (q : Real)))
    (hA : Finset.sum (Finset.Ioc A B) (fun m => norm (outer m) ^ 2) <= A2)
    (hB2 : 0 <= B2) (hB : forall n, Membership.mem (Finset.Ioc C D) n -> norm (inner n) ^ 2 <= B2) :
    norm (Finset.sum (Finset.Ioc A B) (fun m => outer m *
      Finset.sum (Finset.Ioc C D) (fun n => inner n * lpfBilinearFrequencyWindowPhase N s L k m n))) ^ 2 <=
        A2 * B2 * ((D - C : Nat) : Real) * (((D - C) / q + 1 : Nat) : Real) *
          (((B - A : Nat) : Real) + 2 * (q : Real) * (1 + Real.log (q : Real))) := by
  let S := Finset.Ioc A B
  let T := Finset.Ioc C D
  let K : Nat -> Nat -> Complex := fun n1 n2 =>
    Finset.sum (Finset.Ioc (max (max A (s / n1)) (s / n2))
      (min (min B ((s + L) / n1)) ((s + L) / n2))) (fun m =>
        ZMod.stdAddChar (N := N)
          ((k : ZMod N) * (m : ZMod N) * ((n1 : ZMod N) - (n2 : ZMod N))))
  let F : Nat -> Nat -> Real := fun n1 n2 => lpfMinorResidueAllowance q ((B - A : Nat) : Real)
    (((u : ZMod q) * ((n1 : ZMod q) - (n2 : ZMod q))).val)
  let Gamma : Real := Finset.sum T (fun n1 => Finset.sum T (F n1))
  let G : Real := ((D - C : Nat) : Real) * (((D - C) / q + 1 : Nat) : Real) *
    (((B - A : Nat) : Real) + 2 * (q : Real) * (1 + Real.log (q : Real)))
  let pair : Nat -> Nat -> Complex := fun n1 n2 => (inner n1 * star (inner n2)) * K n1 n2
  let E : Real := (Finset.sum T (fun n1 => Finset.sum T (pair n1))).re
  have hT : forall n, Membership.mem T n -> 0 < n := by
    intro n hn
    have h := Finset.mem_Ioc.mp hn
    omega
  have hCauchy := lpf_bilinear_frequency_cauchy_packet (N := N) k A B s L T hT outer inner
  change norm (Finset.sum S (fun m => outer m *
    Finset.sum T (fun n => inner n * lpfBilinearFrequencyWindowPhase N s L k m n))) ^ 2 <=
      Finset.sum S (fun m => norm (outer m) ^ 2) * E at hCauchy
  have hPoint : forall n1, Membership.mem T n1 -> forall n2, Membership.mem T n2 ->
      norm (K n1 n2) <= F n1 n2 := by
    intro n1 hn1 n2 hn2
    exact lpf_bilinear_window_minor_point_bound k a u hU beta A B C D s L n1 n2 hn1 hn2 hAlpha hBeta
  have hTerm : forall n1, Membership.mem T n1 -> forall n2, Membership.mem T n2 ->
      norm (pair n1 n2) <= B2 * F n1 n2 := by
    intro n1 hn1 n2 hn2
    have h1 := hB n1 hn1
    have h2 := hB n2 hn2
    have hProduct : norm (inner n1) * norm (inner n2) <= B2 := by
      nlinarith only [h1, h2, sq_nonneg (norm (inner n1) - norm (inner n2))]
    change norm ((inner n1 * star (inner n2)) * K n1 n2) <= B2 * F n1 n2
    rw [norm_mul, norm_mul, norm_star]
    exact mul_le_mul hProduct (hPoint n1 hn1 n2 hn2) (norm_nonneg _) hB2
  have hEnergy : E <= B2 * Gamma := by
    calc
      E <= norm (Finset.sum T (fun n1 => Finset.sum T (pair n1))) := Complex.re_le_norm _
      _ <= Finset.sum T (fun n1 => norm (Finset.sum T (pair n1))) := norm_sum_le T _
      _ <= Finset.sum T (fun n1 => Finset.sum T (fun n2 => norm (pair n1 n2))) := by
        apply Finset.sum_le_sum
        intro n1 hn1
        exact norm_sum_le T _
      _ <= Finset.sum T (fun n1 => Finset.sum T (fun n2 => B2 * F n1 n2)) := by
        apply Finset.sum_le_sum
        intro n1 hn1
        apply Finset.sum_le_sum
        intro n2 hn2
        exact hTerm n1 hn1 n2 hn2
      _ = _ := by dsimp [Gamma]; simp_rw [<- Finset.mul_sum]
  have hGammaNonneg : 0 <= Gamma := by
    apply Finset.sum_nonneg
    intro n1 hn1
    apply Finset.sum_nonneg
    intro n2 hn2
    exact lpfMinorResidueAllowance_nonneg q _ _ (Nat.cast_nonneg _)
  have hGamma : Gamma <= G :=
    lpf_unit_difference_allowance_pair_bound u C D ((B - A : Nat) : Real) (Nat.cast_nonneg _)
  have hG : 0 <= G := hGammaNonneg.trans hGamma
  have hE : E <= B2 * G := hEnergy.trans (mul_le_mul_of_nonneg_left hGamma hB2)
  have hOuterNonneg : 0 <= Finset.sum S (fun m => norm (outer m) ^ 2) := by positivity
  have hFinal := (hCauchy.trans (mul_le_mul_of_nonneg_left hE hOuterNonneg)).trans
    (mul_le_mul_of_nonneg_right hA (mul_nonneg hB2 hG))
  calc
    _ <= A2 * (B2 * G) := hFinal
    _ = _ := by dsimp [G]; ring

theorem lpf_nat_div_cast_le (L q : Nat) (hq : 0 < q) :
    ((L / q : Nat) : Real) <= (L : Real) / (q : Real) := by
  have hNat : q * (L / q) <= L := by
    have h := Nat.div_add_mod L q
    omega
  have hMul : (q : Real) * ((L / q : Nat) : Real) <= (L : Real) := by exact_mod_cast hNat
  have hqR : (0 : Real) < (q : Real) := Nat.cast_pos.mpr hq
  have h := div_le_div_of_nonneg_right hMul hqR.le
  have hCancel : ((q : Real) * ((L / q : Nat) : Real)) / (q : Real) = ((L / q : Nat) : Real) := by
    field_simp
  rw [hCancel] at h
  exact h

theorem lpf_typeII_residue_cost_bound (x y M R q Z : Real)
    (hx : 0 <= x) (hy : 0 <= y) (hM : 0 <= M) (hR : 0 <= R)
    (hq : 0 < q) (hZ : 1 <= Z) (hProduct : x * y <= M) (hWidth : x + y <= R) :
    x * y * (y / q + 1) * (x + 2 * q * Z) <= M * (M / q + 2 * R + 2 * q) * Z := by
  have hZ0 : 0 <= Z := by linarith
  have hExpand : (y / q + 1) * (x + 2 * q * Z) = x * y / q + x + 2 * y * Z + 2 * q * Z := by
    field_simp
    ring
  have hFirst : x * y / q <= (M / q) * Z := by
    have hDiv := div_le_div_of_nonneg_right hProduct hq.le
    have hScale := mul_le_mul_of_nonneg_left hZ (by positivity : 0 <= M / q)
    nlinarith only [hDiv, hScale]
  have hMiddle : x + 2 * y * Z <= 2 * R * Z := by
    have hX := mul_le_mul_of_nonneg_left hZ hx
    have hWidthZ := mul_le_mul_of_nonneg_right hWidth hZ0
    have hY := mul_nonneg hy hZ0
    nlinarith only [hX, hWidthZ, hY, hx]
  have hBracket : (y / q + 1) * (x + 2 * q * Z) <= (M / q + 2 * R + 2 * q) * Z := by
    rw [hExpand]
    nlinarith only [hFirst, hMiddle]
  have hNonneg : 0 <= (M / q + 2 * R + 2 * q) * Z := by positivity
  calc
    _ = (x * y) * ((y / q + 1) * (x + 2 * q * Z)) := by ring
    _ <= (x * y) * ((M / q + 2 * R + 2 * q) * Z) :=
      mul_le_mul_of_nonneg_left hBracket (mul_nonneg hx hy)
    _ <= M * ((M / q + 2 * R + 2 * q) * Z) := mul_le_mul_of_nonneg_right hProduct hNonneg
    _ = _ := by ring

theorem lpf_typeII_natural_residue_cost_bound (Qm Qn q : Nat) (hq : 0 < q) (M R : Real)
    (hM : 0 <= M) (hR : 0 <= R)
    (hProduct : (Qm : Real) * (Qn : Real) <= M) (hWidth : (Qm : Real) + (Qn : Real) <= R) :
    (Qm : Real) * (Qn : Real) * ((Qn / q + 1 : Nat) : Real) *
      ((Qm : Real) + 2 * (q : Real) * (1 + Real.log (q : Real))) <=
        M * (M / (q : Real) + 2 * R + 2 * (q : Real)) * (1 + Real.log (q : Real)) := by
  have hLog : 0 <= Real.log (q : Real) := Real.log_nonneg (by exact_mod_cast (show 1 <= q by omega))
  have hZ : 1 <= 1 + Real.log (q : Real) := by linarith
  have hFloor : ((Qn / q + 1 : Nat) : Real) <= (Qn : Real) / (q : Real) + 1 := by
    push_cast
    have h := lpf_nat_div_cast_le Qn q hq
    linarith
  calc
    _ <= (Qm : Real) * (Qn : Real) * ((Qn : Real) / (q : Real) + 1) *
        ((Qm : Real) + 2 * (q : Real) * (1 + Real.log (q : Real))) := by
      gcongr
    _ <= _ := lpf_typeII_residue_cost_bound (Qm : Real) (Qn : Real) M R (q : Real)
      (1 + Real.log (q : Real)) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hM hR
      (Nat.cast_pos.mpr hq) hZ hProduct hWidth

theorem exists_lpf_typeII_actual_packet_bound :
    exists Ctau : Real, And (0 < Ctau)
      (forall {N q : Nat} [NeZero N] [NeZero q] (k a : Int) (u : Units (ZMod q)),
        (a : ZMod q) = (u : ZMod q) -> forall (beta : Real) (U V A B C D s L H : Nat),
        B <= H -> D <= H -> 1 <= H ->
        (k : Real) / (N : Real) = (a : Real) / (q : Real) + beta ->
        abs beta * ((D - C : Nat) : Real) <= 1 / (4 * (q : Real)) ->
        norm (Finset.sum (Finset.Ioc A B) (fun m =>
          ((ArithmeticFunction.vonMangoldt m - lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U m : Real) : Complex) *
            Finset.sum (Finset.Ioc C D) (fun n => ((lpfVaughanB V n : Real) : Complex) *
              lpfBilinearFrequencyWindowPhase N s L k m n))) ^ 2 <=
          Ctau * (H : Real) ^ ((1 : Real) / 160) * Real.log (H : Real) ^ 2 *
            ((B - A : Nat) : Real) * ((D - C : Nat) : Real) * (((D - C) / q + 1 : Nat) : Real) *
              (((B - A : Nat) : Real) + 2 * (q : Real) * (1 + Real.log (q : Real)))) := by
  choose Ctau hCtau hTau using exists_lpf_divisors_square_power_bound
  refine Exists.intro Ctau (And.intro hCtau ?_)
  intro N q instN instQ k a u hU beta U V A B C D s L H hB hD hH hAlpha hBeta
  have hOuter := lpfVaughanHighLambda_square_sum_le U A B H hB hH
  have hInner : forall n, Membership.mem (Finset.Ioc C D) n ->
      norm ((lpfVaughanB V n : Real) : Complex) ^ 2 <= Ctau * (H : Real) ^ ((1 : Real) / 160) := by
    intro n hn
    exact lpfVaughanB_square_le_power Ctau hCtau.le hTau V n H ((Finset.mem_Ioc.mp hn).2.trans hD)
  have h := lpf_typeII_weighted_packet_bound (N := N) (q := q) k a u hU beta A B C D s L
    (fun m => ((ArithmeticFunction.vonMangoldt m - lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U m : Real) : Complex))
    (fun n => ((lpfVaughanB V n : Real) : Complex))
    (((B - A : Nat) : Real) * Real.log (H : Real) ^ 2)
    (Ctau * (H : Real) ^ ((1 : Real) / 160)) hAlpha hBeta hOuter (by positivity) hInner
  convert h using 1 <;> ring

end PrimeFactorOscillations.LPF
