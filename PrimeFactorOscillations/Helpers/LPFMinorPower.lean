/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFMinorWeightedPacket

/-!
# Physical-scale specialization of the complete Type II residue cost

For box-width product at most2*M, total width at most4*M^(3/5), and
q<=2*M, the exact finite residue cost is at most
16*(M^2/q+M^(8/5)+M*q)*(1+log(2*M)). The actual weighted packet
consumer is provided by LPFMinorWeightedPacket; full minor-arc assembly
still requires Type I, range coverage and rational approximation.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem lpf_typeII_physical_cost_bound (M Qm Qn q : Nat) (hM : 1 <= M) (hq0 : 0 < q)
    (hq : q <= 2 * M) (hProduct : Qm * Qn <= 2 * M)
    (hWidth : (Qm : Real) + (Qn : Real) <= 4 * (M : Real) ^ (3 / 5 : Real)) :
    (Qm : Real) * (Qn : Real) * ((Qn / q + 1 : Nat) : Real) *
      ((Qm : Real) + 2 * (q : Real) * (1 + Real.log (q : Real))) <=
        16 * ((M : Real) ^ 2 / (q : Real) + (M : Real) ^ (8 / 5 : Real) + (M : Real) * (q : Real)) *
          (1 + Real.log (2 * (M : Real))) := by
  have hMR : (0 : Real) < (M : Real) := Nat.cast_pos.mpr (by omega : 0 < M)
  have hqR : (0 : Real) < (q : Real) := Nat.cast_pos.mpr hq0
  have hProductR : (Qm : Real) * (Qn : Real) <= 2 * (M : Real) := by exact_mod_cast hProduct
  have hCost := lpf_typeII_natural_residue_cost_bound Qm Qn q hq0 (2 * (M : Real))
    (4 * (M : Real) ^ (3 / 5 : Real)) (by positivity) (by positivity) hProductR hWidth
  have hPower : (M : Real) * (M : Real) ^ (3 / 5 : Real) = (M : Real) ^ (8 / 5 : Real) := by
    rw [show (8 / 5 : Real) = (1 : Real) + (3 / 5 : Real) by norm_num,
      Real.rpow_add hMR, Real.rpow_one]
  have hRaw : 2 * (M : Real) * (2 * (M : Real) / (q : Real) +
      2 * (4 * (M : Real) ^ (3 / 5 : Real)) + 2 * (q : Real)) =
        4 * (M : Real) ^ 2 / (q : Real) + 16 * (M : Real) ^ (8 / 5 : Real) + 4 * (M : Real) * (q : Real) := by
    rw [<- hPower]
    ring
  rw [hRaw] at hCost
  have hLogq : 0 <= Real.log (q : Real) := Real.log_nonneg (by exact_mod_cast (show 1 <= q by omega))
  have hQMax : (q : Real) <= 2 * (M : Real) := by exact_mod_cast hq
  have hLogs : 1 + Real.log (q : Real) <= 1 + Real.log (2 * (M : Real)) := by
    have h := Real.log_le_log hqR hQMax
    linarith
  let T : Real := (M : Real) ^ 2 / (q : Real) + (M : Real) ^ (8 / 5 : Real) + (M : Real) * (q : Real)
  have hT : 0 <= T := by dsimp [T]; positivity
  have hPoly : 4 * (M : Real) ^ 2 / (q : Real) + 16 * (M : Real) ^ (8 / 5 : Real) +
      4 * (M : Real) * (q : Real) <= 16 * T := by
    have h1 : 0 <= (M : Real) ^ 2 / (q : Real) := by positivity
    have h3 : 0 <= (M : Real) * (q : Real) := by positivity
    dsimp [T]
    simp only [div_eq_mul_inv] at h1
    simp only [div_eq_mul_inv]
    nlinarith only [h1, h3]
  exact (hCost.trans (mul_le_mul_of_nonneg_right hPoly (by positivity))).trans
    (mul_le_mul_of_nonneg_left hLogs (by positivity))

theorem exists_lpf_typeII_actual_power_bound :
    exists K : Real, And (0 < K)
      (forall {N q : Nat} [NeZero N] [NeZero q] (M : Nat), 1 <= M -> q <= 2 * M ->
        forall (k a : Int) (u : Units (ZMod q)), (a : ZMod q) = (u : ZMod q) ->
        forall (beta : Real) (U V A B C D s L : Nat), B <= 2 * M -> D <= 2 * M ->
        (B - A) * (D - C) <= 2 * M ->
        ((B - A : Nat) : Real) + ((D - C : Nat) : Real) <= 4 * (M : Real) ^ (3 / 5 : Real) ->
        (k : Real) / (N : Real) = (a : Real) / (q : Real) + beta ->
        abs beta * ((D - C : Nat) : Real) <= 1 / (4 * (q : Real)) ->
        norm (Finset.sum (Finset.Ioc A B) (fun m =>
          ((ArithmeticFunction.vonMangoldt m - lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U m : Real) : Complex) *
            Finset.sum (Finset.Ioc C D) (fun n => ((lpfVaughanB V n : Real) : Complex) *
              lpfBilinearFrequencyWindowPhase N s L k m n))) ^ 2 <=
          K * (M : Real) ^ ((1 : Real) / 160) *
            ((M : Real) ^ 2 / (q : Real) + (M : Real) ^ (8 / 5 : Real) + (M : Real) * (q : Real)) *
              (1 + Real.log (2 * (M : Real))) ^ 3) := by
  choose Ctau hCtau hActual using exists_lpf_typeII_actual_packet_bound
  refine Exists.intro (16 * Ctau * (2 : Real) ^ ((1 : Real) / 160)) (And.intro (by positivity) ?_)
  intro N q instN instQ M hM hQ k a u hU beta U V A B C D s L hB hD hProduct hWidth hAlpha hBeta
  have hMR : (0 : Real) < (M : Real) := Nat.cast_pos.mpr (by omega : 0 < M)
  have hH : 1 <= 2 * M := by omega
  let cost : Real := ((B - A : Nat) : Real) * ((D - C : Nat) : Real) *
    (((D - C) / q + 1 : Nat) : Real) *
      (((B - A : Nat) : Real) + 2 * (q : Real) * (1 + Real.log (q : Real)))
  let T : Real := (M : Real) ^ 2 / (q : Real) + (M : Real) ^ (8 / 5 : Real) + (M : Real) * (q : Real)
  let Z : Real := 1 + Real.log (2 * (M : Real))
  have hBound0 := hActual (N := N) (q := q) k a u hU beta U V A B C D s L (2 * M) hB hD hH hAlpha hBeta
  have hBound : norm (Finset.sum (Finset.Ioc A B) (fun m =>
      ((ArithmeticFunction.vonMangoldt m - lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U m : Real) : Complex) *
        Finset.sum (Finset.Ioc C D) (fun n => ((lpfVaughanB V n : Real) : Complex) *
          lpfBilinearFrequencyWindowPhase N s L k m n))) ^ 2 <=
      Ctau * ((2 * M : Nat) : Real) ^ ((1 : Real) / 160) * Real.log ((2 * M : Nat) : Real) ^ 2 * cost := by
    convert hBound0 using 1 <;> dsimp [cost] <;> ring
  have hCast : ((2 * M : Nat) : Real) = 2 * (M : Real) := by simp only [Nat.cast_mul, Nat.cast_ofNat]
  rw [hCast, Real.mul_rpow (by norm_num : (0 : Real) <= 2) hMR.le] at hBound
  have hqLog : 0 <= Real.log (q : Real) :=
    Real.log_nonneg (by exact_mod_cast (show 1 <= q from Nat.pos_of_ne_zero (NeZero.ne q)))
  have hCostNonneg : 0 <= cost := by dsimp [cost]; positivity
  have hT : 0 <= T := by dsimp [T]; positivity
  have hLog : 0 <= Real.log (2 * (M : Real)) := by
    apply Real.log_nonneg
    have hOne : (1 : Real) <= (M : Real) := by exact_mod_cast hM
    linarith
  have hZ : 0 <= Z := by dsimp [Z]; linarith
  have hLogSq : Real.log (2 * (M : Real)) ^ 2 <= Z ^ 2 := by dsimp [Z]; nlinarith
  have hCost : cost <= 16 * T * Z :=
    lpf_typeII_physical_cost_bound M (B - A) (D - C) q hM (Nat.pos_of_ne_zero (NeZero.ne q))
      hQ hProduct hWidth
  calc
    _ <= Ctau * ((2 : Real) ^ ((1 : Real) / 160) * (M : Real) ^ ((1 : Real) / 160)) *
        Real.log (2 * (M : Real)) ^ 2 * cost := hBound
    _ <= Ctau * ((2 : Real) ^ ((1 : Real) / 160) * (M : Real) ^ ((1 : Real) / 160)) * Z ^ 2 * cost := by
      gcongr
    _ <= Ctau * ((2 : Real) ^ ((1 : Real) / 160) * (M : Real) ^ ((1 : Real) / 160)) * Z ^ 2 * (16 * T * Z) := by
      gcongr
    _ = _ := by dsimp [T, Z]; ring

end PrimeFactorOscillations.LPF
