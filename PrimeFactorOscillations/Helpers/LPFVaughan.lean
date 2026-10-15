/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimeFactorOscillations.Helpers.LPFDivisorMoment

/-!
# Exact Vaughan decomposition of the actual von Mangoldt weight

All products here are Dirichlet convolutions of ArithmeticFunction Real.
The four signed terms hold for every natural U,V, including zero, using
Mathlib's genuine mu*zeta=1 and zeta*Lambda=log identities. The cutoffs
retain all inputs, including prime powers and prime 2. These identities
prepare the coupled minor-arc consumer; they do not bound its bilinear sum.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

noncomputable def lpfArithmeticCutoff (f : ArithmeticFunction Real) (K : Nat) : ArithmeticFunction Real :=
  ZeroHom.mk (fun n => if n <= K then f n else 0) (by simp)

theorem lpfArithmeticCutoff_apply (f : ArithmeticFunction Real) (K n : Nat) :
    lpfArithmeticCutoff f K n = if n <= K then f n else 0 := rfl

theorem lpfVaughanIdentity (U V : Nat) :
    ArithmeticFunction.vonMangoldt =
      lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U +
      lpfArithmeticCutoff (ArithmeticFunction.moebius : ArithmeticFunction Real) V * ArithmeticFunction.log -
      lpfArithmeticCutoff (ArithmeticFunction.moebius : ArithmeticFunction Real) V *
        (ArithmeticFunction.zeta : ArithmeticFunction Real) *
          lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U +
      ((ArithmeticFunction.moebius : ArithmeticFunction Real) -
        lpfArithmeticCutoff (ArithmeticFunction.moebius : ArithmeticFunction Real) V) *
        (ArithmeticFunction.zeta : ArithmeticFunction Real) *
          (ArithmeticFunction.vonMangoldt - lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U) := by
  have hCancel : (ArithmeticFunction.moebius : ArithmeticFunction Real) *
      (ArithmeticFunction.zeta : ArithmeticFunction Real) = 1 := ArithmeticFunction.coe_moebius_mul_coe_zeta
  symm
  calc
    _ = ((ArithmeticFunction.moebius : ArithmeticFunction Real) *
        (ArithmeticFunction.zeta : ArithmeticFunction Real)) * ArithmeticFunction.vonMangoldt +
      (1 - (ArithmeticFunction.moebius : ArithmeticFunction Real) *
        (ArithmeticFunction.zeta : ArithmeticFunction Real)) *
          lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U := by
      rw [<- ArithmeticFunction.zeta_mul_vonMangoldt]
      ring
    _ = _ := by rw [hCancel]; simp

theorem abs_lpfArithmeticCutoff_moebius_le (V n : Nat) :
    abs (lpfArithmeticCutoff (ArithmeticFunction.moebius : ArithmeticFunction Real) V n) <= 1 := by
  rw [lpfArithmeticCutoff_apply]
  split_ifs
  . have h : ((abs (ArithmeticFunction.moebius n) : Int) : Real) <= ((1 : Int) : Real) :=
      Int.cast_le.mpr (ArithmeticFunction.abs_moebius_le_one (n := n))
    simpa only [ArithmeticFunction.intCoe_apply, Int.cast_abs, Int.cast_one] using h
  . norm_num

theorem lpfArithmeticCutoff_vonMangoldt_nonneg (U n : Nat) :
    0 <= lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U n := by
  rw [lpfArithmeticCutoff_apply]
  split_ifs
  . exact ArithmeticFunction.vonMangoldt_nonneg
  . rfl

theorem lpfArithmeticCutoff_vonMangoldt_le (U n : Nat) :
    lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U n <= ArithmeticFunction.vonMangoldt n := by
  rw [lpfArithmeticCutoff_apply]
  split_ifs
  . rfl
  . exact ArithmeticFunction.vonMangoldt_nonneg

noncomputable def lpfVaughanB (V : Nat) : ArithmeticFunction Real :=
  ((ArithmeticFunction.moebius : ArithmeticFunction Real) -
    lpfArithmeticCutoff (ArithmeticFunction.moebius : ArithmeticFunction Real) V) *
      (ArithmeticFunction.zeta : ArithmeticFunction Real)

noncomputable def lpfVaughanA (U V : Nat) : ArithmeticFunction Real :=
  lpfArithmeticCutoff (ArithmeticFunction.moebius : ArithmeticFunction Real) V *
    lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U

theorem lpfVaughanB_apply (V n : Nat) :
    lpfVaughanB V n = Finset.sum n.divisors (fun d =>
      if V < d then (ArithmeticFunction.moebius d : Real) else 0) := by
  unfold lpfVaughanB
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  apply Finset.sum_congr rfl
  intro d hd
  change (ArithmeticFunction.moebius d : Real) -
      (if d <= V then (ArithmeticFunction.moebius d : Real) else 0) =
        if V < d then (ArithmeticFunction.moebius d : Real) else 0
  by_cases h : d <= V
  . simp [h, not_lt.mpr h]
  . simp [h, lt_of_not_ge h]

theorem abs_lpfVaughanB_le (V n : Nat) : abs (lpfVaughanB V n) <= (n.divisors.card : Real) := by
  rw [lpfVaughanB_apply]
  calc
    _ <= Finset.sum n.divisors (fun d => abs (if V < d then (ArithmeticFunction.moebius d : Real) else 0)) := by
      simpa only [Real.norm_eq_abs] using norm_sum_le n.divisors
        (fun d => if V < d then (ArithmeticFunction.moebius d : Real) else 0)
    _ <= Finset.sum n.divisors (fun _ => (1 : Real)) := by
      apply Finset.sum_le_sum
      intro d hd
      split_ifs
      . have h : ((abs (ArithmeticFunction.moebius d) : Int) : Real) <= ((1 : Int) : Real) :=
          Int.cast_le.mpr (ArithmeticFunction.abs_moebius_le_one (n := d))
        simpa only [Int.cast_abs, Int.cast_one] using h
      . norm_num
    _ = _ := by simp

theorem lpfVaughanB_eq_zero_of_le (V n : Nat) (hn : n <= V) : lpfVaughanB V n = 0 := by
  rw [lpfVaughanB_apply]
  apply Finset.sum_eq_zero
  intro d hd
  have hMem := Nat.mem_divisors.mp hd
  have hD : d <= V := (Nat.le_of_dvd (Nat.pos_of_ne_zero hMem.2) hMem.1).trans hn
  exact ite_eq_right (not_lt.mpr hD)

theorem abs_lpfArithmeticCutoff_moebius_le_zeta (V n : Nat) :
    abs (lpfArithmeticCutoff (ArithmeticFunction.moebius : ArithmeticFunction Real) V n) <=
      (ArithmeticFunction.zeta : ArithmeticFunction Real) n := by
  by_cases hn : n = 0
  . subst n
    simp
  . have hZ : (ArithmeticFunction.zeta : ArithmeticFunction Real) n = 1 := by
      rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne hn, Nat.cast_one]
    rw [hZ]
    exact abs_lpfArithmeticCutoff_moebius_le V n

theorem abs_lpfVaughanA_le_log (U V n : Nat) : abs (lpfVaughanA U V n) <= Real.log (n : Real) := by
  unfold lpfVaughanA
  rw [ArithmeticFunction.mul_apply]
  calc
    _ <= Finset.sum n.divisorsAntidiagonal (fun x =>
        abs (lpfArithmeticCutoff (ArithmeticFunction.moebius : ArithmeticFunction Real) V x.1 *
          lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U x.2)) := by
      simpa only [Real.norm_eq_abs] using norm_sum_le n.divisorsAntidiagonal
        (fun x => lpfArithmeticCutoff (ArithmeticFunction.moebius : ArithmeticFunction Real) V x.1 *
          lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U x.2)
    _ <= Finset.sum n.divisorsAntidiagonal (fun x =>
        (ArithmeticFunction.zeta : ArithmeticFunction Real) x.1 * ArithmeticFunction.vonMangoldt x.2) := by
      apply Finset.sum_le_sum
      intro x hx
      rw [abs_mul, abs_of_nonneg (lpfArithmeticCutoff_vonMangoldt_nonneg U x.2)]
      have hZ : 0 <= (ArithmeticFunction.zeta : ArithmeticFunction Real) x.1 := by
        rw [ArithmeticFunction.natCoe_apply]
        exact Nat.cast_nonneg _
      exact mul_le_mul (abs_lpfArithmeticCutoff_moebius_le_zeta V x.1)
        (lpfArithmeticCutoff_vonMangoldt_le U x.2) (lpfArithmeticCutoff_vonMangoldt_nonneg U x.2) hZ
    _ = ((ArithmeticFunction.zeta : ArithmeticFunction Real) * ArithmeticFunction.vonMangoldt) n :=
      ArithmeticFunction.mul_apply.symm
    _ = _ := by rw [ArithmeticFunction.zeta_mul_vonMangoldt, ArithmeticFunction.log_apply]

theorem lpfVaughanA_eq_zero_of_lt (U V n : Nat) (hn : U * V < n) : lpfVaughanA U V n = 0 := by
  unfold lpfVaughanA
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro x hx
  have hProd := (Nat.mem_divisorsAntidiagonal.mp hx).1
  by_cases hV : x.1 <= V
  . by_cases hU : x.2 <= U
    . have h : n <= U * V := by
        rw [<- hProd]
        exact (Nat.mul_le_mul hV hU).trans_eq (Nat.mul_comm V U)
      exact False.elim (not_lt_of_ge h hn)
    . simp only [lpfArithmeticCutoff_apply, ite_eq_right hU, mul_zero]
  . simp only [lpfArithmeticCutoff_apply, ite_eq_right hV, zero_mul]

theorem lpfVaughanTypeI_reordered (U V : Nat) :
    lpfArithmeticCutoff (ArithmeticFunction.moebius : ArithmeticFunction Real) V *
        (ArithmeticFunction.zeta : ArithmeticFunction Real) *
          lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U =
      lpfVaughanA U V * (ArithmeticFunction.zeta : ArithmeticFunction Real) := by
  unfold lpfVaughanA
  ring

theorem lpfVaughanHighLambda_eq_zero_of_le (U n : Nat) (hn : n <= U) :
    ArithmeticFunction.vonMangoldt n - lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U n = 0 := by
  rw [lpfArithmeticCutoff_apply, ite_eq_left hn, sub_self]

theorem lpfVaughanHighLambda_nonneg (U n : Nat) :
    0 <= ArithmeticFunction.vonMangoldt n - lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U n :=
  sub_nonneg.mpr (lpfArithmeticCutoff_vonMangoldt_le U n)

theorem lpfVaughanHighLambda_le_log (U n : Nat) :
    ArithmeticFunction.vonMangoldt n - lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U n <=
      Real.log (n : Real) :=
  (sub_le_self _ (lpfArithmeticCutoff_vonMangoldt_nonneg U n)).trans ArithmeticFunction.vonMangoldt_le_log

theorem lpfVaughanHighLambda_square_sum_le (U A B H : Nat) (hB : B <= H) (hH : 1 <= H) :
    Finset.sum (Finset.Ioc A B) (fun m => norm
      ((ArithmeticFunction.vonMangoldt m - lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U m : Real) : Complex) ^ 2) <=
        ((B - A : Nat) : Real) * Real.log (H : Real) ^ 2 := by
  have hPoint : forall m, Membership.mem (Finset.Ioc A B) m -> norm
      ((ArithmeticFunction.vonMangoldt m - lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U m : Real) : Complex) ^ 2 <=
        Real.log (H : Real) ^ 2 := by
    intro m hm
    have hMem := Finset.mem_Ioc.mp hm
    have hmPos : (0 : Real) < (m : Real) := Nat.cast_pos.mpr (by omega : 0 < m)
    have hmH : (m : Real) <= (H : Real) := Nat.cast_le.mpr (hMem.2.trans hB)
    have hLog : Real.log (m : Real) <= Real.log (H : Real) := Real.log_le_log hmPos hmH
    have hUpper := (lpfVaughanHighLambda_le_log U m).trans hLog
    have hLow := lpfVaughanHighLambda_nonneg U m
    have hLogNonneg : 0 <= Real.log (H : Real) := Real.log_nonneg (by exact_mod_cast hH)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hLow]
    have h := mul_le_mul hUpper hUpper hLow hLogNonneg
    simpa only [pow_two] using h
  calc
    _ <= Finset.sum (Finset.Ioc A B) (fun _ => Real.log (H : Real) ^ 2) := Finset.sum_le_sum hPoint
    _ = _ := by simp only [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]

theorem lpfVaughanB_square_le_power (Ctau : Real) (hCtau : 0 <= Ctau)
    (hTau : forall n : Nat, (n.divisors.card : Real) ^ 2 <= Ctau * (n : Real) ^ ((1 : Real) / 160))
    (V n H : Nat) (hNH : n <= H) :
    norm ((lpfVaughanB V n : Real) : Complex) ^ 2 <= Ctau * (H : Real) ^ ((1 : Real) / 160) := by
  have hAbs := abs_lpfVaughanB_le V n
  have hSq : abs (lpfVaughanB V n) ^ 2 <= (n.divisors.card : Real) ^ 2 := by
    have h := mul_le_mul hAbs hAbs (abs_nonneg _) (Nat.cast_nonneg _)
    simpa only [pow_two] using h
  have hPower : (n : Real) ^ ((1 : Real) / 160) <= (H : Real) ^ ((1 : Real) / 160) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr hNH) (by norm_num)
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact (hSq.trans (hTau n)).trans (mul_le_mul_of_nonneg_left hPower hCtau)

end PrimeFactorOscillations.LPF
