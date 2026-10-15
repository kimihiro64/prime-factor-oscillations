/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import PrimeFactorOscillations.Helpers.LPFPhaseVariation

/-!
# Exact additive principal coefficient

Use the full Mobius coprimality mask before the geometric sum. All positive
moduli, including one and nonsquarefree moduli, remain in the domain.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

namespace PrimeFactorOscillations.LPF

private theorem lpf_sum_moebius_divisors (n : Nat) :
    Finset.sum n.divisors (fun d => (ArithmeticFunction.moebius d : Complex)) =
      if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction Complex => f n)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := Complex))
  simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.one_apply] using h

theorem lpf_coprime_moebius_mask (q n : Nat) (hq : Not (q = 0)) :
    Finset.sum q.divisors (fun d => (ArithmeticFunction.moebius d : Complex) *
      (if Dvd.dvd d n then 1 else 0)) = if Nat.Coprime n q then 1 else 0 := by
  classical
  have hg : Not (Nat.gcd n q = 0) := by
    intro hZero
    exact hq (Nat.gcd_eq_zero_iff.mp hZero).2
  have hSet : q.divisors.filter (fun d => Dvd.dvd d n) = (Nat.gcd n q).divisors := by
    apply Finset.ext
    intro d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    . intro h
      exact And.intro (Nat.dvd_gcd h.2 h.1.1) hg
    . intro h
      have hd := Nat.dvd_gcd_iff.mp h.1
      exact And.intro (And.intro hd.2 hq) hd.1
  simp only [mul_ite, mul_one, mul_zero]
  rw [<- Finset.sum_filter, hSet, lpf_sum_moebius_divisors]

theorem lpf_divisor_phase_sum {q : Nat} [NeZero q] {d : Nat}
    (hd : Membership.mem q.divisors d) :
    Finset.sum ((Finset.range q).filter (fun n => Dvd.dvd d n))
      (fun n => (ZMod.stdAddChar (N := q)) (n : ZMod q)) =
        if d = q then 1 else 0 := by
  classical
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hDvd := Nat.dvd_of_mem_divisors hd
  have hdPos := Nat.pos_of_mem_divisors hd
  by_cases hEq : d = q
  . subst d
    have hFilter : (Finset.range q).filter (fun n => Dvd.dvd q n) = {0} := by
      apply Finset.ext
      intro n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      . intro h
        by_cases hn : n = 0
        . exact hn
        . have hLe := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h.2
          omega
      . intro hn
        subst n
        exact And.intro hq (dvd_zero q)
    rw [hFilter]
    simp
  . rw [ite_eq_right hEq]
    have hProduct : d * (q / d) = q := by
      rw [Nat.mul_comm, Nat.div_mul_cancel hDvd]
    have hCastZero : (q : ZMod q) = 0 := by simp
    have hChar (k : Nat) : (ZMod.stdAddChar (N := q)) ((d * k : Nat) : ZMod q) =
        (ZMod.stdAddChar (N := q) (d : ZMod q)) ^ k := by
      rw [<- AddChar.map_nsmul_eq_pow]
      congr 1
      simp only [nsmul_eq_mul, Nat.cast_mul]
      ring
    have hPow : (ZMod.stdAddChar (N := q) (d : ZMod q)) ^ (q / d) = 1 := by
      rw [<- hChar, hProduct, hCastZero]
      exact AddChar.map_zero_eq_one _
    have hNontrivial : Not (ZMod.stdAddChar (N := q) (d : ZMod q) = 1) := by
      intro hOne
      have hZero : (d : ZMod q) = 0 := ZMod.injective_stdAddChar (by simpa using hOne)
      have hBack : Dvd.dvd q d := (CharP.cast_eq_zero_iff (ZMod q) q d).mp hZero
      exact hEq (Nat.dvd_antisymm hDvd hBack)
    have hMap : Finset.sum (Finset.range (q / d)) (fun k =>
        (ZMod.stdAddChar (N := q)) ((d * k : Nat) : ZMod q)) =
        Finset.sum ((Finset.range q).filter (fun n => Dvd.dvd d n))
          (fun n => (ZMod.stdAddChar (N := q)) (n : ZMod q)) := by
      apply Finset.sum_bij (fun k _ => d * k)
      . intro k hk
        have hk' := Finset.mem_range.mp hk
        apply Finset.mem_filter.mpr
        refine And.intro (Finset.mem_range.mpr ?_) (dvd_mul_right d k)
        calc
          _ < d * (q / d) := Nat.mul_lt_mul_of_pos_left hk' hdPos
          _ = _ := hProduct
      . intro k hk l hl hEqKL
        exact Nat.eq_of_mul_eq_mul_left hdPos hEqKL
      . intro n hn
        have hN := Finset.mem_filter.mp hn
        have hNlt := Finset.mem_range.mp hN.1
        have hNProduct : d * (n / d) = n := by rw [Nat.mul_comm, Nat.div_mul_cancel hN.2]
        refine Exists.intro (n / d) (Exists.intro ?_ hNProduct)
        apply Finset.mem_range.mpr
        by_contra hNot
        have hLe : q / d <= n / d := le_of_not_gt hNot
        have hMul := Nat.mul_le_mul_left d hLe
        rw [hProduct, hNProduct] at hMul
        exact Nat.not_le_of_gt hNlt hMul
      . intro k hk
        rfl
    rw [<- hMap]
    simp_rw [hChar]
    have hGeom := geom_sum_mul (ZMod.stdAddChar (N := q) (d : ZMod q)) (q / d)
    rw [hPow, sub_self] at hGeom
    exact (mul_eq_zero.mp hGeom).resolve_right (sub_ne_zero.mpr hNontrivial)

theorem lpf_coprime_phase_sum {q : Nat} [NeZero q] :
    Finset.sum (Finset.range q) (fun n =>
      if Nat.Coprime n q then ZMod.stdAddChar (N := q) (n : ZMod q) else 0) =
      (ArithmeticFunction.moebius q : Complex) := by
  classical
  calc
    _ = Finset.sum (Finset.range q) (fun n =>
        (Finset.sum q.divisors (fun d => (ArithmeticFunction.moebius d : Complex) *
          (if Dvd.dvd d n then 1 else 0))) * ZMod.stdAddChar (N := q) (n : ZMod q)) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [lpf_coprime_moebius_mask q n (NeZero.ne q)]
      by_cases h : Nat.Coprime n q <;> simp [h]
    _ = Finset.sum q.divisors (fun d => (ArithmeticFunction.moebius d : Complex) *
        Finset.sum (Finset.range q) (fun n =>
          if Dvd.dvd d n then ZMod.stdAddChar (N := q) (n : ZMod q) else 0)) := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      by_cases h : Dvd.dvd d n <;> simp [h]
    _ = Finset.sum q.divisors (fun d => (ArithmeticFunction.moebius d : Complex) *
        (if d = q then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [<- Finset.sum_filter, lpf_divisor_phase_sum hd]
    _ = _ := by simp [mul_ite, Nat.mem_divisors, NeZero.ne q]

private theorem lpf_unit_sum_eq_coprime_sum {q : Nat} [NeZero q] (g : ZMod q -> Complex) :
    Finset.sum Finset.univ (fun a : Units (ZMod q) => g (a : ZMod q)) =
      Finset.sum (Finset.range q) (fun n => if Nat.Coprime n q then g (n : ZMod q) else 0) := by
  classical
  rw [<- Finset.sum_filter]
  apply Finset.sum_bij (fun (a : Units (ZMod q)) _ => (a : ZMod q).val)
  . intro a _
    exact Finset.mem_filter.mpr (And.intro (Finset.mem_range.mpr (a : ZMod q).val_lt)
      (ZMod.val_coe_unit_coprime a))
  . intro a ha b hb hEq
    exact Units.ext (ZMod.val_injective q hEq)
  . intro n hn
    have hN := Finset.mem_filter.mp hn
    have hUnit : IsUnit (n : ZMod q) := (ZMod.isUnit_iff_coprime n q).mpr hN.2
    refine Exists.intro hUnit.unit (Exists.intro (Finset.mem_univ _) ?_)
    rw [hUnit.unit_spec, ZMod.val_natCast_of_lt (Finset.mem_range.mp hN.1)]
  . intro a _
    rw [ZMod.natCast_zmod_val]

theorem lpf_stdAddChar_sum_units {q : Nat} [NeZero q] :
    Finset.sum Finset.univ (fun a : Units (ZMod q) => ZMod.stdAddChar (N := q) (a : ZMod q)) =
      (ArithmeticFunction.moebius q : Complex) := by
  rw [lpf_unit_sum_eq_coprime_sum]
  exact lpf_coprime_phase_sum

noncomputable def lpfResiduePhase {q : Nat} [NeZero q]
    (a : Units (ZMod q)) (z : ZMod q) : Complex :=
  ZMod.stdAddChar ((a : ZMod q) * z)

theorem unitFourierCoefficient_lpfResiduePhase {q : Nat} [NeZero q]
    (a : Units (ZMod q)) :
    unitFourierCoefficient (lpfResiduePhase a) 1 = (ArithmeticFunction.moebius q : Complex) := by
  classical
  simp only [unitFourierCoefficient, MulChar.one_apply_coe, mul_one, lpfResiduePhase]
  calc
    _ = Finset.sum Finset.univ (fun u : Units (ZMod q) => ZMod.stdAddChar (N := q) (u : ZMod q)) := by
      apply Fintype.sum_equiv (Equiv.mulLeft a)
      intro u
      rfl
    _ = _ := lpf_stdAddChar_sum_units

theorem norm_lpfResiduePhase {q : Nat} [NeZero q] (a : Units (ZMod q)) (z : ZMod q) :
    norm (lpfResiduePhase a z) = 1 := by
  rw [lpfResiduePhase, ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

end PrimeFactorOscillations.LPF
