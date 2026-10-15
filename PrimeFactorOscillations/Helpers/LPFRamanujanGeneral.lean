/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFRamanujan
import PrimeFactorOscillations.Helpers.LPFTotientTail

/-!
The full Ramanujan coefficient, including its signed Mobius divisor mask.
The retained tail consumer needs |c_q(t)| <= sum_{d|gcd(q,t)} d and
1/phi(q)^2 <= 4/q^(3/2), followed by a joint divisor/tail summation.
This file does not assert that analytic tail estimate or density entry.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

namespace PrimeFactorOscillations.LPF

theorem lpf_divisor_frequency_phase_sum {q : Nat} [NeZero q] {d : Nat}
    (hd : Membership.mem q.divisors d) (t : Nat) :
    Finset.sum ((Finset.range q).filter (fun n => Dvd.dvd d n))
      (fun n => ZMod.stdAddChar (N := q) ((n * t : Nat) : ZMod q)) =
      if Dvd.dvd q (d * t) then ((q / d : Nat) : Complex) else (0 : Complex) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hDvd := Nat.dvd_of_mem_divisors hd
  have hdPos := Nat.pos_of_mem_divisors hd
  have hProduct : d * (q / d) = q := by rw [Nat.mul_comm, Nat.div_mul_cancel hDvd]
  have hMap : Finset.sum (Finset.range (q / d)) (fun k =>
      ZMod.stdAddChar (N := q) ((d * k * t : Nat) : ZMod q)) =
      Finset.sum ((Finset.range q).filter (fun n => Dvd.dvd d n))
        (fun n => ZMod.stdAddChar (N := q) ((n * t : Nat) : ZMod q)) := by
    apply Finset.sum_bij (fun k _ => d * k)
    . intro k hk
      have hk' := Finset.mem_range.mp hk
      apply Finset.mem_filter.mpr
      refine And.intro (Finset.mem_range.mpr ?_) (dvd_mul_right d k)
      calc
        _ < d * (q / d) := Nat.mul_lt_mul_of_pos_left hk' hdPos
        _ = _ := hProduct
    . intro k hk l hl hEq
      exact Nat.eq_of_mul_eq_mul_left hdPos hEq
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
  have hChar (k : Nat) :
      ZMod.stdAddChar (N := q) ((d * k * t : Nat) : ZMod q) =
        (ZMod.stdAddChar (N := q) ((d * t : Nat) : ZMod q)) ^ k := by
    rw [<- AddChar.map_nsmul_eq_pow]
    congr 1
    simp only [nsmul_eq_mul, Nat.cast_mul]
    ring
  rw [<- hMap]
  simp_rw [hChar]
  by_cases hDiv : Dvd.dvd q (d * t)
  . rw [ite_eq_left hDiv]
    have hZero : ((d * t : Nat) : ZMod q) = 0 :=
      (CharP.cast_eq_zero_iff (ZMod q) q (d * t)).mpr hDiv
    simp [hZero]
  . rw [ite_eq_right hDiv]
    have hPow : (ZMod.stdAddChar (N := q) ((d * t : Nat) : ZMod q)) ^ (q / d) = 1 := by
      rw [<- hChar]
      rw [show d * (q / d) * t = q * t by rw [hProduct]]
      simp only [Nat.cast_mul, CharP.cast_eq_zero, zero_mul, AddChar.map_zero_eq_one]
    have hNotOne : Not (ZMod.stdAddChar (N := q) ((d * t : Nat) : ZMod q) = 1) := by
      intro hOne
      have hZero : ((d * t : Nat) : ZMod q) = 0 :=
        ZMod.injective_stdAddChar (by simpa using hOne)
      exact hDiv ((CharP.cast_eq_zero_iff (ZMod q) q (d * t)).mp hZero)
    have hGeom := geom_sum_mul (ZMod.stdAddChar (N := q) ((d * t : Nat) : ZMod q)) (q / d)
    rw [hPow, sub_self] at hGeom
    exact (mul_eq_zero.mp hGeom).resolve_right (sub_ne_zero.mpr hNotOne)

private theorem lpf_unit_sum_eq_coprime_sum_general {q : Nat} [NeZero q] (g : ZMod q -> Complex) :
    Finset.sum Finset.univ (fun a : Units (ZMod q) => g (a : ZMod q)) =
      Finset.sum (Finset.range q) (fun n => if Nat.Coprime n q then g (n : ZMod q) else 0) := by
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

noncomputable def lpfRamanujanSum {q : Nat} [NeZero q] (t : Nat) : Complex :=
  Finset.sum Finset.univ (fun a : Units (ZMod q) =>
    ZMod.stdAddChar ((a : ZMod q) * (t : ZMod q)))

theorem lpfRamanujanSum_divisor_mask {q : Nat} [NeZero q] (t : Nat) :
    lpfRamanujanSum (q := q) t = Finset.sum q.divisors (fun d =>
      (ArithmeticFunction.moebius d : Complex) *
        (if Dvd.dvd q (d * t) then ((q / d : Nat) : Complex) else 0)) := by
  rw [lpfRamanujanSum, lpf_unit_sum_eq_coprime_sum_general
    (fun z : ZMod q => ZMod.stdAddChar (z * (t : ZMod q)))]
  calc
    _ = Finset.sum (Finset.range q) (fun n =>
      (Finset.sum q.divisors (fun d => (ArithmeticFunction.moebius d : Complex) *
        (if Dvd.dvd d n then 1 else 0))) * ZMod.stdAddChar ((n : ZMod q) * (t : ZMod q))) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [lpf_coprime_moebius_mask q n (NeZero.ne q)]
      by_cases h : Nat.Coprime n q <;> simp [h]
    _ = Finset.sum q.divisors (fun d => (ArithmeticFunction.moebius d : Complex) *
        Finset.sum (Finset.range q) (fun n =>
          if Dvd.dvd d n then ZMod.stdAddChar ((n : ZMod q) * (t : ZMod q)) else 0)) := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases h : Dvd.dvd d n <;> simp [h]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [<- Finset.sum_filter]
      simp only [<- Nat.cast_mul]
      rw [lpf_divisor_frequency_phase_sum hd t]

theorem lpfRamanujanSum_neg_frequency {q : Nat} [NeZero q] (t : Nat) :
    Finset.sum Finset.univ (fun a : Units (ZMod q) =>
      ZMod.stdAddChar (-((a : ZMod q) * (t : ZMod q)))) = lpfRamanujanSum (q := q) t := by
  unfold lpfRamanujanSum
  apply Fintype.sum_equiv (Equiv.mulLeft (-1 : Units (ZMod q)))
  intro a
  simp

private theorem lpf_divisor_complement_facts {q : Nat} [NeZero q] {d : Nat}
    (hd : Membership.mem q.divisors d) (t : Nat) :
    And (q / (q / d) = d) (Dvd.dvd q (d * t) <-> Dvd.dvd (q / d) t) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hDvd := Nat.dvd_of_mem_divisors hd
  have hdPos := Nat.pos_of_mem_divisors hd
  have hEPos : 0 < q / d := Nat.div_pos (Nat.le_of_dvd hq hDvd) hdPos
  have hProduct : d * (q / d) = q := by rw [Nat.mul_comm, Nat.div_mul_cancel hDvd]
  have hEDvd : Dvd.dvd (q / d) q := by
    exact Eq.mp (congrArg (fun x => Dvd.dvd (q / d) x) hProduct)
      (dvd_mul_left (q / d) d)
  have hInv : q / (q / d) = d := by
    apply Nat.eq_of_mul_eq_mul_left hEPos
    calc
      _ = q := by rw [Nat.mul_comm, Nat.div_mul_cancel hEDvd]
      _ = _ := by rw [Nat.mul_comm]; exact hProduct.symm
  refine And.intro hInv ?_
  constructor
  . intro h
    choose m hm using h
    refine Exists.intro m ?_
    apply Nat.eq_of_mul_eq_mul_left hdPos
    calc
      d * t = q * m := hm
      _ = (d * (q / d)) * m := congrArg (fun x => x * m) hProduct.symm
      _ = d * ((q / d) * m) := by ring
  . intro h
    choose m hm using h
    refine Exists.intro m ?_
    calc
      d * t = d * ((q / d) * m) := congrArg (fun x => d * x) hm
      _ = (d * (q / d)) * m := by ring
      _ = q * m := by rw [hProduct]

theorem lpfRamanujanSum_divisors {q : Nat} [NeZero q] (t : Nat) :
    lpfRamanujanSum (q := q) t = Finset.sum (Nat.gcd q t).divisors (fun d =>
      (d : Complex) * (ArithmeticFunction.moebius (q / d) : Complex)) := by
  let f : Nat -> Complex := fun d => (ArithmeticFunction.moebius (q / d) : Complex) *
    (if Dvd.dvd d t then (d : Complex) else 0)
  have hGcd : Not (Nat.gcd q t = 0) := by
    intro h
    exact (NeZero.ne q) (Nat.gcd_eq_zero_iff.mp h).1
  have hSet : q.divisors.filter (fun d => Dvd.dvd d t) = (Nat.gcd q t).divisors := by
    apply Finset.ext
    intro d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    . intro h
      exact And.intro (Nat.dvd_gcd h.1.1 h.2) hGcd
    . intro h
      have hd := Nat.dvd_gcd_iff.mp h.1
      exact And.intro (And.intro hd.1 (NeZero.ne q)) hd.2
  rw [lpfRamanujanSum_divisor_mask]
  calc
    _ = Finset.sum q.divisors (fun d => f (q / d)) := by
      apply Finset.sum_congr rfl
      intro d hd
      have h := lpf_divisor_complement_facts hd t
      dsimp [f]
      simp only [h.1, <- h.2]
    _ = Finset.sum q.divisors f := Nat.sum_div_divisors q f
    _ = _ := by
      dsimp [f]
      simp only [mul_ite, mul_zero]
      rw [<- Finset.sum_filter, hSet]
      apply Finset.sum_congr rfl
      intro d hd
      ring

theorem norm_lpfRamanujanSum_le_divisors {q : Nat} [NeZero q] (t : Nat) :
    norm (lpfRamanujanSum (q := q) t) <=
      Finset.sum (Nat.gcd q t).divisors (fun d => (d : Real)) := by
  rw [lpfRamanujanSum_divisors]
  calc
    _ <= Finset.sum (Nat.gcd q t).divisors (fun d =>
      norm ((d : Complex) * (ArithmeticFunction.moebius (q / d) : Complex))) := norm_sum_le _ _
    _ <= _ := by
      apply Finset.sum_le_sum
      intro d hd
      have hMu : norm (ArithmeticFunction.moebius (q / d) : Complex) <= 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q / d)
      rw [norm_mul, Complex.norm_natCast]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hMu (Nat.cast_nonneg d)

end PrimeFactorOscillations.LPF
