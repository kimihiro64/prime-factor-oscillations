/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
/-!
# Field-independent integral odd-divisor probes

The finite index set and integer coefficients depend only on the selected
odd positive degrees. Their divisibility amplitudes are exact indicators
at every positive degree, over any ring. No field-dependent division occurs.
-/

set_option autoImplicit false
set_option Elab.async false
open scoped ArithmeticFunction

namespace UniversalOddDivisorProbe

theorem sum_moebius (n : Nat) (hn : Not (n = 0)) :
    n.divisors.sum (fun r => ArithmeticFunction.moebius r) =
      (if n = 1 then 1 else 0) := by
  have h := congrArg (fun f : ArithmeticFunction Int => f n)
    ArithmeticFunction.moebius_mul_coe_zeta
  rw [ArithmeticFunction.mul_apply] at h
  rw [Nat.sum_divisorsAntidiagonal (fun r s =>
    ArithmeticFunction.moebius r * (ArithmeticFunction.zeta : ArithmeticFunction Int) s)] at h
  change n.divisors.sum (fun r =>
    ArithmeticFunction.moebius r * (ArithmeticFunction.zeta (n / r) : Int)) =
      (1 : ArithmeticFunction Int) n at h
  simp only [ArithmeticFunction.one_apply] at h
  have he : n.divisors.sum (fun r =>
      ArithmeticFunction.moebius r * (ArithmeticFunction.zeta (n / r) : Int)) =
      n.divisors.sum (fun r => ArithmeticFunction.moebius r) := by
    apply Finset.sum_congr rfl
    intro r hr
    have hd := (Nat.mem_divisors.mp hr).1
    have hrpos : 0 < r := Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hn)
    have hrle : r <= n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd
    have hq : Not (n / r = 0) := Nat.ne_of_gt (Nat.div_pos hrle hrpos)
    simp [ArithmeticFunction.zeta_apply, hq]
  rw [he] at h
  exact h

theorem divisor_filter (d e : Nat) (hd : Not (d = 0)) (he : 0 < e) :
    d.divisors.filter (fun r => Dvd.dvd e (d / r)) =
      if Dvd.dvd e d then (d / e).divisors
        else (EmptyCollection.emptyCollection : Finset Nat) := by
  classical
  by_cases hed : Dvd.dvd e d
  . rw [ite_eq_left hed]
    have heq : Not (d / e = 0) :=
      Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hd) hed) he)
    apply Finset.ext
    intro r
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    . intro h
      have hr := h.1.1
      have hm : Dvd.dvd (r * e) d := (Nat.dvd_div_iff_mul_dvd hr).mp h.2
      have hm' : Dvd.dvd (e * r) d := by simpa only [Nat.mul_comm] using hm
      exact And.intro ((Nat.dvd_div_iff_mul_dvd hed).mpr hm') heq
    . intro h
      have hm : Dvd.dvd (e * r) d := (Nat.dvd_div_iff_mul_dvd hed).mp h.1
      have hr : Dvd.dvd r d := Nat.dvd_trans h.1 (Nat.div_dvd_of_dvd hed)
      have hm' : Dvd.dvd (r * e) d := by simpa only [Nat.mul_comm] using hm
      exact And.intro (And.intro hr hd) ((Nat.dvd_div_iff_mul_dvd hr).mpr hm')
  . rw [ite_eq_right hed]
    apply Finset.ext
    intro r
    simp only [Finset.notMem_empty, iff_false]
    intro hr
    have hh := Finset.mem_filter.mp hr
    have hdv := (Nat.mem_divisors.mp hh.1).1
    exact hed (Nat.dvd_trans hh.2 (Nat.div_dvd_of_dvd hdv))

theorem filtered_moebius (d e : Nat) (hd : Not (d = 0)) (he : 0 < e) :
    (d.divisors.filter (fun r => Dvd.dvd e (d / r))).sum
      (fun r => ArithmeticFunction.moebius r) =
        (if e = d then 1 else 0) := by
  classical
  rw [divisor_filter d e hd he]
  by_cases hed : Dvd.dvd e d
  . rw [ite_eq_left hed]
    have hq : Not (d / e = 0) :=
      Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hd) hed) he)
    rw [sum_moebius (d / e) hq]
    have hi : (d / e = 1) <-> e = d := by
      constructor
      . intro hh
        have hm := Nat.div_mul_cancel hed
        rw [hh, one_mul] at hm
        exact hm
      . intro hh
        subst e
        exact Nat.div_self (Nat.pos_of_ne_zero hd)
    simp only [hi]
  . rw [ite_eq_right hed]
    have hne : Not (e = d) := by
      intro hh
      apply hed
      rw [hh]
    simp only [Finset.sum_empty, ite_eq_right hne]


def probeIndex (d r : Nat) : Nat := (d / r - 1) / 2

def probeIndices (D : Finset Nat) : Finset Nat :=
  D.biUnion (fun d => d.divisors.image (probeIndex d))

noncomputable def probeCoefficients (D : Finset Nat) (k : Nat) : Int :=
  D.sum (fun d => d.divisors.sum (fun r =>
    if k = probeIndex d r then ArithmeticFunction.moebius r else 0))

theorem mem_probeIndices (D : Finset Nat) (d r : Nat)
    (hd : Membership.mem D d) (hr : Membership.mem d.divisors r) :
    Membership.mem (probeIndices D) (probeIndex d r) := by
  apply Finset.mem_biUnion.mpr
  apply Exists.intro d
  apply And.intro hd
  exact Finset.mem_image.mpr (Exists.intro r (And.intro hr rfl))

theorem evaluate {R : Type*} [Ring R] (D : Finset Nat) (f : Nat -> R) :
    (probeIndices D).sum (fun k => (probeCoefficients D k : R) * f k) =
      D.sum (fun d => d.divisors.sum (fun r =>
        (ArithmeticFunction.moebius r : R) * f (probeIndex d r))) := by
  classical
  simp only [probeCoefficients, Int.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  have hi := mem_probeIndices D d r hd hr
  calc
    _ = (probeIndices D).sum (fun k =>
        if k = probeIndex d r then (ArithmeticFunction.moebius r : R) * f k else 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases he : k = probeIndex d r
      . simp only [ite_eq_left he]
      . simp only [ite_eq_right he, Int.cast_zero, zero_mul]
    _ = _ := by rw [Finset.sum_ite_eq', ite_eq_left hi]

theorem index_identity (d r : Nat) (hd : Odd d)
    (hr : Membership.mem d.divisors r) :
    2 * probeIndex d r + 1 = d / r := by
  have hq : Odd (d / r) := hd.of_dvd_nat (Nat.div_dvd_of_dvd (Nat.mem_divisors.mp hr).1)
  choose k hk using hq
  unfold probeIndex
  rw [hk]
  omega

theorem amplitude (D : Finset Nat)
    (hD : forall d, Membership.mem D d -> Odd d /\ 0 < d)
    (e : Nat) (he : 0 < e) :
    ((probeIndices D).filter (fun k => Dvd.dvd e (2 * k + 1))).sum
      (probeCoefficients D) = (if Membership.mem D e then 1 else 0) := by
  classical
  have h := evaluate D (fun k => if Dvd.dvd e (2 * k + 1) then (1 : Int) else 0)
  simp only [mul_ite, mul_one, mul_zero] at h
  rw [<- Finset.sum_filter] at h
  calc
    _ = D.sum (fun d => d.divisors.sum (fun r =>
        if Dvd.dvd e (2 * probeIndex d r + 1) then ArithmeticFunction.moebius r else 0)) := h
    _ = D.sum (fun d => if e = d then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdata := hD d hd
      calc
        _ = (d.divisors.filter (fun r => Dvd.dvd e (d / r))).sum
            (fun r => ArithmeticFunction.moebius r) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro r hr
          rw [index_identity d r hdata.1 hr]
        _ = _ := filtered_moebius d e (Nat.ne_of_gt hdata.2) he
    _ = _ := Finset.sum_ite_eq D e (fun _ => (1 : Int))

end UniversalOddDivisorProbe

