/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFPowerTail
import PrimeFactorOscillations.Helpers.LPFRamanujanGeneral
import PrimeFactorOscillations.Helpers.LPFRationalGrid

/-!
The absolute finite singular-series tail with all moving endpoints retained.
The target is sum_{P<q<=Q} |mu(q)^2*c_q(t)/phi(q)^2|
<= 16*tau(t)/sqrt(P), for P>=1 and t>0. Frequency zero is excluded:
c_q(0)=phi(q) does not have this absolutely convergent tail.
This is the pointwise input for the full M^3/P mean-square packet; its
divisor second moment and the other signed packets remain separate obligations.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Classical

namespace PrimeFactorOscillations.LPF

noncomputable def lpfRamanujanCoefficient (q t : Nat) : Complex :=
  if hq : q = 0 then 0 else
    letI : NeZero q := NeZero.mk hq
    lpfRationalCoefficient q ^ 2 * lpfRamanujanSum (q := q) t

theorem lpfRamanujanCoefficient_eq {q : Nat} [NeZero q] (t : Nat) :
    lpfRamanujanCoefficient q t = lpfRationalCoefficient q ^ 2 * lpfRamanujanSum (q := q) t := by
  simp [lpfRamanujanCoefficient, NeZero.ne q]

noncomputable def lpfDivisorResonance (t q : Nat) : Real :=
  Finset.sum t.divisors (fun d => if Dvd.dvd d q then (d : Real) else 0)

theorem norm_lpfRamanujanSum_le_resonance {q : Nat} [NeZero q] (t : Nat) (ht : 0 < t) :
    norm (lpfRamanujanSum (q := q) t) <= lpfDivisorResonance t q := by
  have hGcd : Not (Nat.gcd q t = 0) := by
    intro h; exact (NeZero.ne q) (Nat.gcd_eq_zero_iff.mp h).1
  have hSet : t.divisors.filter (fun d => Dvd.dvd d q) = (Nat.gcd q t).divisors := by
    apply Finset.ext
    intro d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    . intro h
      exact And.intro (Nat.dvd_gcd h.2 h.1.1) hGcd
    . intro h
      have hd := Nat.dvd_gcd_iff.mp h.1
      exact And.intro (And.intro hd.2 (Nat.ne_of_gt ht)) hd.1
  unfold lpfDivisorResonance
  rw [<- Finset.sum_filter, hSet]
  exact norm_lpfRamanujanSum_le_divisors (q := q) t

theorem norm_lpfRamanujanCoefficient_le (q t : Nat) (hq : 0 < q) (ht : 0 < t) :
    norm (lpfRamanujanCoefficient q t) <= 4 * lpfDivisorResonance t q / (q : Real) ^ (3 / 2 : Real) := by
  letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
  have hRes : 0 <= lpfDivisorResonance t q := Finset.sum_nonneg (fun d hd => by
    split_ifs <;> positivity)
  have hRho := norm_lpfRationalCoefficient_le q hq
  have hSquare : norm (lpfRationalCoefficient q ^ 2) <= 1 / (q.totient : Real) ^ 2 := by
    rw [norm_pow]
    calc
      _ <= (1 / (q.totient : Real)) ^ 2 := by
        have h := mul_le_mul hRho hRho (norm_nonneg _) (by positivity)
        simpa only [pow_two] using h
      _ = _ := by rw [div_pow, one_pow]
  rw [lpfRamanujanCoefficient_eq, norm_mul]
  have hOne := mul_le_mul hSquare (norm_lpfRamanujanSum_le_resonance (q := q) t ht)
    (norm_nonneg _) (by positivity : 0 <= 1 / (q.totient : Real) ^ 2)
  have hTwo := mul_le_mul_of_nonneg_right (lpf_totient_inverse_sq_power_bound q hq) hRes
  exact hOne.trans (by convert hTwo using 1 <;> ring)

theorem lpf_multiples_tail_Ioc (d P Q : Nat) (hd : 1 <= d) (hP : 1 <= P) :
    Finset.sum ((Finset.Ioc P Q).filter (fun q => Dvd.dvd d q))
      (fun q => (d : Real) / (q : Real) ^ (3 / 2 : Real)) <= 4 / Real.sqrt (P : Real) := by
  let K := P / d
  let L := Q / d - K
  have hdPos : 0 < d := by omega
  have hDivP := Nat.div_add_mod P d
  have hModP := Nat.mod_lt P hdPos
  have hLow : P < d * (K + 1) := by change d * K + P % d = P at hDivP; nlinarith only [hDivP, hModP]
  have hBaseP : d * K <= P := by change d * K + P % d = P at hDivP; omega
  have hBaseQ : d * (Q / d) <= Q := by have h := Nat.div_add_mod Q d; omega
  have hMap : Finset.sum (Finset.range L) (fun i =>
      (d : Real) / ((d * (K + 1 + i) : Nat) : Real) ^ (3 / 2 : Real)) =
      Finset.sum ((Finset.Ioc P Q).filter (fun q => Dvd.dvd d q))
        (fun q => (d : Real) / (q : Real) ^ (3 / 2 : Real)) := by
    apply Finset.sum_bij (fun i _ => d * (K + 1 + i))
    . intro i hi
      have hiL := Finset.mem_range.mp hi
      have hHigh : K + 1 + i <= Q / d := by dsimp [L] at hiL; omega
      refine Finset.mem_filter.mpr (And.intro (Finset.mem_Ioc.mpr (And.intro ?_ ?_)) (dvd_mul_right d _))
      . exact hLow.trans_le (Nat.mul_le_mul_left d (by omega))
      . exact (Nat.mul_le_mul_left d hHigh).trans hBaseQ
    . intro i hi j hj hEq
      have h := Nat.eq_of_mul_eq_mul_left hdPos hEq
      omega
    . intro q hq
      have h := Finset.mem_filter.mp hq
      have hRange := Finset.mem_Ioc.mp h.1
      have hProduct : d * (q / d) = q := by rw [Nat.mul_comm, Nat.div_mul_cancel h.2]
      have hUpper : q / d <= Q / d := Nat.div_le_div_right hRange.2
      have hLower : K < q / d := by
        by_contra hNot
        have hLe : q / d <= K := le_of_not_gt hNot
        have hQle := (Nat.mul_le_mul_left d hLe).trans hBaseP
        rw [hProduct] at hQle
        exact Nat.not_le_of_gt hRange.1 hQle
      let i := q / d - K - 1
      have hi : Membership.mem (Finset.range L) i := by apply Finset.mem_range.mpr; dsimp [L, i]; omega
      have hIndex : K + 1 + i = q / d := by dsimp [i]; omega
      refine Exists.intro i (Exists.intro hi ?_)
      rw [hIndex, hProduct]
    . intro i hi
      rfl
  rw [<- hMap]
  exact lpf_inverse_power_multiples_tail d P L hd hP

theorem lpfRamanujanCoefficient_absolute_tail (P Q t : Nat) (hP : 1 <= P) (ht : 0 < t) :
    Finset.sum (Finset.Ioc P Q) (fun q => norm (lpfRamanujanCoefficient q t)) <=
      16 * (t.divisors.card : Real) / Real.sqrt (P : Real) := by
  have hPoint : Finset.sum (Finset.Ioc P Q) (fun q => norm (lpfRamanujanCoefficient q t)) <=
      Finset.sum (Finset.Ioc P Q) (fun q => 4 * lpfDivisorResonance t q / (q : Real) ^ (3 / 2 : Real)) := by
    apply Finset.sum_le_sum
    intro q hq
    have hRange := Finset.mem_Ioc.mp hq
    exact norm_lpfRamanujanCoefficient_le q t (by omega) ht
  have hReorder : Finset.sum (Finset.Ioc P Q) (fun q => 4 * lpfDivisorResonance t q / (q : Real) ^ (3 / 2 : Real)) =
      4 * Finset.sum t.divisors (fun d => Finset.sum ((Finset.Ioc P Q).filter (fun q => Dvd.dvd d q))
        (fun q => (d : Real) / (q : Real) ^ (3 / 2 : Real))) := by
    unfold lpfDivisorResonance
    simp only [Finset.mul_sum, Finset.sum_div]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q hq
    by_cases h : Dvd.dvd d q <;> simp [h, mul_div_assoc]
  rw [hReorder] at hPoint
  have hSum : Finset.sum t.divisors (fun d =>
      Finset.sum ((Finset.Ioc P Q).filter (fun q => Dvd.dvd d q))
        (fun q => (d : Real) / (q : Real) ^ (3 / 2 : Real))) <=
      Finset.sum t.divisors (fun _ => 4 / Real.sqrt (P : Real)) := by
    apply Finset.sum_le_sum
    intro d hd
    exact lpf_multiples_tail_Ioc d P Q (Nat.pos_of_mem_divisors hd) hP
  have hFinal := mul_le_mul_of_nonneg_left hSum (by norm_num : (0 : Real) <= 4)
  exact hPoint.trans (by convert hFinal using 1 <;> simp only [Finset.sum_const, nsmul_eq_mul] <;> ring)

end PrimeFactorOscillations.LPF
