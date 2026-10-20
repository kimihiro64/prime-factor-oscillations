/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.IntegerQuadraticMaskedPoisson

/-!
# CoprimeSchwartzPoisson

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described by LICENSE.
Authors: Prime Factor Oscillations contributors
-/


noncomputable section
open scoped BigOperators Classical

namespace PrimeFactorOscillations.CoprimeSchwartzPoisson

open IntegerQuadraticPoisson IntegerQuadraticScale IntegerQuadraticMaskedPoisson
open MeasureTheory

theorem scaled_samples_summable (a : Real) (ha : Not (a = 0))
    (f : SchwartzMap Real Complex) :
    Summable (fun n : Int => f (a * (n : Real))) := by
  simpa only [dilate_apply] using schwartz_int_summable (dilate a ha f)

theorem plain_poisson_scale (a : Real) (ha : 0 < a) (f : SchwartzMap Real Complex) :
    tsum (fun n : Int => f (a * (n : Real))) =
      (((a ^ (-1 : Int) : Real) : Complex) *
        tsum (fun n : Int => (FourierTransform.fourier f) ((n : Real) / a))) := by
  let g := dilate a (ne_of_gt ha) f
  calc
    _ = tsum (fun n : Int => g (n : Real)) := rfl
    _ = tsum (fun n : Int => (FourierTransform.fourier g) (n : Real)) := by
      simpa using g.tsum_eq_tsum_fourier (0 : Real)
    _ = tsum (fun n : Int => ((a ^ (-1 : Int) : Real) : Complex) *
        (FourierTransform.fourier f) ((n : Real) / a)) := by
      apply tsum_congr
      intro n
      exact fourier_dilate a ha f _
    _ = _ := tsum_mul_left

theorem quotient_samples_summable (X : Real) (hX : 0 < X)
    (f : SchwartzMap Real Complex) :
    Summable (fun n : Int => f ((n : Real) / X)) := by
  have h := scaled_samples_summable (1 / X) (ne_of_gt (div_pos (by norm_num) hX)) f
  apply h.congr
  intro n
  congr 1
  ring

def coprimeSum (q : Nat) (X : Real) (f : SchwartzMap Real Complex) : Complex :=
  tsum (fun n : Int => if Nat.Coprime n.natAbs q then f ((n : Real) / X) else 0)

theorem coprime_poisson (q : Nat) (hq : 0 < q)
    (X : Real) (hX : 0 < X) (f : SchwartzMap Real Complex) :
    coprimeSum q X f =
      q.divisors.sum (fun d => (ArithmeticFunction.moebius d : Complex) *
        (((X / (d : Real) : Real) : Complex) *
          tsum (fun l : Int => (FourierTransform.fourier f) ((l : Real) * X / (d : Real))))) := by
  unfold coprimeSum
  rw [tsum_coprime q hq _ (quotient_samples_summable X hX f)]
  apply Finset.sum_congr rfl
  intro d hd
  have hdq := (Nat.mem_divisors.mp hd).1
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdq hq
  have hdR : (0 : Real) < (d : Real) := by exact_mod_cast hdpos
  let a := (d : Real) / X
  have ha : 0 < a := div_pos hdR hX
  have hi : a ^ (-1 : Int) = X / (d : Real) := by
    dsimp only [a]
    simp only [zpow_neg_one, inv_div]
  have hl (v : Int) : f ((((d : Int) * v : Int) : Real) / X) = f (a * (v : Real)) := by
    congr 1
    simp only [Int.cast_mul, Int.cast_natCast]
    dsimp only [a]
    ring
  have hr (v : Int) : (v : Real) / a = (v : Real) * X / (d : Real) := by
    dsimp only [a]
    field_simp
  have hinner :
      tsum (fun v : Int => f ((((d : Int) * v : Int) : Real) / X)) =
        (((X / (d : Real) : Real) : Complex) *
          tsum (fun l : Int => (FourierTransform.fourier f) ((l : Real) * X / (d : Real)))) := by
    calc
      _ = tsum (fun v : Int => f (a * (v : Real))) := tsum_congr hl
      _ = _ := by
        rw [plain_poisson_scale a ha f, hi]
        congr 1
        apply tsum_congr
        intro l
        rw [hr l]
  rw [hinner]

theorem fourier_at_zero (f : SchwartzMap Real Complex) :
    (FourierTransform.fourier f) (0 : Real) =
      integral volume (fun x : Real => f x) := by
  change ((FourierTransform.fourier f) : Real -> Complex) 0 = _
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  simp

end PrimeFactorOscillations.CoprimeSchwartzPoisson
