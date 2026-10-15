/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import PrimeFactorOscillations.Helpers.LPFMinorGeometric
import PrimeFactorOscillations.Helpers.LPFVaughan

/-!
# Exact paired Type II energy on the actual product window

Cauchy is applied to the outer coefficient and the entire inner sum.
The paired expansion retains b(n1)*star(b(n2)), the relative phase,
and their common product-window intersection. Diagonals count their
exact admissible interval. The complete minor-arc estimate is still open.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem lpf_bilinear_cauchy {I : Type} (S : Finset I) (a f : I -> Complex) :
    norm (Finset.sum S (fun m => a m * f m)) ^ 2 <=
      Finset.sum S (fun m => norm (a m) ^ 2) * Finset.sum S (fun m => norm (f m) ^ 2) := by
  have hTriangle : norm (Finset.sum S (fun m => a m * f m)) <=
      Finset.sum S (fun m => norm (a m) * norm (f m)) := by
    simpa only [norm_mul] using norm_sum_le S (fun m => a m * f m)
  have hNonneg : 0 <= Finset.sum S (fun m => norm (a m) * norm (f m)) := by positivity
  have hSquare : norm (Finset.sum S (fun m => a m * f m)) ^ 2 <=
      (Finset.sum S (fun m => norm (a m) * norm (f m))) ^ 2 := by
    nlinarith only [hTriangle, hNonneg, norm_nonneg (Finset.sum S (fun m => a m * f m))]
  exact hSquare.trans (Finset.sum_mul_sq_le_sq_mul_sq S (fun m => norm (a m)) (fun m => norm (f m)))

theorem lpf_bilinear_pair_expansion {I J : Type} (S : Finset I) (T : Finset J)
    (b : J -> Complex) (w : I -> J -> Complex) :
    Finset.sum S (fun m => (Finset.sum T (fun n => b n * w m n)) *
      star (Finset.sum T (fun n => b n * w m n))) =
        Finset.sum T (fun n1 => Finset.sum T (fun n2 =>
          (b n1 * star (b n2)) * Finset.sum S (fun m => w m n1 * star (w m n2)))) := by
  have hPoint (m : I) :
      (Finset.sum T (fun n => b n * w m n)) * star (Finset.sum T (fun n => b n * w m n)) =
        Finset.sum T (fun n1 => Finset.sum T (fun n2 =>
          (b n1 * star (b n2)) * (w m n1 * star (w m n2)))) := by
    have hStar : star (Finset.sum T (fun n => b n * w m n)) =
        Finset.sum T (fun n => star (b n * w m n)) := by
      change (starRingEnd Complex) (Finset.sum T (fun n => b n * w m n)) = _
      rw [map_sum]
      rfl
    rw [hStar, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n1 hn1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n2 hn2
    rw [star_mul]
    ring
  simp_rw [hPoint]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n1 hn1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n2 hn2
  rw [Finset.mul_sum]

theorem lpf_bilinear_energy_pair_expansion {I J : Type} (S : Finset I) (T : Finset J)
    (b : J -> Complex) (w : I -> J -> Complex) :
    Finset.sum S (fun m => norm (Finset.sum T (fun n => b n * w m n)) ^ 2) =
      (Finset.sum T (fun n1 => Finset.sum T (fun n2 =>
        (b n1 * star (b n2)) * Finset.sum S (fun m => w m n1 * star (w m n2))))).re := by
  have h := congrArg Complex.re (lpf_bilinear_pair_expansion S T b w)
  have hNorm (z : Complex) : norm z ^ 2 = (z * star z).re := by
    change norm z ^ 2 = (z * (starRingEnd Complex) z).re
    rw [Complex.mul_conj, Complex.ofReal_re]
    rw [Complex.normSq_eq_norm_sq]
  have hRe (R : Finset I) (f : I -> Complex) :
      (Finset.sum R f).re = Finset.sum R (fun m => (f m).re) := by
    classical
    induction R using Finset.induction_on with
    | empty => simp
    | @insert m R hm ih => rw [Finset.sum_insert hm, Complex.add_re, ih, Finset.sum_insert hm]
  rw [<- h, hRe]
  apply Finset.sum_congr rfl
  intro m hm
  exact hNorm _

theorem lpf_bilinear_cauchy_packet {I J : Type} (S : Finset I) (T : Finset J)
    (a : I -> Complex) (b : J -> Complex) (w : I -> J -> Complex) :
    norm (Finset.sum S (fun m => a m * Finset.sum T (fun n => b n * w m n))) ^ 2 <=
      Finset.sum S (fun m => norm (a m) ^ 2) *
        (Finset.sum T (fun n1 => Finset.sum T (fun n2 =>
          (b n1 * star (b n2)) * Finset.sum S (fun m => w m n1 * star (w m n2))))).re := by
  have h := lpf_bilinear_cauchy S a (fun m => Finset.sum T (fun n => b n * w m n))
  rw [lpf_bilinear_energy_pair_expansion S T b w] at h
  exact h

theorem lpf_bilinear_phase_pair {N : Nat} [NeZero N] (m n1 n2 : Nat) :
    ZMod.stdAddChar (N := N) ((m : ZMod N) * (n1 : ZMod N)) *
      star (ZMod.stdAddChar (N := N) ((m : ZMod N) * (n2 : ZMod N))) =
        ZMod.stdAddChar (N := N) ((m : ZMod N) * ((n1 : ZMod N) - (n2 : ZMod N))) := by
  rw [<- lpf_stdAddChar_neg_star, <- AddChar.map_add_eq_mul]
  congr 1
  ring

noncomputable def lpfBilinearWindowPhase (N s L m n : Nat) [NeZero N] : Complex :=
  if And (s < m * n) (m * n <= s + L) then
    ZMod.stdAddChar (N := N) ((m : ZMod N) * (n : ZMod N)) else 0

theorem lpf_bilinear_window_pair {N : Nat} [NeZero N] (A B s L n1 n2 : Nat)
    (hn1 : 0 < n1) (hn2 : 0 < n2) :
    Finset.sum (Finset.Ioc A B) (fun m =>
      lpfBilinearWindowPhase N s L m n1 * star (lpfBilinearWindowPhase N s L m n2)) =
        Finset.sum (Finset.Ioc (max (max A (s / n1)) (s / n2))
          (min (min B ((s + L) / n1)) ((s + L) / n2))) (fun m =>
            ZMod.stdAddChar (N := N) ((m : ZMod N) * ((n1 : ZMod N) - (n2 : ZMod N)))) := by
  rw [<- lpf_product_window_pair_intersection A B s L n1 n2 hn1 hn2,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases h1 : And (s < m * n1) (m * n1 <= s + L)
  . by_cases h2 : And (s < m * n2) (m * n2 <= s + L)
    . simp only [lpfBilinearWindowPhase, h1, h2, ite_true, and_self]
      exact lpf_bilinear_phase_pair m n1 n2
    . simp [lpfBilinearWindowPhase, h1, h2]
  . simp [lpfBilinearWindowPhase, h1]

theorem lpf_bilinear_window_diagonal {N : Nat} [NeZero N] (A B s L n : Nat) (hn : 0 < n) :
    Finset.sum (Finset.Ioc A B) (fun m =>
      lpfBilinearWindowPhase N s L m n * star (lpfBilinearWindowPhase N s L m n)) =
        (((min B ((s + L) / n) - max A (s / n) : Nat) : Real) : Complex) := by
  rw [lpf_bilinear_window_pair A B s L n n hn hn]
  simp

noncomputable def lpfBilinearFrequencyWindowPhase (N s L : Nat) (k : Int) (m n : Nat) [NeZero N] : Complex :=
  if And (s < m * n) (m * n <= s + L) then
    ZMod.stdAddChar (N := N) ((k : ZMod N) * (m : ZMod N) * (n : ZMod N)) else 0

theorem lpf_bilinear_frequency_window_pair {N : Nat} [NeZero N] (k : Int) (A B s L n1 n2 : Nat)
    (hn1 : 0 < n1) (hn2 : 0 < n2) :
    Finset.sum (Finset.Ioc A B) (fun m =>
      lpfBilinearFrequencyWindowPhase N s L k m n1 * star (lpfBilinearFrequencyWindowPhase N s L k m n2)) =
        Finset.sum (Finset.Ioc (max (max A (s / n1)) (s / n2))
          (min (min B ((s + L) / n1)) ((s + L) / n2))) (fun m =>
            ZMod.stdAddChar (N := N) ((k : ZMod N) * (m : ZMod N) * ((n1 : ZMod N) - (n2 : ZMod N)))) := by
  rw [<- lpf_product_window_pair_intersection A B s L n1 n2 hn1 hn2, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  have hPhase : ZMod.stdAddChar (N := N) ((k : ZMod N) * (m : ZMod N) * (n1 : ZMod N)) *
      star (ZMod.stdAddChar (N := N) ((k : ZMod N) * (m : ZMod N) * (n2 : ZMod N))) =
        ZMod.stdAddChar (N := N) ((k : ZMod N) * (m : ZMod N) * ((n1 : ZMod N) - (n2 : ZMod N))) := by
    rw [<- lpf_stdAddChar_neg_star, <- AddChar.map_add_eq_mul]
    congr 1
    ring
  by_cases h1 : And (s < m * n1) (m * n1 <= s + L)
  . by_cases h2 : And (s < m * n2) (m * n2 <= s + L)
    . simp only [lpfBilinearFrequencyWindowPhase, h1, h2, ite_true, and_self]
      exact hPhase
    . simp [lpfBilinearFrequencyWindowPhase, h1, h2]
  . simp [lpfBilinearFrequencyWindowPhase, h1]

theorem lpf_bilinear_frequency_cauchy_packet {N : Nat} [NeZero N] (k : Int) (A B s L : Nat)
    (T : Finset Nat) (hT : forall n, Membership.mem T n -> 0 < n)
    (a b : Nat -> Complex) :
    norm (Finset.sum (Finset.Ioc A B) (fun m => a m *
      Finset.sum T (fun n => b n * lpfBilinearFrequencyWindowPhase N s L k m n))) ^ 2 <=
        Finset.sum (Finset.Ioc A B) (fun m => norm (a m) ^ 2) *
          (Finset.sum T (fun n1 => Finset.sum T (fun n2 =>
            (b n1 * star (b n2)) *
              Finset.sum (Finset.Ioc (max (max A (s / n1)) (s / n2))
                (min (min B ((s + L) / n1)) ((s + L) / n2))) (fun m =>
                  ZMod.stdAddChar (N := N)
                    ((k : ZMod N) * (m : ZMod N) * ((n1 : ZMod N) - (n2 : ZMod N))))))).re := by
  have h := lpf_bilinear_cauchy_packet (Finset.Ioc A B) T a b
    (fun m n => lpfBilinearFrequencyWindowPhase N s L k m n)
  have hPairs : Finset.sum T (fun n1 => Finset.sum T (fun n2 =>
      (b n1 * star (b n2)) * Finset.sum (Finset.Ioc A B) (fun m =>
        lpfBilinearFrequencyWindowPhase N s L k m n1 * star (lpfBilinearFrequencyWindowPhase N s L k m n2)))) =
          Finset.sum T (fun n1 => Finset.sum T (fun n2 => (b n1 * star (b n2)) *
            Finset.sum (Finset.Ioc (max (max A (s / n1)) (s / n2))
              (min (min B ((s + L) / n1)) ((s + L) / n2))) (fun m =>
                ZMod.stdAddChar (N := N)
                  ((k : ZMod N) * (m : ZMod N) * ((n1 : ZMod N) - (n2 : ZMod N)))))) := by
    apply Finset.sum_congr rfl
    intro n1 hn1
    apply Finset.sum_congr rfl
    intro n2 hn2
    rw [lpf_bilinear_frequency_window_pair k A B s L n1 n2 (hT n1 hn1) (hT n2 hn2)]
  rw [hPairs] at h
  exact h

end PrimeFactorOscillations.LPF
