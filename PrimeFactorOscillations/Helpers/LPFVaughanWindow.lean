/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.LPFMinorDyadic
import PrimeFactorOscillations.Helpers.LPFMinorTypeILog

/-!
# Exact divisor-convolution and frequency-window reindexing

Every positive divisor pair appears once, with its exact product mask.
The Type I reindexing keeps integer quotient endpoints and the original
frequency. The complete signed Vaughan decomposition is proved in frequency
windows with actual coefficients and cutoff supports. Rational selection and
the full minor-arc/Parseval consumer remain open.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.LPF

theorem lpf_divisor_frequency_window_reindex {N : Nat} [NeZero N]
    (s L : Nat) (k : Int) (f g : Nat -> Complex) :
    Finset.sum (Finset.Ioc s (s + L)) (fun t => Finset.sum t.divisorsAntidiagonal (fun x =>
      f x.1 * g x.2 * ZMod.stdAddChar (N := N) ((k : ZMod N) * (t : ZMod N)))) =
        Finset.sum (Finset.Ioc 0 (s + L)) (fun d => f d *
          Finset.sum (Finset.Ioc 0 (s + L)) (fun m =>
            g m * lpfBilinearFrequencyWindowPhase N s L k d m)) := by
  classical
  let S := Finset.Ioc s (s + L)
  let T := ((Finset.Ioc 0 (s + L)).product (Finset.Ioc 0 (s + L))).filter
    (fun x : Prod Nat Nat => And (s < x.1 * x.2) (x.1 * x.2 <= s + L))
  have hReindex : Finset.sum (S.sigma (fun t => t.divisorsAntidiagonal)) (fun x =>
      f x.2.1 * g x.2.2 * ZMod.stdAddChar (N := N) ((k : ZMod N) * (x.1 : ZMod N))) =
        Finset.sum T (fun x => f x.1 * g x.2 * ZMod.stdAddChar (N := N)
          ((k : ZMod N) * (x.1 : ZMod N) * (x.2 : ZMod N))) := by
    apply Finset.sum_bij (fun x _ => x.2)
    . intro x hx
      have h := Finset.mem_sigma.mp hx
      have hIndex := Finset.mem_Ioc.mp h.1
      have hProd := (Nat.mem_divisorsAntidiagonal.mp h.2).1
      have htPos : 0 < x.1 := by omega
      have hdPos : 0 < x.2.1 := by
        by_contra hBad
        have hZero : x.2.1 = 0 := by omega
        rw [hZero, zero_mul] at hProd
        omega
      have hmPos : 0 < x.2.2 := by
        by_contra hBad
        have hZero : x.2.2 = 0 := by omega
        rw [hZero, mul_zero] at hProd
        omega
      have hdLe : x.2.1 <= x.1 := Nat.le_of_dvd htPos (Exists.intro x.2.2 hProd.symm)
      have hmLe : x.2.2 <= x.1 := Nat.le_of_dvd htPos (Exists.intro x.2.1 (by rw [Nat.mul_comm]; exact hProd.symm))
      apply Finset.mem_filter.mpr
      refine And.intro (Finset.mem_product.mpr (And.intro
        (Finset.mem_Ioc.mpr (And.intro hdPos (hdLe.trans hIndex.2)))
        (Finset.mem_Ioc.mpr (And.intro hmPos (hmLe.trans hIndex.2))))) ?_
      rw [hProd]
      exact hIndex
    . intro x hx y hy hPair
      have hX := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hx).2).1
      have hY := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hy).2).1
      have hIndex : x.1 = y.1 := by rw [<- hX, <- hY, hPair]
      apply Sigma.ext hIndex
      exact heq_of_eq hPair
    . intro x hx
      have h := (Finset.mem_filter.mp hx).2
      have hPositive : 0 < x.1 * x.2 := (Nat.zero_le s).trans_lt h.1
      refine Exists.intro (Sigma.mk (x.1 * x.2) x) (Exists.intro ?_ rfl)
      exact Finset.mem_sigma.mpr (And.intro (Finset.mem_Ioc.mpr h)
        (Nat.mem_divisorsAntidiagonal.mpr (And.intro rfl (Nat.ne_of_gt hPositive))))
    . intro x hx
      have hProd := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hx).2).1
      rw [<- hProd]
      simp only [Nat.cast_mul, mul_assoc]
  rw [Finset.sum_sigma] at hReindex
  change Finset.sum S _ = _
  rw [hReindex]
  dsimp [T]
  rw [Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  dsimp [lpfBilinearFrequencyWindowPhase]
  split_ifs <;> ring

theorem lpf_dirichlet_frequency_window_reindex {N : Nat} [NeZero N]
    (s L : Nat) (k : Int) (f g : ArithmeticFunction Real) :
    Finset.sum (Finset.Ioc s (s + L)) (fun t =>
      (((f * g) t : Real) : Complex) * ZMod.stdAddChar (N := N) ((k : ZMod N) * (t : ZMod N))) =
        Finset.sum (Finset.Ioc 0 (s + L)) (fun d => ((f d : Real) : Complex) *
          Finset.sum (Finset.Ioc 0 (s + L)) (fun m =>
            ((g m : Real) : Complex) * lpfBilinearFrequencyWindowPhase N s L k d m)) := by
  rw [<- lpf_divisor_frequency_window_reindex s L k]
  apply Finset.sum_congr rfl
  intro t ht
  rw [ArithmeticFunction.mul_apply]
  push_cast
  rw [Finset.sum_mul]

theorem lpf_typeI_product_window (s L d : Nat) (hd : 0 < d) :
    (Finset.Ioc 0 (s + L)).filter (fun m => And (s < d * m) (d * m <= s + L)) =
      Finset.Ioc (s / d) ((s + L) / d) := by
  ext m
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  constructor
  . intro h
    refine And.intro ?_ ?_
    . exact (Nat.div_lt_iff_lt_mul hd).mpr (by simpa only [Nat.mul_comm] using h.2.1)
    . exact (Nat.le_div_iff_mul_le hd).mpr (by simpa only [Nat.mul_comm] using h.2.2)
  . intro h
    have hLoNonneg : 0 <= s / d := Nat.zero_le _
    refine And.intro (And.intro (by omega) (h.2.trans (Nat.div_le_self _ _))) (And.intro ?_ ?_)
    . simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hd).mp h.1
    . simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp h.2

theorem lpf_typeI_weighted_window_sum {N : Nat} [NeZero N]
    (s L d : Nat) (hd : 0 < d) (k : Int) (g : Nat -> Complex) :
    Finset.sum (Finset.Ioc 0 (s + L)) (fun m => g m * lpfBilinearFrequencyWindowPhase N s L k d m) =
      Finset.sum (Finset.Ioc (s / d) ((s + L) / d)) (fun m => g m *
        ZMod.stdAddChar (N := N) ((k : ZMod N) * (m : ZMod N) * (d : ZMod N))) := by
  classical
  simp_rw [lpfBilinearFrequencyWindowPhase, mul_ite, mul_zero]
  rw [<- Finset.sum_filter, lpf_typeI_product_window s L d hd]
  apply Finset.sum_congr rfl
  intro m hm
  rw [mul_right_comm (k : ZMod N) (d : ZMod N) (m : ZMod N)]

theorem lpf_dirichlet_typeI_window_reindex {N : Nat} [NeZero N]
    (s L : Nat) (k : Int) (f g : ArithmeticFunction Real) :
    Finset.sum (Finset.Ioc s (s + L)) (fun t =>
      (((f * g) t : Real) : Complex) * ZMod.stdAddChar (N := N) ((k : ZMod N) * (t : ZMod N))) =
        Finset.sum (Finset.Ioc 0 (s + L)) (fun d => ((f d : Real) : Complex) *
          Finset.sum (Finset.Ioc (s / d) ((s + L) / d)) (fun m => ((g m : Real) : Complex) *
            ZMod.stdAddChar (N := N) ((k : ZMod N) * (m : ZMod N) * (d : ZMod N)))) := by
  rw [lpf_dirichlet_frequency_window_reindex]
  apply Finset.sum_congr rfl
  intro d hd
  rw [lpf_typeI_weighted_window_sum s L d (Finset.mem_Ioc.mp hd).1]

theorem lpf_frequency_window_typeII_cutoffs {N : Nat} [NeZero N]
    (U V H s L : Nat) (k : Int) :
    Finset.sum (Finset.Ioc 0 H) (fun m =>
      ((ArithmeticFunction.vonMangoldt m - lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U m : Real) : Complex) *
        Finset.sum (Finset.Ioc 0 H) (fun n => ((lpfVaughanB V n : Real) : Complex) *
          lpfBilinearFrequencyWindowPhase N s L k m n)) =
      Finset.sum (Finset.Ioc U H) (fun m =>
        ((ArithmeticFunction.vonMangoldt m - lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U m : Real) : Complex) *
          Finset.sum (Finset.Ioc V H) (fun n => ((lpfVaughanB V n : Real) : Complex) *
            lpfBilinearFrequencyWindowPhase N s L k m n)) := by
  classical
  have hSubset (D : Nat) : Finset.Ioc D H <= Finset.Ioc 0 H := by
    intro m hm
    have h := Finset.mem_Ioc.mp hm
    exact Finset.mem_Ioc.mpr (by omega)
  calc
    _ = Finset.sum (Finset.Ioc U H) (fun m =>
        ((ArithmeticFunction.vonMangoldt m - lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U m : Real) : Complex) *
          Finset.sum (Finset.Ioc 0 H) (fun n => ((lpfVaughanB V n : Real) : Complex) *
            lpfBilinearFrequencyWindowPhase N s L k m n)) := by
      symm
      apply Finset.sum_subset (hSubset U)
      intro m hm hNot
      have hRange := Finset.mem_Ioc.mp hm
      have hLe : m <= U := by
        by_contra hBad
        exact hNot (Finset.mem_Ioc.mpr (And.intro (by omega) hRange.2))
      rw [lpfVaughanHighLambda_eq_zero_of_le U m hLe]
      simp only [Complex.ofReal_zero, zero_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m hm
      congr 1
      symm
      apply Finset.sum_subset (hSubset V)
      intro n hn hNot
      have hRange := Finset.mem_Ioc.mp hn
      have hLe : n <= V := by
        by_contra hBad
        exact hNot (Finset.mem_Ioc.mpr (And.intro (by omega) hRange.2))
      rw [lpfVaughanB_eq_zero_of_le V n hLe]
      simp only [Complex.ofReal_zero, zero_mul]

theorem lpf_moebius_log_frequency_window_reindex {N : Nat} [NeZero N]
    (V s L : Nat) (k : Int) (hV : V <= s + L) :
    Finset.sum (Finset.Ioc s (s + L)) (fun t =>
      (((lpfArithmeticCutoff (ArithmeticFunction.moebius : ArithmeticFunction Real) V * ArithmeticFunction.log) t : Real) : Complex) *
        ZMod.stdAddChar (N := N) ((k : ZMod N) * (t : ZMod N))) =
      Finset.sum (Finset.Ioc 0 V) (fun d =>
        ((lpfArithmeticCutoff (ArithmeticFunction.moebius : ArithmeticFunction Real) V d : Real) : Complex) *
          Finset.sum (Finset.Ioc (s / d) ((s + L) / d)) (fun m =>
            (Real.log (m : Real) : Complex) * ZMod.stdAddChar (N := N)
              ((k : ZMod N) * (m : ZMod N) * (d : ZMod N)))) := by
  classical
  rw [lpf_dirichlet_typeI_window_reindex]
  simp only [ArithmeticFunction.log_apply]
  symm
  apply Finset.sum_subset
  . intro d hd
    have h := Finset.mem_Ioc.mp hd
    exact Finset.mem_Ioc.mpr (And.intro h.1 (h.2.trans hV))
  . intro d hd hNot
    have hRange := Finset.mem_Ioc.mp hd
    have hLarge : V < d := by
      by_contra hBad
      exact hNot (Finset.mem_Ioc.mpr (And.intro hRange.1 (by omega)))
    rw [lpfArithmeticCutoff_apply, ite_eq_right (not_le.mpr hLarge)]
    simp only [Complex.ofReal_zero, zero_mul]

theorem lpf_vaughanA_frequency_window_reindex {N : Nat} [NeZero N]
    (U V s L : Nat) (k : Int) (hUV : U * V <= s + L) :
    Finset.sum (Finset.Ioc s (s + L)) (fun t =>
      (((lpfVaughanA U V * (ArithmeticFunction.zeta : ArithmeticFunction Real)) t : Real) : Complex) *
        ZMod.stdAddChar (N := N) ((k : ZMod N) * (t : ZMod N))) =
      Finset.sum (Finset.Ioc 0 (U * V)) (fun d => ((lpfVaughanA U V d : Real) : Complex) *
        Finset.sum (Finset.Ioc (s / d) ((s + L) / d)) (fun m =>
          ZMod.stdAddChar (N := N) ((k : ZMod N) * (m : ZMod N) * (d : ZMod N)))) := by
  classical
  rw [lpf_dirichlet_typeI_window_reindex]
  have hInner (d : Nat) :
      Finset.sum (Finset.Ioc (s / d) ((s + L) / d)) (fun m =>
        (((ArithmeticFunction.zeta : ArithmeticFunction Real) m : Real) : Complex) *
          ZMod.stdAddChar (N := N) ((k : ZMod N) * (m : ZMod N) * (d : ZMod N))) =
      Finset.sum (Finset.Ioc (s / d) ((s + L) / d)) (fun m =>
        ZMod.stdAddChar (N := N) ((k : ZMod N) * (m : ZMod N) * (d : ZMod N))) := by
    apply Finset.sum_congr rfl
    intro m hm
    have hRange := Finset.mem_Ioc.mp hm
    have hLo : 0 <= s / d := Nat.zero_le _
    have hmPos : 0 < m := by omega
    rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne (Nat.ne_of_gt hmPos),
      Nat.cast_one, Complex.ofReal_one, one_mul]
  simp_rw [hInner]
  symm
  apply Finset.sum_subset
  . intro d hd
    have h := Finset.mem_Ioc.mp hd
    exact Finset.mem_Ioc.mpr (And.intro h.1 (h.2.trans hUV))
  . intro d hd hNot
    have hRange := Finset.mem_Ioc.mp hd
    have hLarge : U * V < d := by
      by_contra hBad
      exact hNot (Finset.mem_Ioc.mpr (And.intro hRange.1 (by omega)))
    rw [lpfVaughanA_eq_zero_of_lt U V d hLarge]
    simp only [Complex.ofReal_zero, zero_mul]

noncomputable def lpfArithmeticFrequencyWindow (N : Nat) [NeZero N]
    (f : ArithmeticFunction Real) (s L : Nat) (k : Int) : Complex :=
  Finset.sum (Finset.Ioc s (s + L)) (fun t => ((f t : Real) : Complex) *
    ZMod.stdAddChar (N := N) ((k : ZMod N) * (t : ZMod N)))

theorem lpf_vaughan_frequency_window_exact {N : Nat} [NeZero N]
    (U V s L : Nat) (k : Int) (hV : V <= s + L) (hUV : U * V <= s + L) :
    lpfArithmeticFrequencyWindow N ArithmeticFunction.vonMangoldt s L k =
      lpfArithmeticFrequencyWindow N (lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U) s L k +
      Finset.sum (Finset.Ioc 0 V) (fun d =>
        ((lpfArithmeticCutoff (ArithmeticFunction.moebius : ArithmeticFunction Real) V d : Real) : Complex) *
          Finset.sum (Finset.Ioc (s / d) ((s + L) / d)) (fun m =>
            (Real.log (m : Real) : Complex) * ZMod.stdAddChar (N := N)
              ((k : ZMod N) * (m : ZMod N) * (d : ZMod N)))) -
      Finset.sum (Finset.Ioc 0 (U * V)) (fun d => ((lpfVaughanA U V d : Real) : Complex) *
        Finset.sum (Finset.Ioc (s / d) ((s + L) / d)) (fun m =>
          ZMod.stdAddChar (N := N) ((k : ZMod N) * (m : ZMod N) * (d : ZMod N)))) +
      Finset.sum (Finset.Ioc U (s + L)) (fun m =>
        ((ArithmeticFunction.vonMangoldt m - lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U m : Real) : Complex) *
          Finset.sum (Finset.Ioc V (s + L)) (fun n => ((lpfVaughanB V n : Real) : Complex) *
            lpfBilinearFrequencyWindowPhase N s L k m n)) := by
  have hId : ArithmeticFunction.vonMangoldt =
      lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U +
      lpfArithmeticCutoff (ArithmeticFunction.moebius : ArithmeticFunction Real) V * ArithmeticFunction.log -
      lpfVaughanA U V * (ArithmeticFunction.zeta : ArithmeticFunction Real) +
      (ArithmeticFunction.vonMangoldt - lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U) * lpfVaughanB V := by
    convert lpfVaughanIdentity U V using 1
    dsimp only [lpfVaughanA, lpfVaughanB]
    ring
  have hPoint (t : Nat) : ArithmeticFunction.vonMangoldt t =
      lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U t +
      (lpfArithmeticCutoff (ArithmeticFunction.moebius : ArithmeticFunction Real) V * ArithmeticFunction.log) t -
      (lpfVaughanA U V * (ArithmeticFunction.zeta : ArithmeticFunction Real)) t +
      ((ArithmeticFunction.vonMangoldt - lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U) * lpfVaughanB V) t := by
    exact congrArg (fun f : ArithmeticFunction Real => f t) hId
  have hWindow : lpfArithmeticFrequencyWindow N ArithmeticFunction.vonMangoldt s L k =
      lpfArithmeticFrequencyWindow N (lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U) s L k +
      lpfArithmeticFrequencyWindow N (lpfArithmeticCutoff (ArithmeticFunction.moebius : ArithmeticFunction Real) V * ArithmeticFunction.log) s L k -
      lpfArithmeticFrequencyWindow N (lpfVaughanA U V * (ArithmeticFunction.zeta : ArithmeticFunction Real)) s L k +
      lpfArithmeticFrequencyWindow N ((ArithmeticFunction.vonMangoldt - lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U) * lpfVaughanB V) s L k := by
    unfold lpfArithmeticFrequencyWindow
    calc
      _ = Finset.sum (Finset.Ioc s (s + L)) (fun t =>
          ((lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U t : Real) : Complex) *
            ZMod.stdAddChar (N := N) ((k : ZMod N) * (t : ZMod N)) +
          (((lpfArithmeticCutoff (ArithmeticFunction.moebius : ArithmeticFunction Real) V * ArithmeticFunction.log) t : Real) : Complex) *
            ZMod.stdAddChar (N := N) ((k : ZMod N) * (t : ZMod N)) -
          (((lpfVaughanA U V * (ArithmeticFunction.zeta : ArithmeticFunction Real)) t : Real) : Complex) *
            ZMod.stdAddChar (N := N) ((k : ZMod N) * (t : ZMod N)) +
          ((((ArithmeticFunction.vonMangoldt - lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U) * lpfVaughanB V) t : Real) : Complex) *
            ZMod.stdAddChar (N := N) ((k : ZMod N) * (t : ZMod N))) := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [hPoint t]
        push_cast
        ring
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  unfold lpfArithmeticFrequencyWindow at hWindow
  rw [lpf_moebius_log_frequency_window_reindex V s L k hV,
    lpf_vaughanA_frequency_window_reindex U V s L k hUV,
    lpf_dirichlet_frequency_window_reindex] at hWindow
  have hHigh (m : Nat) :
      (ArithmeticFunction.vonMangoldt - lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U) m =
        ArithmeticFunction.vonMangoldt m - lpfArithmeticCutoff ArithmeticFunction.vonMangoldt U m := rfl
  simp only [hHigh] at hWindow
  rw [lpf_frequency_window_typeII_cutoffs] at hWindow
  exact hWindow


theorem lpf_typeII_frequency_window_extend {N : Nat} [NeZero N]
    (U V s L H : Nat) (k : Int) (f g : Nat -> Complex) (hH : s + L <= H) :
    Finset.sum (Finset.Ioc U (s + L)) (fun m => f m *
      Finset.sum (Finset.Ioc V (s + L)) (fun n =>
        g n * lpfBilinearFrequencyWindowPhase N s L k m n)) =
      Finset.sum (Finset.Ioc U H) (fun m => f m *
        Finset.sum (Finset.Ioc V H) (fun n =>
          g n * lpfBilinearFrequencyWindowPhase N s L k m n)) := by
  classical
  have hInner (m : Nat) (hm : U < m) :
      Finset.sum (Finset.Ioc V (s + L)) (fun n =>
        g n * lpfBilinearFrequencyWindowPhase N s L k m n) =
      Finset.sum (Finset.Ioc V H) (fun n =>
        g n * lpfBilinearFrequencyWindowPhase N s L k m n) := by
    apply Finset.sum_subset
    . intro n hn
      have h := Finset.mem_Ioc.mp hn
      exact Finset.mem_Ioc.mpr (And.intro h.1 (h.2.trans hH))
    . intro n hn hNot
      have hRange := Finset.mem_Ioc.mp hn
      have hLarge : s + L < n := by
        by_contra hBad
        exact hNot (Finset.mem_Ioc.mpr (And.intro hRange.1 (by omega)))
      have hmPos : 1 <= m := by omega
      have hnProd : n <= m * n := by
        simpa only [Nat.one_mul] using Nat.mul_le_mul_right n hmPos
      have hMask : Not (And (s < m * n) (m * n <= s + L)) := by omega
      simp only [lpfBilinearFrequencyWindowPhase, if_neg hMask, mul_zero]
  calc
    _ = Finset.sum (Finset.Ioc U (s + L)) (fun m => f m *
        Finset.sum (Finset.Ioc V H) (fun n =>
          g n * lpfBilinearFrequencyWindowPhase N s L k m n)) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [hInner m (Finset.mem_Ioc.mp hm).1]
    _ = _ := by
      apply Finset.sum_subset
      . intro m hm
        have h := Finset.mem_Ioc.mp hm
        exact Finset.mem_Ioc.mpr (And.intro h.1 (h.2.trans hH))
      . intro m hm hNot
        have hRange := Finset.mem_Ioc.mp hm
        have hLarge : s + L < m := by
          by_contra hBad
          exact hNot (Finset.mem_Ioc.mpr (And.intro hRange.1 (by omega)))
        have hZero : Finset.sum (Finset.Ioc V H) (fun n =>
            g n * lpfBilinearFrequencyWindowPhase N s L k m n) = 0 := by
          apply Finset.sum_eq_zero
          intro n hn
          have hnRange := Finset.mem_Ioc.mp hn
          have hnPos : 1 <= n := by omega
          have hmProd : m <= m * n := by
            simpa only [Nat.mul_one] using Nat.mul_le_mul_left m hnPos
          have hMask : Not (And (s < m * n) (m * n <= s + L)) := by omega
          simp only [lpfBilinearFrequencyWindowPhase, if_neg hMask, mul_zero]
        rw [hZero, mul_zero]

/-- A cutoff below the physical window contributes exactly zero. -/
theorem lpf_cutoff_frequency_window_eq_zero {N : Nat} [NeZero N]
    (f : ArithmeticFunction Real) (U s L : Nat) (k : Int) (hU : U <= s) :
    lpfArithmeticFrequencyWindow N (lpfArithmeticCutoff f U) s L k = 0 := by
  classical
  unfold lpfArithmeticFrequencyWindow
  apply Finset.sum_eq_zero
  intro t ht
  have hRange := Finset.mem_Ioc.mp ht
  have hLarge : U < t := hU.trans_lt hRange.1
  rw [lpfArithmeticCutoff_apply, if_neg (not_le.mpr hLarge)]
  simp only [Complex.ofReal_zero, zero_mul]
end PrimeFactorOscillations.LPF

