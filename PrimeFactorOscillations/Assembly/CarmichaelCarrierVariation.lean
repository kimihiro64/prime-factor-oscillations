/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelCarrierWindow
import PrimeFactorOscillations.Assembly.CarmichaelCubicResonance

/-!
# Positive-clock variation of the actual compensated carrier

The unchanged four-Gaussian carrier is sampled only at nonnegative physical
norm coordinates. Its discrete variation has a uniform coefficient budget,
without a Schwartz hypothesis on the growing negative-halfline extension.
All signed carrier coefficients and compensation windows remain in the packet.
The full signed small-square estimate and unbounded Abel passage remain open.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.CarmichaelCarrierVariation
open scoped Classical
open OAI OAI.SevenEighths EisensteinSchwartzPoisson ProbeRadialMellin
open CubicReciprocalGaussian CarmichaelCompanionCancellation

/-- Positive antitone samples have exactly their initial value as endpoint variation. -/
theorem antitone_positive_variation (g : Nat -> Real)
    (hg : forall i, 0 <= g i) (hanti : Antitone g) (N : Nat) :
    windowVariation (fun i => (g i : Complex)) N = g 0 := by
  have htel (n : Nat) :
      (Finset.range n).sum (fun i => g i - g (i + 1)) = g 0 - g n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  have hinc (i : Nat) : abs (g (i + 1) - g i) = g i - g (i + 1) := by
    rw [abs_of_nonpos (sub_nonpos.mpr (hanti (Nat.le_succ i)))]
    ring
  unfold windowVariation
  simp only [<- Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (hg (N - 1))]
  simp_rw [hinc]
  rw [htel]
  ring

/-- Finite linear compensation is kept inside the window before its variation is bounded. -/
theorem variation_finite_linear {iota : Type} (S : Finset iota)
    (c : iota -> Complex) (w : iota -> Nat -> Complex) (N : Nat) :
    windowVariation (fun n => S.sum (fun i => c i * w i n)) N <=
      S.sum (fun i => norm (c i) * windowVariation (w i) N) := by
  have hend : norm (S.sum (fun i => c i * w i (N - 1))) <=
      S.sum (fun i => norm (c i) * norm (w i (N - 1))) := by
    simpa only [norm_mul] using norm_sum_le S (fun i => c i * w i (N - 1))
  have hinc (j : Nat) :
      norm (S.sum (fun i => c i * w i (j + 1)) - S.sum (fun i => c i * w i j)) <=
      S.sum (fun i => norm (c i) * norm (w i (j + 1) - w i j)) := by
    rw [<- Finset.sum_sub_distrib]
    calc
      _ <= S.sum (fun i => norm (c i * w i (j + 1) - c i * w i j)) :=
        norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [<- mul_sub, norm_mul]
  unfold windowVariation
  calc
    _ <= S.sum (fun i => norm (c i) * norm (w i (N - 1))) +
        (Finset.range (N - 1)).sum (fun j =>
          S.sum (fun i => norm (c i) * norm (w i (j + 1) - w i j))) :=
      add_le_add hend (Finset.sum_le_sum (fun j _ => hinc j))
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]

/-- Every positive Gaussian clock has variation at most one, independently of scale. -/
theorem gaussian_positive_clock_variation (a : Real) (ha : 0 < a)
    (P : Nat -> Real) (hP : Monotone P) (hP0 : 0 <= P 0) (N : Nat) :
    windowVariation (fun i => Complex.exp (-(a : Complex) * (P i : Complex))) N <= 1 := by
  have hanti : Antitone (fun i => Real.exp (-a * P i)) := by
    intro i j hij
    apply Real.exp_le_exp.mpr
    have h := hP hij
    nlinarith only [h, ha]
  have he : (fun i => Complex.exp (-(a : Complex) * (P i : Complex))) =
      (fun i => (Real.exp (-a * P i) : Complex)) := by
    funext i
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [he, antitone_positive_variation _ (fun i => le_of_lt (Real.exp_pos _)) hanti]
  calc
    _ <= Real.exp 0 := Real.exp_le_exp.mpr (by nlinarith only [ha, hP0])
    _ = _ := Real.exp_zero

/-- The actual four-Gaussian carrier has the scale-free positive-clock budget 21/8. -/
theorem carrier_positive_clock_variation
    (P : Nat -> Real) (hP : Monotone P) (hP0 : 0 <= P 0) (N : Nat) :
    windowVariation (fun i => carrierProfile (P i)) N <= (21 / 8 : Real) := by
  calc
    _ <= Finset.univ.sum (fun i : Fin 4 => norm (coefficients i) *
        windowVariation (fun n => Complex.exp
          (-((paperConstant * scales i : Real) : Complex) * (P n : Complex))) N) :=
      variation_finite_linear Finset.univ coefficients
        (fun i n => Complex.exp
          (-((paperConstant * scales i : Real) : Complex) * (P n : Complex))) N
    _ <= Finset.univ.sum (fun i : Fin 4 => norm (coefficients i) * 1) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (gaussian_positive_clock_variation (paperConstant * scales i)
          (mul_pos paperConstant_pos (scales_pos i)) P hP hP0 N)
        (norm_nonneg _)
    _ = _ := by norm_num [coefficients, Fin.sum_univ_succ]

private theorem variation_const_mul (c : Complex) (w : Nat -> Complex) (N : Nat) :
    windowVariation (fun i => c * w i) N = norm c * windowVariation w N := by
  unfold windowVariation
  simp only [<- mul_sub, norm_mul, <- Finset.mul_sum]
  ring

private theorem variation_add (w v : Nat -> Complex) (N : Nat) :
    windowVariation (fun i => w i + v i) N <= windowVariation w N + windowVariation v N := by
  have h := variation_finite_linear Finset.univ (fun _ : Fin 2 => (1 : Complex))
    ![w, v] N
  simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_one, one_mul, norm_one, add_zero] using h

/-- Both scales and every complex compensation coefficient have an explicit joint budget. -/
theorem compensated_carrier_clock_variation (P Q : Nat -> Real)
    (hP : Monotone P) (hQ : Monotone Q) (hP0 : 0 <= P 0) (hQ0 : 0 <= Q 0)
    (z : Complex) (N : Nat) :
    windowVariation (fun i => carrierProfile (P i) - z * carrierProfile (Q i)) N <=
      (21 / 8 : Real) * (1 + norm z) := by
  have he : (fun i => carrierProfile (P i) - z * carrierProfile (Q i)) =
      (fun i => carrierProfile (P i) + (-z) * carrierProfile (Q i)) := by
    funext i
    ring
  rw [he]
  calc
    _ <= windowVariation (fun i => carrierProfile (P i)) N +
        windowVariation (fun i => (-z) * carrierProfile (Q i)) N :=
      variation_add _ _ N
    _ = windowVariation (fun i => carrierProfile (P i)) N +
        norm z * windowVariation (fun i => carrierProfile (Q i)) N := by
      rw [variation_const_mul, norm_neg]
    _ <= (21 / 8 : Real) + norm z * (21 / 8 : Real) :=
      add_le_add (carrier_positive_clock_variation P hP hP0 N)
        (mul_le_mul_of_nonneg_left (carrier_positive_clock_variation Q hQ hQ0 N)
          (norm_nonneg _))
    _ = _ := by ring


/-- The physical quartic compensation uses D^(-3) and the reference scale D^4. -/
def quarticCarrierWindow (D : Nat) (x : Real) : Complex :=
  carrierProfile x - (D : Complex) ^ (-3 : Complex) *
    carrierProfile (x / (D : Real) ^ 3)

private theorem square_clock_monotone (A D : Nat) :
    Monotone (fun i : Nat => ((A * (i + 1) ^ 2 : Nat) : Real) / (D : Real)) := by
  intro i j hij
  have hs : (i + 1) ^ 2 <= (j + 1) ^ 2 := by nlinarith
  exact div_le_div_of_nonneg_right
    (Nat.cast_le.mpr (Nat.mul_le_mul_left A hs)) (Nat.cast_nonneg D)

/-- Every square-part dilation of the unchanged carrier has the same budget. -/
theorem carrier_rescaled_variation (A D B k : Nat) (hD : 0 < D) (hk : 0 < k) :
    windowVariation
      (CarmichaelSquarepartCancellation.dilatedWindow k
        (CarmichaelSquarepartCancellation.squaredWindow carrierProfile A D)) (B / k) <=
      (21 / 8 : Real) := by
  rw [CarmichaelSquarepartCancellation.squared_window_dilate carrierProfile A D k hk]
  exact carrier_positive_clock_variation
    (fun i => (((A * k ^ 2) * (i + 1) ^ 2 : Nat) : Real) / (D : Real))
    (square_clock_monotone (A * k ^ 2) D) (by positivity) (B / k)

/-- The exact physical compensation coefficient is at most one for every positive integer scale. -/
theorem quartic_compensation_norm_le_one (D : Nat) (hD : 0 < D) :
    norm ((D : Complex) ^ (-3 : Complex)) <= 1 := by
  have hpos : (0 : Real) < (D : Real) := Nat.cast_pos.mpr hD
  have hbase : (1 : Real) <= (D : Real) := by exact_mod_cast hD
  have hn : norm ((D : Complex) ^ (-3 : Complex)) =
      (D : Real) ^ (-3 : Complex).re := by
    simpa only [Complex.ofReal_natCast] using
      (Complex.norm_cpow_eq_rpow_re_of_pos hpos (-3 : Complex))
  rw [hn]
  have h := Real.rpow_le_rpow_of_exponent_le hbase (show (-3 : Real) <= 0 by norm_num)
  convert h using 1 <;> norm_num

/-- Both physical scales stay coupled under every square-part rescaling, with budget 21/4. -/
theorem quartic_carrier_rescaled_variation (A D B k : Nat) (hD : 0 < D) (hk : 0 < k) :
    windowVariation
      (CarmichaelSquarepartCancellation.dilatedWindow k
        (CarmichaelSquarepartCancellation.squaredWindow (quarticCarrierWindow D) A D))
      (B / k) <= (21 / 4 : Real) := by
  rw [CarmichaelSquarepartCancellation.squared_window_dilate
    (quarticCarrierWindow D) A D k hk]
  let P : Nat -> Real :=
    fun i => (((A * k ^ 2) * (i + 1) ^ 2 : Nat) : Real) / (D : Real)
  have hP : Monotone P := square_clock_monotone (A * k ^ 2) D
  have hP0 : 0 <= P 0 := by dsimp only [P]; positivity
  have hQ : Monotone (fun i => P i / (D : Real) ^ 3) := by
    intro i j hij
    exact div_le_div_of_nonneg_right (hP hij) (by positivity)
  have hQ0 : 0 <= P 0 / (D : Real) ^ 3 := by positivity
  have hv := compensated_carrier_clock_variation P
    (fun i => P i / (D : Real) ^ 3) hP hQ hP0 hQ0
    ((D : Complex) ^ (-3 : Complex)) (B / k)
  change windowVariation (fun i => carrierProfile (P i) -
    (D : Complex) ^ (-3 : Complex) * carrierProfile (P i / (D : Real) ^ 3)) (B / k) <= _
  calc
    _ <= (21 / 8 : Real) * (1 + norm ((D : Complex) ^ (-3 : Complex))) := hv
    _ <= (21 / 8 : Real) * (1 + 1) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (le_refl (1 : Real)) (quartic_compensation_norm_le_one D hD))
        (by norm_num)
    _ = _ := by norm_num

/-- The complete compensated carrier rectangle satisfies the physical square-root mean. -/
theorem quartic_carrier_rectangle_subpower (eps : Real) (heps : 0 < eps) :
    exists Ceps : Real, 0 < Ceps /\
      forall {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
      (G : Finset Nat), (forall p, Membership.mem G p -> Nat.Prime p) ->
      forall (H K a c B C R T A E D : Nat),
      0 < H -> 0 < K -> 0 < a -> 0 < c -> 0 < R -> 0 < T -> 0 < D ->
      norm (CarmichaelSquarepartPhysical.squarefreeRectanglePacket
        (OAI.ShortDraftHeckeBridge.baseChangeChar (chi ^ 2))
        G H K a c B C R T
        (CarmichaelSquarepartCancellation.squaredWindow (quarticCarrierWindow D) A D)
        (CarmichaelSquarepartCancellation.squaredWindow (quarticCarrierWindow D) E D)) <=
        Ceps * (((q * 3 : Nat) : Real) ^ 2) * (21 / 4 : Real) * (21 / 4 : Real) *
          (((H + K + a + c + 1) * (B + C + 1) : Nat) : Real) ^ eps *
            Real.sqrt ((B : Real) * (C : Real)) := by
  choose Ceps hCeps hmain using
    CarmichaelSquarepartPhysical.rectangle_subpower_of_variation eps heps
  refine Exists.intro Ceps (And.intro hCeps ?_)
  intro q inst chi G hG H K a c B C R T A E D hH hK ha hc hR hT hD
  exact hmain chi G hG H K a c B C R T hH hK ha hc hR hT _ _
    (21 / 4) (21 / 4) (by norm_num) (by norm_num)
    (fun B1 _ k hk => quartic_carrier_rescaled_variation A D B1 k hD hk)
    (fun C1 _ k hk => quartic_carrier_rescaled_variation E D C1 k hD hk)


open CarmichaelSquarepartPhysical CarmichaelNativeSquarepart CarmichaelNativeLowSector
open ActualEisensteinCubic ConcreteTraceCRT EisensteinEmbedding

/-- At a positive scale, the compensated profile is exactly the two original physical windows. -/
theorem quartic_window_norm_coordinate (D : Nat) (hD : 0 < D) (x : Real) :
    quarticCarrierWindow D (x / (D : Real)) =
      carrierProfile (x / (D : Real)) -
        (D : Complex) ^ (-3 : Complex) * carrierProfile (x / (D : Real) ^ 4) := by
  have hDn : Not ((D : Real) = 0) := ne_of_gt (Nat.cast_pos.mpr hD)
  have he : (x / (D : Real)) / (D : Real) ^ 3 = x / (D : Real) ^ 4 := by
    field_simp
    <;> ring
  simp only [quarticCarrierWindow, he]

/-- Fixed finite supports transfer to the very same compensated physical packet. -/
theorem quartic_physical_packet_transfer
    (Z : Finset ActualEisensteinCubic.O) (a : ActualEisensteinCubic.O -> Complex)
    (D : Nat) (hD : 0 < D) :
    CarmichaelWindowTransfer.quarticPhysicalProbe
      (CarmichaelCarrierWindow.physicalCarrierPacket Z a) (D : Real) =
      Z.sum (fun z => a z *
        quarticCarrierWindow D (norm (eisEmbedding z) ^ 2 / (D : Real))) := by
  simp only [CarmichaelWindowTransfer.quarticPhysicalProbe,
    CarmichaelWindowTransfer.quarticPhysicalReference,
    CarmichaelCarrierWindow.physicalCarrierPacket, Complex.ofReal_natCast, Finset.mul_sum]
  rw [<- Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro z _
  rw [quartic_window_norm_coordinate D hD]
  ring

private theorem unit_good_reverse (H n m : Nat)
    (h : CarmichaelNativeHyperbola.unitGood H n m) :
    CarmichaelNativeHyperbola.unitGood H m n :=
  And.intro h.1.symm (And.intro h.2.2 h.2.1)

/-- The complete masked physical kernel is Hermitian for every complex window. -/
theorem rational_kernel_star_swap (G : Finset Nat) (H : Nat)
    (W : Nat -> Complex) (n m : Nat) :
    star (CarmichaelNativeHyperbola.rationalKernel G H W n m) =
      CarmichaelNativeHyperbola.rationalKernel G H W m n := by
  by_cases h : CarmichaelNativeHyperbola.unitGood H n m
  . have hswap := unit_good_reverse H n m h
    simp only [CarmichaelNativeHyperbola.rationalKernel, ite_eq_left h, ite_eq_left hswap,
      star_mul, star_star]
  . have hswap : Not (CarmichaelNativeHyperbola.unitGood H m n) := by
      intro hm
      exact h (unit_good_reverse H m n hm)
    simp only [CarmichaelNativeHyperbola.rationalKernel, ite_eq_right h, ite_eq_right hswap,
      star_zero]

/-- All return overlaps and compensation cross terms obey the exact row-exchange symmetry. -/
theorem physical_rectangle_star_swap {q : Nat} (chi : DirichletCharacter Complex q)
    (G : Finset Nat) (H r u b d B C D R T : Nat) (f : Real -> Complex) :
    star (physicalSquarepartRectangle chi G H r u b d B C D R T f) =
      physicalSquarepartRectangle chi G H u r d b C B D T R f := by
  simp only [physicalSquarepartRectangle, star_sum, star_mul, star_star,
    rational_kernel_star_swap]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- The actual plain-companion phases have the same symmetry, with no order or modulus exception. -/
theorem phased_physical_rectangle_star_swap {q : Nat}
    (chi : DirichletCharacter Complex q) (G : Finset Nat)
    (H r u b d B C D R T : Nat) (f : Real -> Complex) :
    star (((OAI.ShortDraftHeckeBridge.baseChangeChar chi) (b : ZMod (q * 3)) *
      star ((OAI.ShortDraftHeckeBridge.baseChangeChar chi) (d : ZMod (q * 3)))) *
      physicalSquarepartRectangle chi G H r u b d B C D R T f) =
      ((OAI.ShortDraftHeckeBridge.baseChangeChar chi) (d : ZMod (q * 3)) *
        star ((OAI.ShortDraftHeckeBridge.baseChangeChar chi) (b : ZMod (q * 3)))) *
          physicalSquarepartRectangle chi G H u r d b C B D T R f := by
  rw [star_mul, star_mul, star_star, physical_rectangle_star_swap]
  ring

/-- The actual quartic window qualifies the complete native physical row, including the unit row. -/
theorem quartic_carrier_physical_row_bound (eps : Real) (heps : 0 < eps) :
    exists Ceps : Real, 0 < Ceps /\
      forall {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
      (G : Finset Nat), (forall p, Membership.mem G p -> Nat.Prime p) ->
      forall (H r u b d B C D R T : Nat), 0 < H -> 0 < r -> 0 < u -> 0 < b -> 0 < d ->
      0 < D -> 0 < R -> 0 < T ->
      norm (physicalSquarepartRectangle chi G H r u b d B C D R T
        (quarticCarrierWindow D)) <=
        norm (nativeCoefficient chi r) * norm (nativeCoefficient chi u) *
          (Ceps * (((q * 3 : Nat) : Real) ^ 2) * (21 / 4 : Real) ^ 2 *
            (((H * r * (u * d) + H * u * (r * b) + r * b + u * d + 1) *
                (B + C + 1) : Nat) : Real) ^ eps *
              Real.sqrt ((B : Real) * (C : Real))) := by
  choose Ceps hCeps hrect using quartic_carrier_rectangle_subpower eps heps
  refine Exists.intro Ceps (And.intro hCeps ?_)
  intro q inst chi G hG H r u b d B C D R T hH hr hu hb hd hD hR hT
  rw [physical_squarepart_rectangle chi G hG H r u b d B C D R T hR hT]
  by_cases houter : CarmichaelNativeHyperbola.unitGood H (r * b) (u * d)
  . rw [ite_eq_left houter, norm_mul, norm_mul, norm_star]
    have hm : 0 < r * b := Nat.mul_pos hr hb
    have hn : 0 < u * d := Nat.mul_pos hu hd
    have hleft : 0 < H * r * (u * d) := Nat.mul_pos (Nat.mul_pos hH hr) hn
    have hright : 0 < H * u * (r * b) := Nat.mul_pos (Nat.mul_pos hH hu) hm
    have hmean := hrect chi G hG
      (H * r * (u * d)) (H * u * (r * b)) (r * b) (u * d)
      B C R T (r * b) (u * d) D hleft hright hm hn hR hT hD
    calc
      _ <= norm (nativeCoefficient chi r) * norm (nativeCoefficient chi u) *
          (Ceps * (((q * 3 : Nat) : Real) ^ 2) * (21 / 4 : Real) * (21 / 4 : Real) *
            (((H * r * (u * d) + H * u * (r * b) + r * b + u * d + 1) *
                (B + C + 1) : Nat) : Real) ^ eps *
              Real.sqrt ((B : Real) * (C : Real))) :=
        mul_le_mul_of_nonneg_left hmean (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = _ := by ring
  . rw [ite_eq_right houter, norm_zero]
    positivity

end PrimeFactorOscillations.CarmichaelCarrierVariation
