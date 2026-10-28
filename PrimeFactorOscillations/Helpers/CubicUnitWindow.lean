/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.CubicPairReflection

/-!
# The cubic unit lattice row with complete compensation

Retains its zero mode and proves an explicit decaying nonzero remainder for
anti-Fourier Schwartz windows. The four-scale identity keeps both mixed terms.
This lattice row is distinct from the arithmetic Abel-endpoint unit.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.CubicUnitWindow
open OAI OAI.SevenEighths
open ActualEisensteinCubic ConcreteTraceCRT EisensteinEmbedding
open EisensteinSchwartzPoisson CubicPairReflection
local notation "Eis" => ActualEisensteinCubic.O

theorem unit_kernel_eq (W : SchwartzMap Real Complex) (M : Real) :
    pairedKernel 1 1 W M =
      tsum (fun z : Eis => W (norm (eisEmbedding z) ^ 2 / M)) := by
  unfold pairedKernel
  simp only [CubicSieve.cubicRow_one, star_one, one_mul]

theorem unit_kernel_poisson (W : SchwartzMap Real Complex) (M : Real) (hM : 0 < M) :
    pairedKernel 1 1 W M = (M : Complex) *
      tsum (fun z : Eis => paperRadialFourier W (M * norm (eisEmbedding z) ^ 2)) := by
  letI : Finite (HasQuotient.Quotient Eis (Ideal.span {(1 : Eis)})) :=
    finite_quotient_span (one_ne_zero : Not ((1 : Eis) = 0))
  letI : Fintype (HasQuotient.Quotient Eis (Ideal.span {(1 : Eis)})) := Fintype.ofFinite _
  haveI : Subsingleton (HasQuotient.Quotient Eis (Ideal.span {(1 : Eis)})) := by
    rw [Ideal.span_singleton_one]
    infer_instance
  have hs (x : HasQuotient.Quotient Eis (Ideal.span {(1 : Eis)})) : x = 0 :=
    Subsingleton.elim x 0
  letI : Unique (HasQuotient.Quotient Eis (Ideal.span {(1 : Eis)})) :=
    { default := 0, uniq := hs }
  have hc : Fintype.card (HasQuotient.Quotient Eis (Ideal.span {(1 : Eis)})) = 1 :=
    Fintype.card_unique
  have hp := actual_radial_paper_poisson_trace W M hM (1 : Eis) one_ne_zero
    (fun _ => (1 : Complex))
  rw [unit_kernel_eq]
  simpa [hs] using hp

theorem unit_kernel_anti_reflection (W : SchwartzMap Real Complex)
    (hanti : forall t : Real, 0 <= t -> paperRadialFourier W t = -W t)
    (M : Real) (hM : 0 < M) :
    pairedKernel 1 1 W M = -(M : Complex) * pairedKernel 1 1 W (1 / M) := by
  rw [unit_kernel_poisson W M hM, unit_kernel_eq]
  have he : (tsum fun z : Eis => paperRadialFourier W (M * norm (eisEmbedding z) ^ 2)) =
      -(tsum fun z : Eis => W (norm (eisEmbedding z) ^ 2 / (1 / M))) := by
    rw [<- tsum_neg]
    apply tsum_congr
    intro z
    rw [hanti _ (by positivity)]
    congr 2
    field_simp
  rw [he]
  ring

def windowSize3 (W : SchwartzMap Real Complex) : Real :=
  abs (SchwartzMap.seminorm Real 0 0 W) +
    3 * abs (SchwartzMap.seminorm Real 1 0 W) +
    3 * abs (SchwartzMap.seminorm Real 2 0 W) +
    abs (SchwartzMap.seminorm Real 3 0 W)

theorem windowSize3_nonneg (W : SchwartzMap Real Complex) : 0 <= windowSize3 W := by
  unfold windowSize3
  positivity

theorem window_weight3 (W : SchwartzMap Real Complex) (u : Real) (hu : 0 <= u) :
    (1 + u) ^ 3 * norm (W u) <= windowSize3 W := by
  have h0 := (SchwartzMap.norm_le_seminorm Real W u).trans
    (le_abs_self (SchwartzMap.seminorm Real 0 0 W))
  have h1 := (SchwartzMap.norm_pow_mul_le_seminorm Real W 1 u).trans
    (le_abs_self (SchwartzMap.seminorm Real 1 0 W))
  have h2 := (SchwartzMap.norm_pow_mul_le_seminorm Real W 2 u).trans
    (le_abs_self (SchwartzMap.seminorm Real 2 0 W))
  have h3 := (SchwartzMap.norm_pow_mul_le_seminorm Real W 3 u).trans
    (le_abs_self (SchwartzMap.seminorm Real 3 0 W))
  simp only [Real.norm_eq_abs, abs_of_nonneg hu, pow_one] at h1 h2 h3
  unfold windowSize3
  nlinarith only [h0, h1, h2, h3]

theorem nonzero_tail_bound (W : SchwartzMap Real Complex) (M : Real) (hM : 1 <= M) :
    norm (tsum fun z : {z : Eis // Not (z = 0)} =>
      W (M * norm (eisEmbedding z.val) ^ 2)) <=
        nonzeroLatticeEnvelopeConstant * windowSize3 W / M ^ 2 := by
  have hMp : 0 < M := by linarith
  have hC : 0 <= windowSize3 W / M :=
    div_nonneg (windowSize3_nonneg W) hMp.le
  have hb (z : {z : Eis // Not (z = 0)}) :
      (1 + M * norm (eisEmbedding z.val) ^ 2) ^ 2 *
        norm (W (M * norm (eisEmbedding z.val) ^ 2)) <= windowSize3 W / M := by
    let u : Real := M * norm (eisEmbedding z.val) ^ 2
    have hQ : 1 <= norm (eisEmbedding z.val) ^ 2 := by
      rw [eisEmbedding_norm_sq_eq_absNorm_span]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr z.property))
    have hu : 0 <= u := by dsimp [u]; positivity
    have hMu : M <= u := by dsimp [u]; nlinarith
    have hw := window_weight3 W u hu
    have hm := mul_nonneg (sub_nonneg.mpr (show M <= 1 + u by linarith))
      (mul_nonneg (sq_nonneg (1 + u)) (norm_nonneg (W u)))
    have hmul : ((1 + u) ^ 2 * norm (W u)) * M <= windowSize3 W := by
      nlinarith only [hw, hm]
    change (1 + u) ^ 2 * norm (W u) <= _
    calc
      _ = (((1 + u) ^ 2 * norm (W u)) * M) / M := by field_simp
      _ <= windowSize3 W / M := div_le_div_of_nonneg_right hmul hMp.le
  have hs := nonzero_lattice_envelope_sum M (windowSize3 W / M) hMp hC
    (fun z : {z : Eis // Not (z = 0)} => norm (W (M * norm (eisEmbedding z.val) ^ 2)))
    (fun _ => norm_nonneg _) hb
  have hn := norm_tsum_le_tsum_norm hs.1
  have hmul := (mul_le_mul_of_nonneg_left hn hMp.le).trans hs.2
  calc
    _ = (M * norm (tsum fun z : {z : Eis // Not (z = 0)} =>
        W (M * norm (eisEmbedding z.val) ^ 2))) / M := by field_simp
    _ <= (nonzeroLatticeEnvelopeConstant * (windowSize3 W / M)) / M :=
      div_le_div_of_nonneg_right hmul hMp.le
    _ = _ := by ring

def unitRemainder (W : SchwartzMap Real Complex) (M : Real) : Complex :=
  pairedKernel 1 1 W M + (M : Complex) * W 0

theorem unit_zero_mode (W : SchwartzMap Real Complex)
    (hanti : forall t : Real, 0 <= t -> paperRadialFourier W t = -W t)
    (M : Real) (hM : 0 < M) :
    unitRemainder W M = -(M : Complex) *
      tsum (fun z : {z : Eis // Not (z = 0)} =>
        W (M * norm (eisEmbedding z.val) ^ 2)) := by
  classical
  let f : Eis -> Complex := fun z => W (M * norm (eisEmbedding z) ^ 2)
  have hs : Summable f := (CubicPairRadius.dominated_lattice_sum f M (CubicPairRadius.windowSize0 W)
    hM (CubicPairRadius.windowSize0_nonneg W) (fun z =>
      CubicPairRadius.window_bound0 W _ (by positivity))).1
  let e : Equiv {z : Eis // Not (Membership.mem ({0} : Finset Eis) z)}
      {z : Eis // Not (z = 0)} :=
    Equiv.subtypeEquivRight (fun _ => Finset.notMem_singleton)
  have hindex :
      (tsum fun z : {z : Eis // Not (Membership.mem ({0} : Finset Eis) z)} => f z.val) =
      (tsum fun z : {z : Eis // Not (z = 0)} => f z.val) :=
    Equiv.tsum_eq e (fun z => f z.val)
  have he : W 0 + (tsum fun z : {z : Eis // Not (z = 0)} => f z.val) = tsum f := by
    have hh := hs.sum_add_tsum_subtype_compl ({0} : Finset Eis)
    rw [hindex] at hh
    simpa [f] using hh
  have hscale :
      (tsum fun z : Eis => W (norm (eisEmbedding z) ^ 2 / (1 / M))) = tsum f := by
    apply tsum_congr
    intro z
    change W (norm (eisEmbedding z) ^ 2 / (1 / M)) =
      W (M * norm (eisEmbedding z) ^ 2)
    congr 1
    field_simp
  have hp := unit_kernel_anti_reflection W hanti M hM
  simp only [unit_kernel_eq] at hp
  rw [hscale, <- he] at hp
  unfold unitRemainder
  rw [unit_kernel_eq]
  dsimp [f] at hp
  linear_combination hp

theorem unit_remainder_bound (W : SchwartzMap Real Complex)
    (hanti : forall t : Real, 0 <= t -> paperRadialFourier W t = -W t)
    (M : Real) (hM : 1 <= M) :
    norm (unitRemainder W M) <=
      nonzeroLatticeEnvelopeConstant * windowSize3 W / M := by
  have hMp : 0 < M := by linarith
  rw [unit_zero_mode W hanti M hMp, norm_mul, norm_neg,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hMp]
  calc
    _ <= M * (nonzeroLatticeEnvelopeConstant * windowSize3 W / M ^ 2) :=
      mul_le_mul_of_nonneg_left (nonzero_tail_bound W M hM) hMp.le
    _ = _ := by field_simp

theorem unit_kernel_bound_of_zero (W : SchwartzMap Real Complex)
    (hanti : forall t : Real, 0 <= t -> paperRadialFourier W t = -W t)
    (hzero : W 0 = 0) (M : Real) (hM : 1 <= M) :
    norm (pairedKernel 1 1 W M) <=
      nonzeroLatticeEnvelopeConstant * windowSize3 W / M := by
  simpa only [unitRemainder, hzero, mul_zero, add_zero] using
    unit_remainder_bound W hanti M hM

theorem compensated_unit_zero_mode (W : SchwartzMap Real Complex)
    (c : Complex) (Maa Mab Mba Mbb : Real) :
    pairedKernel 1 1 W Maa - star c * pairedKernel 1 1 W Mab -
      c * pairedKernel 1 1 W Mba + c * star c * pairedKernel 1 1 W Mbb =
    -((Maa : Complex) - star c * (Mab : Complex) -
      c * (Mba : Complex) + c * star c * (Mbb : Complex)) * W 0 +
      unitRemainder W Maa - star c * unitRemainder W Mab -
        c * unitRemainder W Mba + c * star c * unitRemainder W Mbb := by
  unfold unitRemainder
  ring

end PrimeFactorOscillations.CubicUnitWindow
