/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelCorrelationSpectrum

/-!
# Phase-preserving cross-correlation of finite probability profiles

The normalized cross-correlation of two nonnegative real profiles is
nonnegative, has mean one, and has principal character coefficient one.
Its exact Fourier coefficients retain the complex relative phase between
the two profiles. The final theorem specializes Fourier inversion to the
actual full Dirichlet character group. No prime-sampling estimate or
zero-free exponent improvement is asserted here.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.CarmichaelCrossCorrelation
open CarmichaelCorrelation CarmichaelCorrelationSpectrum

section General
variable {G : Type*} [CommGroup G] [Fintype G]

def rawCross (w v : G -> Real) (g : G) : Real :=
  Finset.univ.sum (fun h : G => w h * v (h * g))

def crossKernel (w v : G -> Real) (g : G) : Real :=
  (Fintype.card G : Real) * rawCross w v g / (weightSum w * weightSum v)

def crossCoefficient (w v : G -> Real) (chi : MonoidHom G Complex) : Complex :=
  (starRingEnd Complex) (characterSum w chi) * characterSum v chi /
    ((weightSum w : Complex) * (weightSum v : Complex))

theorem rawCross_character_sum (w v : G -> Real) (chi : MonoidHom G Complex) :
    characterSum (rawCross w v) chi =
      (starRingEnd Complex) (characterSum w chi) * characterSum v chi := by
  classical
  let F := characterSum v chi
  have hInner (h : G) :
      Finset.univ.sum (fun g : G => (v (h * g) : Complex) * chi g) =
        (starRingEnd Complex) (chi h) * F := by
    calc
      _ = Finset.univ.sum (fun g : G =>
          (starRingEnd Complex) (chi h) * ((v (h * g) : Complex) * chi (h * g))) := by
        apply Finset.sum_congr rfl
        intro g _
        rw [map_mul]
        have hu : (starRingEnd Complex) (chi h) * chi h = 1 := by
          rw [mul_comm, character_mul_conj_one]
        calc
          _ = ((starRingEnd Complex) (chi h) * chi h) *
              ((v (h * g) : Complex) * chi g) := by rw [hu, one_mul]
          _ = _ := by ring
      _ = (starRingEnd Complex) (chi h) * F := by
        rw [<- Finset.mul_sum]
        congr 1
        exact Equiv.sum_comp (Equiv.mulLeft h) (fun g : G => (v g : Complex) * chi g)
  have hConj : Finset.univ.sum (fun h : G =>
      (w h : Complex) * (starRingEnd Complex) (chi h)) =
        (starRingEnd Complex) (characterSum w chi) := by
    simp only [characterSum, map_sum, map_mul, Complex.conj_ofReal]
  calc
    _ = Finset.univ.sum (fun h : G => (w h : Complex) *
        Finset.univ.sum (fun g : G => (v (h * g) : Complex) * chi g)) := by
      unfold characterSum rawCross
      simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      ring
    _ = Finset.univ.sum (fun h : G =>
        ((w h : Complex) * (starRingEnd Complex) (chi h)) * F) := by
      simp_rw [hInner]
      apply Finset.sum_congr rfl
      intro h _
      ring
    _ = _ := by rw [<- Finset.sum_mul, hConj]

theorem rawCross_sum (w v : G -> Real) :
    Finset.univ.sum (rawCross w v) = weightSum w * weightSum v := by
  have hh := rawCross_character_sum w v (1 : MonoidHom G Complex)
  simp only [characterSum, MonoidHom.one_apply, mul_one, <- Complex.ofReal_sum,
    Complex.conj_ofReal] at hh
  exact_mod_cast hh

theorem crossKernel_character_sum (w v : G -> Real) (chi : MonoidHom G Complex) :
    characterSum (crossKernel w v) chi =
      ((Fintype.card G : Real) : Complex) * crossCoefficient w v chi := by
  have hPoint (g : G) : (crossKernel w v g : Complex) * chi g =
      ((Fintype.card G : Real) : Complex) /
        ((weightSum w : Complex) * (weightSum v : Complex)) *
          ((rawCross w v g : Complex) * chi g) := by
    unfold crossKernel
    push_cast
    ring
  unfold characterSum
  simp_rw [hPoint]
  rw [<- Finset.mul_sum]
  rw [show Finset.univ.sum (fun g : G => (rawCross w v g : Complex) * chi g) =
    (starRingEnd Complex) (characterSum w chi) * characterSum v chi from
      rawCross_character_sum w v chi]
  unfold crossCoefficient
  ring

theorem crossKernel_nonneg (w v : G -> Real)
    (hw : forall g : G, 0 <= w g) (hv : forall g : G, 0 <= v g) (g : G) :
    0 <= crossKernel w v g := by
  unfold crossKernel rawCross
  apply div_nonneg
  . exact mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg
      (fun h _ => mul_nonneg (hw h) (hv (h * g))))
  . exact mul_nonneg (Finset.sum_nonneg (fun h _ => hw h))
      (Finset.sum_nonneg (fun h _ => hv h))

theorem crossKernel_mean (w v : G -> Real)
    (hw : 0 < weightSum w) (hv : 0 < weightSum v) :
    weightMean (crossKernel w v) = 1 := by
  have hn : Not ((Fintype.card G : Real) = 0) := by
    exact_mod_cast Fintype.card_ne_zero
  unfold weightMean weightSum crossKernel
  rw [<- Finset.sum_div, <- Finset.mul_sum, rawCross_sum]
  field_simp [ne_of_gt hw, ne_of_gt hv, hn]

theorem crossCoefficient_principal (w v : G -> Real)
    (hw : 0 < weightSum w) (hv : 0 < weightSum v) :
    crossCoefficient w v (1 : MonoidHom G Complex) = 1 := by
  unfold crossCoefficient
  simp only [characterSum, MonoidHom.one_apply, mul_one, <- Complex.ofReal_sum,
    Complex.conj_ofReal]
  have hn : Not ((weightSum w : Complex) * (weightSum v : Complex) = 0) := by
    apply mul_ne_zero <;> exact_mod_cast ne_of_gt (by assumption)
  exact div_self hn

end General

variable {q : Nat} [NeZero q]

theorem crossKernel_expansion (w v : Units (ZMod q) -> Real)
    (u : Units (ZMod q)) :
    (crossKernel w v u : Complex) =
      Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
        crossCoefficient w v (unitCharacter chi) * unitCharacter chi (Inv.inv u)) := by
  classical
  let n : Complex := ((Fintype.card (Units (ZMod q)) : Real) : Complex)
  have hn : Not (n = 0) := by
    dsimp [n]
    exact_mod_cast Fintype.card_ne_zero
  have hCoeff (chi : DirichletCharacter Complex q) :
      characterSum (crossKernel w v) (unitCharacter chi) =
        n * crossCoefficient w v (unitCharacter chi) :=
    crossKernel_character_sum w v (unitCharacter chi)
  have hInv := unit_fourier_inversion q (crossKernel w v) u
  let T : Complex := Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
    crossCoefficient w v (unitCharacter chi) * unitCharacter chi (Inv.inv u))
  have hScale : n * T = n * (crossKernel w v u : Complex) := by
    calc
      _ = Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
          characterSum (crossKernel w v) (unitCharacter chi) *
            unitCharacter chi (Inv.inv u)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro chi _
        rw [hCoeff]
        ring
      _ = _ := hInv
  apply Eq.symm
  have hDiff : n * (T - (crossKernel w v u : Complex)) = 0 := by
    rw [mul_sub, hScale, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hDiff).resolve_left hn)

end PrimeFactorOscillations.CarmichaelCrossCorrelation
