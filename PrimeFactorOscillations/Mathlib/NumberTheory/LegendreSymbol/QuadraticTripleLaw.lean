/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticTripleTwist
/-!
# Positive common-scale quadratic triple laws

The exact shared-coefficient average retains all three exceptional root rows.
For cardinality at least eleven its explicit normalizer is positive, giving
a nonnegative mean-one density and an exact compensated character background.
No Hasse bound or integer short-window estimate is used.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FiniteField.QuadraticTripleTwist
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def shapeSigma (h k : F) : Int :=
  (quadraticChar F) (h*k) + (quadraticChar F) (h*(h-k)) +
    (quadraticChar F) (k*(k-h))

def shapeDenominator (h k : F) : Int :=
  (Fintype.card F : Int) - 6 - shapeSigma h k


theorem sum_symmetricMask_zero (hF : Not (ringChar F = 2)) (h k : F)
    (hh : Not (h = 0)) (hk : Not (k = 0)) (hhk : Not (h = k)) :
    (Finset.univ.sum fun y : F => symmetricMask 0 y 0 h k) =
      2 * shapeDenominator h k := by
  have hp (y : F) :=
    symmetricMask_corrected 0 y (0 : F) h k (Ne.symm hh) (Ne.symm hk) hhk
  simp_rw [hp]
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,Finset.sum_sub_distrib,
    <- Finset.mul_sum,sum_basePolynomial_zero hF (0 : F) h k
      (Ne.symm hh) (Ne.symm hk) hhk]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have hprod : (quadraticChar F) (-h) * (quadraticChar F) (-k) =
      (quadraticChar F) (h*k) := by
    rw [<- map_mul]
    congr 1
    ring
  unfold rootCorrection shapeDenominator shapeSigma
  simp only [zero_mul,sub_zero,zero_sub]
  rw [hprod,<- map_mul,<- map_mul]
  ring

theorem four_sum_twistTotal (hF : Not (ringChar F = 2)) (h k t : F)
    (hh : Not (h = 0)) (hk : Not (k = 0)) (hhk : Not (h = k))
    (ht : Not (t = 0)) (hchi : (quadraticChar F) t = -1) :
    4 * (Finset.univ.sum fun x : F => twistTotal x (x+h) (x+k) t) =
      (Fintype.card F : Int) * shapeDenominator h k := by
  have hp := tripleCount_scaled_linear_average hF (1 : F) h k one_ne_zero
  have hm := tripleCount_scaled_linear_average hF t h k ht
  simp only [one_mul,map_one] at hp
  rw [hchi] at hm
  have hcombine :
      (Finset.univ.sum fun y : F => symmetricMask 0 y 0 h k) =
        (Finset.univ.sum fun y : F =>
          twistedMask 1 y 0 * twistedMask 1 y h * twistedMask 1 y k) +
        (Finset.univ.sum fun y : F =>
          twistedMask (-1) y 0 * twistedMask (-1) y h * twistedMask (-1) y k) := by
    unfold symmetricMask
    simp only [zero_add,neg_zero,one_mul,Finset.sum_add_distrib]
  have hs :
      8 * (Finset.univ.sum fun x : F => twistTotal x (x+h) (x+k) t) =
        (Fintype.card F : Int) *
          (Finset.univ.sum fun y : F => symmetricMask 0 y 0 h k) := by
    rw [hcombine]
    unfold twistTotal
    rw [Finset.sum_add_distrib]
    nlinarith only [hp,hm]
  rw [sum_symmetricMask_zero hF h k hh hk hhk] at hs
  nlinarith only [hs]

theorem tripleCount_nonneg (a b c : F) : 0 <= tripleCount a b c := by
  unfold tripleCount
  apply Finset.sum_nonneg
  intro z _
  split_ifs <;> norm_num

theorem twistTotal_nonneg (a b c t : F) : 0 <= twistTotal a b c t := by
  unfold twistTotal
  exact add_nonneg (tripleCount_nonneg a b c)
    (tripleCount_nonneg (t*a) (t*b) (t*c))

theorem shapeSigma_bounds (h k : F)
    (hh : Not (h = 0)) (hk : Not (k = 0)) (hhk : Not (h = k)) :
    -3 <= shapeSigma h k /\ shapeSigma h k <= 3 := by
  have hb (v : Int) (hv : v^2=1) : -1 <= v /\ v <= 1 := by
    constructor
    . nlinarith only [hv,sq_nonneg (v+1)]
    . nlinarith only [hv,sq_nonneg (v-1)]
  have h1 := hb _ (quadraticChar_sq_one (mul_ne_zero hh hk))
  have h2 := hb _ (quadraticChar_sq_one (mul_ne_zero hh (sub_ne_zero.mpr hhk)))
  have h3 := hb _ (quadraticChar_sq_one (mul_ne_zero hk (sub_ne_zero.mpr (Ne.symm hhk))))
  unfold shapeSigma
  constructor <;> linarith only [h1.1,h1.2,h2.1,h2.2,h3.1,h3.2]

theorem shapeDenominator_bounds (h k : F)
    (hq : 11 <= (Fintype.card F : Int))
    (hh : Not (h = 0)) (hk : Not (k = 0)) (hhk : Not (h = k)) :
    0 < shapeDenominator h k /\
      shapeDenominator h k <= (Fintype.card F : Int)-3 := by
  have hb := shapeSigma_bounds h k hh hk hhk
  unfold shapeDenominator
  constructor <;> linarith only [hb.1,hb.2,hq]

def density (h k t x : F) : Real :=
  4 * (twistTotal x (x+h) (x+k) t : Real) / (shapeDenominator h k : Real)

def background (h k x : F) : Real :=
  ((Fintype.card F : Real)+1-(totalCorrection x (x+h) (x+k) : Real)) /
    (shapeDenominator h k : Real)

theorem density_nonneg (h k t x : F)
    (hD : 0 < shapeDenominator h k) : 0 <= density h k t x := by
  have hp : (0 : Real) <= (twistTotal x (x+h) (x+k) t : Real) := by
    exact_mod_cast twistTotal_nonneg x (x+h) (x+k) t
  have hd : (0 : Real) < (shapeDenominator h k : Real) := by exact_mod_cast hD
  exact div_nonneg (mul_nonneg (by norm_num) hp) (le_of_lt hd)

theorem sum_density (hF : Not (ringChar F = 2)) (h k t : F)
    (hh : Not (h = 0)) (hk : Not (k = 0)) (hhk : Not (h = k))
    (ht : Not (t = 0)) (hchi : (quadraticChar F) t = -1)
    (hD : 0 < shapeDenominator h k) :
    (Finset.univ.sum fun x : F => density h k t x) = (Fintype.card F : Real) := by
  have hs := four_sum_twistTotal hF h k t hh hk hhk ht hchi
  have hr : (4 : Real) * (Finset.univ.sum fun x : F =>
        (twistTotal x (x+h) (x+k) t : Real)) =
      (Fintype.card F : Real)*(shapeDenominator h k : Real) := by
    exact_mod_cast hs
  have hd : Not ((shapeDenominator h k : Real)=0) := by
    have hp : (0 : Real) < (shapeDenominator h k : Real) := by exact_mod_cast hD
    exact ne_of_gt hp
  unfold density
  rw [<- Finset.sum_div,<- Finset.mul_sum,hr]
  field_simp [hd]

theorem density_sub_background (h k t x : F) :
    density h k t x-background h k x =
      (4*(twistTotal x (x+h) (x+k) t : Real) -
        (Fintype.card F : Real)-1+(totalCorrection x (x+h) (x+k) : Real)) /
        (shapeDenominator h k : Real) := by
  unfold density background
  ring

end FiniteField.QuadraticTripleTwist
