/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.NicolasSpectralPsi

/-!
# The positive higher-power correction beyond prime squares

The exact root squeeze bounds the correction after retaining the full square
root psi integral. No prime-power contribution is silently discarded.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

open MeasureTheory Robin1984 Set

def nicolasPsiRootTail (k : Nat) (x : Real) : Real :=
  integral (volume.restrict (Ioi x)) (fun t : Real =>
    Chebyshev.psi (t ^ (Inv.inv (k : Real))) * robinRealWeight 1 t)

theorem nicolasPsiRootTail_upper {k : Nat} (hk : 2 <= k)
    {x : Real} (hx : 1 < x) :
    nicolasPsiRootTail k x <=
      (Real.log 4 + 4) * (robinZeroKernel 1 ((Inv.inv (k : Real)) : Complex) x).re := by
  have hpsi := integrableOn_psi_root_mul_robinRealWeight (n := 1) (by norm_num) hk hx
  have hmain := integrableOn_rpow_mul_robinRealWeight (n := 1) hx
    (inv_nat_lt_nat_of_two_le (by norm_num : 1 <= (1 : Nat)) hk)
  have h : nicolasPsiRootTail k x <=
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        (Real.log 4 + 4) * (t ^ (Inv.inv (k : Real)) * robinRealWeight 1 t)) := by
    apply integral_mono_ae hpsi (hmain.const_mul (Real.log 4 + 4))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : 1 < t := hx.trans ht
    have hweight := robinRealWeight_nonneg (n := 1) ht1
    have hb := mul_le_mul_of_nonneg_right
      (Chebyshev.psi_le_const_mul_self (Real.rpow_nonneg (zero_lt_one.trans ht1).le
        (Inv.inv (k : Real)))) hweight
    nlinarith only [hb]
  rw [integral_const_mul, integral_rpow_mul_robinRealWeight 1 _ hx] at h
  simpa only [Complex.ofReal_inv] using h

theorem nicolasPrimePowerTail_square_sandwich {x : Real} (hx : 3 <= x) :
    0 <= nicolasPrimePowerTail x - nicolasPsiRootTail 2 x /\
    nicolasPrimePowerTail x - nicolasPsiRootTail 2 x <=
      (Real.log 4 + 4) *
        ((robinZeroKernel 1 (1 / 3 : Complex) x).re +
          (robinZeroKernel 1 (1 / 5 : Complex) x).re) := by
  have hx1 : 1 < x := by linarith
  have h2 := integrableOn_psi_root_mul_robinRealWeight (n := 1) (k := 2)
    (by norm_num) (by norm_num) hx1
  have h3 := integrableOn_psi_root_mul_robinRealWeight (n := 1) (k := 3)
    (by norm_num) (by norm_num) hx1
  have h5 := integrableOn_psi_root_mul_robinRealWeight (n := 1) (k := 5)
    (by norm_num) (by norm_num) hx1
  have hP := integrableOn_robinPrimePowerWeightedTail (n := 1) (by norm_num) hx1
  have hU : robinPrimePowerWeightedTail 1 x <=
      integral (volume.restrict (Ioi x)) (fun t : Real =>
        Chebyshev.psi (t ^ (Inv.inv (2 : Real))) * robinRealWeight 1 t +
        Chebyshev.psi (t ^ (Inv.inv (3 : Real))) * robinRealWeight 1 t +
        Chebyshev.psi (t ^ (Inv.inv (5 : Real))) * robinRealWeight 1 t) := by
    apply integral_mono_ae hP ((h2.add h3).add h5)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hw := robinRealWeight_nonneg (n := 1) (hx1.trans ht)
    simpa only [Pi.add_apply, add_mul, Nat.cast_ofNat] using
      mul_le_mul_of_nonneg_right (Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi t) hw
  have hAdd := integral_add (h2.add h3) h5
  simp only [Pi.add_apply] at hAdd
  rw [integral_add h2 h3] at hAdd
  simp only [Nat.cast_ofNat] at hAdd
  rw [hAdd] at hU
  change robinPrimePowerWeightedTail 1 x <=
    nicolasPsiRootTail 2 x + nicolasPsiRootTail 3 x + nicolasPsiRootTail 5 x at hU
  have hL := three_root_integrals_le_robinPrimePowerWeightedTail (n := 1) (by norm_num) hx1
  change nicolasPsiRootTail 2 x + nicolasPsiRootTail 3 x + nicolasPsiRootTail 7 x <=
    robinPrimePowerWeightedTail 1 x at hL
  have hnonneg (k : Nat) : 0 <= nicolasPsiRootTail k x := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro t ht
    exact mul_nonneg (Chebyshev.psi_nonneg _)
      (robinRealWeight_nonneg (n := 1) (hx1.trans ht))
  rw [<- nicolasPrimePowerTail_eq_weighted_one hx] at hU hL
  have h3b := nicolasPsiRootTail_upper (k := 3) (by norm_num) hx1
  have h5b := nicolasPsiRootTail_upper (k := 5) (by norm_num) hx1
  norm_num only [Nat.cast_ofNat, Complex.ofReal_inv, Complex.ofReal_ofNat, inv_eq_one_div] at h3b h5b
  exact And.intro (by linarith [hnonneg 3, hnonneg 7]) (by nlinarith only [hU, h3b, h5b])

theorem nicolasRealKernel_upper {r x : Real} (hr : r < 1)
    (hx : 1 < x) (hlog : 1 <= Real.log x) :
    (robinZeroKernel 1 (r : Complex) x).re <=
      (2 / (1 - r)) * x ^ (r - 1) * Inv.inv (Real.log x) := by
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hlpos : 0 < Real.log x := Real.log_pos hx
  have hsplit := robinZeroKernel_eq_nat_mul_tail_one_add_tail_two
    (n := 1) (rho := (r : Complex)) hx (by simpa only [Complex.ofReal_re, Nat.cast_one] using hr)
  have hreal := congrArg Complex.re hsplit
  simp only [Nat.cast_one, one_mul, Complex.add_re] at hreal
  have he : (r : Complex) - 1 = ((r - 1 : Real) : Complex) := by push_cast; rfl
  rw [he] at hreal
  have h1 := robinCpowLogTail_ofReal_re_le (a := r - 1) (by linarith) 1 hx
  have h2 := robinCpowLogTail_ofReal_re_le (a := r - 1) (by linarith) 2 hx
  have heq : -x ^ (r - 1) / (r - 1) = x ^ (r - 1) / (1 - r) := by
    rw [neg_div, <- div_neg]
    congr 1
    ring
  rw [heq] at h1 h2
  simp only [pow_one] at h1
  have hinv : Inv.inv ((Real.log x) ^ 2) <= Inv.inv (Real.log x) := by
    simpa only [one_div] using one_div_le_one_div_of_le hlpos
      (show Real.log x <= (Real.log x) ^ 2 by nlinarith only [hlog])
  have hq : 0 <= x ^ (r - 1) / (1 - r) :=
    div_nonneg (Real.rpow_nonneg hxpos.le _) (by linarith)
  have hsmall := mul_le_mul_of_nonneg_left hinv hq
  rw [hreal]
  calc
    _ <= 2 * (x ^ (r - 1) / (1 - r) * Inv.inv (Real.log x)) := by
      linarith only [h1, h2, hsmall]
    _ = _ := by ring

theorem nicolasRealKernel_higher_root_bound {r x : Real} (hr : r < 1 / 2)
    (hx : 1 < x) (hlog : 1 <= Real.log x) :
    (robinZeroKernel 1 (r : Complex) x).re <=
      (2 / ((1 - r) * (1 / 2 - r))) *
        x ^ (-(1 / 2 : Real)) * Inv.inv ((Real.log x) ^ 2) := by
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hlpos : 0 < Real.log x := Real.log_pos hx
  let d : Real := 1 / 2 - r
  have hd : 0 < d := by dsimp [d]; linarith
  have hp := Real.rpow_pos_of_pos hxpos d
  have hlogr := Real.log_le_sub_one_of_pos hp
  rw [Real.log_rpow hxpos] at hlogr
  have hlinear : d * Real.log x <= x ^ d := by linarith only [hlogr]
  have hprod : x ^ d * x ^ (r - 1) = x ^ (-(1 / 2 : Real)) := by
    rw [<- Real.rpow_add hxpos]
    congr 1
    dsimp [d]
    ring
  have hcore := mul_le_mul_of_nonneg_right hlinear (Real.rpow_nonneg hxpos.le (r - 1))
  rw [hprod] at hcore
  have hratio : x ^ (r - 1) * Inv.inv (Real.log x) <=
      (1 / d) * x ^ (-(1 / 2 : Real)) * Inv.inv ((Real.log x) ^ 2) := by
    have h := mul_le_mul_of_nonneg_right hcore
      (show 0 <= Inv.inv d * Inv.inv ((Real.log x) ^ 2) by positivity)
    convert h using 1
    . field_simp
    . simp only [one_div]
      ring
  have hcoef : 0 <= (2 : Real) / (1 - r) :=
    div_nonneg (by norm_num) (by linarith)
  calc
    _ <= (2 / (1 - r)) * x ^ (r - 1) * Inv.inv (Real.log x) :=
      nicolasRealKernel_upper (by linarith) hx hlog
    _ = (2 / (1 - r)) * (x ^ (r - 1) * Inv.inv (Real.log x)) := by ring
    _ <= (2 / (1 - r)) *
        ((1 / d) * x ^ (-(1 / 2 : Real)) * Inv.inv ((Real.log x) ^ 2)) :=
      mul_le_mul_of_nonneg_left hratio hcoef
    _ = _ := by
      dsimp [d]
      simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
      ring

theorem nicolasPrimePowerTail_higher_roots_bound {x : Real}
    (hx : 3 <= x) (hlog : 1 <= Real.log x) :
    0 <= nicolasPrimePowerTail x - nicolasPsiRootTail 2 x /\
    nicolasPrimePowerTail x - nicolasPsiRootTail 2 x <=
      (Real.log 4 + 4) * (79 / 3 : Real) *
        x ^ (-(1 / 2 : Real)) * Inv.inv ((Real.log x) ^ 2) := by
  have hx1 : 1 < x := by linarith
  have h := nicolasPrimePowerTail_square_sandwich hx
  have h3 := nicolasRealKernel_higher_root_bound (r := (1 / 3 : Real))
    (by norm_num) hx1 hlog
  have h5 := nicolasRealKernel_higher_root_bound (r := (1 / 5 : Real))
    (by norm_num) hx1 hlog
  norm_num at h3 h5
  have hconst : 0 <= Real.log 4 + 4 := by
    have h4 := Real.log_nonneg (by norm_num : (1 : Real) <= 4)
    linarith
  have hb := mul_le_mul_of_nonneg_left (add_le_add h3 h5) hconst
  refine And.intro h.1 (h.2.trans ?_)
  nlinarith only [hb]

end PrimeFactorOscillations
