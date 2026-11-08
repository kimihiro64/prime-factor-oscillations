/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.DirichletCarrierReadout
import PrimeFactorOscillations.Mathlib.NumberTheory.LSeries.UniformRemainder

/-!
# Zero-density normalization of probability carriers

The coordinate and amplitude are scaled together. Analytic multiplicities and
pole orders are unchanged, while the actual coefficient correction is divided
by the density. The estimate is uniform in characters and imaginary parts.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations.DirichletDensityNormalization

open DirichletPacketMellin DirichletCarrierReadout

def densityPoint (center : Complex) (density : Real) (z : Complex) : Complex :=
  center + z / (density : Complex)

def densityReadout {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    (a : Nat -> Complex) (center : Complex) (density : Real) (z : Complex) : Complex :=
  continuation chi a (densityPoint center density z) / (density : Complex)

theorem densityPoint_hasDerivAt (center : Complex) (density : Real) (z : Complex) :
    HasDerivAt (densityPoint center density) (1 / (density : Complex)) z := by
  have hi : HasDerivAt (fun w : Complex => w) (1 : Complex) z := hasDerivAt_id z
  have hh : HasDerivAt (fun w : Complex => w / (density : Complex))
      (1 / (density : Complex)) z := hi.div_const (density : Complex)
  exact hh.const_add center

theorem densityPoint_analyticAt (center : Complex) (density : Real) (z : Complex) :
    AnalyticAt Complex (densityPoint center density) z := by
  change AnalyticAt Complex (fun w : Complex => center + w / (density : Complex)) z
  exact analyticAt_const.add analyticAt_id.div_const

theorem correction_uniform_bound {q : Nat} (chi : DirichletCharacter Complex q)
    (k n0 : Nat) (hk : 3 <= k) (hn0 : 2 <= n0)
    (a : Nat -> Complex) (C : Real) (hC : 0 <= C)
    (herror : forall n : Nat, Not (n = 0) ->
      norm (a n - coefficient chi n) <= C / (n : Real) ^ (k - 1))
    (hsmall : forall n : Nat, n < n0 -> a n = coefficient chi n)
    (s : Complex) (hs : 0 <= s.re) :
    norm (correction chi a s) <= C / ((n0 : Real) - 1) := by
  have hbound : forall n : Nat, Not (n = 0) ->
      norm (a n - coefficient chi n) <= C / (n : Real) ^ 2 := by
    intro n hn
    have hnpos : (0 : Real) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hn1 : (1 : Real) <= n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hpow : (n : Real) ^ 2 <= (n : Real) ^ (k - 1) := by
      gcongr
      omega
    exact (herror n hn).trans
      (div_le_div_of_nonneg_left hC (sq_pos_of_pos hnpos) hpow)
  have hzero : forall n : Nat, n <= n0 - 1 -> a n - coefficient chi n = 0 := by
    intro n hn
    rw [hsmall n (by omega), sub_self]
  have hh := LSeries.norm_le_of_initial_vanishing_inv_sq
    (fun n => a n - coefficient chi n) C hC hbound (n0 - 1) (by omega) hzero s hs
  simpa only [correction, Nat.cast_sub (by omega : 1 <= n0), Nat.cast_one] using hh

theorem densityReadout_error {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    (k n0 : Nat) (hk : 3 <= k) (hn0 : 2 <= n0)
    (a : Nat -> Complex) (C : Real) (hC : 0 <= C)
    (herror : forall n : Nat, Not (n = 0) ->
      norm (a n - coefficient chi n) <= C / (n : Real) ^ (k - 1))
    (hsmall : forall n : Nat, n < n0 -> a n = coefficient chi n)
    (center : Complex) (density : Real) (hd : 0 < density) (z : Complex)
    (hs : 0 <= (densityPoint center density z).re) :
    norm (densityReadout chi a center density z -
      (-logDeriv (DirichletCharacter.LFunction chi) (densityPoint center density z)) /
        (density : Complex)) <= C / (density * ((n0 : Real) - 1)) := by
  have hh := correction_uniform_bound chi k n0 hk hn0 a C hC herror hsmall
    (densityPoint center density z) hs
  change norm ((-logDeriv (DirichletCharacter.LFunction chi)
      (densityPoint center density z) + correction chi a (densityPoint center density z)) /
        (density : Complex) - _) <= _
  rw [add_div, add_sub_cancel_left, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hd]
  calc
    _ <= (C / ((n0 : Real) - 1)) / density := div_le_div_of_nonneg_right hh hd.le
    _ = _ := by simp only [div_div, mul_comm]

theorem densityReadout_logDeriv {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (a : Nat -> Complex)
    (center : Complex) (density : Real) (z : Complex)
    (hOne : Not (densityPoint center density z = 1)) :
    densityReadout chi a center density z =
      -logDeriv (fun w => DirichletCharacter.LFunction chi (densityPoint center density w)) z +
        correction chi a (densityPoint center density z) / (density : Complex) := by
  have ha := DirichletZeroReadout.analyticOnNhd_LFunction_off_one chi
    (densityPoint center density z) (Set.mem_compl_singleton_iff.mpr hOne)
  have hd := densityPoint_hasDerivAt center density z
  have hc := logDeriv_comp ha.differentiableAt hd.differentiableAt
  rw [hd.deriv] at hc
  have hc' : logDeriv
      (fun w => DirichletCharacter.LFunction chi (densityPoint center density w)) z =
      logDeriv (DirichletCharacter.LFunction chi) (densityPoint center density z) /
        (density : Complex) := by
    simpa only [Function.comp_def, div_eq_mul_inv, one_mul] using hc
  rw [hc']
  change (-logDeriv (DirichletCharacter.LFunction chi) (densityPoint center density z) +
      correction chi a (densityPoint center density z)) / (density : Complex) = _
  rw [add_div, neg_div]

theorem densityLFunction_multiplicity {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (center : Complex)
    (density : Real) (hd : 0 < density) (z : Complex) :
    analyticOrderAt (fun w => DirichletCharacter.LFunction chi (densityPoint center density w)) z =
      analyticOrderAt (DirichletCharacter.LFunction chi) (densityPoint center density z) := by
  have hdC : Not ((density : Complex) = 0) := by exact_mod_cast hd.ne'
  have hh := densityPoint_hasDerivAt center density z
  have he : Not (deriv (densityPoint center density) z = 0) := by
    rw [hh.deriv]
    exact one_div_ne_zero hdC
  simpa only [Function.comp_def] using
    (analyticOrderAt_comp_of_deriv_ne_zero
      (f := DirichletCharacter.LFunction chi) (densityPoint_analyticAt center density z) he)

theorem densityReadout_order {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (a : Nat -> Complex)
    (center : Complex) (density : Real) (hd : 0 < density) (z : Complex) :
    meromorphicOrderAt (densityReadout chi a center density) z =
      meromorphicOrderAt (continuation chi a) (densityPoint center density z) := by
  have hdC : Not ((density : Complex) = 0) := by exact_mod_cast hd.ne'
  have hh := densityPoint_hasDerivAt center density z
  have he : Not (deriv (densityPoint center density) z = 0) := by
    rw [hh.deriv]
    exact one_div_ne_zero hdC
  have hcomp := meromorphicOrderAt_comp_of_deriv_ne_zero
    (f := continuation chi a) (densityPoint_analyticAt center density z) he
  have hscale := meromorphicOrderAt_fun_const_smul_eq_meromorphicOrderAt
    (f := fun w => continuation chi a (densityPoint center density w))
    (x := z) (s := Inv.inv (density : Complex)) (inv_ne_zero hdC)
  have hcomp' : meromorphicOrderAt
      (fun w => continuation chi a (densityPoint center density w)) z =
      meromorphicOrderAt (continuation chi a) (densityPoint center density z) := by
    simpa only [Function.comp_def] using hcomp
  have hfun : densityReadout chi a center density =
      (fun w => Inv.inv (density : Complex) * continuation chi a (densityPoint center density w)) := by
    funext w
    simp only [densityReadout, div_eq_mul_inv, mul_comm]
  rw [hfun]
  exact hscale.trans hcomp'

theorem densityReadout_zero_iff {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (k : Nat) (hk : 3 <= k)
    (a : Nat -> Complex) (C : Real)
    (herror : forall n : Nat, Not (n = 0) ->
      norm (a n - coefficient chi n) <= C / (n : Real) ^ (k - 1))
    (center : Complex) (density : Real) (hd : 0 < density) (z : Complex)
    (hs : 0 <= (densityPoint center density z).re)
    (hOne : Not (densityPoint center density z = 1)) :
    meromorphicOrderAt (densityReadout chi a center density) z = -1 <->
      DirichletCharacter.LFunction chi (densityPoint center density z) = 0 := by
  rw [densityReadout_order chi a center density hd z]
  have hkR : (3 : Real) <= k := by exact_mod_cast hk
  have hregion : 2 - (k : Real) < (densityPoint center density z).re := by
    linarith only [hkR, hs]
  exact DirichletZeroReadout.readout_order_iff_zero chi _ hOne (correction chi a)
    (analyticOnNhd_power_correction chi k (by omega) a C herror _ hregion)

theorem exists_probability_density_readout :
    exists n0 : Nat, exists C : Real,
      And (100 <= n0) (And (0 < C)
        (forall k : Nat, 3 <= k ->
          forall (q : Nat) [NeZero q], forall chi : DirichletCharacter Complex q,
          exists a : Nat -> Complex,
            And (forall n : Nat, Not (n = 0) ->
              norm (a n - coefficient chi n) <= C / (n : Real) ^ (k - 1))
              (And (forall n : Nat, n0 <= n ->
                exists O : UniformCarrier.CoefficientObservation k n (coefficient chi n)
                  (coefficient_norm_le_nat chi n), a n = O.value)
                (And (forall n : Nat, n < n0 -> a n = coefficient chi n)
                  (forall (center : Complex) (density : Real), 0 < density -> forall z : Complex,
                    0 <= (densityPoint center density z).re ->
                    norm (densityReadout chi a center density z -
                      (-logDeriv (DirichletCharacter.LFunction chi) (densityPoint center density z)) /
                        (density : Complex)) <= C / (density * ((n0 : Real) - 1))))))) := by
  choose n0 C hn0 hC hData using exists_unconditional_dirichlet_readout
  refine Exists.intro n0 (Exists.intro C (And.intro hn0 (And.intro hC ?_)))
  intro k hk q inst chi
  choose a ha using hData k (by omega) q chi
  refine Exists.intro a (And.intro ha.1 (And.intro ha.2.1 (And.intro ha.2.2.1 ?_)))
  intro center density hd z hs
  exact densityReadout_error chi k n0 hk (by omega) a C hC.le ha.1 ha.2.2.1
    center density hd z hs

end PrimeFactorOscillations.DirichletDensityNormalization
end
