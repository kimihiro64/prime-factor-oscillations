/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Nat.GCD.Basic
import PrimeFactorOscillations.Assembly.CarmichaelPowerTrace

/-!
# Coprime affine-grid geometry for signed carrier sharpness

The coprime arithmetic gives injective grid heights and uniform bounds on a
finite rectangle. These are the supporting geometry for the full simultaneous
reference construction. No arithmetic L-function realization is asserted.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelTraceSharpness

open DirichletCompensatedProbe
open PrimeFactorOscillations.CarmichaelWeightedSignal

private theorem coprime_pow_not_dvd (d e k : Nat) (hd : 1 < d)
    (hde : Nat.Coprime d e) : Not (Dvd.dvd d (e ^ k)) := by
  intro h
  have hg : Dvd.dvd d (Nat.gcd d (e ^ k)) := Nat.dvd_gcd (dvd_refl d) h
  rw [(hde.pow_right k).gcd_eq_one] at hg
  have hsmall : d <= 1 := Nat.le_of_dvd (by decide) hg
  exact (not_le_of_gt hd) hsmall

private theorem coprime_cross_power_index (d e n m u v : Nat)
    (hd : 1 < d) (hde : Nat.Coprime d e)
    (h : e ^ u * d ^ n = e ^ v * d ^ m) : n = m := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => rfl
    | succ m =>
      simp only [pow_zero, mul_one, pow_succ] at h
      have hD : Dvd.dvd d (e ^ u) := by
        refine Exists.intro (e ^ v * d ^ m) ?_
        rw [h]
        ring
      exact False.elim ((coprime_pow_not_dvd d e u hd hde) hD)
  | succ n ih =>
    cases m with
    | zero =>
      simp only [pow_zero, mul_one, pow_succ] at h
      have hD : Dvd.dvd d (e ^ v) := by
        refine Exists.intro (e ^ u * d ^ n) ?_
        rw [<- h]
        ring
      exact False.elim ((coprime_pow_not_dvd d e v hd hde) hD)
    | succ m =>
      have hc : e ^ u * d ^ n = e ^ v * d ^ m := by
        apply Nat.eq_of_mul_eq_mul_right (zero_lt_one.trans hd)
        simpa only [pow_succ, mul_assoc] using h
      exact congrArg Nat.succ (ih m hc)

private theorem realPowStrictMono (a : Real) (ha : 1 < a) :
    StrictMono (fun k : Nat => a ^ k) := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [pow_succ]
  have hp := mul_pos (pow_pos (zero_lt_one.trans ha) k) (sub_pos.mpr ha)
  nlinarith only [hp]

def gridHeight (d e i j : Nat) : Real :=
  ((e : Real) / (d : Real)) ^ i * (e : Real) ^ j

theorem gridHeight_formula (d e i j : Nat) :
    gridHeight d e i j = (e : Real) ^ (i + j) / (d : Real) ^ i := by
  unfold gridHeight
  rw [div_pow, pow_add]
  ring

theorem gridHeight_pos (d e i j : Nat) (hd : 0 < d) (he : 0 < e) :
    0 < gridHeight d e i j := by
  have hdR : 0 < (d : Real) := by exact_mod_cast hd
  have heR : 0 < (e : Real) := by exact_mod_cast he
  exact mul_pos (pow_pos (div_pos heR hdR) i) (pow_pos heR j)

theorem gridHeight_injective (d e : Nat) (hd : 1 < d) (he : 1 < e)
    (hde : Nat.Coprime d e) :
    Function.Injective (fun t : Prod Nat Nat => gridHeight d e t.1 t.2) := by
  intro x y hxy
  have hdR : 0 < (d : Real) := by exact_mod_cast (zero_lt_one.trans hd)
  have hc : gridHeight d e x.1 x.2 = gridHeight d e y.1 y.2 := hxy
  rw [gridHeight_formula, gridHeight_formula] at hc
  have hcross := (div_eq_div_iff (pow_ne_zero x.1 hdR.ne')
    (pow_ne_zero y.1 hdR.ne')).mp hc
  have hNat : e ^ (x.1 + x.2) * d ^ y.1 =
      e ^ (y.1 + y.2) * d ^ x.1 := by exact_mod_cast hcross
  have hi : y.1 = x.1 :=
    coprime_cross_power_index d e y.1 x.1 (x.1 + x.2) (y.1 + y.2) hd hde hNat
  have hNat' : e ^ (x.1 + x.2) = e ^ (y.1 + y.2) := by
    apply Nat.eq_of_mul_eq_mul_right (pow_pos (zero_lt_one.trans hd) x.1)
    simpa only [hi] using hNat
  have heR : 1 < (e : Real) := by exact_mod_cast he
  have hindices : x.1 + x.2 = y.1 + y.2 :=
    (realPowStrictMono (e : Real) heR).injective (by exact_mod_cast hNat')
  apply Prod.ext
  . exact hi.symm
  . have hh : x.1 + x.2 = x.1 + y.2 := by simpa only [hi] using hindices
    exact Nat.add_left_cancel hh

private theorem gridRatio_gt_one (d e : Nat) (hd : 0 < d) (hde : d < e) :
    1 < (e : Real) / (d : Real) := by
  have hdR : 0 < (d : Real) := by exact_mod_cast hd
  have heR : (d : Real) < (e : Real) := by exact_mod_cast hde
  have hmul : (e : Real) / (d : Real) * (d : Real) = (e : Real) := by
    field_simp [hdR.ne']
  by_contra hn
  have hp := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hn)) hdR.le
  nlinarith only [hp, hmul, heR]

theorem gridHeight_top_bound (d e n i j : Nat)
    (hd : 1 < d) (hde : d < e) (hi : i <= n) (hj : j <= n) :
    gridHeight d e i j <= gridHeight d e n n := by
  have hd0 : 0 < d := zero_lt_one.trans hd
  have hr : 1 < (e : Real) / (d : Real) := gridRatio_gt_one d e hd0 hde
  have he1 : 1 < e := hd.trans hde
  have heR : 1 < (e : Real) := by exact_mod_cast he1
  unfold gridHeight
  exact mul_le_mul ((realPowStrictMono _ hr).monotone hi)
    ((realPowStrictMono _ heR).monotone hj)
    (pow_nonneg (zero_lt_one.trans heR).le j)
    (pow_nonneg (zero_lt_one.trans hr).le n)

def gridDelta (d e n : Nat) : Real :=
  1 / (4 * gridHeight d e n n)

def gridRight (d e n i j : Nat) : Complex :=
  Complex.mk (1 - gridDelta d e n * gridHeight d e i j) (gridHeight d e i j)

def gridLeft (d e n i j : Nat) : Complex :=
  Complex.mk (gridDelta d e n * gridHeight d e i j) (gridHeight d e i j)

def gridIndices (n : Nat) : Finset (Prod Bool (Prod Nat Nat)) :=
  Finset.univ.product ((Finset.range (n + 1)).product (Finset.range (n + 1)))

def gridPoint (d e n : Nat) (t : Prod Bool (Prod Nat Nat)) : Complex :=
  if t.1 = true then gridRight d e n t.2.1 t.2.2 else gridLeft d e n t.2.1 t.2.2

theorem mem_gridIndices (n : Nat) (t : Prod Bool (Prod Nat Nat)) :
    Membership.mem (gridIndices n) t <-> t.2.1 <= n /\ t.2.2 <= n := by
  simp [gridIndices, Nat.lt_succ_iff]

theorem gridPoint_im (d e n : Nat) (t : Prod Bool (Prod Nat Nat)) :
    (gridPoint d e n t).im = gridHeight d e t.2.1 t.2.2 := by
  by_cases hs : t.1 = true <;> simp [gridPoint, hs, gridRight, gridLeft]

theorem gridDelta_pos (d e n : Nat) (hd : 1 < d) (hde : d < e) :
    0 < gridDelta d e n := by
  exact one_div_pos.mpr (mul_pos (by norm_num)
    (gridHeight_pos d e n n (zero_lt_one.trans hd) (zero_lt_one.trans (hd.trans hde))))

theorem gridDelta_height_bounds (d e n i j : Nat) (hd : 1 < d) (hde : d < e)
    (hi : i <= n) (hj : j <= n) :
    0 < gridDelta d e n * gridHeight d e i j /\
      gridDelta d e n * gridHeight d e i j <= 1 / 4 := by
  have hp := gridDelta_pos d e n hd hde
  have hg := gridHeight_pos d e i j (zero_lt_one.trans hd)
    (zero_lt_one.trans (hd.trans hde))
  have htop := gridHeight_top_bound d e n i j hd hde hi hj
  have ht := gridHeight_pos d e n n (zero_lt_one.trans hd)
    (zero_lt_one.trans (hd.trans hde))
  have heq : gridDelta d e n * gridHeight d e n n = 1 / 4 := by
    unfold gridDelta
    field_simp [ht.ne']
  have hmul := mul_le_mul_of_nonneg_left htop hp.le
  rw [heq] at hmul
  exact And.intro (mul_pos hp hg) hmul

theorem gridPoint_strip (d e n : Nat) (hd : 1 < d) (hde : d < e)
    (t : Prod Bool (Prod Nat Nat)) (ht : Membership.mem (gridIndices n) t) :
    0 < (gridPoint d e n t).re /\ (gridPoint d e n t).re < 1 := by
  have hi := (mem_gridIndices n t).mp ht
  have hb := gridDelta_height_bounds d e n t.2.1 t.2.2 hd hde hi.1 hi.2
  cases hs : t.1 <;> simp [gridPoint, hs, gridRight, gridLeft]
  all_goals constructor <;> nlinarith only [hb.1, hb.2]

theorem gridLeft_eq_reflection (d e n i j : Nat) :
    gridLeft d e n i j = zeroReflection (gridRight d e n i j) := by
  apply Complex.ext <;> simp [gridLeft, gridRight, zeroReflection]

theorem gridPoint_injective (d e n : Nat) (hd : 1 < d) (hde : d < e)
    (hcop : Nat.Coprime d e) (x y : Prod Bool (Prod Nat Nat))
    (hx : Membership.mem (gridIndices n) x) (hy : Membership.mem (gridIndices n) y)
    (hxy : gridPoint d e n x = gridPoint d e n y) : x = y := by
  have hxI := (mem_gridIndices n x).mp hx
  have hyI := (mem_gridIndices n y).mp hy
  have hIm := congrArg Complex.im hxy
  rw [gridPoint_im, gridPoint_im] at hIm
  have hPair : x.2 = y.2 := gridHeight_injective d e hd (hd.trans hde) hcop hIm
  have hSide : x.1 = y.1 := by
    have hRe := congrArg Complex.re hxy
    have hxb := gridDelta_height_bounds d e n x.2.1 x.2.2 hd hde hxI.1 hxI.2
    have hyb := gridDelta_height_bounds d e n y.2.1 y.2.2 hd hde hyI.1 hyI.2
    cases hxs : x.1 <;> cases hys : y.1
    all_goals try rfl
    all_goals
      simp [gridPoint, gridRight, gridLeft, hxs, hys] at hRe
      exfalso
      nlinarith only [hRe, hxb.2, hyb.2]
  exact Prod.ext hSide hPair

private theorem powerMap_gridRight_of_height (d e n i j k l : Nat)
    (a : Real) (ha : 0 < a)
    (hHeight : gridHeight d e i j = a * gridHeight d e k l) :
    powerMap a (gridRight d e n i j) = gridRight d e n k l := by
  apply Complex.ext
  . change (powerMap a (gridRight d e n i j)).re =
      1 - gridDelta d e n * gridHeight d e k l
    have h := powerMap_real_identity a ha (gridRight d e n i j)
    change (powerMap a (gridRight d e n i j)).re * a =
      1 - gridDelta d e n * gridHeight d e i j + a - 1 at h
    rw [(eq_div_iff ha.ne').mpr h, hHeight]
    field_simp [ha.ne']
    ring
  . change (powerMap a (gridRight d e n i j)).im = gridHeight d e k l
    have h := powerMap_im_identity a ha (gridRight d e n i j)
    change (powerMap a (gridRight d e n i j)).im * a = gridHeight d e i j at h
    rw [(eq_div_iff ha.ne').mpr h, hHeight]
    field_simp [ha.ne']

theorem powerMap_gridRight_e (d e n i j : Nat) (he : 0 < e) :
    powerMap (e : Real) (gridRight d e n i (j + 1)) = gridRight d e n i j := by
  have heR : 0 < (e : Real) := by exact_mod_cast he
  apply powerMap_gridRight_of_height d e n i (j + 1) i j (e : Real) heR
  simp only [gridHeight, pow_succ]
  ring

theorem powerMap_gridRight_d (d e n i j : Nat) (hd : 0 < d) :
    powerMap (d : Real) (gridRight d e n i (j + 1)) = gridRight d e n (i + 1) j := by
  have hdR : 0 < (d : Real) := by exact_mod_cast hd
  apply powerMap_gridRight_of_height d e n i (j + 1) (i + 1) j (d : Real) hdR
  simp only [gridHeight, pow_succ]
  field_simp [hdR.ne'] <;> ring

theorem powerMap_gridLeft_ne_point (d e n i j : Nat) (hd : 1 < d)
    (hde : d < e) (hi : i <= n) (hj : j <= n)
    (a : Real) (ha : 2 <= a) (t : Prod Bool (Prod Nat Nat)) :
    Not (powerMap a (gridLeft d e n i j) = gridPoint d e n t) := by
  intro heq
  have ha0 : 0 < a := by linarith
  have hr := powerMap_real_identity a ha0 (gridLeft d e n i j)
  have hIm := powerMap_im_identity a ha0 (gridLeft d e n i j)
  rw [heq] at hr hIm
  rw [gridPoint_im] at hIm
  change gridHeight d e t.2.1 t.2.2 * a = gridHeight d e i j at hIm
  have hs := congrArg (fun x : Real => gridDelta d e n * x) hIm
  have hb := gridDelta_height_bounds d e n i j hd hde hi hj
  cases hside : t.1
  . simp [gridPoint, hside, gridRight, gridLeft] at hr
    nlinarith only [hr, hs, ha]
  . simp [gridPoint, hside, gridRight, gridLeft] at hr
    nlinarith only [hr, hs, hb.2]

theorem powerMap_gridRight_ne_left (d e n i j k l : Nat) (hd : 1 < d)
    (hde : d < e) (hi : i <= n) (hj : j <= n) (a : Real) (ha : 2 <= a) :
    Not (powerMap a (gridRight d e n i j) = gridLeft d e n k l) := by
  intro heq
  have ha0 : 0 < a := by linarith
  have hr := powerMap_real_identity a ha0 (gridRight d e n i j)
  have hIm := powerMap_im_identity a ha0 (gridRight d e n i j)
  rw [heq] at hr hIm
  change gridHeight d e k l * a = gridHeight d e i j at hIm
  have hs := congrArg (fun x : Real => gridDelta d e n * x) hIm
  have hb := gridDelta_height_bounds d e n i j hd hde hi hj
  simp only [gridLeft, gridRight] at hr
  nlinarith only [hr, hs, hb.2, ha]


theorem powerMap_gridRight_e_iff (d e n i j k l : Nat)
    (hd : 1 < d) (he : 1 < e) (hcop : Nat.Coprime d e) :
    powerMap (e : Real) (gridRight d e n i j) = gridRight d e n k l <->
      k = i /\ l + 1 = j := by
  have heR : 0 < (e : Real) := by exact_mod_cast (zero_lt_one.trans he)
  constructor
  . intro h
    have hIm := powerMap_im_identity (e : Real) heR (gridRight d e n i j)
    rw [h] at hIm
    change gridHeight d e k l * (e : Real) = gridHeight d e i j at hIm
    have hh : gridHeight d e k (l + 1) = gridHeight d e i j := by
      calc
        gridHeight d e k (l + 1) = gridHeight d e k l * (e : Real) := by
          simp only [gridHeight, pow_succ]
          ring
        _ = gridHeight d e i j := hIm
    have hp : Prod.mk k (l + 1) = Prod.mk i j :=
      @gridHeight_injective d e hd he hcop (Prod.mk k (l + 1)) (Prod.mk i j) hh
    exact And.intro (congrArg Prod.fst hp) (congrArg Prod.snd hp)
  . intro h
    calc
      powerMap (e : Real) (gridRight d e n i j) =
          powerMap (e : Real) (gridRight d e n k (l + 1)) := by rw [h.1, h.2]
      _ = gridRight d e n k l :=
        powerMap_gridRight_e d e n k l (zero_lt_one.trans he)

theorem powerMap_gridRight_d_iff (d e n i j k l : Nat)
    (hd : 1 < d) (he : 1 < e) (hcop : Nat.Coprime d e) :
    powerMap (d : Real) (gridRight d e n i j) = gridRight d e n k l <->
      k = i + 1 /\ l + 1 = j := by
  have hdR : 0 < (d : Real) := by exact_mod_cast (zero_lt_one.trans hd)
  constructor
  . intro h
    have hIm := powerMap_im_identity (d : Real) hdR (gridRight d e n i j)
    rw [h] at hIm
    change gridHeight d e k l * (d : Real) = gridHeight d e i j at hIm
    have hh : gridHeight d e k (l + 1) = gridHeight d e (i + 1) j := by
      calc
        gridHeight d e k (l + 1) = gridHeight d e k l * (e : Real) := by
          simp only [gridHeight, pow_succ]
          ring
        _ = (gridHeight d e k l * (d : Real)) * ((e : Real) / (d : Real)) := by
          field_simp [hdR.ne']
        _ = gridHeight d e i j * ((e : Real) / (d : Real)) := by rw [hIm]
        _ = gridHeight d e (i + 1) j := by
          simp only [gridHeight, pow_succ]
          ring
    have hp : Prod.mk k (l + 1) = Prod.mk (i + 1) j :=
      @gridHeight_injective d e hd he hcop (Prod.mk k (l + 1)) (Prod.mk (i + 1) j) hh
    exact And.intro (congrArg Prod.fst hp) (congrArg Prod.snd hp)
  . intro h
    calc
      powerMap (d : Real) (gridRight d e n i j) =
          powerMap (d : Real) (gridRight d e n i (l + 1)) := by rw [h.2]
      _ = gridRight d e n (i + 1) l :=
        powerMap_gridRight_d d e n i l (zero_lt_one.trans hd)
      _ = gridRight d e n k l := by rw [h.1]

end PrimeFactorOscillations.CarmichaelTraceSharpness
