/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairEnergy


/-!
# Positive twist averages of conditional quadratic-pair counts

Common nonsquare scaling reverses the actual split-cubic point trace.
The tagged sum of the two actual irreducible-pair counts cancels that
trace before any estimate. Its canonical weight has mean one, exact
admissibility support and an explicit second moment over odd finite
fields of cardinal at least 5, without a Hasse bound. Both singular
constants and the small-field normalization are retained.
No integer short-window prime-pair estimate is asserted.
-/

set_option autoImplicit false
set_option Elab.async false

namespace FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem splitCubicPointTrace_scale (hF : Not (ringChar F = 2))
    (t : F) (ht : Not (t = 0)) (a b : F) :
    splitCubicPointTrace (t * a) (t * b) =
      (quadraticChar F) t * splitCubicPointTrace a b := by
  rw [splitCubicPointTrace_eq hF, splitCubicPointTrace_eq hF]
  let e : Equiv F F :=
    { toFun := fun x => t * x
      invFun := fun x => x / t
      left_inv := by intro x; field_simp [ht]
      right_inv := by intro x; field_simp [ht] }
  have hcube : ((quadraticChar F) t) ^ 3 = (quadraticChar F) t := by
    calc
      _ = ((quadraticChar F) t) ^ 2 * (quadraticChar F) t := by ring
      _ = _ := by rw [quadraticChar_sq_one ht, one_mul]
  have hs :
      (Finset.univ.sum fun x : F =>
        (quadraticChar F) (x * (x - t * a) * (x - t * b))) =
      (quadraticChar F) t * (Finset.univ.sum fun x : F =>
        (quadraticChar F) (x * (x - a) * (x - b))) := by
    calc
      _ = Finset.univ.sum (fun x : F =>
          (quadraticChar F) ((e x) * (e x - t * a) * (e x - t * b))) :=
        (Equiv.sum_comp e _).symm
      _ = Finset.univ.sum (fun x : F =>
          (quadraticChar F) t * (quadraticChar F) (x * (x - a) * (x - b))) := by
        apply Finset.sum_congr rfl
        intro x _
        change (quadraticChar F) ((t * x) * (t * x - t * a) * (t * x - t * b)) = _
        have he : (t * x) * (t * x - t * a) * (t * x - t * b) =
            t ^ 3 * (x * (x - a) * (x - b)) := by ring
        rw [he, map_mul, map_pow, hcube]
      _ = _ := by rw [Finset.mul_sum]
  rw [hs]
  ring

theorem quadraticPair_twist_count_good
    (hF : Not (ringChar F = 2)) (c h t : F)
    (hc : Not (c = 0)) (hch : Not (c + h = 0)) (hh : Not (h = 0))
    (ht : Not (t = 0)) (hchi : (quadraticChar F) t = -1) :
    2 * (monicQuadraticPairCount c h + monicQuadraticPairCount (t * c) (t * h)) =
      (Fintype.card F : Int) - 1 +
        (quadraticChar F) (-h) * (quadraticChar F) c +
        (quadraticChar F) h * (quadraticChar F) (c + h) := by
  have hs : t * c + t * h = t * (c + h) := by ring
  have hn : -(t * h) = t * (-h) := by ring
  have hi := monicQuadraticPairCount_eq_trace hF c h hc hch hh
  have hiT := monicQuadraticPairCount_eq_trace hF (t * c) (t * h)
    (mul_ne_zero ht hc) (by rw [hs]; exact mul_ne_zero ht hch) (mul_ne_zero ht hh)
  rw [hs, splitCubicPointTrace_scale hF t ht, hn] at hiT
  simp only [map_mul, hchi, neg_one_mul, sub_neg_eq_add] at hiT
  nlinarith only [hi, hiT]


noncomputable def twistPairNumerator (c h : F) : Int :=
  (Fintype.card F : Int) - 1 +
    (quadraticChar F) (-h) * (quadraticChar F) c +
    (quadraticChar F) h * (quadraticChar F) (c + h)

theorem twistPairNumerator_zero (h : F) (hh : Not (h = 0)) :
    twistPairNumerator (0 : F) h = (Fintype.card F : Int) := by
  have hz : (quadraticChar F) (0 : F) = 0 := by simp
  simp only [twistPairNumerator, zero_add, hz, mul_zero, add_zero]
  nlinarith only [quadraticChar_sq_one hh]

theorem twistPairNumerator_neg_shift (h : F) (hh : Not (h = 0)) :
    twistPairNumerator (-h) h = (Fintype.card F : Int) := by
  have hz : (quadraticChar F) (0 : F) = 0 := by simp
  simp only [twistPairNumerator, neg_add_cancel, hz, mul_zero, add_zero]
  nlinarith only [quadraticChar_sq_one (neg_ne_zero.mpr hh)]

noncomputable def traceFreePairNumerator (c h : F) : Int :=
  if c = 0 then 0 else if c = -h then 0 else twistPairNumerator c h

theorem traceFreePairNumerator_completion (c h : F) (hh : Not (h = 0)) :
    traceFreePairNumerator c h =
      twistPairNumerator c h -
        (if c = 0 then (Fintype.card F : Int) else 0) -
        (if c = -h then (Fintype.card F : Int) else 0) := by
  by_cases hc : c = 0
  . subst c
    have hn : Not ((0 : F) = -h) := Ne.symm (neg_ne_zero.mpr hh)
    simp only [traceFreePairNumerator, ite_true, if_neg hn,
      twistPairNumerator_zero h hh, sub_self, sub_zero]
  . by_cases hn : c = -h
    . subst c
      simp only [traceFreePairNumerator, if_neg (neg_ne_zero.mpr hh), ite_true,
        twistPairNumerator_neg_shift h hh, sub_zero, sub_self]
    . simp only [traceFreePairNumerator, if_neg hc, if_neg hn, sub_zero]

theorem traceFreePairNumerator_eq_twist_counts
    (hF : Not (ringChar F = 2)) (c h t : F)
    (hh : Not (h = 0)) (ht : Not (t = 0)) (hchi : (quadraticChar F) t = -1) :
    traceFreePairNumerator c h =
      2 * (monicQuadraticPairCount c h + monicQuadraticPairCount (t * c) (t * h)) := by
  by_cases hc : c = 0
  . subst c
    simp only [traceFreePairNumerator, ite_true, mul_zero,
      monicQuadraticPairCount_zero hF, add_zero]
  . by_cases hn : c = -h
    . subst c
      have hs : t * (-h) = -(t * h) := by ring
      simp only [traceFreePairNumerator, if_neg (neg_ne_zero.mpr hh), ite_true, hs,
        monicQuadraticPairCount_neg_shift hF, add_zero, mul_zero]
    . have hch : Not (c + h = 0) := by
        intro he
        apply hn
        calc
          c = (c + h) - h := by ring
          _ = -h := by rw [he]; ring
      simp only [traceFreePairNumerator, if_neg hc, if_neg hn]
      exact (quadraticPair_twist_count_good hF c h t hc hch hh ht hchi).symm

theorem exists_nonsquare_twist (hF : Not (ringChar F = 2)) :
    Exists (fun t : F => Not (t = 0) /\ (quadraticChar F) t = -1) := by
  classical
  by_contra hnone
  have hp (x : F) :
      (quadraticChar F) x = 1 - (if x = 0 then 1 else 0) := by
    by_cases hx : x = 0
    . subst x
      simp
    . rcases QuadraticPairEuler.quadraticChar_real_signs x hx with he | hn
      . simp only [if_neg hx, sub_zero]
        exact_mod_cast he
      . exact False.elim (hnone (Exists.intro x
          (And.intro hx (by exact_mod_cast hn))))
  have hs : (Finset.univ.sum fun x : F => (quadraticChar F) x) =
      (Fintype.card F : Int) - 1 := by
    simp_rw [hp]
    simp
  rw [quadraticChar_sum_zero hF] at hs
  have hc : 2 <= Fintype.card F := by
    have hi := Finset.card_le_card (Finset.subset_univ ({(0 : F), 1} : Finset F))
    simpa using hi
  have hi : (2 : Int) <= (Fintype.card F : Int) := by exact_mod_cast hc
  linarith only [hs, hi]


noncomputable def traceFreePairWeight (c h : F) : Real :=
  (traceFreePairNumerator c h : Real) / ((Fintype.card F : Real) - 3)

theorem traceFreePairWeight_zero (h : F) :
    traceFreePairWeight (0 : F) h = 0 := by
  simp [traceFreePairWeight, traceFreePairNumerator]

theorem traceFreePairWeight_neg_shift (h : F) :
    traceFreePairWeight (-h) h = 0 := by
  simp [traceFreePairWeight, traceFreePairNumerator]

theorem twistPairNumerator_real_bounds (c h : F)
    (hc : Not (c = 0)) (hch : Not (c + h = 0)) (hh : Not (h = 0)) :
    (Fintype.card F : Real) - 3 <= (twistPairNumerator c h : Real) /\
      (twistPairNumerator c h : Real) <= (Fintype.card F : Real) + 1 := by
  have hr1 : Not ((-h) * c = 0) := mul_ne_zero (neg_ne_zero.mpr hh) hc
  have hr2 : Not (h * (c + h) = 0) := mul_ne_zero hh hch
  have he :
      (twistPairNumerator c h : Real) =
        (Fintype.card F : Real) - 1 +
          ((quadraticChar F) ((-h) * c) : Real) +
          ((quadraticChar F) (h * (c + h)) : Real) := by
    simp only [twistPairNumerator, Int.cast_add, Int.cast_sub, Int.cast_mul,
      Int.cast_natCast, Int.cast_one, map_mul]
  rcases QuadraticPairEuler.quadraticChar_real_signs ((-h) * c) hr1 with ha | ha <;>
    rcases QuadraticPairEuler.quadraticChar_real_signs (h * (c + h)) hr2 with hb | hb <;>
    rw [he, ha, hb] <;> constructor <;> linarith

theorem traceFreePairWeight_good_bounds (c h : F)
    (hc : Not (c = 0)) (hch : Not (c + h = 0)) (hh : Not (h = 0))
    (hq : 5 <= (Fintype.card F : Real)) :
    1 <= traceFreePairWeight c h /\
      traceFreePairWeight c h <=
        ((Fintype.card F : Real) + 1) / ((Fintype.card F : Real) - 3) := by
  have hn : Not (c = -h) := by
    intro he
    apply hch
    rw [he]
    ring
  have hden : 0 < (Fintype.card F : Real) - 3 := by linarith only [hq]
  have hb := twistPairNumerator_real_bounds c h hc hch hh
  have hlo := div_le_div_of_nonneg_right hb.1 (le_of_lt hden)
  rw [div_self (ne_of_gt hden)] at hlo
  simp only [traceFreePairWeight, traceFreePairNumerator, if_neg hc, if_neg hn]
  exact And.intro hlo (div_le_div_of_nonneg_right hb.2 (le_of_lt hden))

theorem traceFreePairWeight_pos_iff (c h : F) (hh : Not (h = 0))
    (hq : 5 <= (Fintype.card F : Real)) :
    0 < traceFreePairWeight c h <-> Not (c = 0) /\ Not (c + h = 0) := by
  constructor
  . intro hp
    have hc : Not (c = 0) := by
      intro he
      exact (ne_of_gt hp) (by rw [he, traceFreePairWeight_zero])
    have hch : Not (c + h = 0) := by
      intro he
      have hn : c = -h := by
        calc
          c = (c + h) - h := by ring
          _ = -h := by rw [he]; ring
      exact (ne_of_gt hp) (by rw [hn, traceFreePairWeight_neg_shift])
    exact And.intro hc hch
  . intro hc
    exact lt_of_lt_of_le (by norm_num)
      (traceFreePairWeight_good_bounds c h hc.1 hc.2 hh hq).1


theorem quadraticChar_shift_product (h : F) (hh : Not (h = 0)) :
    (quadraticChar F) (-h) * (quadraticChar F) h = (quadraticChar F) (-1) := by
  have he : -h = (-1 : F) * h := by ring
  rw [he, map_mul]
  calc
    _ = (quadraticChar F) (-1) * ((quadraticChar F) h) ^ 2 := by ring
    _ = _ := by rw [quadraticChar_sq_one hh, mul_one]

theorem sum_twistPairNumerator (hF : Not (ringChar F = 2)) (h : F) :
    (Finset.univ.sum fun c : F => twistPairNumerator c h) =
      (Fintype.card F : Int) * ((Fintype.card F : Int) - 1) := by
  unfold twistPairNumerator
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, <- Finset.mul_sum]
  rw [quadraticChar_sum_zero hF, quadraticChar_translate_sum hF h]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_zero, add_zero, mul_one]
  ring

theorem sum_traceFreePairNumerator
    (hF : Not (ringChar F = 2)) (h : F) (hh : Not (h = 0)) :
    (Finset.univ.sum fun c : F => traceFreePairNumerator c h) =
      (Fintype.card F : Int) * ((Fintype.card F : Int) - 3) := by
  classical
  have hp (c : F) := traceFreePairNumerator_completion c h hh
  simp_rw [hp]
  simp only [Finset.sum_sub_distrib]
  rw [sum_twistPairNumerator hF h]
  simp
  ring

theorem sum_twistPairNumerator_square
    (hF : Not (ringChar F = 2)) (h : F) (hh : Not (h = 0)) :
    (Finset.univ.sum fun c : F => (twistPairNumerator c h) ^ 2) =
      (Fintype.card F : Int) * ((Fintype.card F : Int) - 1) ^ 2 +
        2 * ((Fintype.card F : Int) - 1) - 2 * (quadraticChar F) (-1) := by
  have hx := quadraticChar_translate_square_sum (F := F) hF
  have hy := quadraticChar_translate_correlation hF h h
  simp only [ite_true, mul_one, <- pow_two] at hy
  have hxy := quadraticChar_translate_correlation hF (0 : F) h
  simp only [add_zero, if_neg hh, mul_zero, zero_sub] at hxy
  have hp (c : F) :
      (twistPairNumerator c h) ^ 2 =
      ((Fintype.card F : Int) - 1) ^ 2 +
        ((quadraticChar F) (-h)) ^ 2 * ((quadraticChar F) c) ^ 2 +
        ((quadraticChar F) h) ^ 2 * ((quadraticChar F) (c + h)) ^ 2 +
        (2 * ((Fintype.card F : Int) - 1) * (quadraticChar F) (-h)) *
          (quadraticChar F) c +
        (2 * ((Fintype.card F : Int) - 1) * (quadraticChar F) h) *
          (quadraticChar F) (c + h) +
        (2 * (quadraticChar F) (-h) * (quadraticChar F) h) *
          ((quadraticChar F) c * (quadraticChar F) (c + h)) := by
    unfold twistPairNumerator
    ring
  simp_rw [hp]
  simp only [Finset.sum_add_distrib, <- Finset.mul_sum]
  rw [hx, hy, quadraticChar_sum_zero hF, quadraticChar_translate_sum hF h, hxy,
    quadraticChar_sq_one hh, quadraticChar_sq_one (neg_ne_zero.mpr hh)]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_zero, add_zero]
  nlinarith only [quadraticChar_shift_product h hh]


theorem traceFreePairNumerator_square_completion (c h : F)
    (hh : Not (h = 0)) :
    (traceFreePairNumerator c h) ^ 2 =
      (twistPairNumerator c h) ^ 2 -
        (if c = 0 then (Fintype.card F : Int) ^ 2 else 0) -
        (if c = -h then (Fintype.card F : Int) ^ 2 else 0) := by
  by_cases hc : c = 0
  . subst c
    have hn : Not ((0 : F) = -h) := Ne.symm (neg_ne_zero.mpr hh)
    simp only [traceFreePairNumerator, ite_true, if_neg hn,
      twistPairNumerator_zero h hh, sub_self, sub_zero]
    norm_num
  . by_cases hn : c = -h
    . subst c
      simp only [traceFreePairNumerator, if_neg (neg_ne_zero.mpr hh), ite_true,
        twistPairNumerator_neg_shift h hh, sub_zero, sub_self]
      norm_num
    . simp only [traceFreePairNumerator, if_neg hc, if_neg hn, sub_zero]

theorem sum_traceFreePairNumerator_square
    (hF : Not (ringChar F = 2)) (h : F) (hh : Not (h = 0)) :
    (Finset.univ.sum fun c : F => (traceFreePairNumerator c h) ^ 2) =
      (Fintype.card F : Int) * ((Fintype.card F : Int) - 3) ^ 2 +
        2 * (Fintype.card F : Int) * ((Fintype.card F : Int) - 3) -
          2 * (1 + (quadraticChar F) (-1)) := by
  classical
  have hp (c : F) := traceFreePairNumerator_square_completion c h hh
  simp_rw [hp]
  simp only [Finset.sum_sub_distrib]
  rw [sum_twistPairNumerator_square hF h hh]
  simp
  ring

theorem traceFreePairWeight_eq_twist_counts
    (hF : Not (ringChar F = 2)) (c h t : F)
    (hh : Not (h = 0)) (ht : Not (t = 0)) (hchi : (quadraticChar F) t = -1) :
    traceFreePairWeight c h =
      2 * ((monicQuadraticPairCount c h : Real) +
        (monicQuadraticPairCount (t * c) (t * h) : Real)) /
          ((Fintype.card F : Real) - 3) := by
  unfold traceFreePairWeight
  rw [traceFreePairNumerator_eq_twist_counts hF c h t hh ht hchi]
  norm_num only [Int.cast_mul, Int.cast_add, Int.cast_ofNat]

theorem traceFreePairWeight_mean_one
    (hF : Not (ringChar F = 2)) (h : F) (hh : Not (h = 0))
    (hq : 5 <= (Fintype.card F : Real)) :
    (1 / (Fintype.card F : Real)) *
      (Finset.univ.sum fun c : F => traceFreePairWeight c h) = 1 := by
  let q : Real := Fintype.card F
  have hq0 : Not (q = 0) := ne_of_gt (by dsimp [q]; linarith only [hq])
  have hq3 : Not (q - 3 = 0) := ne_of_gt (by dsimp [q]; linarith only [hq])
  have hi := sum_traceFreePairNumerator hF h hh
  have hs : (Finset.univ.sum fun c : F => (traceFreePairNumerator c h : Real)) =
      q * (q - 3) := by
    dsimp [q]
    exact_mod_cast hi
  change (1 / q) *
    (Finset.univ.sum fun c : F => (traceFreePairNumerator c h : Real) / (q - 3)) = 1
  simp only [div_eq_mul_inv]
  rw [<- Finset.sum_mul, hs]
  field_simp [hq0, hq3] <;> ring

theorem traceFreePairWeight_second_moment
    (hF : Not (ringChar F = 2)) (h : F) (hh : Not (h = 0))
    (hq : 5 <= (Fintype.card F : Real)) :
    (1 / (Fintype.card F : Real)) *
      (Finset.univ.sum fun c : F => (traceFreePairWeight c h) ^ 2) =
      1 + 2 / ((Fintype.card F : Real) - 3) -
        2 * (1 + ((quadraticChar F) (-1) : Real)) /
          ((Fintype.card F : Real) * ((Fintype.card F : Real) - 3) ^ 2) := by
  let q : Real := Fintype.card F
  have hq0 : Not (q = 0) := ne_of_gt (by dsimp [q]; linarith only [hq])
  have hq3 : Not (q - 3 = 0) := ne_of_gt (by dsimp [q]; linarith only [hq])
  have hi := sum_traceFreePairNumerator_square hF h hh
  have hs :
      (Finset.univ.sum fun c : F => (traceFreePairNumerator c h : Real) ^ 2) =
        q * (q - 3) ^ 2 + 2 * q * (q - 3) -
          2 * (1 + ((quadraticChar F) (-1) : Real)) := by
    dsimp [q]
    exact_mod_cast hi
  change (1 / q) *
    (Finset.univ.sum fun c : F => ((traceFreePairNumerator c h : Real) / (q - 3)) ^ 2) =
      1 + 2 / (q - 3) -
        2 * (1 + ((quadraticChar F) (-1) : Real)) / (q * (q - 3) ^ 2)
  simp only [div_eq_mul_inv, mul_pow]
  rw [<- Finset.sum_mul, hs]
  generalize hz : q - 3 = z
  have hz0 : Not (z = 0) := by rw [<- hz]; exact hq3
  field_simp [hq0, hz0] <;> rw [<- hz] <;> ring

theorem sum_twistTaggedPairCount
    (hF : Not (ringChar F = 2)) (h t : F)
    (hh : Not (h = 0)) (ht : Not (t = 0)) (hchi : (quadraticChar F) t = -1) :
    2 * (Finset.univ.sum fun c : F =>
      monicQuadraticPairCount c h + monicQuadraticPairCount (t * c) (t * h)) =
        (Fintype.card F : Int) * ((Fintype.card F : Int) - 3) := by
  have hp (c : F) := traceFreePairNumerator_eq_twist_counts hF c h t hh ht hchi
  have hs := sum_traceFreePairNumerator hF h hh
  simp_rw [hp] at hs
  rw [<- Finset.mul_sum] at hs
  exact hs

theorem traceFreePairWeight_eq_tagged_law
    (hF : Not (ringChar F = 2)) (c h t : F)
    (hh : Not (h = 0)) (ht : Not (t = 0)) (hchi : (quadraticChar F) t = -1)
    (hq : 5 <= (Fintype.card F : Real)) :
    traceFreePairWeight c h =
      (Fintype.card F : Real) *
        ((monicQuadraticPairCount c h : Real) +
          (monicQuadraticPairCount (t * c) (t * h) : Real)) /
        (Finset.univ.sum fun z : F =>
          (monicQuadraticPairCount z h : Real) +
            (monicQuadraticPairCount (t * z) (t * h) : Real)) := by
  let q : Real := Fintype.card F
  let C : Real := (monicQuadraticPairCount c h : Real) +
    (monicQuadraticPairCount (t * c) (t * h) : Real)
  let S : Real := Finset.univ.sum (fun z : F =>
    (monicQuadraticPairCount z h : Real) +
      (monicQuadraticPairCount (t * z) (t * h) : Real))
  have hi := sum_twistTaggedPairCount hF h t hh ht hchi
  have hs : 2 * S = q * (q - 3) := by
    dsimp [S, q]
    exact_mod_cast hi
  have hS : S = q * (q - 3) / 2 := by linarith only [hs]
  have hq0 : Not (q = 0) := ne_of_gt (by dsimp [q]; linarith only [hq])
  have hq3 : Not (q - 3 = 0) := ne_of_gt (by dsimp [q]; linarith only [hq])
  rw [traceFreePairWeight_eq_twist_counts hF c h t hh ht hchi]
  change 2 * C / (q - 3) = q * C / S
  rw [hS]
  generalize hz : q - 3 = z
  have hz0 : Not (z = 0) := by rw [<- hz]; exact hq3
  field_simp [hq0, hz0] <;> ring

end FiniteField
