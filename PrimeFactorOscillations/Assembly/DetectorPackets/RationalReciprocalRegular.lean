/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/

import PrimeFactorOscillations.Assembly.DetectorPackets.RationalInverseLine

/-!
# RationalReciprocalRegular

Maintained extraction of completed detector/packet proof components.
All original theorem hypotheses and retained proof bodies are preserved.
This module alone asserts no improved zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false

/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described by LICENSE.
Authors: Prime Factor Oscillations contributors
-/


noncomputable section
open scoped BigOperators Classical
open PrimeFactorOscillations.PeriodicCompanion

namespace PrimeFactorOscillations.RationalInverseLine

theorem principal_value_re_nonneg {q : Nat} (a : ZMod q) :
    0 <= ((1 : DirichletCharacter Complex q) a).re := by
  by_cases h : IsUnit a
  . rw [MulChar.one_apply h]
    norm_num
  . rw [MulChar.map_nonunit _ h]
    norm_num

theorem principal_mean_ne_zero (q : Nat) (hq : 0 < q) :
    Not (mean (characterSequence (1 : DirichletCharacter Complex q)) q = 0) := by
  have hre : (blockPrefix (characterSequence (1 : DirichletCharacter Complex q)) q).re =
      (Finset.range q).sum
        (fun n => (characterSequence (1 : DirichletCharacter Complex q) n).re) := by
    exact map_sum Complex.reCLM _ _
  have hsum : 1 <=
      (blockPrefix (characterSequence (1 : DirichletCharacter Complex q)) q).re := by
    rw [hre]
    calc
      _ = (characterSequence (1 : DirichletCharacter Complex q) 0).re := by
        simp [characterSequence]
      _ <= _ := Finset.single_le_sum
        (fun n _ => principal_value_re_nonneg ((n + 1 : Nat) : ZMod q))
        (Finset.mem_range.mpr hq)
  have hq0 : Not ((q : Complex) = 0) := by exact_mod_cast Nat.ne_of_gt hq
  intro hm
  change blockPrefix (characterSequence (1 : DirichletCharacter Complex q)) q /
    (q : Complex) = 0 at hm
  cases (div_eq_zero_iff).mp hm with
  | inl hn =>
    rw [hn] at hsum
    norm_num at hsum
  | inr hd => exact hq0 hd

def rationalRegularizedL {q : Nat} (chi : DirichletCharacter Complex q)
    (s : Complex) : Complex :=
  mean (characterSequence chi) q * s +
    (s - 1) * s * errorMellin (characterSequence chi) q s

theorem rationalRegularizedL_differentiableAt {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : 0 < q)
    (s : Complex) (hs : 0 < s.re) :
    DifferentiableAt Complex (rationalRegularizedL chi) s := by
  exact ((differentiableAt_const (mean (characterSequence chi) q)).mul
    differentiableAt_id).add
    (((differentiableAt_id.sub_const 1).mul differentiableAt_id).mul
      (errorMellin_differentiableAt (characterSequence chi) q hq
        (characterSequence_periodic chi) (characterSequence_norm_le chi) s hs))

theorem rationalRegularizedL_eq {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : 0 < q)
    (s : Complex) (hs : 0 < s.re) (hs1 : Not (s = 1)) :
    letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
    rationalRegularizedL chi s = (s - 1) * DirichletCharacter.LFunction chi s := by
  letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
  rw [<- companionContinuation_eq_LFunction chi hq s hs hs1]
  unfold rationalRegularizedL companionContinuation
  field_simp [sub_ne_zero.mpr hs1]
  <;> ring

theorem rationalRegularizedL_one {q : Nat} (chi : DirichletCharacter Complex q) :
    rationalRegularizedL chi 1 = mean (characterSequence chi) q := by
  simp [rationalRegularizedL]

def regularizedInverse {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    (s : Complex) : Complex :=
  if chi = 1 then (s - 1) / rationalRegularizedL chi s
  else Inv.inv (DirichletCharacter.LFunction chi s)

theorem regularizedInverse_eq_inv {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : 0 < q)
    (s : Complex) (hs : 0 < s.re) (hs1 : Not (s = 1)) :
    letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
    regularizedInverse chi s = Inv.inv (DirichletCharacter.LFunction chi s) := by
  letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
  unfold regularizedInverse
  split_ifs
  . rw [rationalRegularizedL_eq chi hq s hs hs1]
    rw [div_mul_eq_div_div, div_self (sub_ne_zero.mpr hs1), one_div]
  . rfl

theorem regularizedInverse_principal_one {q : Nat} (hq : 0 < q) :
    letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
    regularizedInverse (1 : DirichletCharacter Complex q) 1 = 0 := by
  letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
  simp [regularizedInverse]

theorem principal_regularizedL_ne_zero {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : 0 < q) (hchi : chi = 1)
    (s : Complex) (hs : (7 / 8 : Real) < s.re) :
    Not (rationalRegularizedL chi s = 0) := by
  letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
  by_cases hs1 : s = 1
  . rw [hs1, hchi, rationalRegularizedL_one]
    exact principal_mean_ne_zero q hq
  . rw [rationalRegularizedL_eq chi hq s (by linarith) hs1]
    exact mul_ne_zero (sub_ne_zero.mpr hs1)
      (OAI.SevenEighths.ProbeFinalAssemblyUnconditional.dirichlet_nonzero
        q (Nat.ne_of_gt hq) chi s hs (fun h => hs1 h.2))

theorem regularizedInverse_differentiableAt {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : 0 < q)
    (s : Complex) (hs : (7 / 8 : Real) < s.re) :
    letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
    DifferentiableAt Complex (regularizedInverse chi) s := by
  letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
  by_cases hchi : chi = 1
  . have heq : regularizedInverse chi =
        (fun z : Complex => (z - 1) / rationalRegularizedL chi z) := by
      funext z
      simp only [regularizedInverse, ite_eq_left hchi]
    rw [heq]
    exact (differentiableAt_id.sub_const 1).div
      (rationalRegularizedL_differentiableAt chi hq s (by linarith))
      (principal_regularizedL_ne_zero chi hq hchi s hs)
  . have heq : regularizedInverse chi =
        (fun z : Complex => Inv.inv (DirichletCharacter.LFunction chi z)) := by
      funext z
      simp only [regularizedInverse, ite_eq_right hchi]
    rw [heq]
    exact (chi.differentiableAt_LFunction s (Or.inr hchi)).inv
      (OAI.SevenEighths.ProbeFinalAssemblyUnconditional.dirichlet_nonzero
        q (Nat.ne_of_gt hq) chi s hs (fun h => hchi h.1))

theorem dirichlet_LFunction_high_strip_bound {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : 0 < q)
    (a : Real) (ha : 0 < a) (s : Complex)
    (hlo : a <= s.re) (hhi : s.re <= 2) (ht : 1 <= abs s.im) :
    letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
    norm (DirichletCharacter.LFunction chi s) <=
      (3 * (1 + (2 * (q : Real) + 1) / a)) * (1 + s.im ^ 2) := by
  letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
  have hre : 0 < s.re := ha.trans_le hlo
  have hs1 : Not (s = 1) := by
    intro he
    rw [he] at ht
    norm_num at ht
  have hden : 1 <= norm (s - 1) := by
    calc
      _ <= abs (s - 1).im := by simpa only [Complex.sub_im, Complex.one_im, sub_zero] using ht
      _ <= _ := Complex.abs_im_le_norm _
  have hrecip : 1 / norm (s - 1) <= 1 := by
    simpa only [div_one] using
      one_div_le_one_div_of_le (show (0 : Real) < 1 by norm_num) hden
  have hfrac : (2 * (q : Real) + 1) / s.re <= (2 * (q : Real) + 1) / a :=
    div_le_div_of_nonneg_left (by positivity) ha hlo
  have hsform : s = (s.re : Complex) + (s.im : Complex) * Complex.I := by
    apply Complex.ext <;> simp
  have hn : norm s <= s.re + abs s.im := by
    calc
      _ = norm ((s.re : Complex) + (s.im : Complex) * Complex.I) := congrArg norm hsform
      _ <= norm (s.re : Complex) + norm ((s.im : Complex) * Complex.I) := norm_add_le _ _
      _ = _ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
          mul_one, abs_of_pos hre]
  have habs : abs s.im <= 1 + s.im ^ 2 := by
    nlinarith [sq_abs s.im, sq_nonneg (abs s.im - (1 / 2 : Real))]
  have hn3 : norm s <= 3 * (1 + s.im ^ 2) := by
    apply hn.trans
    nlinarith [sq_nonneg s.im]
  calc
    _ <= norm s * (1 / norm (s - 1) + (2 * (q : Real) + 1) / s.re) :=
      dirichlet_LFunction_norm_bound chi hq s hre hs1
    _ <= norm s * (1 + (2 * (q : Real) + 1) / a) :=
      mul_le_mul_of_nonneg_left (add_le_add hrecip hfrac) (norm_nonneg _)
    _ <= (3 * (1 + s.im ^ 2)) * (1 + (2 * (q : Real) + 1) / a) :=
      mul_le_mul_of_nonneg_right hn3 (by positivity)
    _ = _ := by ring

theorem regularizedInverse_high_strip_bound {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : 0 < q)
    (a : Real) (ha : (7 / 8 : Real) < a) :
    letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
    Exists (fun K : Real => 0 <= K /\ forall s : Complex,
      a <= s.re -> s.re <= 2 -> 1 <= abs s.im ->
      norm (regularizedInverse chi s) <= K * (1 + s.im ^ 2) ^ 2) := by
  letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
  have hbeta : OAI.SevenEighths.HeckeZeroSupremum.beta <= (7 / 8 : Real) :=
    OAI.SevenEighths.HeckeCommonProbe.beta_le_seven_eighths
      (OAI.SevenEighths.ProbeFinalAssembly.common_probe_of_chosen_moments
        (OAI.SevenEighths.ProbeFinalAssemblyCertifiedBands.chosen_moments_of_certified
          OAI.SevenEighths.ProbeFinalAssemblyUnconditional.detector_certified_bands))
  let eta := OAI.SevenEighths.HeckeDirichlet.character chi
  choose C hC using OAI.SevenEighths.HeckeReciprocalGrowth.polynomial_reciprocal_bound
    eta a (hbeta.trans_lt ha)
  have ha0 : 0 < a := by linarith
  let K0 : Real := 3 * (1 + (2 * ((q * 3 : Nat) : Real) + 1) / a)
  have hK0 : 0 <= K0 := by dsimp [K0]; positivity
  refine Exists.intro (K0 * C) (And.intro (mul_nonneg hK0 hC.1) ?_)
  intro s hlo hhi ht
  have hre : 0 < s.re := ha0.trans_le hlo
  have hs0 : Not (s = 0) := by
    intro he
    rw [he] at hre
    norm_num at hre
  have hs1 : Not (s = 1) := by
    intro he
    rw [he] at ht
    norm_num at ht
  rw [regularizedInverse_eq_inv chi hq s hre hs1,
    dirichlet_inverse_eq_baseChange_product chi hq s
      (hbeta.trans_lt (ha.trans_le hlo)) hs0 hs1, norm_mul]
  have hp := dirichlet_LFunction_high_strip_bound
    (OAI.ShortDraftHeckeBridge.baseChangeChar chi)
    (Nat.mul_pos hq (by norm_num)) a ha0 s hlo hhi ht
  have hi := hC.2 s hlo
  rw [sq_abs] at hi
  calc
    _ <= (K0 * (1 + s.im ^ 2)) * (C * (1 + s.im ^ 2)) :=
      mul_le_mul hp hi (norm_nonneg _) (mul_nonneg hK0 (by positivity))
    _ = _ := by ring

theorem regularizedInverse_strip_bound {q : Nat}
    (chi : DirichletCharacter Complex q) (hq : 0 < q)
    (a : Real) (ha : (7 / 8 : Real) < a) :
    letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
    Exists (fun K : Real => 0 <= K /\ forall s : Complex,
      a <= s.re -> s.re <= 2 ->
      norm (regularizedInverse chi s) <= K * (1 + s.im ^ 2) ^ 2) := by
  letI : NeZero q := NeZero.mk (Nat.ne_of_gt hq)
  let S : Set Complex := Inter.inter (Metric.closedBall (0 : Complex) 3)
    (fun s => a <= s.re)
  have hcompact : IsCompact S :=
    (isCompact_closedBall (0 : Complex) 3).inter_right
      (isClosed_le continuous_const Complex.continuous_re)
  have hcont : ContinuousOn (regularizedInverse chi) S := by
    intro s hs
    exact (regularizedInverse_differentiableAt chi hq s
      (ha.trans_le hs.2)).continuousAt.continuousWithinAt
  choose C hC using hcompact.exists_bound_of_continuousOn hcont
  choose K hK using regularizedInverse_high_strip_bound chi hq a ha
  have hCpos : 0 <= max 0 C := le_max_left _ _
  refine Exists.intro (K + max 0 C) (And.intro (add_nonneg hK.1 hCpos) ?_)
  intro s hlo hhi
  by_cases ht : 1 <= abs s.im
  . calc
      _ <= K * (1 + s.im ^ 2) ^ 2 := hK.2 s hlo hhi ht
      _ <= _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCpos) (sq_nonneg _)
  . have hre : 0 < s.re := by linarith
    have htim : abs s.im <= 1 := (lt_of_not_ge ht).le
    have hsform : s = (s.re : Complex) + (s.im : Complex) * Complex.I := by
      apply Complex.ext <;> simp
    have hn : norm s <= s.re + abs s.im := by
      calc
        _ = norm ((s.re : Complex) + (s.im : Complex) * Complex.I) := congrArg norm hsform
        _ <= norm (s.re : Complex) + norm ((s.im : Complex) * Complex.I) := norm_add_le _ _
        _ = _ := by
          simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
            mul_one, abs_of_pos hre]
    have hmem : Membership.mem S s := by
      refine And.intro ?_ hlo
      change dist s 0 <= 3
      rw [dist_zero_right]
      exact hn.trans (by linarith)
    have hp : 1 <= (1 + s.im ^ 2) ^ 2 := by nlinarith [sq_nonneg s.im]
    calc
      _ <= C := hC s hmem
      _ <= max 0 C := le_max_right _ _
      _ = max 0 C * 1 := by ring
      _ <= max 0 C * (1 + s.im ^ 2) ^ 2 := mul_le_mul_of_nonneg_left hp hCpos
      _ <= (K + max 0 C) * (1 + s.im ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hK.1) (sq_nonneg _)

end PrimeFactorOscillations.RationalInverseLine
