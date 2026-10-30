/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.LegendreSymbol.QuadraticPairTwistEnergy
/-!
# Uniform two-character references for positive quadratic-twist averages

The exact trace-free local law has a reference with two quadratic-character
Euler factors and a squared unmarked factor. Its correction has only two
possible forms on unit character inputs. For every real q >= 5, its
absolute error is at most (143/25)/q^2, with equality at q = 5.

The actual tagged conditional count has this full factorization at every
constant, including its two forbidden residues. The completed correction
is positive with the same uniform error; no Hasse bound is used.
Every supported finite tail above N >= 4 has correction between
exp(-286/(25*N)) and exp(286/(25*N)). The complete packet comparison
retains the opening masks without division by a possibly zero packet.
No integer short-window mass estimate or zero-free theorem is asserted.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FiniteField.QuadraticPairTwistEuler
attribute [local instance] Classical.propDecidable

def correction (q a b : Real) : Real :=
  ((q - 1 + a + b) / (q - 3)) *
    (1 - 1 / q) ^ 2 * (1 - a / q) * (1 - b / q)

def correctionMinus (q : Real) : Real := (1 - 1 / q ^ 2) ^ 2

def correctionPlus (q : Real) : Real :=
  (q + 1) * (q - 1) ^ 4 / (q ^ 4 * (q - 3))

theorem correction_table (q a b : Real) (hq : 5 <= q)
    (ha : a = 1 \/ a = -1) (hb : b = 1 \/ b = -1) :
    correction q a b =
      if a = -1 /\ b = -1 then correctionMinus q else correctionPlus q := by
  have hq0 : Not (q = 0) := ne_of_gt (by linarith only [hq])
  have hq3 : Not (q - 3 = 0) := ne_of_gt (by linarith only [hq])
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> subst a <;> subst b <;>
    norm_num [correction, correctionMinus, correctionPlus] <;>
    field_simp [hq0, hq3] <;> ring

theorem correctionMinus_bounds (q : Real) (hq : 5 <= q) :
    0 < correctionMinus q /\
      |correctionMinus q - 1| <= ((143 : Real) / 25) / q ^ 2 := by
  have hq0 : 0 < q := by linarith only [hq]
  have hsq : 25 <= q ^ 2 := by nlinarith only [sq_nonneg (q - 5), hq]
  have hq4 : 0 < q ^ 4 := pow_pos hq0 4
  have ht : 0 < 1 - 1 / q ^ 2 := by
    have hd : 1 / q ^ 2 < (1 : Real) :=
      (div_lt_one (pow_pos hq0 2)).mpr (by linarith only [hsq])
    linarith only [hd]
  have hp : 0 < correctionMinus q := by
    unfold correctionMinus
    exact pow_pos ht 2
  have hid : correctionMinus q - 1 = (1 - 2 * q ^ 2) / q ^ 4 := by
    unfold correctionMinus
    field_simp [ne_of_gt hq0]
    <;> ring
  have habs : |correctionMinus q - 1| = (2 * q ^ 2 - 1) / q ^ 4 := by
    rw [hid, abs_div, abs_of_pos hq4, abs_of_neg (by linarith only [hsq])]
    congr 1
    ring
  have he : |correctionMinus q - 1| <= ((143 : Real) / 25) / q ^ 2 := by
    rw [habs]
    calc
      _ <= (((143 : Real) / 25) * q ^ 2) / q ^ 4 :=
        div_le_div_of_nonneg_right (by nlinarith only [sq_nonneg q]) (le_of_lt hq4)
      _ = _ := by field_simp [ne_of_gt hq0] <;> ring
  exact And.intro hp he

theorem correctionPlus_bounds (q : Real) (hq : 5 <= q) :
    0 < correctionPlus q /\
      |correctionPlus q - 1| <= ((143 : Real) / 25) / q ^ 2 := by
  have hq0 : 0 < q := by linarith only [hq]
  have hq3 : 0 < q - 3 := by linarith only [hq]
  have hd : 0 < q ^ 4 * (q - 3) := mul_pos (pow_pos hq0 4) hq3
  let P : Real := 2 * q ^ 3 + 2 * q ^ 2 - 3 * q + 1
  have hP : 0 < P := by
    have hx := mul_pos (show 0 < q - 1 by linarith only [hq])
      (show 0 < 2 * q ^ 2 + 4 * q + 1 by nlinarith only [sq_nonneg q, hq])
    dsimp [P]
    nlinarith only [hx]
  have hcap : P <= ((143 : Real) / 25) * q ^ 2 * (q - 3) := by
    have hquad : 0 <= 93 * q ^ 2 - 14 * q + 5 := by
      nlinarith only [sq_nonneg (q - 5), hq]
    have hprod := div_nonneg
      (mul_nonneg (show 0 <= q - 5 by linarith only [hq]) hquad)
      (show 0 <= (25 : Real) by norm_num)
    have hid : ((143 : Real) / 25) * q ^ 2 * (q - 3) - P =
        (q - 5) * (93 * q ^ 2 - 14 * q + 5) / 25 := by dsimp [P]; ring
    rw [<- hid] at hprod
    linarith only [hprod]
  have hid : correctionPlus q - 1 = P / (q ^ 4 * (q - 3)) := by
    unfold correctionPlus P
    field_simp [ne_of_gt hq0, ne_of_gt hq3]
    <;> ring
  have hp : 0 < correctionPlus q := by
    unfold correctionPlus
    exact div_pos
      (mul_pos (by linarith only [hq]) (pow_pos (by linarith only [hq]) 4)) hd
  have he : |correctionPlus q - 1| <= ((143 : Real) / 25) / q ^ 2 := by
    rw [hid, abs_div, abs_of_pos hP, abs_of_pos hd]
    calc
      _ <= (((143 : Real) / 25) * q ^ 2 * (q - 3)) / (q ^ 4 * (q - 3)) :=
        div_le_div_of_nonneg_right hcap (le_of_lt hd)
      _ = _ := by field_simp [ne_of_gt hq0, ne_of_gt hq3] <;> ring
  exact And.intro hp he

theorem correction_bounds (q a b : Real) (hq : 5 <= q)
    (ha : a = 1 \/ a = -1) (hb : b = 1 \/ b = -1) :
    0 < correction q a b /\
      |correction q a b - 1| <= ((143 : Real) / 25) / q ^ 2 := by
  rw [correction_table q a b hq ha hb]
  split_ifs
  . exact correctionMinus_bounds q hq
  . exact correctionPlus_bounds q hq

theorem correction_sharp :
    |correction (5 : Real) 1 (-1) - 1| = ((143 : Real) / 25) / 5 ^ 2 := by
  norm_num [correction]

def denominator (q a b : Real) : Real :=
  (1 - 1 / q) ^ 2 * (1 - a / q) * (1 - b / q)

def reference (q a b : Real) : Real := 1 / denominator q a b

theorem denominator_pos (q a b : Real) (hq : 5 <= q)
    (ha : a <= 1) (hb : b <= 1) : 0 < denominator q a b := by
  have hq0 : 0 < q := by linarith only [hq]
  have hi : 1 / q < (1 : Real) := (div_lt_one hq0).mpr (by linarith only [hq])
  have ha' : a / q <= 1 / q := div_le_div_of_nonneg_right ha (le_of_lt hq0)
  have hb' : b / q <= 1 / q := div_le_div_of_nonneg_right hb (le_of_lt hq0)
  unfold denominator
  exact mul_pos
    (mul_pos (pow_pos (by linarith only [hi]) 2) (by linarith only [hi, ha']))
    (by linarith only [hi, hb'])

theorem reference_pos (q a b : Real) (hq : 5 <= q)
    (ha : a <= 1) (hb : b <= 1) : 0 < reference q a b :=
  one_div_pos.mpr (denominator_pos q a b hq ha hb)

theorem reference_factorization (q a b : Real) (hq : 5 <= q)
    (ha : a <= 1) (hb : b <= 1) :
    (q - 1 + a + b) / (q - 3) = reference q a b * correction q a b := by
  have hd : Not (denominator q a b = 0) := ne_of_gt (denominator_pos q a b hq ha hb)
  have hi : correction q a b =
      ((q - 1 + a + b) / (q - 3)) * denominator q a b := by
    unfold correction denominator
    ring
  rw [hi]
  unfold reference
  have hq3 : Not (q - 3 = 0) := ne_of_gt (by linarith only [hq])
  field_simp [hd, hq3]
  <;> ring

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def characterA (c h : F) : Real := ((quadraticChar F) ((-h) * c) : Real)
def characterB (c h : F) : Real := ((quadraticChar F) (h * (c + h)) : Real)

def openingMask (c h : F) : Real :=
  if c = 0 then 0 else if c = -h then 0 else 1

def completedCorrection (c h : F) : Real :=
  if c = 0 then 1 else if c = -h then 1 else
    correction (Fintype.card F : Real) (characterA c h) (characterB c h)

theorem character_le_one (x : F) : ((quadraticChar F) x : Real) <= 1 := by
  by_cases hx : x = 0
  . simp [hx]
  . rcases QuadraticPairEuler.quadraticChar_real_signs x hx with he | he <;>
      linarith only [he]

theorem traceFreePairWeight_scalar (c h : F)
    (hc : Not (c = 0)) (hn : Not (c = -h)) :
    traceFreePairWeight c h =
      ((Fintype.card F : Real) - 1 + characterA c h + characterB c h) /
        ((Fintype.card F : Real) - 3) := by
  simp only [traceFreePairWeight, traceFreePairNumerator, ite_eq_right hc, ite_eq_right hn,
    twistPairNumerator, characterA, characterB, map_mul,
    Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_one]

theorem completedCorrection_bounds (c h : F) (hh : Not (h = 0))
    (hq : 5 <= (Fintype.card F : Real)) :
    0 < completedCorrection c h /\
      |completedCorrection c h - 1| <= ((143 : Real) / 25) / (Fintype.card F : Real) ^ 2 := by
  have hC : 0 <= ((143 : Real) / 25) / (Fintype.card F : Real) ^ 2 :=
    div_nonneg (by norm_num) (sq_nonneg _)
  unfold completedCorrection
  split_ifs with hc hn
  . exact And.intro (by norm_num) (by simpa using hC)
  . exact And.intro (by norm_num) (by simpa using hC)
  . have hch : Not (c + h = 0) := by
      intro hz
      apply hn
      calc
        c = (c + h) - h := by ring
        _ = -h := by rw [hz]; ring
    apply correction_bounds _ _ _ hq
    . exact QuadraticPairEuler.quadraticChar_real_signs ((-h) * c)
        (mul_ne_zero (neg_ne_zero.mpr hh) hc)
    . exact QuadraticPairEuler.quadraticChar_real_signs (h * (c + h))
        (mul_ne_zero hh hch)

theorem traceFreePairWeight_factorization (c h : F)
    (hq : 5 <= (Fintype.card F : Real)) :
    traceFreePairWeight c h =
      openingMask c h *
        reference (Fintype.card F : Real) (characterA c h) (characterB c h) *
        completedCorrection c h := by
  by_cases hc : c = 0
  . subst c
    simp [openingMask, completedCorrection, traceFreePairWeight_zero]
  . by_cases hn : c = -h
    . subst c
      simp [openingMask, completedCorrection, traceFreePairWeight_neg_shift]
    . rw [traceFreePairWeight_scalar c h hc hn]
      have hi := reference_factorization (Fintype.card F : Real)
        (characterA c h) (characterB c h) hq
        (character_le_one ((-h) * c)) (character_le_one (h * (c + h)))
      simpa [openingMask, completedCorrection, hc, hn] using hi

theorem tagged_law_factorization
    (hF : Not (ringChar F = 2)) (c h t : F)
    (hh : Not (h = 0)) (ht : Not (t = 0)) (hchi : (quadraticChar F) t = -1)
    (hq : 5 <= (Fintype.card F : Real)) :
    (Fintype.card F : Real) *
        ((monicQuadraticPairCount c h : Real) +
          (monicQuadraticPairCount (t * c) (t * h) : Real)) /
        (Finset.univ.sum fun z : F =>
          (monicQuadraticPairCount z h : Real) +
            (monicQuadraticPairCount (t * z) (t * h) : Real)) =
      openingMask c h *
        reference (Fintype.card F : Real) (characterA c h) (characterB c h) *
        completedCorrection c h := by
  rw [<- traceFreePairWeight_eq_tagged_law hF c h t hh ht hchi hq]
  exact traceFreePairWeight_factorization c h hq

theorem packet_factorization
    {I : Type*} [Fintype I] [DecidableEq I]
    (K : I -> Type*) [forall i, Field (K i)] [forall i, Fintype (K i)]
    [forall i, DecidableEq (K i)]
    (c h : (i : I) -> K i)
    (hq : forall i, 5 <= (Fintype.card (K i) : Real)) :
    (Finset.univ.prod fun i : I => traceFreePairWeight (c i) (h i)) =
      (Finset.univ.prod fun i : I => openingMask (c i) (h i)) *
        (Finset.univ.prod fun i : I =>
          reference (Fintype.card (K i) : Real) (characterA (c i) (h i)) (characterB (c i) (h i))) *
        (Finset.univ.prod fun i : I => completedCorrection (c i) (h i)) := by
  calc
    _ = Finset.univ.prod (fun i : I =>
        openingMask (c i) (h i) *
          reference (Fintype.card (K i) : Real) (characterA (c i) (h i)) (characterB (c i) (h i)) *
          completedCorrection (c i) (h i)) := by
      apply Finset.prod_congr rfl
      intro i _
      exact traceFreePairWeight_factorization (c i) (h i) (hq i)
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]

theorem completed_product_bounds
    (N M : Nat) (hN : 4 <= N) (hNM : N <= M)
    (T : Finset Nat) (hT : T <= Finset.Ico (N + 1) (M + 1))
    (K : Nat -> Type*) [forall n, Field (K n)] [forall n, Fintype (K n)]
    [forall n, DecidableEq (K n)]
    (c h : (n : Nat) -> K n)
    (hcard : forall n, Membership.mem T n -> Fintype.card (K n) = n)
    (hh : forall n, Membership.mem T n -> Not (h n = 0)) :
    Real.exp (-(286 / (25 * (N : Real)))) <=
        T.prod (fun n => completedCorrection (c n) (h n)) /\
      T.prod (fun n => completedCorrection (c n) (h n)) <=
        Real.exp (286 / (25 * (N : Real))) := by
  have hq (n : Nat) (hn : Membership.mem T n) : 5 <= (Fintype.card (K n) : Real) := by
    rw [hcard n hn]
    have hlo := (Finset.mem_Ico.mp (hT hn)).1
    have hi : 5 <= n := le_trans (Nat.succ_le_succ hN) hlo
    exact_mod_cast hi
  have hb (n : Nat) (hn : Membership.mem T n) :
      |completedCorrection (c n) (h n) - 1| <= ((143 : Real) / 25) / (n : Real) ^ 2 := by
    have hi := (completedCorrection_bounds (c n) (h n) (hh n hn) (hq n hn)).2
    rwa [hcard n hn] at hi
  have hs (n : Nat) (hn : Membership.mem T n) :
      ((143 : Real) / 25) / (n : Real) ^ 2 <= 1 / 2 := by
    have hn5 : 5 <= (n : Real) := by simpa only [hcard n hn] using hq n hn
    have hsq : 25 <= (n : Real) ^ 2 := by
      nlinarith only [sq_nonneg ((n : Real) - 5), hn5]
    calc
      _ <= ((143 : Real) / 25) / 25 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsq
      _ <= _ := by norm_num
  have hl := QuadraticPairEuler.log_product_tail_bound N M
    (le_trans (by decide : 1 <= 4) hN) hNM T hT
    (fun n => completedCorrection (c n) (h n)) ((143 : Real) / 25) (by norm_num) hb hs
  have hNreal : 0 < (N : Real) := by
    exact_mod_cast lt_of_lt_of_le (by decide : 0 < 4) hN
  have hl' :
      |Real.log (T.prod fun n => completedCorrection (c n) (h n))| <=
        286 / (25 * (N : Real)) := by
    convert hl using 1 <;> field_simp [ne_of_gt hNreal] <;> ring
  have hp : 0 < T.prod (fun n => completedCorrection (c n) (h n)) := by
    apply Finset.prod_pos
    intro n hn
    exact (completedCorrection_bounds (c n) (h n) (hh n hn) (hq n hn)).1
  exact QuadraticPairEuler.product_bounds_of_log_bound _ _ hp hl'

theorem complete_packet_comparison
    (N M : Nat) (hN : 4 <= N) (hNM : N <= M)
    (T : Finset Nat) (hT : T <= Finset.Ico (N + 1) (M + 1))
    (K : Nat -> Type*) [forall n, Field (K n)] [forall n, Fintype (K n)]
    [forall n, DecidableEq (K n)]
    (c h : (n : Nat) -> K n)
    (hcard : forall n, Membership.mem T n -> Fintype.card (K n) = n)
    (hh : forall n, Membership.mem T n -> Not (h n = 0)) :
    (T.prod (fun n => openingMask (c n) (h n) *
        reference (n : Real) (characterA (c n) (h n)) (characterB (c n) (h n)))) *
      Real.exp (-(286 / (25 * (N : Real)))) <=
        T.prod (fun n => traceFreePairWeight (c n) (h n)) /\
    T.prod (fun n => traceFreePairWeight (c n) (h n)) <=
      (T.prod (fun n => openingMask (c n) (h n) *
        reference (n : Real) (characterA (c n) (h n)) (characterB (c n) (h n)))) *
      Real.exp (286 / (25 * (N : Real))) := by
  let P : Real := T.prod (fun n => openingMask (c n) (h n) *
    reference (n : Real) (characterA (c n) (h n)) (characterB (c n) (h n)))
  have hq (n : Nat) (hn : Membership.mem T n) : 5 <= (n : Real) := by
    have hlo := (Finset.mem_Ico.mp (hT hn)).1
    have hi : 5 <= n := le_trans (Nat.succ_le_succ hN) hlo
    exact_mod_cast hi
  have hP : 0 <= P := by
    apply Finset.prod_nonneg
    intro n hn
    apply mul_nonneg
    . unfold openingMask
      split_ifs <;> norm_num
    . exact le_of_lt (reference_pos _ _ _ (hq n hn)
        (character_le_one ((-h n) * c n)) (character_le_one (h n * (c n + h n))))
  have hid :
      T.prod (fun n => traceFreePairWeight (c n) (h n)) =
        P * T.prod (fun n => completedCorrection (c n) (h n)) := by
    dsimp [P]
    rw [<- Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro n hn
    have hi := traceFreePairWeight_factorization (c n) (h n)
      (by simpa only [hcard n hn] using hq n hn)
    simpa only [hcard n hn] using hi
  have hb := completed_product_bounds N M hN hNM T hT K c h hcard hh
  change P * _ <= _ /\ _ <= P * _
  rw [hid]
  exact And.intro (mul_le_mul_of_nonneg_left hb.1 hP) (mul_le_mul_of_nonneg_left hb.2 hP)

end FiniteField.QuadraticPairTwistEuler
