/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelArithmeticUnit
import PrimeFactorOscillations.Assembly.DetectorPackets.DirichletCompanionIdentity
import PrimeFactorOscillations.Helpers.LPFPhaseVariation

/-!
# Cancellation in the actual plain companion

These estimates concern the plain Dirichlet companion in the exact native
inverse convolution. Prime powers are retained. Complete character periods
cancel before a remainder is estimated. The long native sector remains open.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.CarmichaelCompanionCancellation
open scoped Classical
open PeriodicCompanion

private theorem natCast_sum {q : Nat} [NeZero q]
    (psi : DirichletCharacter Complex q) :
    (Finset.range q).sum (fun n => psi (n : ZMod q)) =
      Finset.univ.sum psi := by
  classical
  refine Finset.sum_bij (fun n _ => (n : ZMod q)) ?_ ?_ ?_ ?_
  . intro n hn
    exact Finset.mem_univ _
  . intro n hn m hm he
    have hv := congrArg (fun x : ZMod q => x.val) he
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hn),
      Nat.mod_eq_of_lt (Finset.mem_range.mp hm)] using hv
  . intro x _
    exact Exists.intro x.val
      (Exists.intro (Finset.mem_range.mpr x.val_lt) (ZMod.natCast_zmod_val x))
  . intro n _
    rfl

private theorem nonprincipal_block_zero {q : Nat} [NeZero q]
    (psi : DirichletCharacter Complex q) (hpsi : Not (psi = 1)) :
    blockPrefix (characterSequence psi) q = 0 := by
  have hz : (Finset.range q).sum (fun n => psi (n : ZMod q)) = 0 :=
    (natCast_sum psi).trans (MulChar.sum_eq_zero_of_ne_one hpsi)
  have h1 := Finset.sum_range_succ' (fun n : Nat => psi (n : ZMod q)) q
  have h2 := Finset.sum_range_succ (fun n : Nat => psi (n : ZMod q)) q
  have hq : psi (q : ZMod q) = psi (0 : ZMod q) := by simp
  rw [hq] at h2
  have he := h1.symm.trans h2
  have hc :
      (Finset.range q).sum (fun n => psi ((n + 1 : Nat) : ZMod q)) =
        (Finset.range q).sum (fun n => psi (n : ZMod q)) := by
    apply add_right_cancel (b := psi (0 : ZMod q))
    simpa only [Nat.cast_zero] using he
  exact hc.trans hz

theorem nonprincipal_prefix_bound {q : Nat} [NeZero q]
    (psi : DirichletCharacter Complex q) (hpsi : Not (psi = 1)) (N : Nat) :
    norm ((Finset.Icc 1 N).sum (fun n => psi (n : ZMod q))) <= (q : Real) := by
  rw [character_sum_Icc_eq_blockPrefix]
  simpa only [mul_one] using
    periodic_zero_block_prefix_bound (characterSequence psi) q
      (Nat.pos_of_ne_zero (NeZero.ne q)) (characterSequence_periodic psi)
      (nonprincipal_block_zero psi hpsi) 1 (by norm_num)
      (characterSequence_norm_le psi) N

def progression {q : Nat} (psi : DirichletCharacter Complex q)
    (k N : Nat) : Complex :=
  (Finset.Icc 1 N).sum (fun n => if Dvd.dvd k n then psi (n : ZMod q) else 0)

theorem progression_eq {q : Nat} (psi : DirichletCharacter Complex q) (k N : Nat) :
    progression psi k N =
      psi (k : ZMod q) *
        (Finset.Icc 1 (N / k)).sum (fun n => psi (n : ZMod q)) := by
  classical
  by_cases hk : k = 0
  . subst k
    unfold progression
    rw [Nat.div_zero]
    simp only [Finset.Icc_eq_empty_of_lt (by omega : (0 : Nat) < 1),
      Finset.sum_empty, mul_zero]
    apply Finset.sum_eq_zero
    intro n hn
    have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
    have hnd : Not (Dvd.dvd 0 n) := by
      intro hd
      have hz : n = 0 := zero_dvd_iff.mp hd
      omega
    simp only [ite_eq_right hnd]
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  unfold progression
  rw [<- Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_bij (fun n _ => n / k) ?_ ?_ ?_ ?_
  . intro n hn
    have hmem := Finset.mem_filter.mp hn
    have hnmem := Finset.mem_Icc.mp hmem.1
    apply Finset.mem_Icc.mpr
    exact And.intro
      (Nat.div_pos (Nat.le_of_dvd hnmem.1 hmem.2) hkpos)
      (Nat.div_le_div_right hnmem.2)
  . intro n hn m hm he
    have hnd := (Finset.mem_filter.mp hn).2
    have hmd := (Finset.mem_filter.mp hm).2
    calc
      n = n / k * k := (Nat.div_mul_cancel hnd).symm
      _ = m / k * k := congrArg (fun t : Nat => t * k) he
      _ = m := Nat.div_mul_cancel hmd
  . intro t ht
    have htm := Finset.mem_Icc.mp ht
    have htn : Membership.mem (Finset.Icc 1 N) (t * k) := by
      apply Finset.mem_Icc.mpr
      exact And.intro (Nat.mul_pos htm.1 hkpos)
        ((Nat.le_div_iff_mul_le hkpos).mp htm.2)
    have hdk : Dvd.dvd k (t * k) := Exists.intro t (Nat.mul_comm t k)
    exact Exists.intro (t * k)
      (Exists.intro (Finset.mem_filter.mpr (And.intro htn hdk))
        (Nat.mul_div_cancel t hkpos))
  . intro n hn
    have hd := (Finset.mem_filter.mp hn).2
    calc
      psi (n : ZMod q) = psi ((n / k * k : Nat) : ZMod q) := by
        rw [Nat.div_mul_cancel hd]
      _ = psi (n / k : ZMod q) * psi (k : ZMod q) := by
        rw [Nat.cast_mul, map_mul]
      _ = psi (k : ZMod q) * psi (n / k : ZMod q) := mul_comm _ _

theorem progression_bound {q : Nat} [NeZero q]
    (psi : DirichletCharacter Complex q) (hpsi : Not (psi = 1)) (k N : Nat) :
    norm (progression psi k N) <= (q : Real) := by
  rw [progression_eq, norm_mul]
  calc
    _ <= 1 * (q : Real) :=
      mul_le_mul (psi.norm_le_one _) (nonprincipal_prefix_bound psi hpsi (N / k))
        (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

def maskedProgression {q : Nat} (psi : DirichletCharacter Complex q)
    (H k N : Nat) : Complex :=
  (Finset.Icc 1 N).sum (fun n => if Dvd.dvd k n then
    (if Nat.Coprime n H then psi (n : ZMod q) else 0) else 0)

theorem masked_progression_identity {q : Nat}
    (psi : DirichletCharacter Complex q) (H k N : Nat) (hH : 0 < H) :
    maskedProgression psi H k N =
      H.divisors.sum (fun e => (ArithmeticFunction.moebius e : Complex) *
        progression psi (Nat.lcm k e) N) := by
  classical
  unfold maskedProgression progression
  calc
    _ = (Finset.Icc 1 N).sum (fun n => H.divisors.sum (fun e =>
        (ArithmeticFunction.moebius e : Complex) *
          (if Dvd.dvd (Nat.lcm k e) n then psi (n : ZMod q) else 0))) := by
      apply Finset.sum_congr rfl
      intro n _
      have hf :
          (if Dvd.dvd k n then
            (if Nat.Coprime n H then psi (n : ZMod q) else 0) else 0) =
          (if Nat.Coprime n H then (1 : Complex) else 0) *
            (if Dvd.dvd k n then psi (n : ZMod q) else 0) := by
        by_cases hd : Dvd.dvd k n <;> by_cases hc : Nat.Coprime n H
        all_goals simp [hd, hc]
      rw [hf, IntegerQuadraticMask.coprime_mask H n hH, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _
      by_cases hk : Dvd.dvd k n <;> by_cases he : Dvd.dvd e n
      all_goals simp [Nat.lcm_dvd_iff, hk, he]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.mul_sum]

private theorem moebius_norm_le_one (n : Nat) :
    norm (ArithmeticFunction.moebius n : Complex) <= 1 := by
  calc
    _ = ((abs (ArithmeticFunction.moebius n) : Int) : Real) := by simp
    _ <= 1 := by exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))

theorem masked_progression_bound {q : Nat} [NeZero q]
    (psi : DirichletCharacter Complex q) (hpsi : Not (psi = 1))
    (H k N : Nat) (hH : 0 < H) :
    norm (maskedProgression psi H k N) <=
      (H.divisors.card : Real) * (q : Real) := by
  rw [masked_progression_identity psi H k N hH]
  calc
    _ <= H.divisors.sum (fun e =>
        norm ((ArithmeticFunction.moebius e : Complex) *
          progression psi (Nat.lcm k e) N)) := norm_sum_le _ _
    _ <= H.divisors.sum (fun _ => (q : Real)) := by
      apply Finset.sum_le_sum
      intro e _
      rw [norm_mul]
      calc
        _ <= 1 * (q : Real) :=
          mul_le_mul (moebius_norm_le_one e)
            (progression_bound psi hpsi (Nat.lcm k e) N)
            (norm_nonneg _) (by norm_num)
        _ = _ := one_mul _
    _ = _ := by simp

def maskedCharacter {q : Nat} (psi : DirichletCharacter Complex q)
    (H n : Nat) : Complex :=
  if Nat.Coprime n H then psi (n : ZMod q) else 0

def companionPacket {q : Nat} (psi : DirichletCharacter Complex q)
    (H K B C : Nat) : Complex :=
  (Finset.Icc 1 B).sum (fun n => (Finset.Icc 1 C).sum (fun m =>
    if Nat.Coprime n m then
      maskedCharacter psi H n * star (maskedCharacter psi K m) else 0))

private theorem rectangular_coprime_identity (F G : Nat -> Complex) (B C : Nat) :
    (Finset.Icc 1 B).sum (fun n => (Finset.Icc 1 C).sum (fun m =>
      if Nat.Coprime n m then F n * star (G m) else 0)) =
      (Finset.range (B + 1)).sum (fun k =>
        (ArithmeticFunction.moebius k : Complex) *
          (Finset.Icc 1 B).sum (fun n => if Dvd.dvd k n then F n else 0) *
            star ((Finset.Icc 1 C).sum
              (fun m => if Dvd.dvd k m then G m else 0))) := by
  classical
  calc
    _ = (Finset.Icc 1 B).sum (fun n => (Finset.Icc 1 C).sum (fun m =>
        (Finset.range (B + 1)).sum (fun k =>
          (ArithmeticFunction.moebius k : Complex) *
            (if Dvd.dvd k n then F n else 0) *
              star (if Dvd.dvd k m then G m else 0)))) := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m _
      have hmask :
          (if Nat.Coprime n m then (1 : Complex) else 0) =
          (Finset.range (B + 1)).sum (fun k =>
            (ArithmeticFunction.moebius k : Complex) *
              (if And (Dvd.dvd k n) (Dvd.dvd k m) then 1 else 0)) := by
        simpa only [Nat.coprime_comm, and_comm] using
          CoprimeDivisorKernel.coprime_range_mask B m n
            (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2
      have hf :
          (if Nat.Coprime n m then
            F n * star (G m) else 0) =
          (if Nat.Coprime n m then (1 : Complex) else 0) * (F n * star (G m)) := by
        by_cases hc : Nat.Coprime n m <;> simp [hc]
      rw [hf, hmask, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hn : Dvd.dvd k n <;> by_cases hm : Dvd.dvd k m
      all_goals simp [hn, hm, mul_assoc]
    _ = (Finset.range (B + 1)).sum (fun k =>
        (Finset.Icc 1 B).sum (fun n => (Finset.Icc 1 C).sum (fun m =>
          (ArithmeticFunction.moebius k : Complex) *
            (if Dvd.dvd k n then F n else 0) *
              star (if Dvd.dvd k m then G m else 0)))) := by
      conv_lhs =>
        arg 2
        ext n
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      have hstar :
          star ((Finset.Icc 1 C).sum (fun m => if Dvd.dvd k m then G m else 0)) =
            (Finset.Icc 1 C).sum (fun m =>
              star (if Dvd.dvd k m then G m else 0)) := by simp
      rw [hstar]
      simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]

theorem coprime_companion_identity {q : Nat}
    (psi : DirichletCharacter Complex q) (H K B C : Nat) :
    companionPacket psi H K B C =
      (Finset.range (B + 1)).sum (fun k =>
        (ArithmeticFunction.moebius k : Complex) *
          maskedProgression psi H k B * star (maskedProgression psi K k C)) :=
  rectangular_coprime_identity
    (maskedCharacter psi H) (maskedCharacter psi K) B C

theorem coprime_companion_bound_left {q : Nat} [NeZero q]
    (psi : DirichletCharacter Complex q) (hpsi : Not (psi = 1))
    (H K B C : Nat) (hH : 0 < H) (hK : 0 < K) :
    norm (companionPacket psi H K B C) <=
      ((B + 1 : Nat) : Real) *
        ((H.divisors.card : Real) * (q : Real)) *
          ((K.divisors.card : Real) * (q : Real)) := by
  rw [coprime_companion_identity]
  let L : Real := (H.divisors.card : Real) * (q : Real)
  let R : Real := (K.divisors.card : Real) * (q : Real)
  have hL : 0 <= L := by positivity
  have hR : 0 <= R := by positivity
  calc
    _ <= (Finset.range (B + 1)).sum (fun k =>
        norm ((ArithmeticFunction.moebius k : Complex) *
          maskedProgression psi H k B * star (maskedProgression psi K k C))) :=
      norm_sum_le _ _
    _ <= (Finset.range (B + 1)).sum (fun _ => L * R) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul, norm_mul, norm_star]
      calc
        _ <= (1 * L) * R :=
          mul_le_mul
            (mul_le_mul (moebius_norm_le_one k)
              (masked_progression_bound psi hpsi H k B hH)
              (norm_nonneg _) (by norm_num))
            (masked_progression_bound psi hpsi K k C hK)
            (norm_nonneg _) (by positivity)
        _ = L * R := by ring
    _ = _ := by simp [L, R, mul_assoc]

private theorem rectangular_star (F G : Nat -> Complex) (B C : Nat) :
    star ((Finset.Icc 1 B).sum (fun n => (Finset.Icc 1 C).sum (fun m =>
      if Nat.Coprime n m then F n * star (G m) else 0))) =
      (Finset.Icc 1 C).sum (fun m => (Finset.Icc 1 B).sum (fun n =>
        if Nat.Coprime m n then G m * star (F n) else 0)) := by
  classical
  have hstar (s : Finset Nat) (f : Nat -> Complex) :
      star (s.sum f) = s.sum (fun n => star (f n)) := by simp
  rw [hstar]
  simp_rw [hstar]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro n _
  by_cases hc : Nat.Coprime n m
  . have hcm : Nat.Coprime m n := hc.symm
    rw [ite_eq_left hc, ite_eq_left hcm]
    simp only [star_mul, star_star]
  . have hcm : Not (Nat.Coprime m n) := fun h => hc h.symm
    rw [ite_eq_right hc, ite_eq_right hcm, star_zero]

theorem companionPacket_star {q : Nat}
    (psi : DirichletCharacter Complex q) (H K B C : Nat) :
    star (companionPacket psi H K B C) = companionPacket psi K H C B :=
  rectangular_star (maskedCharacter psi H) (maskedCharacter psi K) B C

theorem coprime_companion_bound {q : Nat} [NeZero q]
    (psi : DirichletCharacter Complex q) (hpsi : Not (psi = 1))
    (H K B C : Nat) (hH : 0 < H) (hK : 0 < K) :
    norm (companionPacket psi H K B C) <=
      ((min B C + 1 : Nat) : Real) *
        ((H.divisors.card : Real) * (q : Real)) *
          ((K.divisors.card : Real) * (q : Real)) := by
  by_cases hBC : B <= C
  . simpa only [min_eq_left hBC] using
      coprime_companion_bound_left psi hpsi H K B C hH hK
  . have hCB : C <= B := Nat.le_of_lt (Nat.lt_of_not_ge hBC)
    have he : norm (companionPacket psi H K B C) =
        norm (companionPacket psi K H C B) := by
      rw [<- companionPacket_star, norm_star]
    rw [he, min_eq_right hCB]
    calc
      _ <= ((C + 1 : Nat) : Real) *
          ((K.divisors.card : Real) * (q : Real)) *
            ((H.divisors.card : Real) * (q : Real)) :=
        coprime_companion_bound_left psi hpsi K H C B hK hH
      _ = _ := by ring

private theorem sum_Icc_one_eq_range (f : Nat -> Complex) (N : Nat) :
    (Finset.Icc 1 N).sum f = (Finset.range N).sum (fun i => f (i + 1)) := by
  have hset : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hset, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.add_comm]

def windowVariation (w : Nat -> Complex) (N : Nat) : Real :=
  norm (w (N - 1)) + (Finset.range (N - 1)).sum
    (fun i => norm (w (i + 1) - w i))

private theorem windowVariation_nonneg (w : Nat -> Complex) (N : Nat) :
    0 <= windowVariation w N := by
  unfold windowVariation
  positivity

def weightedMaskedProgression {q : Nat} (psi : DirichletCharacter Complex q)
    (H k N : Nat) (w : Nat -> Complex) : Complex :=
  (Finset.Icc 1 N).sum (fun n => if Dvd.dvd k n then
    w (n - 1) * maskedCharacter psi H n else 0)

theorem weighted_masked_progression_bound {q : Nat} [NeZero q]
    (psi : DirichletCharacter Complex q) (hpsi : Not (psi = 1))
    (H k N : Nat) (hH : 0 < H) (w : Nat -> Complex) :
    norm (weightedMaskedProgression psi H k N w) <=
      windowVariation w N * ((H.divisors.card : Real) * (q : Real)) := by
  let f : Nat -> Complex := fun i =>
    if Dvd.dvd k (i + 1) then maskedCharacter psi H (i + 1) else 0
  have hp : forall n, n <= N ->
      norm ((Finset.range n).sum f) <= (H.divisors.card : Real) * (q : Real) := by
    intro n _
    have he := sum_Icc_one_eq_range
      (fun t => if Dvd.dvd k t then maskedCharacter psi H t else 0) n
    rw [<- he]
    exact masked_progression_bound psi hpsi H k n hH
  have hb := LPF.norm_sum_range_mul_le_of_variation w f N
    ((H.divisors.card : Real) * (q : Real)) hp
  unfold weightedMaskedProgression
  rw [sum_Icc_one_eq_range]
  simpa only [windowVariation, f, Nat.add_sub_cancel, mul_ite, mul_zero] using hb

def weightedCompanionPacket {q : Nat} (psi : DirichletCharacter Complex q)
    (H K B C : Nat) (w v : Nat -> Complex) : Complex :=
  (Finset.Icc 1 B).sum (fun n => (Finset.Icc 1 C).sum (fun m =>
    if Nat.Coprime n m then
      (w (n - 1) * maskedCharacter psi H n) *
        star (v (m - 1) * maskedCharacter psi K m) else 0))

theorem weighted_coprime_companion_identity {q : Nat}
    (psi : DirichletCharacter Complex q) (H K B C : Nat)
    (w v : Nat -> Complex) :
    weightedCompanionPacket psi H K B C w v =
      (Finset.range (B + 1)).sum (fun k =>
        (ArithmeticFunction.moebius k : Complex) *
          weightedMaskedProgression psi H k B w *
            star (weightedMaskedProgression psi K k C v)) :=
  rectangular_coprime_identity
    (fun n => w (n - 1) * maskedCharacter psi H n)
    (fun m => v (m - 1) * maskedCharacter psi K m) B C

theorem weighted_companion_bound_left {q : Nat} [NeZero q]
    (psi : DirichletCharacter Complex q) (hpsi : Not (psi = 1))
    (H K B C : Nat) (hH : 0 < H) (hK : 0 < K) (w v : Nat -> Complex) :
    norm (weightedCompanionPacket psi H K B C w v) <=
      ((B + 1 : Nat) : Real) *
        (windowVariation w B * ((H.divisors.card : Real) * (q : Real))) *
          (windowVariation v C * ((K.divisors.card : Real) * (q : Real))) := by
  rw [weighted_coprime_companion_identity]
  let L : Real := windowVariation w B * ((H.divisors.card : Real) * (q : Real))
  let R : Real := windowVariation v C * ((K.divisors.card : Real) * (q : Real))
  have hL : 0 <= L := mul_nonneg (windowVariation_nonneg w B) (by positivity)
  have hR : 0 <= R := mul_nonneg (windowVariation_nonneg v C) (by positivity)
  calc
    _ <= (Finset.range (B + 1)).sum (fun k =>
        norm ((ArithmeticFunction.moebius k : Complex) *
          weightedMaskedProgression psi H k B w *
            star (weightedMaskedProgression psi K k C v))) := norm_sum_le _ _
    _ <= (Finset.range (B + 1)).sum (fun _ => L * R) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul, norm_mul, norm_star]
      calc
        _ <= (1 * L) * R :=
          mul_le_mul
            (mul_le_mul (moebius_norm_le_one k)
              (weighted_masked_progression_bound psi hpsi H k B hH w)
              (norm_nonneg _) (by norm_num))
            (weighted_masked_progression_bound psi hpsi K k C hK v)
            (norm_nonneg _) (by positivity)
        _ = L * R := by ring
    _ = _ := by simp [L, R, mul_assoc]

theorem weightedCompanionPacket_star {q : Nat}
    (psi : DirichletCharacter Complex q) (H K B C : Nat)
    (w v : Nat -> Complex) :
    star (weightedCompanionPacket psi H K B C w v) =
      weightedCompanionPacket psi K H C B v w :=
  rectangular_star
    (fun n => w (n - 1) * maskedCharacter psi H n)
    (fun m => v (m - 1) * maskedCharacter psi K m) B C

theorem weighted_coprime_companion_bound {q : Nat} [NeZero q]
    (psi : DirichletCharacter Complex q) (hpsi : Not (psi = 1))
    (H K B C : Nat) (hH : 0 < H) (hK : 0 < K) (w v : Nat -> Complex) :
    norm (weightedCompanionPacket psi H K B C w v) <=
      ((min B C + 1 : Nat) : Real) *
        (windowVariation w B * ((H.divisors.card : Real) * (q : Real))) *
          (windowVariation v C * ((K.divisors.card : Real) * (q : Real))) := by
  by_cases hBC : B <= C
  . simpa only [min_eq_left hBC] using
      weighted_companion_bound_left psi hpsi H K B C hH hK w v
  . have hCB : C <= B := Nat.le_of_lt (Nat.lt_of_not_ge hBC)
    have he : norm (weightedCompanionPacket psi H K B C w v) =
        norm (weightedCompanionPacket psi K H C B v w) := by
      rw [<- weightedCompanionPacket_star, norm_star]
    rw [he, min_eq_right hCB]
    calc
      _ <= ((C + 1 : Nat) : Real) *
          (windowVariation v C * ((K.divisors.card : Real) * (q : Real))) *
            (windowVariation w B * ((H.divisors.card : Real) * (q : Real))) :=
        weighted_companion_bound_left psi hpsi K H C B hK hH v w
      _ = _ := by ring

theorem cubic_companion_ne_one {q : Nat}
    (chi : DirichletCharacter Complex q) (hchi : chi ^ 3 = 1) :
    Not (OAI.ShortDraftHeckeBridge.baseChangeChar chi = 1) := by
  have heven : chi (-1) = 1 :=
    MulChar.val_neg_one_eq_one_of_odd_order (by decide : Odd (3 : Nat)) hchi
  have hcop : IsCoprime (-1 : Int) ((q * 3 : Nat) : Int) := by
    exact Exists.intro (-1) (Exists.intro 0 (by ring))
  have hbase :
      OAI.ShortDraftHeckeBridge.baseChangeChar chi (-1) =
        chi (-1) * OAI.ShortDraftHeckeBridge.chiMinusThree (-1) := by
    simp only [OAI.ShortDraftHeckeBridge.baseChangeChar, MulChar.mul_apply]
    have hleft := DirichletCharacter.changeLevel_eq_cast_of_dvd' chi
      (show Dvd.dvd q (q * 3) from Exists.intro 3 rfl) hcop
    have hright := DirichletCharacter.changeLevel_eq_cast_of_dvd'
      OAI.ShortDraftHeckeBridge.chiMinusThree
      (show Dvd.dvd 3 (q * 3) from Exists.intro q (Nat.mul_comm q 3)) hcop
    simp only [Int.cast_neg, Int.cast_one] at hleft hright
    rw [hleft, hright]
  have heps : OAI.ShortDraftHeckeBridge.chiMinusThree (-1 : ZMod 3) = -1 := by
    have hcast : (2 : ZMod 3) = -1 := by decide
    rw [<- hcast]
    exact OAI.ShortDraftHeckeBridge.chiMinusThree_mod_two 2 (by decide)
  have hvalue : OAI.ShortDraftHeckeBridge.baseChangeChar chi (-1) = -1 := by
    rw [hbase, heven, heps, one_mul]
  intro h
  rw [h, MulChar.one_apply (isUnit_one.neg)] at hvalue
  norm_num at hvalue

theorem compensated_companion_expansion {q : Nat}
    (psi : DirichletCharacter Complex q) (H K B C : Nat)
    (WA WB VA VB : Nat -> Complex) (c : Complex) :
    weightedCompanionPacket psi H K B C
        (fun n => WA n - c * WB n) (fun n => VA n - c * VB n) =
      weightedCompanionPacket psi H K B C WA VA -
        star c * weightedCompanionPacket psi H K B C WA VB -
          c * weightedCompanionPacket psi H K B C WB VA +
            (c * star c) * weightedCompanionPacket psi H K B C WB VB := by
  classical
  have hf (n m : Nat) :
      (if Nat.Coprime n m then
        ((WA (n - 1) - c * WB (n - 1)) * maskedCharacter psi H n) *
          star ((VA (m - 1) - c * VB (m - 1)) * maskedCharacter psi K m) else 0) =
      (if Nat.Coprime n m then
        (WA (n - 1) * maskedCharacter psi H n) *
          star (VA (m - 1) * maskedCharacter psi K m) else 0) -
      star c * (if Nat.Coprime n m then
        (WA (n - 1) * maskedCharacter psi H n) *
          star (VB (m - 1) * maskedCharacter psi K m) else 0) -
      c * (if Nat.Coprime n m then
        (WB (n - 1) * maskedCharacter psi H n) *
          star (VA (m - 1) * maskedCharacter psi K m) else 0) +
      (c * star c) * (if Nat.Coprime n m then
        (WB (n - 1) * maskedCharacter psi H n) *
          star (VB (m - 1) * maskedCharacter psi K m) else 0) := by
    by_cases hc : Nat.Coprime n m
    . simp only [ite_eq_left hc, star_mul, star_sub]
      ring
    . simp only [ite_eq_right hc, mul_zero, sub_zero, zero_add]
  unfold weightedCompanionPacket
  simp_rw [hf]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, <- Finset.mul_sum]

theorem pair_inverse_coeff_divisor_bound {q r : Nat}
    (chi : DirichletCharacter Complex q) (psi : DirichletCharacter Complex r)
    (n : Nat) :
    norm (OAI.ShortDraftHeckeBridge.pairInverseCoeff chi psi n) <=
      (n.divisors.card : Real) := by
  have hi {s : Nat} (eta : DirichletCharacter Complex s) (j : Nat) :
      norm (eta (j : ZMod s) * (ArithmeticFunction.moebius j : Complex)) <= 1 := by
    rw [norm_mul]
    calc
      _ <= 1 * 1 :=
        mul_le_mul (eta.norm_le_one _) (moebius_norm_le_one j)
          (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  unfold OAI.ShortDraftHeckeBridge.pairInverseCoeff
  rw [LSeries.convolution_def]
  calc
    _ <= n.divisorsAntidiagonal.sum (fun p =>
        norm ((chi (p.1 : ZMod q) * (ArithmeticFunction.moebius p.1 : Complex)) *
          (psi (p.2 : ZMod r) * (ArithmeticFunction.moebius p.2 : Complex)))) :=
      norm_sum_le _ _
    _ <= n.divisorsAntidiagonal.sum (fun _ => (1 : Real)) := by
      apply Finset.sum_le_sum
      intro p _
      rw [norm_mul]
      calc
        _ <= 1 * 1 := mul_le_mul (hi chi p.1) (hi psi p.2)
          (norm_nonneg _) (by norm_num)
        _ = _ := one_mul _
    _ = (n.divisors.card : Real) := by
      rw [Nat.sum_divisorsAntidiagonal (fun _ _ : Nat => (1 : Real))]
      simp

end PrimeFactorOscillations.CarmichaelCompanionCancellation
