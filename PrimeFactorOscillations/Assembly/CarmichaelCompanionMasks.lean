/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelCompanionCancellation
import PrimeFactorOscillations.Assembly.DetectorPackets.AllPrimeMaskFactorization

/-!
# Divisibility masks inside the signed plain-companion estimate

Finite Euler masks must enter as progression conditions before the variation
bound. Their jumps are not charged to the smooth compensated window.
All coprimality Mobius terms and all original prime powers are retained.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.CarmichaelCompanionMasks
open scoped Classical
open CarmichaelCompanionCancellation

/-- A divisibility mask on the positive integer stored at zero-based window index i. -/
def divisorWindow (d : Nat) (w : Nat -> Complex) (i : Nat) : Complex :=
  if Dvd.dvd d (i + 1) then w i else 0

/-- A divisor mask is exactly an lcm progression condition, including index zero. -/
theorem progression_divisor_window {q : Nat}
    (psi : DirichletCharacter Complex q) (H k N d : Nat)
    (w : Nat -> Complex) :
    weightedMaskedProgression psi H k N (divisorWindow d w) =
      weightedMaskedProgression psi H (Nat.lcm k d) N w := by
  classical
  unfold weightedMaskedProgression
  apply Finset.sum_congr rfl
  intro n hn
  have hindex : n - 1 + 1 = n := Nat.sub_add_cancel (Finset.mem_Icc.mp hn).1
  simp only [divisorWindow, hindex]
  by_cases hk : Dvd.dvd k n <;> by_cases hd : Dvd.dvd d n
  all_goals simp [Nat.lcm_dvd_iff, hk, hd]

/-- A finite linear combination of divisibility masks applied to one smooth window. -/
def divisorSumWindow (E : Finset Nat) (coeff w : Nat -> Complex)
    (i : Nat) : Complex :=
  E.sum (fun d => coeff d * divisorWindow d w i)

/-- Move every finite divisor-mask summand into its exact progression. -/
theorem progression_divisor_sum {q : Nat}
    (psi : DirichletCharacter Complex q) (H k N : Nat)
    (E : Finset Nat) (coeff w : Nat -> Complex) :
    weightedMaskedProgression psi H k N (divisorSumWindow E coeff w) =
      E.sum (fun d => coeff d *
        weightedMaskedProgression psi H (Nat.lcm k d) N w) := by
  classical
  calc
    _ = E.sum (fun d => coeff d *
        weightedMaskedProgression psi H k N (divisorWindow d w)) := by
      unfold weightedMaskedProgression divisorSumWindow
      calc
        _ = (Finset.Icc 1 N).sum (fun n => E.sum (fun d =>
            coeff d * (if Dvd.dvd k n then
              divisorWindow d w (n - 1) * maskedCharacter psi H n else 0))) := by
          apply Finset.sum_congr rfl
          intro n _
          by_cases hk : Dvd.dvd k n
          . rw [ite_eq_left hk, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro d _
            rw [ite_eq_left hk]
            ring
          . simp only [ite_eq_right hk, mul_zero, Finset.sum_const_zero]
        _ = _ := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro d _
          rw [Finset.mul_sum]
    _ = _ := by simp_rw [progression_divisor_window]

/-- Bound the full finite mask after complete-period character cancellation. -/
theorem divisor_sum_progression_bound {q : Nat} [NeZero q]
    (psi : DirichletCharacter Complex q) (hpsi : Not (psi = 1))
    (H k N : Nat) (hH : 0 < H) (E : Finset Nat)
    (coeff w : Nat -> Complex) :
    norm (weightedMaskedProgression psi H k N (divisorSumWindow E coeff w)) <=
      E.sum (fun d => norm (coeff d)) *
        windowVariation w N * ((H.divisors.card : Real) * (q : Real)) := by
  rw [progression_divisor_sum]
  calc
    _ <= E.sum (fun d => norm (coeff d *
        weightedMaskedProgression psi H (Nat.lcm k d) N w)) := norm_sum_le _ _
    _ <= E.sum (fun d => norm (coeff d) *
        (windowVariation w N * ((H.divisors.card : Real) * (q : Real)))) := by
      apply Finset.sum_le_sum
      intro d _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (weighted_masked_progression_bound psi hpsi H (Nat.lcm k d) N hH w)
        (norm_nonneg _)
    _ = _ := by rw [<- Finset.sum_mul]; ring

private theorem packet_bound_of_progressions {q : Nat}
    (psi : DirichletCharacter Complex q) (H K B C : Nat)
    (w v : Nat -> Complex) (L R : Real)
    (hLeft : forall k, norm (weightedMaskedProgression psi H k B w) <= L)
    (hRight : forall k, norm (weightedMaskedProgression psi K k C v) <= R) :
    norm (weightedCompanionPacket psi H K B C w v) <=
      ((B + 1 : Nat) : Real) * L * R := by
  have hL : 0 <= L := (norm_nonneg _).trans (hLeft 0)
  have hR : 0 <= R := (norm_nonneg _).trans (hRight 0)
  rw [weighted_coprime_companion_identity]
  calc
    _ <= (Finset.range (B + 1)).sum (fun k =>
        norm ((ArithmeticFunction.moebius k : Complex) *
          weightedMaskedProgression psi H k B w *
            star (weightedMaskedProgression psi K k C v))) := norm_sum_le _ _
    _ <= (Finset.range (B + 1)).sum (fun _ => L * R) := by
      apply Finset.sum_le_sum
      intro k _
      have hmu : norm (ArithmeticFunction.moebius k : Complex) <= 1 := by
        calc
          _ = ((abs (ArithmeticFunction.moebius k) : Int) : Real) := by simp
          _ <= 1 := by
            exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := k))
      rw [norm_mul, norm_mul, norm_star]
      calc
        _ <= (1 * L) * R :=
          mul_le_mul
            (mul_le_mul hmu (hLeft k) (norm_nonneg _) (by norm_num))
            (hRight k) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    _ = _ := by simp [mul_assoc]

/-- Retain the coprime Mobius identity and both full finite divisor masks. -/
theorem divisor_sum_packet_bound {q : Nat} [NeZero q]
    (psi : DirichletCharacter Complex q) (hpsi : Not (psi = 1))
    (H K B C : Nat) (hH : 0 < H) (hK : 0 < K)
    (E F : Finset Nat) (coeff other w v : Nat -> Complex) :
    norm (weightedCompanionPacket psi H K B C
      (divisorSumWindow E coeff w) (divisorSumWindow F other v)) <=
      ((min B C + 1 : Nat) : Real) *
        (E.sum (fun d => norm (coeff d)) *
          windowVariation w B * ((H.divisors.card : Real) * (q : Real))) *
        (F.sum (fun d => norm (other d)) *
          windowVariation v C * ((K.divisors.card : Real) * (q : Real))) := by
  by_cases hBC : B <= C
  . rw [min_eq_left hBC]
    exact packet_bound_of_progressions psi H K B C
      (divisorSumWindow E coeff w) (divisorSumWindow F other v) _ _
      (fun k => divisor_sum_progression_bound psi hpsi H k B hH E coeff w)
      (fun k => divisor_sum_progression_bound psi hpsi K k C hK F other v)
  . have hCB : C <= B := Nat.le_of_lt (Nat.lt_of_not_ge hBC)
    have he :
        norm (weightedCompanionPacket psi H K B C
          (divisorSumWindow E coeff w) (divisorSumWindow F other v)) =
        norm (weightedCompanionPacket psi K H C B
          (divisorSumWindow F other v) (divisorSumWindow E coeff w)) := by
      rw [<- weightedCompanionPacket_star, norm_star]
    rw [he, min_eq_right hCB]
    calc
      _ <= ((C + 1 : Nat) : Real) *
          (F.sum (fun d => norm (other d)) *
            windowVariation v C * ((K.divisors.card : Real) * (q : Real))) *
          (E.sum (fun d => norm (coeff d)) *
            windowVariation w B * ((H.divisors.card : Real) * (q : Real))) :=
        packet_bound_of_progressions psi K H C B
          (divisorSumWindow F other v) (divisorSumWindow E coeff w) _ _
          (fun k => divisor_sum_progression_bound psi hpsi K k C hK F other v)
          (fun k => divisor_sum_progression_bound psi hpsi H k B hH E coeff w)
      _ = _ := by ring

/-- The integer represented by a finite set of distinct prime tags. -/
def tagProduct (T : Finset Nat) : Nat := T.prod id

/-- The nonnegative coefficient in the Euler amplifier expansion. -/
def tagCoefficient (T : Finset Nat) : Real :=
  T.prod (fun p => 1 / ((p : Real) - 1))

/-- A product of distinct primes is positive. -/
theorem tag_product_pos (T : Finset Nat)
    (hT : forall p, Membership.mem T p -> Nat.Prime p) :
    0 < tagProduct T := by
  exact Finset.prod_pos (fun p hp => (hT p hp).pos)

/-- A squarefree prime product divides exactly when each prime divides. -/
theorem tag_product_dvd_iff (T : Finset Nat)
    (hT : forall p, Membership.mem T p -> Nat.Prime p) (n : Nat) :
    Dvd.dvd (tagProduct T) n <->
      forall p, Membership.mem T p -> Dvd.dvd p n := by
  constructor
  . intro hd p hp
    exact (Finset.dvd_prod_of_mem id hp).trans hd
  . intro hd
    by_cases hn : n = 0
    . rw [hn]
      exact dvd_zero _
    . have hs : T <= n.primeFactors := by
        intro p hp
        exact Nat.mem_primeFactors.mpr (And.intro (hT p hp) (And.intro (hd p hp) hn))
      exact (Finset.prod_dvd_prod_of_subset T n.primeFactors id hs).trans
        (Nat.prod_primeFactors_dvd n)

/-- Split the actual product amplifier without assuming coprimality of a and b. -/
theorem amplifier_product_split (G : Finset Nat)
    (hG : forall p, Membership.mem G p -> Nat.Prime p) (a b : Nat) :
    AllPrimeMask.amplifier G (a * b) =
      AllPrimeMask.amplifier G a *
        AllPrimeMask.amplifier (G.filter (fun p => Not (Dvd.dvd p a))) b := by
  classical
  unfold AllPrimeMask.amplifier
  rw [Finset.prod_filter, <- Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  by_cases ha : Dvd.dvd p a <;> by_cases hb : Dvd.dvd p b
  all_goals simp [(hG p hp).dvd_mul, ha, hb]

/-- Expand every Euler factor with its nonnegative squarefree divisor coefficient. -/
theorem amplifier_tag_expansion (G : Finset Nat)
    (hG : forall p, Membership.mem G p -> Nat.Prime p) (n : Nat) :
    AllPrimeMask.amplifier G n =
      G.powerset.sum (fun T =>
        if Dvd.dvd (tagProduct T) n then tagCoefficient T else 0) := by
  classical
  calc
    _ = G.prod (fun p =>
        (if Dvd.dvd p n then 1 / ((p : Real) - 1) else 0) + 1) := by
      apply Finset.prod_congr rfl
      intro p hp
      by_cases hd : Dvd.dvd p n
      . have hp2 : (2 : Real) <= (p : Real) := by exact_mod_cast (hG p hp).two_le
        rw [ite_eq_left hd, ite_eq_left hd]
        have hden : Not ((p : Real) - 1 = 0) := by linarith
        field_simp
        ring
      . simp only [ite_eq_right hd, zero_add]
    _ = G.powerset.sum (fun T => T.prod (fun p =>
        if Dvd.dvd p n then 1 / ((p : Real) - 1) else 0)) :=
      Finset.prod_add_one G
    _ = _ := by
      apply Finset.sum_congr rfl
      intro T hT
      have ht : forall p, Membership.mem T p -> Nat.Prime p :=
        fun p hp => hG p ((Finset.mem_powerset.mp hT) hp)
      by_cases hd : Dvd.dvd (tagProduct T) n
      . rw [ite_eq_left hd]
        apply Finset.prod_congr rfl
        intro p hp
        exact ite_eq_left ((tag_product_dvd_iff T ht n).mp hd p hp)
      . rw [ite_eq_right hd]
        have hz : exists p, Membership.mem T p /\ Not (Dvd.dvd p n) := by
          by_contra h
          apply hd
          apply (tag_product_dvd_iff T ht n).mpr
          intro p hp
          by_contra hpn
          exact h (Exists.intro p (And.intro hp hpn))
        exact Finset.prod_eq_zero hz.choose_spec.1 (ite_eq_right hz.choose_spec.2)

/-- The squarefree divisor coefficient is nonnegative. -/
theorem tag_coefficient_nonneg (T : Finset Nat)
    (hT : forall p, Membership.mem T p -> Nat.Prime p) :
    0 <= tagCoefficient T := by
  apply Finset.prod_nonneg
  intro p hp
  have hp2 : (2 : Real) <= (p : Real) := by exact_mod_cast (hT p hp).two_le
  exact div_nonneg (by norm_num) (by linarith)

/-- Multiplying a tag coefficient by its product recovers its exact amplifier. -/
theorem tag_coefficient_identity (T : Finset Nat) :
    tagCoefficient T * (tagProduct T : Real) =
      AllPrimeMask.amplifier T (tagProduct T) := by
  classical
  unfold tagCoefficient tagProduct AllPrimeMask.amplifier
  rw [Nat.cast_prod, <- Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hd : Dvd.dvd p (T.prod id) := by
    simpa only [id_eq] using (Finset.dvd_prod_of_mem id hp)
  rw [ite_eq_left hd]
  simp only [id_eq, div_eq_mul_inv, one_mul]
  ring

/-- The tag coefficient is bounded by tau(d)/d. -/
theorem tag_coefficient_le (T : Finset Nat)
    (hT : forall p, Membership.mem T p -> Nat.Prime p) :
    tagCoefficient T <=
      ((tagProduct T).divisors.card : Real) / (tagProduct T : Real) := by
  have hpos : 0 < (tagProduct T : Real) :=
    Nat.cast_pos.mpr (tag_product_pos T hT)
  have hm := AllPrimeMask.amplifier_le_divisor_card T (tagProduct T)
    (tag_product_pos T hT) hT
  rw [<- tag_coefficient_identity] at hm
  have he : (((tagProduct T).divisors.card : Real) / (tagProduct T : Real)) *
      (tagProduct T : Real) = ((tagProduct T).divisors.card : Real) := by
    field_simp
  nlinarith

/-- The total coefficient mass of tags no larger than the companion cutoff. -/
def tagMass (G : Finset Nat) (N : Nat) : Real :=
  (G.powerset.filter (fun T => tagProduct T <= N)).sum tagCoefficient

/-- The finite divisor-weighted harmonic sum, with positive support explicit. -/
def divisorHarmonic (N : Nat) : Real :=
  (Finset.Icc 1 N).sum (fun n => (n.divisors.card : Real) / (n : Real))

/-- Inject the truncated distinct prime products into the positive integers up to N. -/
theorem tag_mass_le_divisor_harmonic (G : Finset Nat)
    (hG : forall p, Membership.mem G p -> Nat.Prime p) (N : Nat) :
    tagMass G N <= divisorHarmonic N := by
  classical
  let E := G.powerset.filter (fun T => tagProduct T <= N)
  have hE : forall T, Membership.mem E T ->
      forall p, Membership.mem T p -> Nat.Prime p := by
    intro T hT p hp
    exact hG p ((Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1) hp)
  have hinj : Set.InjOn tagProduct (E : Set (Finset Nat)) := by
    intro T hT U hU he
    have ht : (tagProduct T).primeFactors = T := Nat.primeFactors_prod (hE T hT)
    have hu : (tagProduct U).primeFactors = U := Nat.primeFactors_prod (hE U hU)
    simpa only [ht, hu] using congrArg Nat.primeFactors he
  have hsub : E.image tagProduct <= Finset.Icc 1 N := by
    intro n hn
    have hx := Finset.mem_image.mp hn
    let T := hx.choose
    have hT : Membership.mem E T := hx.choose_spec.1
    have he : tagProduct T = n := hx.choose_spec.2
    rw [<- he]
    exact Finset.mem_Icc.mpr (And.intro (tag_product_pos T (hE T hT))
      (Finset.mem_filter.mp hT).2)
  calc
    _ <= E.sum (fun T =>
        ((tagProduct T).divisors.card : Real) / (tagProduct T : Real)) := by
      apply Finset.sum_le_sum
      intro T hT
      exact tag_coefficient_le T (hE T hT)
    _ = (E.image tagProduct).sum (fun n => (n.divisors.card : Real) / (n : Real)) :=
      (Finset.sum_image (f := fun n : Nat =>
        (n.divisors.card : Real) / (n : Real)) hinj).symm
    _ <= _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun n _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-- The ordinary harmonic prefix on the positive integers up to N. -/
def harmonicPrefix (N : Nat) : Real :=
  (Finset.Ioc 0 N).sum (fun n => 1 / (n : Real))

/-- The divisor harmonic sum is bounded by the full positive harmonic rectangle. -/
theorem divisor_harmonic_le_square (N : Nat) :
    divisorHarmonic N <= (harmonicPrefix N) ^ 2 := by
  classical
  let R := Finset.Ioc 0 N
  let f := fun x : Prod Nat Nat => 1 / ((x.1 * x.2 : Nat) : Real)
  have hrow : forall n, Membership.mem (Finset.Icc 1 N) n ->
      (n.divisors.card : Real) / (n : Real) =
        (Finset.product R R).sum (fun x =>
          if x.1 * x.2 = n then f x else 0) := by
    intro n hn
    have hn0 : Not (n = 0) := Nat.ne_of_gt (Finset.mem_Icc.mp hn).1
    have hcard : (n.divisorsAntidiagonal.card : Real) =
        (n.divisors.card : Real) := by
      simpa using (Nat.sum_divisorsAntidiagonal
        (fun _ _ => (1 : Real)) (n := n))
    calc
      _ = (n.divisorsAntidiagonal.card : Real) * (1 / (n : Real)) := by
        rw [hcard]
        ring
      _ = n.divisorsAntidiagonal.sum (fun _ => 1 / (n : Real)) := by simp
      _ = n.divisorsAntidiagonal.sum f := by
        apply Finset.sum_congr rfl
        intro x hx
        dsimp only [f]
        rw [(Nat.mem_divisorsAntidiagonal.mp hx).1]
      _ = _ := by
        rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le hn0 (Finset.mem_Icc.mp hn).2]
        exact Finset.sum_filter _ _
  calc
    _ = (Finset.Icc 1 N).sum (fun n =>
        (Finset.product R R).sum (fun x =>
          if x.1 * x.2 = n then f x else 0)) := Finset.sum_congr rfl hrow
    _ = (Finset.product R R).sum (fun x =>
        (Finset.Icc 1 N).sum (fun n =>
          if x.1 * x.2 = n then f x else 0)) := Finset.sum_comm
    _ <= (Finset.product R R).sum f := by
      apply Finset.sum_le_sum
      intro x _
      rw [Finset.sum_ite_eq]
      split_ifs
      . exact le_refl _
      . exact div_nonneg (by norm_num) (Nat.cast_nonneg _)
    _ = (harmonicPrefix N) ^ 2 := by
      calc
        (R.product R).sum f = R.sum (fun a => R.sum (fun b => f (a, b))) :=
          Finset.sum_product R R f
        _ = (harmonicPrefix N) ^ 2 := by
          unfold harmonicPrefix
          rw [pow_two, Finset.sum_mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          dsimp only [f]
          simp only [Nat.cast_mul, one_div, mul_inv_rev]
          ring

/-- Only tags at most the actual companion cutoff can contribute. -/
theorem amplifier_truncated_tag_expansion (G : Finset Nat)
    (hG : forall p, Membership.mem G p -> Nat.Prime p)
    (a n N : Nat) (hn : 0 < n) (hnN : n <= N) :
    AllPrimeMask.amplifier G (a * n) =
      AllPrimeMask.amplifier G a *
        ((G.filter (fun p => Not (Dvd.dvd p a))).powerset.filter
          (fun T => tagProduct T <= N)).sum (fun T =>
            if Dvd.dvd (tagProduct T) n then tagCoefficient T else 0) := by
  classical
  rw [amplifier_product_split G hG a n,
    amplifier_tag_expansion _ (fun p hp => hG p (Finset.mem_filter.mp hp).1) n]
  congr 1
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro T _ hnot
  have hlarge : Not (tagProduct T <= N) := by
    intro h
    exact hnot (Finset.mem_filter.mpr (And.intro (by assumption) h))
  have hdiv : Not (Dvd.dvd (tagProduct T) n) := by
    intro hd
    exact hlarge ((Nat.le_of_dvd hn hd).trans hnN)
  exact ite_eq_right hdiv

/-- A finite prime-tag window before progression transfer. -/
def tagWindow (E : Finset (Finset Nat)) (w : Nat -> Complex) (i : Nat) : Complex :=
  E.sum (fun T => (tagCoefficient T : Complex) * divisorWindow (tagProduct T) w i)

/-- Transfer every prime tag to the lcm progression before estimating variation. -/
theorem progression_tag_window {q : Nat}
    (psi : DirichletCharacter Complex q) (H k N : Nat)
    (E : Finset (Finset Nat)) (w : Nat -> Complex) :
    weightedMaskedProgression psi H k N (tagWindow E w) =
      E.sum (fun T => (tagCoefficient T : Complex) *
        weightedMaskedProgression psi H (Nat.lcm k (tagProduct T)) N w) := by
  classical
  calc
    _ = E.sum (fun T => (tagCoefficient T : Complex) *
        weightedMaskedProgression psi H k N (divisorWindow (tagProduct T) w)) := by
      unfold weightedMaskedProgression tagWindow
      calc
        _ = (Finset.Icc 1 N).sum (fun n => E.sum (fun T =>
            (tagCoefficient T : Complex) * (if Dvd.dvd k n then
              divisorWindow (tagProduct T) w (n - 1) * maskedCharacter psi H n
            else 0))) := by
          apply Finset.sum_congr rfl
          intro n _
          by_cases hk : Dvd.dvd k n
          . rw [ite_eq_left hk, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro T _
            rw [ite_eq_left hk]
            ring
          . simp only [ite_eq_right hk, mul_zero, Finset.sum_const_zero]
        _ = _ := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro T _
          rw [Finset.mul_sum]
    _ = _ := by simp_rw [progression_divisor_window]

/-- The actual smooth-window variation pays no jumps of the prime mask. -/
theorem tag_window_progression_bound {q : Nat} [NeZero q]
    (psi : DirichletCharacter Complex q) (hpsi : Not (psi = 1))
    (H k N : Nat) (hH : 0 < H) (G : Finset Nat)
    (hG : forall p, Membership.mem G p -> Nat.Prime p) (w : Nat -> Complex) :
    norm (weightedMaskedProgression psi H k N
      (tagWindow (G.powerset.filter (fun T => tagProduct T <= N)) w)) <=
        tagMass G N * windowVariation w N *
          ((H.divisors.card : Real) * (q : Real)) := by
  rw [progression_tag_window]
  calc
    _ <= (G.powerset.filter (fun T => tagProduct T <= N)).sum (fun T =>
        norm ((tagCoefficient T : Complex) *
          weightedMaskedProgression psi H (Nat.lcm k (tagProduct T)) N w)) :=
      norm_sum_le _ _
    _ <= (G.powerset.filter (fun T => tagProduct T <= N)).sum (fun T =>
        tagCoefficient T * (windowVariation w N *
          ((H.divisors.card : Real) * (q : Real)))) := by
      apply Finset.sum_le_sum
      intro T hT
      have ht : 0 <= tagCoefficient T := tag_coefficient_nonneg T
        (fun p hp => hG p ((Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1) hp))
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
      exact mul_le_mul_of_nonneg_left
        (weighted_masked_progression_bound psi hpsi H (Nat.lcm k (tagProduct T)) N hH w) ht
    _ = _ := by unfold tagMass; rw [<- Finset.sum_mul]; ring

/-- The original amplifier at the full native product a times i+1. -/
def amplifiedWindow (G : Finset Nat) (a : Nat) (w : Nat -> Complex)
    (i : Nat) : Complex :=
  (AllPrimeMask.amplifier G (a * (i + 1)) : Complex) * w i

/-- The native product argument has the exact truncated tag-window expansion. -/
theorem amplified_window_eq (G : Finset Nat)
    (hG : forall p, Membership.mem G p -> Nat.Prime p)
    (a n N : Nat) (hn : 0 < n) (hnN : n <= N) (w : Nat -> Complex) :
    amplifiedWindow G a w (n - 1) =
      (AllPrimeMask.amplifier G a : Complex) *
        tagWindow (((G.filter (fun p => Not (Dvd.dvd p a))).powerset).filter
          (fun T => tagProduct T <= N)) w (n - 1) := by
  have hi : n - 1 + 1 = n := Nat.sub_add_cancel hn
  unfold amplifiedWindow
  rw [hi, amplifier_truncated_tag_expansion G hG a n N hn hnN]
  push_cast
  rw [mul_assoc]
  congr 1
  unfold tagWindow
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro T _
  by_cases hd : Dvd.dvd (tagProduct T) n
  . simp only [divisorWindow, hi, ite_eq_left hd]
  . simp only [divisorWindow, hi, ite_eq_right hd, Complex.ofReal_zero, zero_mul, mul_zero]

/-- Retain the product amplifier in the entire finite character progression. -/
theorem amplified_progression_identity {q : Nat}
    (psi : DirichletCharacter Complex q) (H k N : Nat) (G : Finset Nat)
    (hG : forall p, Membership.mem G p -> Nat.Prime p)
    (a : Nat) (w : Nat -> Complex) :
    weightedMaskedProgression psi H k N (amplifiedWindow G a w) =
      (AllPrimeMask.amplifier G a : Complex) *
        weightedMaskedProgression psi H k N
          (tagWindow (((G.filter (fun p => Not (Dvd.dvd p a))).powerset).filter
            (fun T => tagProduct T <= N)) w) := by
  unfold weightedMaskedProgression
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hk : Dvd.dvd k n
  . rw [ite_eq_left hk, ite_eq_left hk,
      amplified_window_eq G hG a n N (Finset.mem_Icc.mp hn).1
        (Finset.mem_Icc.mp hn).2 w]
    ring
  . simp only [ite_eq_right hk, mul_zero]

/-- A progression estimate uniform over every finite prime mask. -/
theorem amplified_progression_bound {q : Nat} [NeZero q]
    (psi : DirichletCharacter Complex q) (hpsi : Not (psi = 1))
    (H k N : Nat) (hH : 0 < H) (G : Finset Nat)
    (hG : forall p, Membership.mem G p -> Nat.Prime p)
    (a : Nat) (ha : 0 < a) (w : Nat -> Complex) :
    norm (weightedMaskedProgression psi H k N (amplifiedWindow G a w)) <=
      (a.divisors.card : Real) * (harmonicPrefix N) ^ 2 *
        windowVariation w N * ((H.divisors.card : Real) * (q : Real)) := by
  let F := G.filter (fun p => Not (Dvd.dvd p a))
  have hF : forall p, Membership.mem F p -> Nat.Prime p :=
    fun p hp => hG p (Finset.mem_filter.mp hp).1
  have hm : tagMass F N <= (harmonicPrefix N) ^ 2 :=
    (tag_mass_le_divisor_harmonic F hF N).trans (divisor_harmonic_le_square N)
  have hm0 : 0 <= tagMass F N := by
    apply Finset.sum_nonneg
    intro T hT
    exact tag_coefficient_nonneg T
      (fun p hp => hF p ((Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1) hp))
  have ha0 := AllPrimeMask.amplifier_nonneg G a (fun p hp => (hG p hp).two_le)
  have ha1 := AllPrimeMask.amplifier_le_divisor_card G a ha hG
  have hv : 0 <= windowVariation w N := by unfold windowVariation; positivity
  rw [amplified_progression_identity psi H k N G hG a w,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0]
  calc
    _ <= AllPrimeMask.amplifier G a *
        (tagMass F N * windowVariation w N *
          ((H.divisors.card : Real) * (q : Real))) :=
      mul_le_mul_of_nonneg_left (tag_window_progression_bound psi hpsi H k N hH F hF w) ha0
    _ = (AllPrimeMask.amplifier G a * tagMass F N) *
        windowVariation w N * ((H.divisors.card : Real) * (q : Real)) := by ring
    _ <= _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul ha1 hm hm0 (Nat.cast_nonneg _)) hv) (by positivity)

/-- An explicit finite cap with no dependence on the cardinality or product of G. -/
def companionCap (q H a B : Nat) (w : Nat -> Complex) : Real :=
  (a.divisors.card : Real) * (harmonicPrefix B) ^ 2 *
    windowVariation w B * ((H.divisors.card : Real) * (q : Real))

/-- The complete amplified coprime packet has explicit conductor and harmonic costs. -/
theorem amplified_packet_bound {q : Nat} [NeZero q]
    (psi : DirichletCharacter Complex q) (hpsi : Not (psi = 1))
    (H K B C : Nat) (hH : 0 < H) (hK : 0 < K) (G : Finset Nat)
    (hG : forall p, Membership.mem G p -> Nat.Prime p)
    (a c : Nat) (ha : 0 < a) (hc : 0 < c) (w v : Nat -> Complex) :
    norm (weightedCompanionPacket psi H K B C
      (amplifiedWindow G a w) (amplifiedWindow G c v)) <=
      ((min B C + 1 : Nat) : Real) *
        companionCap q H a B w * companionCap q K c C v := by
  by_cases hBC : B <= C
  . rw [min_eq_left hBC]
    exact packet_bound_of_progressions psi H K B C
      (amplifiedWindow G a w) (amplifiedWindow G c v) _ _
      (fun k => amplified_progression_bound psi hpsi H k B hH G hG a ha w)
      (fun k => amplified_progression_bound psi hpsi K k C hK G hG c hc v)
  . have hCB : C <= B := Nat.le_of_lt (Nat.lt_of_not_ge hBC)
    have he :
        norm (weightedCompanionPacket psi H K B C
          (amplifiedWindow G a w) (amplifiedWindow G c v)) =
        norm (weightedCompanionPacket psi K H C B
          (amplifiedWindow G c v) (amplifiedWindow G a w)) := by
      rw [<- weightedCompanionPacket_star, norm_star]
    rw [he, min_eq_right hCB]
    calc
      _ <= ((C + 1 : Nat) : Real) *
          companionCap q K c C v * companionCap q H a B w :=
        packet_bound_of_progressions psi K H C B
          (amplifiedWindow G c v) (amplifiedWindow G a w) _ _
          (fun k => amplified_progression_bound psi hpsi K k C hK G hG c hc v)
          (fun k => amplified_progression_bound psi hpsi H k B hH G hG a ha w)
      _ = _ := by ring

/-- Keep AA, both mixed terms, and the conjugate-square compensation term. -/
theorem amplified_compensation_expansion {q : Nat}
    (psi : DirichletCharacter Complex q) (H K B C : Nat) (G : Finset Nat)
    (a b : Nat) (WA WB VA VB : Nat -> Complex) (c : Complex) :
    weightedCompanionPacket psi H K B C
      (amplifiedWindow G a (fun i => WA i - c * WB i))
      (amplifiedWindow G b (fun i => VA i - c * VB i)) =
      weightedCompanionPacket psi H K B C
        (amplifiedWindow G a WA) (amplifiedWindow G b VA) -
      star c * weightedCompanionPacket psi H K B C
        (amplifiedWindow G a WA) (amplifiedWindow G b VB) -
      c * weightedCompanionPacket psi H K B C
        (amplifiedWindow G a WB) (amplifiedWindow G b VA) +
      (c * star c) * weightedCompanionPacket psi H K B C
        (amplifiedWindow G a WB) (amplifiedWindow G b VB) := by
  have hl : amplifiedWindow G a (fun i => WA i - c * WB i) =
      (fun i => amplifiedWindow G a WA i - c * amplifiedWindow G a WB i) := by
    funext i
    unfold amplifiedWindow
    ring
  have hr : amplifiedWindow G b (fun i => VA i - c * VB i) =
      (fun i => amplifiedWindow G b VA i - c * amplifiedWindow G b VB i) := by
    funext i
    unfold amplifiedWindow
    ring
  rw [hl, hr]
  exact compensated_companion_expansion psi H K B C
    (amplifiedWindow G a WA) (amplifiedWindow G a WB)
    (amplifiedWindow G b VA) (amplifiedWindow G b VB) c

end PrimeFactorOscillations.CarmichaelCompanionMasks
