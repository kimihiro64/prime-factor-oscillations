/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelEisensteinUnitMean

/-!
# Full finite coprime masks in the signed Eisenstein unit frequency

The exact ideal-Mobius dilation identity is retained until the zero mode
has cancelled in every dilated nonprincipal character sum. The bound is
uniform at all positive physical scales, and records the full mask cost
and residue-character mass. No complete source-unit or rational packet
bound, moving-conductor saving, or improved zero-free boundary is asserted.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.CarmichaelEisensteinMaskedMean
open scoped Classical
open OAI.EisensteinSchwartzPoisson hiding O
open OAI.ConcreteTraceCRT
open OAI.ActualEisensteinCubic

/-- Every ideal-Mobius factor in the exact inclusion-exclusion packet has modulus at most one. -/
theorem ideal_moebius_norm_le_one (I : Ideal O) :
    norm (UniqueFactorizationMonoid.moebius I : Complex) <= 1 := by
  by_cases h : Squarefree I
  . simp [UniqueFactorizationMonoid.moebius, h, norm_pow]
  . simp [UniqueFactorizationMonoid.moebius, h]

/-- A finite residue character has modulus at most one, including on nonunits. -/
theorem residue_character_norm_le_one {c : O}
    [Fintype (HasQuotient.Quotient O (Ideal.span {c}))]
    (chi : MulChar (HasQuotient.Quotient O (Ideal.span {c})) Complex)
    (a : HasQuotient.Quotient O (Ideal.span {c})) : norm (chi a) <= 1 := by
  by_cases h : IsUnit a
  . cases h with
    | intro u hu =>
      rw [<- hu]
      have hsq := MulChar.normSq_apply_unit chi u
      rw [Complex.normSq_eq_norm_sq] at hsq
      nlinarith [norm_nonneg (chi u)]
  . rw [chi.map_nonunit h]
    norm_num

/-- All supported prime masks are estimated after signed zero-mode cancellation at every exact dilation. -/
theorem masked_nonprincipal_character_uniform :
    exists (s : Finset (Prod Nat Nat)) (C : Real), 0 < C /\
      forall (W : SchwartzMap Real Complex) (K : Real) (hK : 0 < K)
        (c : O) (hc : Not (c = 0)) [Fintype (HasQuotient.Quotient O (Ideal.span {c}))]
        (chi : MulChar (HasQuotient.Quotient O (Ideal.span {c})) Complex),
        Not (chi = 1) ->
        forall {iota : Type} [DecidableEq iota]
          (J : iota -> Ideal O) [forall i, (J i).IsMaximal],
          Function.Injective J -> forall S : Finset iota,
        norm (tsum (fun u : O => rowCoprimeMask J S u *
          chi (Ideal.Quotient.mk (Ideal.span {c}) u) *
            W (norm (eisEmbedding u) ^ 2 / K))) <=
          C * (s.sup (schwartzSeminormFamily Real Real Complex)) W *
            Finset.univ.sum (fun r => norm (chi r)) * (2 : Real) ^ S.card := by
  choose s C hC hbound using
    CarmichaelEisensteinUnitMean.nonprincipal_character_uniform
  refine Exists.intro s (Exists.intro C (And.intro hC ?_))
  intro W K hK c hc inst chi hchi iota di J ji hinj S
  let r : O -> Complex := fun u => chi (Ideal.Quotient.mk (Ideal.span {c}) u)
  let B : Real := Finset.univ.sum (fun a => norm (chi a))
  let T : Real := C * (s.sup (schwartzSeminormFamily Real Real Complex)) W
  have hr (a b : O) : r (a * b) = r a * r b := by
    dsimp [r]
    rw [map_mul, map_mul]
  have hsum : Summable (fun u : O => r u * W (norm (eisEmbedding u) ^ 2 / K)) := by
    have h := actual_eisenstein_periodic_summable (scaledRadialTest W K hK)
      (fun u : O => Ideal.Quotient.mk (Ideal.span {c}) u) (fun a => chi a)
    simpa only [scaledRadialTest_apply, r] using h
  have hchar (u : O) : norm (r u) <= 1 :=
    residue_character_norm_le_one chi (Ideal.Quotient.mk (Ideal.span {c}) u)
  have hinner (E : Finset iota) :
      norm (tsum (fun u : O => r u *
        W (norm (eisEmbedding u) ^ 2 /
          (K / norm (eisEmbedding (primeSubsetGenerator J E)) ^ 2)))) <= T * B := by
    have hg := eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero J E)
    have hscale : 0 < K / norm (eisEmbedding (primeSubsetGenerator J E)) ^ 2 :=
      div_pos hK (pow_pos (norm_pos_iff.mpr hg) 2)
    simpa only [r, B, T] using
      hbound W (K / norm (eisEmbedding (primeSubsetGenerator J E)) ^ 2)
        hscale c hc chi hchi
  have hid := tsum_masked_radial_dilations J hinj S r hr W K hsum
  change norm (tsum (fun u : O => rowCoprimeMask J S u * r u *
    W (norm (eisEmbedding u) ^ 2 / K))) <= T * B * (2 : Real) ^ S.card
  rw [hid]
  calc
    _ <= S.powerset.sum (fun E =>
        norm ((UniqueFactorizationMonoid.moebius (E.prod J) : Complex) *
          r (primeSubsetGenerator J E) *
          tsum (fun u : O => r u *
            W (norm (eisEmbedding u) ^ 2 /
              (K / norm (eisEmbedding (primeSubsetGenerator J E)) ^ 2))))) :=
      norm_sum_le _ _
    _ <= S.powerset.sum (fun _ => T * B) := by
      apply Finset.sum_le_sum
      intro E _
      rw [norm_mul, norm_mul]
      have hpair :
          norm (UniqueFactorizationMonoid.moebius (E.prod J) : Complex) *
            norm (r (primeSubsetGenerator J E)) <= 1 := by
        calc
          _ <= 1 * 1 := mul_le_mul (ideal_moebius_norm_le_one _)
            (hchar _) (norm_nonneg _) (by norm_num)
          _ = 1 := one_mul _
      calc
        _ <= 1 * (T * B) := mul_le_mul hpair (hinner E) (norm_nonneg _) (by norm_num)
        _ = T * B := by ring
    _ = (S.powerset.card : Real) * (T * B) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = T * B * (2 : Real) ^ S.card := by
      rw [Finset.card_powerset, Nat.cast_pow, Nat.cast_ofNat]
      ring

/-- The complete finite mask always has modulus at most one. -/
theorem row_mask_norm_le_one {iota : Type} (J : iota -> Ideal O)
    (S : Finset iota) (u : O) : norm (rowCoprimeMask J S u) <= 1 := by
  unfold rowCoprimeMask
  split_ifs <;> norm_num

/-- Prime-ideal masks multiply exactly, including every excluded nonunit. -/
theorem row_mask_multiplicative {iota : Type} (J : iota -> Ideal O)
    [forall i, (J i).IsMaximal] (S : Finset iota) (a b : O) :
    rowCoprimeMask J S (a * b) = rowCoprimeMask J S a * rowCoprimeMask J S b := by
  have hbad :
      (exists i, Membership.mem S i /\ Membership.mem (J i) (a * b)) <->
        (exists i, Membership.mem S i /\ Membership.mem (J i) a) \/
          (exists i, Membership.mem S i /\ Membership.mem (J i) b) := by
    constructor
    . intro h
      cases h with
      | intro i hi =>
        have hp : (J i).IsPrime := inferInstance
        cases hp.mem_or_mem hi.2 with
        | inl ha => exact Or.inl (Exists.intro i (And.intro hi.1 ha))
        | inr hb => exact Or.inr (Exists.intro i (And.intro hi.1 hb))
    . intro h
      cases h with
      | inl ha =>
        cases ha with
        | intro i hi =>
          exact Exists.intro i (And.intro hi.1 (Ideal.mul_mem_right b (J i) hi.2))
      | inr hb =>
        cases hb with
        | intro i hi =>
          exact Exists.intro i (And.intro hi.1 (Ideal.mul_mem_left (J i) a hi.2))
  by_cases ha : exists i, Membership.mem S i /\ Membership.mem (J i) a
  . have hab := hbad.mpr (Or.inl ha)
    simp only [rowCoprimeMask, if_pos ha, if_pos hab, zero_mul]
  . by_cases hb : exists i, Membership.mem S i /\ Membership.mem (J i) b
    . have hab := hbad.mpr (Or.inr hb)
      simp only [rowCoprimeMask, if_neg ha, if_pos hb, if_pos hab, mul_zero]
    . have hab : Not (exists i, Membership.mem S i /\ Membership.mem (J i) (a * b)) :=
        fun h => Or.elim (hbad.mp h) ha hb
      simp only [rowCoprimeMask, if_neg ha, if_neg hb, if_neg hab, one_mul]

/-- An arbitrary nonzero frequency ideal retains its complete mask and character phase at the exact dilation. -/
theorem ideal_masked_frequency_dilation {iota : Type} (J : iota -> Ideal O)
    [forall i, (J i).IsMaximal] (S : Finset iota) (D : Ideal O)
    (hD : Not (D = Bot.bot)) {c : O}
    (chi : MulChar (HasQuotient.Quotient O (Ideal.span {c})) Complex)
    (W : Real -> Complex) (K : Real) :
    tsum (fun u : O => if Membership.mem D u then
      rowCoprimeMask J S u * chi (Ideal.Quotient.mk (Ideal.span {c}) u) *
        W (norm (eisEmbedding u) ^ 2 / K) else 0) =
      (rowCoprimeMask J S (OAI.ConcretePrimeRowBridge.idealGenerator D) *
        chi (Ideal.Quotient.mk (Ideal.span {c})
          (OAI.ConcretePrimeRowBridge.idealGenerator D))) *
        tsum (fun z : O => rowCoprimeMask J S z *
          chi (Ideal.Quotient.mk (Ideal.span {c}) z) *
            W (norm (eisEmbedding z) ^ 2 /
              (K / norm (eisEmbedding (OAI.ConcretePrimeRowBridge.idealGenerator D)) ^ 2))) := by
  let g := OAI.ConcretePrimeRowBridge.idealGenerator D
  have hd := OAI.ConcretePrimeRowBridge.tsum_ideal_eq_tsum_generator D hD
    (fun u : O => rowCoprimeMask J S u *
      chi (Ideal.Quotient.mk (Ideal.span {c}) u) * W (norm (eisEmbedding u) ^ 2 / K))
  rw [hd]
  have hargument (z : O) :
      norm (eisEmbedding (g * z)) ^ 2 / K =
        norm (eisEmbedding z) ^ 2 / (K / norm (eisEmbedding g) ^ 2) := by
    rw [map_mul, norm_mul, mul_pow, div_div_eq_mul_div]
    ring
  calc
    _ = tsum (fun z : O =>
        (rowCoprimeMask J S g * chi (Ideal.Quotient.mk (Ideal.span {c}) g)) *
          (rowCoprimeMask J S z * chi (Ideal.Quotient.mk (Ideal.span {c}) z) *
            W (norm (eisEmbedding z) ^ 2 / (K / norm (eisEmbedding g) ^ 2)))) := by
      apply tsum_congr
      intro z
      rw [row_mask_multiplicative J S g z, hargument]
      simp only [map_mul]
      ring
    _ = _ := tsum_mul_left

/-- Every forced ideal-divisibility row has a scale-uniform bound after its exact signed transfer. -/
theorem ideal_divisible_masked_character_bound :
    exists (s : Finset (Prod Nat Nat)) (C : Real), 0 < C /\
      forall (W : SchwartzMap Real Complex) (K : Real) (hK : 0 < K)
        (c : O) (hc : Not (c = 0)) [Fintype (HasQuotient.Quotient O (Ideal.span {c}))]
        (chi : MulChar (HasQuotient.Quotient O (Ideal.span {c})) Complex),
        Not (chi = 1) ->
        forall {iota : Type} [DecidableEq iota]
          (J : iota -> Ideal O) [forall i, (J i).IsMaximal],
          Function.Injective J -> forall (S : Finset iota) (D : Ideal O),
        Not (D = Bot.bot) ->
        norm (tsum (fun u : O => if Membership.mem D u then
          rowCoprimeMask J S u * chi (Ideal.Quotient.mk (Ideal.span {c}) u) *
            W (norm (eisEmbedding u) ^ 2 / K) else 0)) <=
          C * (s.sup (schwartzSeminormFamily Real Real Complex)) W *
            Finset.univ.sum (fun r => norm (chi r)) * (2 : Real) ^ S.card := by
  choose s C hC hbound using masked_nonprincipal_character_uniform
  refine Exists.intro s (Exists.intro C (And.intro hC ?_))
  intro W K hK c hc inst chi hchi iota di J ji hinj S D hD
  let g := OAI.ConcretePrimeRowBridge.idealGenerator D
  let B : Real := Finset.univ.sum (fun a => norm (chi a))
  let T : Real := C * (s.sup (schwartzSeminormFamily Real Real Complex)) W
  have hg := eisEmbedding_ne_zero (OAI.ConcretePrimeRowBridge.idealGenerator_ne_zero D hD)
  have hscale : 0 < K / norm (eisEmbedding g) ^ 2 :=
    div_pos hK (pow_pos (norm_pos_iff.mpr hg) 2)
  have hinner := hbound W (K / norm (eisEmbedding g) ^ 2) hscale c hc chi hchi J hinj S
  have hchar : norm (chi (Ideal.Quotient.mk (Ideal.span {c}) g)) <= 1 :=
    residue_character_norm_le_one chi (Ideal.Quotient.mk (Ideal.span {c}) g)
  have hcoef :
      norm (rowCoprimeMask J S g) *
        norm (chi (Ideal.Quotient.mk (Ideal.span {c}) g)) <= 1 := by
    calc
      _ <= 1 * 1 := mul_le_mul (row_mask_norm_le_one J S g)
        hchar (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul _
  rw [ideal_masked_frequency_dilation J S D hD chi W K, norm_mul, norm_mul]
  calc
    _ <= 1 * (T * B * (2 : Real) ^ S.card) :=
      mul_le_mul hcoef hinner (norm_nonneg _) (by norm_num)
    _ = T * B * (2 : Real) ^ S.card := by ring

end PrimeFactorOscillations.CarmichaelEisensteinMaskedMean
