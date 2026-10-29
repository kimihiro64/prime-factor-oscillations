/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelEisensteinMaskedMean

/-!
# Square-root conductor control of the signed frequency sum

For any primitive nonprincipal Eisenstein character the actual trace is
primitive, including at composite conductors. At maximal conductors the
multiplicative primitivity condition follows from nonprincipality. The finite Fourier coefficient
has norm at most the square root of the residue-field cardinality. Exact
zero-mode cancellation then gives a uniform physical-scale bound. This
finite-frequency improvement is not a bound for the complete compensated
packet or a new zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.CarmichaelEisensteinPrimeMean
open scoped Classical
open OAI.EisensteinSchwartzPoisson
open OAI.ConcreteTraceCRT
open OAI.ActualEisensteinCubic hiding O
open CarmichaelEisensteinMaskedMean

/-- The actual trace discharges additive primitivity at every primitive conductor. -/
theorem primitive_conductor_signed_mean :
    exists (s : Finset (Prod Nat Nat)) (C : Real), 0 < C /\
      forall (W : SchwartzMap Real Complex) (K : Real) (hK : 0 < K)
        (c : O) (hc : Not (c = 0))
        [Fintype (HasQuotient.Quotient O (Ideal.span {c}))]
        (chi : MulChar (HasQuotient.Quotient O (Ideal.span {c})) Complex),
        Not (chi = 1) ->
        OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals chi ->
        norm (tsum (fun z : O =>
          chi (Ideal.Quotient.mk (Ideal.span {c}) z) *
            W (norm (eisEmbedding z) ^ 2 / K))) <=
          C * (s.sup (schwartzSeminormFamily Real Real Complex)) W *
            Real.sqrt (Fintype.card (HasQuotient.Quotient O (Ideal.span {c}))) := by
  choose s C hC hbound using paperRadialFourier_nonzero_lattice_uniform
  refine Exists.intro s (Exists.intro C (And.intro hC ?_))
  intro W K hK c hc inst chi hchi hprimitive
  let psi := OAI.ConcreteTraceCRT.eisTraceModChar
    OAI.ShortDraftTrace.breveE OAI.ConcreteBreveE.breveE_period_coordinates c hc
  let A : O -> Complex := fun h =>
    Finset.univ.sum (fun r => chi r * psi (Ideal.Quotient.mk (Ideal.span {c}) h * r))
  let B : Real := Real.sqrt (Fintype.card (HasQuotient.Quotient O (Ideal.span {c})))
  let L : Real := K / norm (eisEmbedding c) ^ 2
  have hemb : Not (eisEmbedding c = 0) := by
    intro h
    apply hc
    apply eisEmbedding_injective
    simpa only [map_zero] using h
  have hL : 0 < L := div_pos hK (pow_pos (norm_pos_iff.mpr hemb) 2)
  have hB : 0 <= B := Real.sqrt_nonneg _
  have hpsi : psi.IsPrimitive :=
    OAI.GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc
  have hA0 : A 0 = 0 := by
    simpa [A, psi] using (MulChar.sum_eq_zero_of_ne_one hchi)
  have hA (h : O) : norm (A h) <= B := by
    change norm (gaussSum chi
      (psi.mulShift (Ideal.Quotient.mk (Ideal.span {c}) h))) <= B
    rw [OAI.SevenEighths.FiniteFourier.primitive_gaussSum_mulShift
      chi hprimitive psi, norm_mul,
      OAI.SevenEighths.FiniteFourier.primitive_gaussSum_norm
        chi hprimitive psi hpsi]
    exact mul_le_of_le_one_left hB
      (CarmichaelEisensteinMaskedMean.residue_character_norm_le_one
        (Inv.inv chi) (Ideal.Quotient.mk (Ideal.span {c}) h))
  let R : O -> Complex := fun h =>
    paperRadialFourier W (L * norm (eisEmbedding h) ^ 2)
  have hR : Summable (fun h : {h : O // Not (h = 0)} => norm (R h)) :=
    (paperRadialFourier_lattice_summable_norm W L hL).subtype _
  have hpoint (h : {h : O // Not (h = 0)}) :
      norm (A h * R h) <= B * norm (R h) := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hA h) (norm_nonneg _)
  have hAR : Summable (fun h : {h : O // Not (h = 0)} => norm (A h * R h)) :=
    Summable.of_nonneg_of_le (fun h => norm_nonneg _) hpoint (hR.mul_left B)
  have hsub :
      tsum (fun h : O => A h * R h) =
        tsum (fun h : {h : O // Not (h = 0)} => A h * R h) := by
    symm
    calc
      _ = tsum (Set.indicator (fun h : O => Not (h = 0))
          (fun h : O => A h * R h)) :=
        @tsum_subtype Complex O _ _ (fun h : O => Not (h = 0))
          (fun h : O => A h * R h)
      _ = _ := by
        apply tsum_congr
        intro h
        by_cases hh : h = 0
        . calc
            _ = 0 := Set.indicator_of_notMem
              (s := fun a : O => Not (a = 0)) (a := h)
              (fun hm => hm hh) (fun a : O => A a * R a)
            _ = A h * R h := by rw [hh, hA0, zero_mul]
        . exact Set.indicator_of_mem hh (fun a : O => A a * R a)
  have hpoisson := actual_radial_paper_poisson_trace W K hK c hc chi
  have hargument (h : O) :
      K * norm (eisEmbedding h) ^ 2 / norm (eisEmbedding c) ^ 2 =
        L * norm (eisEmbedding h) ^ 2 := by
    dsimp [L]
    ring
  have huniv (i : Fintype (HasQuotient.Quotient O (Ideal.span {c}))) :
      @Finset.univ (HasQuotient.Quotient O (Ideal.span {c})) i =
        @Finset.univ (HasQuotient.Quotient O (Ideal.span {c})) inst := by
    ext r
    simp
  simp_rw [hargument] at hpoisson
  simp only [huniv] at hpoisson
  change _ = @HSMul.hSMul Real Complex Complex inferInstance L
    (tsum (fun h : O => A h * R h)) at hpoisson
  have hnorm (z : Complex) :
      norm (@HSMul.hSMul Real Complex Complex inferInstance L z) = L * norm z := by
    simpa only [Real.norm_eq_abs, abs_of_pos hL] using (norm_smul L z)
  rw [hpoisson, hsub, hnorm]
  calc
    L * norm (tsum (fun h : {h : O // Not (h = 0)} => A h * R h)) <=
        L * tsum (fun h : {h : O // Not (h = 0)} => norm (A h * R h)) :=
      mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hAR) (le_of_lt hL)
    _ <= L * tsum (fun h : {h : O // Not (h = 0)} => B * norm (R h)) :=
      mul_le_mul_of_nonneg_left (Summable.tsum_le_tsum hpoint hAR (hR.mul_left B))
        (le_of_lt hL)
    _ = B * (L * tsum (fun h : {h : O // Not (h = 0)} => norm (R h))) := by
      rw [tsum_mul_left]
      ring
    _ <= B * (C * (s.sup (schwartzSeminormFamily Real Real Complex)) W) :=
      mul_le_mul_of_nonneg_left (hbound W L hL) hB
    _ = C * (s.sup (schwartzSeminormFamily Real Real Complex)) W * B := by ring

/-- Every finite ideal mask retains the square-root conductor saving. -/
theorem primitive_conductor_masked_mean :
    exists (s : Finset (Prod Nat Nat)) (C : Real), 0 < C /\
      forall (W : SchwartzMap Real Complex) (K : Real) (hK : 0 < K)
        (c : O) (hc : Not (c = 0))
        [Fintype (HasQuotient.Quotient O (Ideal.span {c}))]
        (chi : MulChar (HasQuotient.Quotient O (Ideal.span {c})) Complex),
        Not (chi = 1) ->
        OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals chi ->
        forall {iota : Type} [DecidableEq iota]
          (J : iota -> Ideal O) [forall i, (J i).IsMaximal],
          Function.Injective J -> forall S : Finset iota,
        norm (tsum (fun u : O => rowCoprimeMask J S u *
          chi (Ideal.Quotient.mk (Ideal.span {c}) u) *
            W (norm (eisEmbedding u) ^ 2 / K))) <=
          C * (s.sup (schwartzSeminormFamily Real Real Complex)) W *
            Real.sqrt (Fintype.card (HasQuotient.Quotient O (Ideal.span {c}))) * (2 : Real) ^ S.card := by
  choose s C hC hbound using
    primitive_conductor_signed_mean
  refine Exists.intro s (Exists.intro C (And.intro hC ?_))
  intro W K hK c hc inst chi hchi hprimitive iota di J ji hinj S
  let r : O -> Complex := fun u => chi (Ideal.Quotient.mk (Ideal.span {c}) u)
  let B : Real := Real.sqrt (Fintype.card (HasQuotient.Quotient O (Ideal.span {c})))
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
        hscale c hc chi hchi hprimitive
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

/-- Forced frequency divisibility retains all overlap factors and the same conductor saving. -/
theorem primitive_conductor_forced_ideal_mean :
    exists (s : Finset (Prod Nat Nat)) (C : Real), 0 < C /\
      forall (W : SchwartzMap Real Complex) (K : Real) (hK : 0 < K)
        (c : O) (hc : Not (c = 0))
        [Fintype (HasQuotient.Quotient O (Ideal.span {c}))]
        (chi : MulChar (HasQuotient.Quotient O (Ideal.span {c})) Complex),
        Not (chi = 1) ->
        OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals chi ->
        forall {iota : Type} [DecidableEq iota]
          (J : iota -> Ideal O) [forall i, (J i).IsMaximal],
          Function.Injective J -> forall (S : Finset iota) (D : Ideal O),
        Not (D = Bot.bot) ->
        norm (tsum (fun u : O => if Membership.mem D u then
          rowCoprimeMask J S u * chi (Ideal.Quotient.mk (Ideal.span {c}) u) *
            W (norm (eisEmbedding u) ^ 2 / K) else 0)) <=
          C * (s.sup (schwartzSeminormFamily Real Real Complex)) W *
            Real.sqrt (Fintype.card (HasQuotient.Quotient O (Ideal.span {c}))) * (2 : Real) ^ S.card := by
  choose s C hC hbound using primitive_conductor_masked_mean
  refine Exists.intro s (Exists.intro C (And.intro hC ?_))
  intro W K hK c hc inst chi hchi hprimitive iota di J ji hinj S D hD
  let g := OAI.ConcretePrimeRowBridge.idealGenerator D
  let B : Real := Real.sqrt (Fintype.card (HasQuotient.Quotient O (Ideal.span {c})))
  let T : Real := C * (s.sup (schwartzSeminormFamily Real Real Complex)) W
  have hg := eisEmbedding_ne_zero (OAI.ConcretePrimeRowBridge.idealGenerator_ne_zero D hD)
  have hscale : 0 < K / norm (eisEmbedding g) ^ 2 :=
    div_pos hK (pow_pos (norm_pos_iff.mpr hg) 2)
  have hinner := hbound W (K / norm (eisEmbedding g) ^ 2) hscale c hc chi hchi hprimitive J hinj S
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

/-- The source normalizer cancels the conductor at every physical dilation and forced ideal. -/
theorem primitive_source_unit_forced_ideal_mean :
    exists (s : Finset (Prod Nat Nat)) (C : Real), 0 < C /\
      forall (W : SchwartzMap Real Complex) (K X Y : Real)
        (hK : 0 < K) (hX : 0 < X) (hY : 0 < Y)
        (c : O) (hc : Not (c = 0))
        [Fintype (HasQuotient.Quotient O (Ideal.span {c}))]
        (chi : MulChar (HasQuotient.Quotient O (Ideal.span {c})) Complex),
        Not (chi = 1) ->
        OAI.SevenEighths.FiniteFourier.IsPrimitiveOnIdeals chi ->
        forall {iota : Type} [DecidableEq iota]
          (J : iota -> Ideal O) [forall i, (J i).IsMaximal],
          Function.Injective J -> forall (S : Finset iota) (D : Ideal O),
        Not (D = Bot.bot) ->
        norm (tsum (fun u : O => if Membership.mem D u then
          rowCoprimeMask J S u * chi (Ideal.Quotient.mk (Ideal.span {c}) u) *
            W (norm (eisEmbedding u) ^ 2 / K) else 0)) /
          Real.sqrt ((Fintype.card (HasQuotient.Quotient O (Ideal.span {c})) : Real) *
            X * Y) <=
          C * (s.sup (schwartzSeminormFamily Real Real Complex)) W *
            (2 : Real) ^ S.card / Real.sqrt (X * Y) := by
  choose s C hC hbound using primitive_conductor_forced_ideal_mean
  refine Exists.intro s (Exists.intro C (And.intro hC ?_))
  intro W K X Y hK hX hY c hc inst chi hchi hprimitive iota di J ji hinj S D hD
  let q : Real := Fintype.card (HasQuotient.Quotient O (Ideal.span {c}))
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast (Fintype.card_pos :
      0 < Fintype.card (HasQuotient.Quotient O (Ideal.span {c})))
  have hqroot : Not (Real.sqrt q = 0) := ne_of_gt (Real.sqrt_pos.mpr hq)
  have hxyroot : Not (Real.sqrt (X * Y) = 0) :=
    ne_of_gt (Real.sqrt_pos.mpr (mul_pos hX hY))
  have hroot : Real.sqrt (q * X * Y) = Real.sqrt q * Real.sqrt (X * Y) := by
    rw [mul_assoc, Real.sqrt_mul (le_of_lt hq)]
  have h := hbound W K hK c hc chi hchi hprimitive J hinj S D hD
  calc
    _ <= (C * (s.sup (schwartzSeminormFamily Real Real Complex)) W *
        Real.sqrt q * (2 : Real) ^ S.card) / Real.sqrt (q * X * Y) :=
      div_le_div_of_nonneg_right h (Real.sqrt_nonneg _)
    _ = _ := by
      rw [hroot]
      field_simp

/-- Nonprincipality alone discharges multiplicative primitivity at a maximal conductor. -/
theorem prime_conductor_signed_mean :
    exists (s : Finset (Prod Nat Nat)) (C : Real), 0 < C /\
      forall (W : SchwartzMap Real Complex) (K : Real) (hK : 0 < K)
        (c : O) (hc : Not (c = 0)) [(Ideal.span {c}).IsMaximal]
        [Fintype (HasQuotient.Quotient O (Ideal.span {c}))]
        (chi : MulChar (HasQuotient.Quotient O (Ideal.span {c})) Complex),
        Not (chi = 1) ->
        norm (tsum (fun z : O =>
          chi (Ideal.Quotient.mk (Ideal.span {c}) z) *
            W (norm (eisEmbedding z) ^ 2 / K))) <=
          C * (s.sup (schwartzSeminormFamily Real Real Complex)) W *
            Real.sqrt (Fintype.card (HasQuotient.Quotient O (Ideal.span {c}))) := by
  choose s C hC hbound using primitive_conductor_signed_mean
  refine Exists.intro s (Exists.intro C (And.intro hC ?_))
  intro W K hK c hc hmax inst chi hchi
  exact hbound W K hK c hc chi hchi
    (OAI.SevenEighths.FiniteFourier.primitiveOnIdeals_of_field chi hchi)

end PrimeFactorOscillations.CarmichaelEisensteinPrimeMean
