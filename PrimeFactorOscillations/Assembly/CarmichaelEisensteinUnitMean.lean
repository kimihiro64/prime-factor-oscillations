/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelSexticTransfer

/-!
# The signed zero-mean Eisenstein frequency sum

The zero dual frequency is cancelled exactly before a norm is taken.
The remaining bound is uniform in the physical scale and records the
complete residue-weight mass. This is a frequency-row estimate, not a
bound for the full coupled Carmichael packet or a new zero-free boundary.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.CarmichaelEisensteinUnitMean
open scoped Classical
open OAI.EisensteinSchwartzPoisson
open OAI.ConcreteTraceCRT

/-- A zero-mean periodic weight cancels the full zero mode before the uniform lattice-tail estimate. -/
theorem periodic_zero_mean_uniform :
    exists (s : Finset (Prod Nat Nat)) (C : Real), 0 < C /\
      forall (W : SchwartzMap Real Complex) (K : Real) (hK : 0 < K)
        (c : O) (hc : Not (c = 0)) [Fintype (HasQuotient.Quotient O (Ideal.span {c}))]
        (P : HasQuotient.Quotient O (Ideal.span {c}) -> Complex),
        (Finset.univ.sum P = 0) ->
        norm (tsum (fun z : O =>
          P (Ideal.Quotient.mk (Ideal.span {c}) z) *
            W (norm (eisEmbedding z) ^ 2 / K))) <=
          C * (s.sup (schwartzSeminormFamily Real Real Complex)) W *
            Finset.univ.sum (fun r => norm (P r)) := by
  choose s C hC hbound using paperRadialFourier_nonzero_lattice_uniform
  refine Exists.intro s (Exists.intro C (And.intro hC ?_))
  intro W K hK c hc inst P hP
  let psi := OAI.ConcreteTraceCRT.eisTraceModChar
    OAI.ShortDraftTrace.breveE OAI.ConcreteBreveE.breveE_period_coordinates c hc
  let A : O -> Complex := fun h =>
    Finset.univ.sum (fun r => P r * psi (Ideal.Quotient.mk (Ideal.span {c}) h * r))
  let B : Real := Finset.univ.sum (fun r => norm (P r))
  let L : Real := K / norm (eisEmbedding c) ^ 2
  have hemb : Not (eisEmbedding c = 0) := by
    intro h
    apply hc
    apply eisEmbedding_injective
    simpa only [map_zero] using h
  have hL : 0 < L := div_pos hK (pow_pos (norm_pos_iff.mpr hemb) 2)
  have hB : 0 <= B := Finset.sum_nonneg (fun r _ => norm_nonneg (P r))
  have hA0 : A 0 = 0 := by
    simpa [A, psi] using hP
  have hA (h : O) : norm (A h) <= B := by
    calc
      _ <= Finset.univ.sum (fun r =>
          norm (P r * psi (Ideal.Quotient.mk (Ideal.span {c}) h * r))) :=
        norm_sum_le _ _
      _ = B := by simp only [norm_mul, AddChar.norm_apply, mul_one, B]
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
  have hpoisson := actual_radial_paper_poisson_trace W K hK c hc P
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

/-- The zero-mean condition is discharged for every nonprincipal residue character. -/
theorem nonprincipal_character_uniform :
    exists (s : Finset (Prod Nat Nat)) (C : Real), 0 < C /\
      forall (W : SchwartzMap Real Complex) (K : Real) (hK : 0 < K)
        (c : O) (hc : Not (c = 0)) [Fintype (HasQuotient.Quotient O (Ideal.span {c}))]
        (chi : MulChar (HasQuotient.Quotient O (Ideal.span {c})) Complex),
        Not (chi = 1) ->
        norm (tsum (fun z : O =>
          chi (Ideal.Quotient.mk (Ideal.span {c}) z) *
            W (norm (eisEmbedding z) ^ 2 / K))) <=
          C * (s.sup (schwartzSeminormFamily Real Real Complex)) W *
            Finset.univ.sum (fun r => norm (chi r)) := by
  choose s C hC hbound using periodic_zero_mean_uniform
  refine Exists.intro s (Exists.intro C (And.intro hC ?_))
  intro W K hK c hc inst chi hchi
  exact hbound W K hK c hc chi (MulChar.sum_eq_zero_of_ne_one hchi)

end PrimeFactorOscillations.CarmichaelEisensteinUnitMean
