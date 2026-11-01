/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeOddCycleRigidity
import PrimeFactorOscillations.Helpers.NativePrimePhaseRowKernel

/-! # Full native row words with the common field phase retained -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter IntegerQuadraticCharacter FiniteFieldIntegerCharacter
open FiniteFieldIntegerWindowTransfer
open scoped Classical
attribute [local instance] Classical.propDecidable

def nativeSignedPhaseWordEvent (A B : Finset (Prod Nat Nat))
    (a c : Prod Nat Nat -> Bool) (b : Bool) (ell : Nat) : Prop :=
  And (nativeQuadraticPhaseEvent b ell) (nativeSignedWordEvent A B a c ell)

def nativeSignedPhaseWordMass (A B : Finset (Prod Nat Nat))
    (a c : Prod Nat Nat -> Bool) (b : Bool) (Y X : Nat) : Real :=
  ((Finset.Ico Y X).filter Nat.Prime).sum (fun ell =>
    (1 / (ell : Real)) * (if nativeSignedPhaseWordEvent A B a c b ell then 1 else 0))

def nativeSignedPhaseWordRate (A B : Finset (Prod Nat Nat))
    (a c : Prod Nat Nat -> Bool) (b : Bool) : Real :=
  (1 / (2 : Real) ^ (A.card + B.card + 1)) *
    A.powerset.sum (fun O => B.powerset.sum (fun T =>
      nativeSignedWordMaskCoefficient O T a c *
        (numeratorPrincipalIndicator (nativeSignedRowProduct O T) +
          nativeWordSign b * numeratorPrincipalIndicator (-nativeSignedRowProduct O T))))

theorem native_phase_row_indicator_of_independent (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (hind : nativePrimeVertexGapIndependent P)
    (A B : Finset (Prod Nat Nat))
    (hA : A <= nativePrimeVertexEdges P) (hB : B <= nativePrimeVertexEdges P) (b : Bool) :
    numeratorPrincipalIndicator (nativeSignedRowProduct A B) +
        nativeWordSign b * numeratorPrincipalIndicator (-nativeSignedRowProduct A B) =
      if A = B then
        if (forall p : Nat, Membership.mem P p -> nativePrimeVertexCycleDegree A p % 2 = 0)
          then nativeWordSign b ^ A.card else 0
      else 0 := by
  by_cases hAB : A = B
  . subst B
    rw [ite_eq_left rfl]
    exact native_phase_diagonal_indicator P hP A hA b
  . have hD := native_signed_row_product_ne_zero P hP A B hA hB
    have hp : Not (IsSquare (nativeSignedRowProduct A B)) := by
      intro hs
      exact hAB ((native_signed_row_product_isSquare_iff P hP hind A B hA hB).mp hs).1
    have hn : Not (IsSquare (-nativeSignedRowProduct A B)) := by
      intro hs
      exact hAB ((native_negative_signed_row_product_isSquare_iff P hP hind A B hA hB).mp hs).1
    rw [numerator_principal_indicator_int_eq_square _ hD,
      numerator_principal_indicator_int_eq_square _ (neg_ne_zero.mpr hD),
      ite_eq_right hp, ite_eq_right hn, ite_eq_right hAB]
    ring

theorem native_signed_phase_word_pointwise_selector (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (A B : Finset (Prod Nat Nat))
    (hA : A <= nativePrimeVertexEdges P) (hB : B <= nativePrimeVertexEdges P)
    (a c : Prod Nat Nat -> Bool) (b : Bool) (ell : Nat)
    (hell : Nat.Prime ell) (hell2 : 2 < ell)
    (hlarge : forall p : Nat, Membership.mem P p -> p < ell) :
    (if nativeSignedPhaseWordEvent A B a c b ell then (1 : Real) else 0) =
      nativeWordBit b (nativeQuadraticPhase ell) *
        (A.prod (fun e => nativeWordBit (a e)
          (numeratorKernel (nativeSignedLowerCoefficient e) ell).re) *
        B.prod (fun e => nativeWordBit (c e)
          (numeratorKernel (nativeSignedUpperCoefficient e) ell).re)) := by
  rw [native_word_bit_eq_indicator b (nativeQuadraticPhase ell)
      (native_quadratic_phase_square_one ell hell hell2),
    <- native_signed_word_pointwise_selector P hP A B hA hB a c ell hell hell2 hlarge]
  by_cases hp : nativeQuadraticPhase ell = nativeWordSign b
  . by_cases hw : nativeSignedWordEvent A B a c ell
    . have hj : nativeSignedPhaseWordEvent A B a c b ell := And.intro hp hw
      rw [ite_eq_left hj, ite_eq_left hp, ite_eq_left hw]
      norm_num
    . have hn : Not (nativeSignedPhaseWordEvent A B a c b ell) := fun h => hw h.2
      rw [ite_eq_right hn, ite_eq_left hp, ite_eq_right hw]
      norm_num
  . by_cases hw : nativeSignedWordEvent A B a c ell
    . have hn : Not (nativeSignedPhaseWordEvent A B a c b ell) := fun h => hp h.1
      rw [ite_eq_right hn, ite_eq_right hp, ite_eq_left hw]
      norm_num
    . have hn : Not (nativeSignedPhaseWordEvent A B a c b ell) := fun h => hp h.1
      rw [ite_eq_right hn, ite_eq_right hp, ite_eq_right hw]
      norm_num

theorem native_signed_phase_word_pointwise_expansion (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (A B : Finset (Prod Nat Nat))
    (hA : A <= nativePrimeVertexEdges P) (hB : B <= nativePrimeVertexEdges P)
    (a c : Prod Nat Nat -> Bool) (b : Bool) (ell : Nat)
    (hell : Nat.Prime ell) (hell2 : 2 < ell)
    (hlarge : forall p : Nat, Membership.mem P p -> p < ell) :
    (if nativeSignedPhaseWordEvent A B a c b ell then (1 : Real) else 0) =
      (1 / (2 : Real) ^ (A.card + B.card + 1)) *
        A.powerset.sum (fun O => B.powerset.sum (fun T =>
          nativeSignedWordMaskCoefficient O T a c *
            ((numeratorKernel (nativeSignedRowProduct O T) ell).re +
              nativeWordSign b * (numeratorKernel (-nativeSignedRowProduct O T) ell).re))) := by
  rw [native_signed_phase_word_pointwise_selector P hP A B hA hB a c b ell
    hell hell2 hlarge, native_word_full_mask_expansion, pow_succ]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro O _
  apply Finset.sum_congr rfl
  intro T _
  have hodd := hell.odd_of_ne_two (by omega)
  have h0 : (numeratorKernel (nativeSignedRowProduct O T) ell).re =
      O.prod (fun e => (numeratorKernel (nativeSignedLowerCoefficient e) ell).re) *
        T.prod (fun e => (numeratorKernel (nativeSignedUpperCoefficient e) ell).re) := by
    rw [nativeSignedRowProduct, real_kernel_mul,
      real_kernel_finset_product O nativeSignedLowerCoefficient ell hodd,
      real_kernel_finset_product T nativeSignedUpperCoefficient ell hodd]
  have h1 : (numeratorKernel (-nativeSignedRowProduct O T) ell).re =
      nativeQuadraticPhase ell *
        (O.prod (fun e => (numeratorKernel (nativeSignedLowerCoefficient e) ell).re) *
          T.prod (fun e => (numeratorKernel (nativeSignedUpperCoefficient e) ell).re)) := by
    have hn : -nativeSignedRowProduct O T = (-1 : Int) * nativeSignedRowProduct O T := by ring
    rw [hn, real_kernel_mul, h0]
    rfl
  rw [h0, h1]
  unfold nativeWordBit nativeSignedWordMaskCoefficient
  have h2 : Not ((2 : Real) ^ (A.card + B.card) = 0) := pow_ne_zero _ (by norm_num)
  field_simp [h2]

theorem native_signed_phase_word_mass_expansion (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (A B : Finset (Prod Nat Nat))
    (hA : A <= nativePrimeVertexEdges P) (hB : B <= nativePrimeVertexEdges P)
    (a c : Prod Nat Nat -> Bool) (b : Bool) (Y X : Nat) (hY : 2 < Y)
    (hPY : forall p : Nat, Membership.mem P p -> p < Y) :
    nativeSignedPhaseWordMass A B a c b Y X =
      (1 / (2 : Real) ^ (A.card + B.card + 1)) *
        A.powerset.sum (fun O => B.powerset.sum (fun T =>
          nativeSignedWordMaskCoefficient O T a c *
            (primeCorrelation (nativeSignedRowProduct O T) Y X +
              nativeWordSign b * primeCorrelation (-nativeSignedRowProduct O T) Y X))) := by
  let Q := (Finset.Ico Y X).filter Nat.Prime
  let K : Real := 1 / (2 : Real) ^ (A.card + B.card + 1)
  have hpoint : forall ell : Nat, Membership.mem Q ell ->
      (1 / (ell : Real)) * (if nativeSignedPhaseWordEvent A B a c b ell then 1 else 0) =
        K * A.powerset.sum (fun O => B.powerset.sum (fun T =>
          nativeSignedWordMaskCoefficient O T a c *
            ((1 / (ell : Real)) *
              ((numeratorKernel (nativeSignedRowProduct O T) ell).re +
                nativeWordSign b * (numeratorKernel (-nativeSignedRowProduct O T) ell).re)))) := by
    intro ell hell
    have hh := Finset.mem_filter.mp hell
    have hb := Finset.mem_Ico.mp hh.1
    have hlarge : forall p : Nat, Membership.mem P p -> p < ell :=
      fun p hp => (hPY p hp).trans_le hb.1
    rw [native_signed_phase_word_pointwise_expansion P hP A B hA hB a c b ell hh.2
      (by omega) hlarge]
    dsimp only [K]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro O _
    apply Finset.sum_congr rfl
    intro T _
    ring
  unfold nativeSignedPhaseWordMass
  change Q.sum (fun ell => (1 / (ell : Real)) *
    (if nativeSignedPhaseWordEvent A B a c b ell then 1 else 0)) = _
  rw [Finset.sum_congr rfl hpoint, <- Finset.mul_sum]
  change K * _ = K * _
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro O _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  rw [<- Finset.mul_sum]
  congr 1
  unfold primeCorrelation
  change Q.sum _ = Q.sum _ + nativeWordSign b * Q.sum _
  rw [Finset.mul_sum, <- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ell _
  ring

theorem native_signed_phase_word_mass_expansion_eventually (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (A B : Finset (Prod Nat Nat))
    (hA : A <= nativePrimeVertexEdges P) (hB : B <= nativePrimeVertexEdges P)
    (a c : Prod Nat Nat -> Bool) (b : Bool) :
    Filter.Eventually (fun U : Nat =>
      nativeSignedPhaseWordMass A B a c b (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) =
        (1 / (2 : Real) ^ (A.card + B.card + 1)) *
          A.powerset.sum (fun O => B.powerset.sum (fun T =>
            nativeSignedWordMaskCoefficient O T a c *
              (primeCorrelation (nativeSignedRowProduct O T) (preciseCore U + 1)
                (preciseCore U * preciseCore U + 1) +
              nativeWordSign b * primeCorrelation (-nativeSignedRowProduct O T)
                (preciseCore U + 1) (preciseCore U * preciseCore U + 1))))) atTop := by
  filter_upwards [native_graph_field_window_eventually P] with U hU
  exact native_signed_phase_word_mass_expansion P hP A B hA hB a c b _ _ hU.1 hU.2

theorem native_signed_phase_word_joint_ratio_tendsto (P : Finset Nat)
    (hP : forall p : Nat, Membership.mem P p -> Nat.Prime p)
    (A B : Finset (Prod Nat Nat))
    (hA : A <= nativePrimeVertexEdges P) (hB : B <= nativePrimeVertexEdges P)
    (a c : Prod Nat Nat -> Bool) (b : Bool) :
    Tendsto (fun U : Nat =>
      nativeSignedPhaseWordMass A B a c b (preciseCore U + 1)
        (preciseCore U * preciseCore U + 1) /
        reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1))
      atTop (nhds (nativeSignedPhaseWordRate A B a c b)) := by
  let K : Real := 1 / (2 : Real) ^ (A.card + B.card + 1)
  let F : Nat -> Real := fun U =>
    K * A.powerset.sum (fun O => B.powerset.sum (fun T =>
      nativeSignedWordMaskCoefficient O T a c *
        (primeCorrelation (nativeSignedRowProduct O T) (preciseCore U + 1)
            (preciseCore U * preciseCore U + 1) /
            reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1) +
          nativeWordSign b *
            (primeCorrelation (-nativeSignedRowProduct O T) (preciseCore U + 1)
              (preciseCore U * preciseCore U + 1) /
              reciprocalBand (preciseCore U + 1) (preciseCore U * preciseCore U + 1)))))
  have hlim : Tendsto F atTop (nhds (nativeSignedPhaseWordRate A B a c b)) := by
    dsimp only [F, K, nativeSignedPhaseWordRate]
    apply Filter.Tendsto.const_mul
    apply tendsto_finsetSum A.powerset
    intro O hO
    apply tendsto_finsetSum B.powerset
    intro T hT
    have hD := native_signed_row_product_ne_zero P hP O T
      ((Finset.mem_powerset.mp hO).trans hA) ((Finset.mem_powerset.mp hT).trans hB)
    exact Filter.Tendsto.const_mul (nativeSignedWordMaskCoefficient O T a c)
      ((native_phase_fixed_correlation_ratio_tendsto _ hD).add
        (Filter.Tendsto.const_mul (nativeWordSign b)
          (native_phase_fixed_correlation_ratio_tendsto _ (neg_ne_zero.mpr hD))))
  apply hlim.congr'
  filter_upwards [native_signed_phase_word_mass_expansion_eventually P hP A B hA hB
    a c b] with U hU
  dsimp only [F, K]
  rw [hU]
  simp only [mul_div_assoc, Finset.sum_div, add_div]

end PrimeFactorOscillations.FiniteFieldIntegerSignature
