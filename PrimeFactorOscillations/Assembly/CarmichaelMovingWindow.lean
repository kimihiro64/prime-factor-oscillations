/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelMarkedWindow

/-!
# Complete compensated moving-ideal packet

Applies the native overlap provider with the compensated weight itself.
The character conductor q remains distinct from the moving residual ideal.
All overlap Mobius signs and both mixed terms remain in the physical row.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.CarmichaelMovingWindow
open OAI OAI.SevenEighths
open scoped Classical
local notation "Eis" => ConcretePrimeRowBridge.O

variable (F : Finset (Ideal Eis))
variable (hFpos : forall I, Membership.mem F I -> Not (I = Bot.bot))
variable (hFgood : forall I, Membership.mem F I ->
  forall P, Membership.mem (UniqueFactorizationMonoid.normalizedFactors I) P ->
    Not (Membership.mem P ConcretePrimeRowBridge.goodLambda))

theorem idealRowSum_compensation {q : Nat} (chi : DirichletCharacter Complex q)
    (WA WB : Nat -> Complex) (c : Complex) (u : Eis) :
    ConcretePrimeRowBridge.idealRowSum F hFpos hFgood chi (fun n => WA n - c * WB n) u =
      ConcretePrimeRowBridge.idealRowSum F hFpos hFgood chi WA u -
        c * ConcretePrimeRowBridge.idealRowSum F hFpos hFgood chi WB u := by
  unfold ConcretePrimeRowBridge.idealRowSum
  rw [Finset.mul_sum, <- Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro I _
  ring

theorem compensated_mobius_packet {q : Nat} (chi : DirichletCharacter Complex q)
    (WA WB : Nat -> Complex) (c : Complex) (R : Finset Eis) (V : Eis -> Complex) :
    R.sum (fun u => V u *
      ((norm (ConcretePrimeRowBridge.idealRowSum F hFpos hFgood chi WA u -
        c * ConcretePrimeRowBridge.idealRowSum F hFpos hFgood chi WB u) ^ 2 : Real) : Complex)) =
      F.sum (fun I => F.sum (fun J =>
        star (ShortDraftHeckeBridge.baseChangeWeight chi I *
          (WA (Ideal.absNorm I) - c * WB (Ideal.absNorm I))) *
        (ShortDraftHeckeBridge.baseChangeWeight chi J *
          (WA (Ideal.absNorm J) - c * WB (Ideal.absNorm J))) *
        (Inter.inter (ConcretePrimeRowBridge.idealSupport F I)
          (ConcretePrimeRowBridge.idealSupport F J)).powerset.sum (fun E =>
          (UniqueFactorizationMonoid.moebius
            (ConcretePrimeRowBridge.primeSubsetProduct F E) : Complex) *
          (R.filter (fun u => Membership.mem
            (ConcretePrimeRowBridge.primeSubsetProduct F E) u)).sum (fun u =>
              V u *
                star (ConcretePrimeRowBridge.residualSexticRow F hFpos hFgood I J u) *
                  ConcretePrimeRowBridge.residualSexticRow F hFpos hFgood J I u)))) := by
  classical
  have h := ConcretePrimeRowBridge.idealRowSum_mean_square_mobius
    F hFpos hFgood chi (fun n => WA n - c * WB n) R V
  simp_rw [idealRowSum_compensation F hFpos hFgood chi WA WB c] at h
  exact h

theorem compensation_cross_terms (aA aB bA bB c : Complex) :
    star (aA - c * aB) * (bA - c * bB) =
      star aA * bA - c * star aA * bB - star c * star aB * bA +
        c * star c * star aB * bB := by
  rw [star_sub, star_mul]
  ring

open ActualEisensteinCubic ConcreteTraceCRT EisensteinEmbedding
open CubicReciprocalGaussian ProbeRadialMellin

def periodicTheta (c : Eis)
    (P : HasQuotient.Quotient Eis (Ideal.span {c}) -> Complex) (a : Real) : Complex :=
  tsum fun z : Eis =>
    P (Ideal.Quotient.mk (Ideal.span {c}) z) * gaussian a (eisEmbedding z)

def periodicWindow (c : Eis)
    (P : HasQuotient.Quotient Eis (Ideal.span {c}) -> Complex) (M : Real) : Complex :=
  tsum fun z : Eis =>
    P (Ideal.Quotient.mk (Ideal.span {c}) z) *
      carrierProfile (norm (eisEmbedding z) ^ 2 / M)

def periodicFourier (c : Eis) (hc : Not (c = 0))
    (P : HasQuotient.Quotient Eis (Ideal.span {c}) -> Complex)
    (w : HasQuotient.Quotient Eis (Ideal.span {c})) : Complex := by
  classical
  have : Finite (HasQuotient.Quotient Eis (Ideal.span {c})) := finite_quotient_span hc
  let : Fintype (HasQuotient.Quotient Eis (Ideal.span {c})) := Fintype.ofFinite _
  exact Finset.univ.sum (fun r =>
    P r * (TraceCharacter.traceCharacter c hc) (w * r))

theorem periodic_gaussian_summable (c : Eis) (hc : Not (c = 0))
    (P : HasQuotient.Quotient Eis (Ideal.span {c}) -> Complex)
    (a : Real) (ha : 0 < a) :
    Summable (fun z : Eis =>
      P (Ideal.Quotient.mk (Ideal.span {c}) z) * gaussian a (eisEmbedding z)) := by
  classical
  have : Finite (HasQuotient.Quotient Eis (Ideal.span {c})) := finite_quotient_span hc
  let : Fintype (HasQuotient.Quotient Eis (Ideal.span {c})) := Fintype.ofFinite _
  let B : Real := Finset.univ.sum (fun x : HasQuotient.Quotient Eis (Ideal.span {c}) =>
    norm (P x))
  have hBound (z : Eis) :
      norm (P (Ideal.Quotient.mk (Ideal.span {c}) z) * gaussian a (eisEmbedding z)) <=
        B * norm (gaussian a (eisEmbedding z)) := by
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact Finset.single_le_sum (fun x _ => norm_nonneg (P x)) (Finset.mem_univ _)
  have hs : Summable (fun z : Eis => norm (gaussian a (eisEmbedding z))) := by
    simpa only [div_one] using
      (CubicGaussianUnit.gaussian_lattice_summable a 1 ha (by norm_num)).norm
  exact (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hBound (hs.mul_left B)).of_norm

theorem periodic_window_hasSum (c : Eis) (hc : Not (c = 0))
    (P : HasQuotient.Quotient Eis (Ideal.span {c}) -> Complex)
    (M : Real) (hM : 0 < M) :
    HasSum (fun z : Eis =>
      P (Ideal.Quotient.mk (Ideal.span {c}) z) *
        carrierProfile (norm (eisEmbedding z) ^ 2 / M))
      (Finset.univ.sum (fun i : Fin 4 => coefficients i * periodicTheta c P (scales i / M))) := by
  classical
  let A : Eis -> Complex := fun z => P (Ideal.Quotient.mk (Ideal.span {c}) z)
  have hFinite (S : Finset (Fin 4)) :
      HasSum (fun z : Eis => S.sum (fun i =>
        coefficients i * (A z * gaussian (scales i / M) (eisEmbedding z))))
        (S.sum (fun i => coefficients i * periodicTheta c P (scales i / M))) := by
    induction S using Finset.induction_on with
    | empty =>
      simpa only [Finset.sum_empty] using
        (hasSum_zero : HasSum (fun _ : Eis => (0 : Complex)) 0)
    | @insert i S hi ih =>
      simp only [Finset.sum_insert hi]
      have hh := (periodic_gaussian_summable c hc P (scales i / M)
        (div_pos (scales_pos i) hM)).hasSum
      change HasSum (fun z : Eis => A z * gaussian (scales i / M) (eisEmbedding z))
        (periodicTheta c P (scales i / M)) at hh
      exact (hh.mul_left (coefficients i)).add ih
  have hPoint (z : Eis) :
      A z * carrierProfile (norm (eisEmbedding z) ^ 2 / M) =
        Finset.univ.sum (fun i : Fin 4 =>
          coefficients i * (A z * gaussian (scales i / M) (eisEmbedding z))) := by
    rw [CubicGaussianWindow.profile_eq_gaussian_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simpa only [<- hPoint, A] using hFinite Finset.univ

theorem periodic_window_gaussian_expansion (c : Eis) (hc : Not (c = 0))
    (P : HasQuotient.Quotient Eis (Ideal.span {c}) -> Complex)
    (M : Real) (hM : 0 < M) :
    periodicWindow c P M =
      Finset.univ.sum (fun i : Fin 4 => coefficients i * periodicTheta c P (scales i / M)) :=
  (periodic_window_hasSum c hc P M hM).tsum_eq

theorem periodic_gaussian_transfer (c : Eis) (hc : Not (c = 0))
    (P : HasQuotient.Quotient Eis (Ideal.span {c}) -> Complex)
    (a : Real) (ha : 0 < a) :
    periodicTheta c P a =
      ((1 / (a * norm (eisEmbedding c) ^ 2) : Real) : Complex) *
        periodicTheta c (periodicFourier c hc P) (1 / (a * norm (eisEmbedding c) ^ 2)) := by
  simpa only [periodicTheta, periodicFourier] using
    CubicGaussianPair.periodic_gaussian c hc P a ha

private theorem gaussian_factor (a C : Real) :
    ((1 / (a * C ^ 2) : Real) : Complex) =
      (1 / (C : Complex)) / ((a : Complex) * (C : Complex)) := by
  push_cast
  simp only [div_eq_mul_inv, pow_two, mul_inv_rev, one_mul]
  ring

theorem periodic_window_transfer (c : Eis) (hc : Not (c = 0))
    (P : HasQuotient.Quotient Eis (Ideal.span {c}) -> Complex)
    (M : Real) (hM : 0 < M) :
    periodicWindow c P M =
      -((M : Complex) / (norm (eisEmbedding c) : Complex) ^ 2) *
        periodicWindow c (periodicFourier c hc P) (norm (eisEmbedding c) ^ 2 / M) := by
  let C : Real := norm (eisEmbedding c)
  have hC : 0 < C := norm_pos_iff.mpr (eisEmbedding_ne_zero hc)
  have hDual : 0 < C ^ 2 / M := div_pos (sq_pos_of_pos hC) hM
  rw [periodic_window_gaussian_expansion c hc P M hM,
    periodic_window_gaussian_expansion c hc (periodicFourier c hc P) (C ^ 2 / M) hDual]
  calc
    _ = Finset.univ.sum (fun i : Fin 4 => coefficients i *
        ((1 / (C : Complex)) / (((scales i / M : Real) : Complex) * (C : Complex)) *
          periodicTheta c (periodicFourier c hc P) (1 / ((scales i / M) * C ^ 2)))) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [periodic_gaussian_transfer c hc P (scales i / M)
        (div_pos (scales_pos i) hM), gaussian_factor]
    _ = -((M : Complex) / (C : Complex)) * (1 / (C : Complex)) *
        Finset.univ.sum (fun i : Fin 4 =>
          coefficients i * periodicTheta c (periodicFourier c hc P) (scales i / (C ^ 2 / M))) :=
      CubicGaussianWindow.reciprocal_four_sum
        (periodicTheta c (periodicFourier c hc P)) M C (1 / (C : Complex))
    _ = _ := by
      change _ = -((M : Complex) / (C : Complex) ^ 2) * _
      simp only [div_eq_mul_inv, pow_two, mul_inv_rev, one_mul]
      ring

section FullPair
variable {Index : Type} [DecidableEq Index]
variable (P : Index -> Ideal Eis)

abbrev pairSupport (S T : Finset Index) : Finset Index := Union.union S T

def fullModulus (S T : Finset Index) : Eis :=
  ActualEisensteinCubic.finitePrimeModulus (fun i : pairSupport S T => P i.val)

theorem fullModulus_ne_zero [forall i, (P i).IsMaximal] (S T : Finset Index) :
    Not (fullModulus P S T = 0) :=
  ActualEisensteinCubic.finitePrimeModulus_ne_zero (fun i : pairSupport S T => P i.val)

theorem fullModulus_mem (S T : Finset Index) (i : pairSupport S T) :
    Membership.mem (P i.val) (fullModulus P S T) := by
  let Q : pairSupport S T -> Ideal Eis := fun j => P j.val
  have hProd : Finset.univ.prod Q <= P i.val := by
    rw [<- Finset.prod_erase_mul Finset.univ Q (Finset.mem_univ i)]
    apply Ideal.mul_le.mpr
    intro r _ t ht
    exact Ideal.mul_mem_left (P i.val) r ht
  exact hProd (Submodule.IsPrincipal.generator_mem (Finset.univ.prod Q))

theorem fullModulus_norm_sq (S T : Finset Index) :
    norm (eisEmbedding (fullModulus P S T)) ^ 2 =
      (Ideal.absNorm (Finset.univ.prod (fun i : pairSupport S T => P i.val)) : Real) :=
  ActualEisensteinCubic.finitePrimeModulus_norm_sq (fun i : pairSupport S T => P i.val)

def residueFactor (S T : Finset Index) (i : pairSupport S T) :
    RingHom (HasQuotient.Quotient Eis (Ideal.span {fullModulus P S T}))
      (HasQuotient.Quotient Eis (P i.val)) :=
  Ideal.Quotient.factor ((Ideal.span_singleton_le_iff_mem (P i.val)).mpr
    (fullModulus_mem P S T i))

theorem residueFactor_mk (S T : Finset Index) (i : pairSupport S T) (z : Eis) :
    residueFactor P S T i (Ideal.Quotient.mk (Ideal.span {fullModulus P S T}) z) =
      Ideal.Quotient.mk (P i.val) z := rfl

variable [forall i, (P i).IsMaximal]
variable (hgood : forall i, Not (Membership.mem (P i) ActualEisensteinCubic.lambda))

def pairProfile (S T : Finset Index)
    (x : HasQuotient.Quotient Eis (Ideal.span {fullModulus P S T})) : Complex :=
  star (S.attach.prod (fun i : S =>
    (ActualEisensteinCubic.canonicalSextic (P i.val) (hgood i.val))
      (residueFactor P S T
        (Subtype.mk i.val (Finset.mem_union_left T i.property)) x))) *
  T.attach.prod (fun i : T =>
    (ActualEisensteinCubic.canonicalSextic (P i.val) (hgood i.val))
      (residueFactor P S T
        (Subtype.mk i.val (Finset.mem_union_right S i.property)) x))

theorem pairProfile_mk (S T : Finset Index) (z : Eis) :
    pairProfile P hgood S T (Ideal.Quotient.mk (Ideal.span {fullModulus P S T}) z) =
      star (ActualEisensteinCubic.finiteSquarefreeRow P hgood S z) *
        ActualEisensteinCubic.finiteSquarefreeRow P hgood T z := by
  unfold pairProfile
  simp_rw [residueFactor_mk]
  have hS := Finset.prod_attach S (fun i =>
    (ActualEisensteinCubic.canonicalSextic (P i) (hgood i)) (Ideal.Quotient.mk (P i) z))
  have hT := Finset.prod_attach T (fun i =>
    (ActualEisensteinCubic.canonicalSextic (P i) (hgood i)) (Ideal.Quotient.mk (P i) z))
  rw [hS, hT]
  rfl

theorem full_pair_window_hasSum (S T : Finset Index) (M : Real) (hM : 0 < M) :
    HasSum (fun z : Eis =>
      (star (ActualEisensteinCubic.finiteSquarefreeRow P hgood S z) *
        ActualEisensteinCubic.finiteSquarefreeRow P hgood T z) *
          carrierProfile (norm (eisEmbedding z) ^ 2 / M))
      (Finset.univ.sum (fun i : Fin 4 => coefficients i *
        periodicTheta (fullModulus P S T) (pairProfile P hgood S T) (scales i / M))) := by
  simpa only [pairProfile_mk] using
    periodic_window_hasSum (fullModulus P S T) (fullModulus_ne_zero P S T)
      (pairProfile P hgood S T) M hM

theorem full_pair_window_transfer (S T : Finset Index) (M : Real) (hM : 0 < M) :
    (tsum fun z : Eis =>
      (star (ActualEisensteinCubic.finiteSquarefreeRow P hgood S z) *
        ActualEisensteinCubic.finiteSquarefreeRow P hgood T z) *
          carrierProfile (norm (eisEmbedding z) ^ 2 / M)) =
      -((M : Complex) / (norm (eisEmbedding (fullModulus P S T)) : Complex) ^ 2) *
        periodicWindow (fullModulus P S T)
          (periodicFourier (fullModulus P S T) (fullModulus_ne_zero P S T)
            (pairProfile P hgood S T))
          (norm (eisEmbedding (fullModulus P S T)) ^ 2 / M) := by
  calc
    _ = periodicWindow (fullModulus P S T) (pairProfile P hgood S T) M := by
      unfold periodicWindow
      apply tsum_congr
      intro z
      rw [pairProfile_mk]
    _ = _ := periodic_window_transfer (fullModulus P S T)
      (fullModulus_ne_zero P S T) (pairProfile P hgood S T) M hM

def pairWindow (S T : Finset Index) (M : Real) : Complex :=
  periodicWindow (fullModulus P S T) (pairProfile P hgood S T) M

def dualPairWindow (S T : Finset Index) (M : Real) : Complex :=
  -((M : Complex) / (norm (eisEmbedding (fullModulus P S T)) : Complex) ^ 2) *
    periodicWindow (fullModulus P S T)
      (periodicFourier (fullModulus P S T) (fullModulus_ne_zero P S T)
        (pairProfile P hgood S T))
      (norm (eisEmbedding (fullModulus P S T)) ^ 2 / M)

def finiteRowSum {Coeff : Type} (C : Finset Coeff) (support : Coeff -> Finset Index)
    (a : Coeff -> Complex) (z : Eis) : Complex :=
  C.sum (fun i => a i * ActualEisensteinCubic.finiteSquarefreeRow P hgood (support i) z)

private theorem finite_hasSum {Coeff : Type} (C : Finset Coeff)
    (f : Coeff -> Eis -> Complex) (a : Coeff -> Complex)
    (h : forall i, Membership.mem C i -> HasSum (f i) (a i)) :
    HasSum (fun z : Eis => C.sum (fun i => f i z)) (C.sum a) := by
  classical
  induction C using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty] using
      (hasSum_zero : HasSum (fun _ : Eis => (0 : Complex)) 0)
  | @insert i C hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i C)).add
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

omit [DecidableEq Index] in
theorem finiteRowSum_norm_square {Coeff : Type} (C : Finset Coeff)
    (support : Coeff -> Finset Index) (a : Coeff -> Complex) (z : Eis) :
    ((norm (finiteRowSum P hgood C support a z) ^ 2 : Real) : Complex) =
      C.sum (fun i => C.sum (fun j => star (a i) * a j *
        (star (ActualEisensteinCubic.finiteSquarefreeRow P hgood (support i) z) *
          ActualEisensteinCubic.finiteSquarefreeRow P hgood (support j) z))) := by
  let v : Coeff -> Complex := fun i =>
    a i * ActualEisensteinCubic.finiteSquarefreeRow P hgood (support i) z
  have hNorm :
      ((norm (C.sum v) ^ 2 : Real) : Complex) =
        (starRingEnd Complex) (C.sum v) * C.sum v := by
    rw [Complex.sq_norm]
    exact (Complex.mul_conj (C.sum v)).symm.trans (mul_comm _ _)
  change ((norm (C.sum v) ^ 2 : Real) : Complex) = _
  rw [hNorm, map_sum, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul]
  change (star (a i) *
    star (ActualEisensteinCubic.finiteSquarefreeRow P hgood (support i) z)) *
      (a j * ActualEisensteinCubic.finiteSquarefreeRow P hgood (support j) z) = _
  ring

theorem finite_packet_window_hasSum {Coeff : Type} (C : Finset Coeff)
    (support : Coeff -> Finset Index) (a : Coeff -> Complex) (M : Real) (hM : 0 < M) :
    HasSum (fun z : Eis => carrierProfile (norm (eisEmbedding z) ^ 2 / M) *
      ((norm (finiteRowSum P hgood C support a z) ^ 2 : Real) : Complex))
      (C.sum (fun i => C.sum (fun j =>
        star (a i) * a j * pairWindow P hgood (support i) (support j) M))) := by
  have hPair (i j : Coeff) :
      HasSum (fun z : Eis =>
        (star (ActualEisensteinCubic.finiteSquarefreeRow P hgood (support i) z) *
          ActualEisensteinCubic.finiteSquarefreeRow P hgood (support j) z) *
            carrierProfile (norm (eisEmbedding z) ^ 2 / M))
        (pairWindow P hgood (support i) (support j) M) := by
    have h := (periodic_window_hasSum
      (fullModulus P (support i) (support j)) (fullModulus_ne_zero P (support i) (support j))
      (pairProfile P hgood (support i) (support j)) M hM).summable.hasSum
    simpa only [pairWindow, periodicWindow, pairProfile_mk] using h
  have hInner (i : Coeff) :
      HasSum (fun z : Eis => C.sum (fun j => star (a i) * a j *
        ((star (ActualEisensteinCubic.finiteSquarefreeRow P hgood (support i) z) *
          ActualEisensteinCubic.finiteSquarefreeRow P hgood (support j) z) *
            carrierProfile (norm (eisEmbedding z) ^ 2 / M))))
        (C.sum (fun j => star (a i) * a j *
          pairWindow P hgood (support i) (support j) M)) :=
    finite_hasSum C _ _ (fun j _ => (hPair i j).mul_left (star (a i) * a j))
  have hAll :
      HasSum (fun z : Eis => C.sum (fun i => C.sum (fun j => star (a i) * a j *
        ((star (ActualEisensteinCubic.finiteSquarefreeRow P hgood (support i) z) *
          ActualEisensteinCubic.finiteSquarefreeRow P hgood (support j) z) *
            carrierProfile (norm (eisEmbedding z) ^ 2 / M)))))
        (C.sum (fun i => C.sum (fun j => star (a i) * a j *
          pairWindow P hgood (support i) (support j) M))) :=
    finite_hasSum C _ _ (fun i _ => hInner i)
  have hPoint (z : Eis) :
      carrierProfile (norm (eisEmbedding z) ^ 2 / M) *
          ((norm (finiteRowSum P hgood C support a z) ^ 2 : Real) : Complex) =
        C.sum (fun i => C.sum (fun j => star (a i) * a j *
          ((star (ActualEisensteinCubic.finiteSquarefreeRow P hgood (support i) z) *
            ActualEisensteinCubic.finiteSquarefreeRow P hgood (support j) z) *
              carrierProfile (norm (eisEmbedding z) ^ 2 / M)))) := by
    rw [finiteRowSum_norm_square, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simpa only [<- hPoint] using hAll

theorem finite_packet_window_transfer {Coeff : Type} (C : Finset Coeff)
    (support : Coeff -> Finset Index) (a : Coeff -> Complex) (M : Real) (hM : 0 < M) :
    (tsum fun z : Eis => carrierProfile (norm (eisEmbedding z) ^ 2 / M) *
      ((norm (finiteRowSum P hgood C support a z) ^ 2 : Real) : Complex)) =
      C.sum (fun i => C.sum (fun j =>
        star (a i) * a j * dualPairWindow P hgood (support i) (support j) M)) := by
  rw [(finite_packet_window_hasSum P hgood C support a M hM).tsum_eq]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun x : Complex => star (a i) * a j * x)
  exact periodic_window_transfer (fullModulus P (support i) (support j))
    (fullModulus_ne_zero P (support i) (support j))
    (pairProfile P hgood (support i) (support j)) M hM

end FullPair

section Unit
variable {Index : Type} [DecidableEq Index]
variable (P : Index -> Ideal Eis) [forall i, (P i).IsMaximal]
variable (hgood : forall i, Not (Membership.mem (P i) ActualEisensteinCubic.lambda))

theorem pairWindow_unit (M : Real) :
    pairWindow P hgood Finset.empty Finset.empty M =
      CubicGaussianUnit.unitPacket M := by
  unfold pairWindow periodicWindow CubicGaussianUnit.unitPacket
  apply tsum_congr
  intro z
  rw [pairProfile_mk]
  simp [ActualEisensteinCubic.finiteSquarefreeRow, Finset.empty]

theorem dualPairWindow_unit (M : Real) (hM : 0 < M) :
    dualPairWindow P hgood Finset.empty Finset.empty M =
      CubicGaussianUnit.unitPacket M := by
  rw [<- pairWindow_unit P hgood M]
  exact (periodic_window_transfer _ (fullModulus_ne_zero P _ _) _ M hM).symm

theorem dualPairWindow_unit_bound (M : Real) (hM : 1 <= M) :
    norm (dualPairWindow P hgood Finset.empty Finset.empty M) <=
      EisensteinSchwartzPoisson.nonzeroLatticeEnvelopeConstant *
        CubicGaussianUnit.windowConstant / M := by
  rw [dualPairWindow_unit P hgood M (by linarith)]
  exact CubicGaussianUnit.unitPacket_bound M hM

end Unit

def nativePairWindow (I J : Ideal Eis) (M : Real) : Complex := by
  have : forall i : ConcretePrimeRowBridge.primePool F, (i.val).IsMaximal :=
    fun i => ConcretePrimeRowBridge.primePool_maximal F hFpos i
  exact pairWindow (fun i : ConcretePrimeRowBridge.primePool F => i.val)
    (ConcretePrimeRowBridge.primePool_good F hFgood)
    (ConcretePrimeRowBridge.idealSupport F I) (ConcretePrimeRowBridge.idealSupport F J) M

def nativeDualPairWindow (I J : Ideal Eis) (M : Real) : Complex := by
  have : forall i : ConcretePrimeRowBridge.primePool F, (i.val).IsMaximal :=
    fun i => ConcretePrimeRowBridge.primePool_maximal F hFpos i
  exact dualPairWindow (fun i : ConcretePrimeRowBridge.primePool F => i.val)
    (ConcretePrimeRowBridge.primePool_good F hFgood)
    (ConcretePrimeRowBridge.idealSupport F I) (ConcretePrimeRowBridge.idealSupport F J) M

theorem native_compensated_window_hasSum {q : Nat} (chi : DirichletCharacter Complex q)
    (WA WB : Nat -> Complex) (c : Complex) (M : Real) (hM : 0 < M) :
    HasSum (fun z : Eis => carrierProfile (norm (eisEmbedding z) ^ 2 / M) *
      ((norm (ConcretePrimeRowBridge.idealRowSum F hFpos hFgood chi WA z -
        c * ConcretePrimeRowBridge.idealRowSum F hFpos hFgood chi WB z) ^ 2 : Real) : Complex))
      (F.sum (fun I => F.sum (fun J =>
        star (ShortDraftHeckeBridge.baseChangeWeight chi I *
          (WA (Ideal.absNorm I) - c * WB (Ideal.absNorm I))) *
        (ShortDraftHeckeBridge.baseChangeWeight chi J *
          (WA (Ideal.absNorm J) - c * WB (Ideal.absNorm J))) *
            nativePairWindow F hFpos hFgood I J M))) := by
  have : forall i : ConcretePrimeRowBridge.primePool F, (i.val).IsMaximal :=
    fun i => ConcretePrimeRowBridge.primePool_maximal F hFpos i
  let a : Ideal Eis -> Complex := fun I =>
    ShortDraftHeckeBridge.baseChangeWeight chi I *
      (WA (Ideal.absNorm I) - c * WB (Ideal.absNorm I))
  have h := finite_packet_window_hasSum
    (fun i : ConcretePrimeRowBridge.primePool F => i.val)
    (ConcretePrimeRowBridge.primePool_good F hFgood)
    F (ConcretePrimeRowBridge.idealSupport F) a M hM
  have hRow (z : Eis) :
      finiteRowSum (fun i : ConcretePrimeRowBridge.primePool F => i.val)
        (ConcretePrimeRowBridge.primePool_good F hFgood)
        F (ConcretePrimeRowBridge.idealSupport F) a z =
      ConcretePrimeRowBridge.idealRowSum F hFpos hFgood chi WA z -
        c * ConcretePrimeRowBridge.idealRowSum F hFpos hFgood chi WB z := by
    change ConcretePrimeRowBridge.idealRowSum F hFpos hFgood chi
      (fun n => WA n - c * WB n) z = _
    exact idealRowSum_compensation F hFpos hFgood chi WA WB c z
  simp_rw [hRow] at h
  exact h

theorem native_compensated_window_transfer {q : Nat} (chi : DirichletCharacter Complex q)
    (WA WB : Nat -> Complex) (c : Complex) (M : Real) (hM : 0 < M) :
    (tsum fun z : Eis => carrierProfile (norm (eisEmbedding z) ^ 2 / M) *
      ((norm (ConcretePrimeRowBridge.idealRowSum F hFpos hFgood chi WA z -
        c * ConcretePrimeRowBridge.idealRowSum F hFpos hFgood chi WB z) ^ 2 : Real) : Complex)) =
      F.sum (fun I => F.sum (fun J =>
        star (ShortDraftHeckeBridge.baseChangeWeight chi I *
          (WA (Ideal.absNorm I) - c * WB (Ideal.absNorm I))) *
        (ShortDraftHeckeBridge.baseChangeWeight chi J *
          (WA (Ideal.absNorm J) - c * WB (Ideal.absNorm J))) *
            nativeDualPairWindow F hFpos hFgood I J M)) := by
  have : forall i : ConcretePrimeRowBridge.primePool F, (i.val).IsMaximal :=
    fun i => ConcretePrimeRowBridge.primePool_maximal F hFpos i
  let a : Ideal Eis -> Complex := fun I =>
    ShortDraftHeckeBridge.baseChangeWeight chi I *
      (WA (Ideal.absNorm I) - c * WB (Ideal.absNorm I))
  have h := finite_packet_window_transfer
    (fun i : ConcretePrimeRowBridge.primePool F => i.val)
    (ConcretePrimeRowBridge.primePool_good F hFgood)
    F (ConcretePrimeRowBridge.idealSupport F) a M hM
  have hRow (z : Eis) :
      finiteRowSum (fun i : ConcretePrimeRowBridge.primePool F => i.val)
        (ConcretePrimeRowBridge.primePool_good F hFgood)
        F (ConcretePrimeRowBridge.idealSupport F) a z =
      ConcretePrimeRowBridge.idealRowSum F hFpos hFgood chi WA z -
        c * ConcretePrimeRowBridge.idealRowSum F hFpos hFgood chi WB z := by
    change ConcretePrimeRowBridge.idealRowSum F hFpos hFgood chi
      (fun n => WA n - c * WB n) z = _
    exact idealRowSum_compensation F hFpos hFgood chi WA WB c z
  simp_rw [hRow] at h
  exact h

theorem idealSupport_one :
    ConcretePrimeRowBridge.idealSupport F (1 : Ideal Eis) = Finset.empty := by
  unfold ConcretePrimeRowBridge.idealSupport
  rw [UniqueFactorizationMonoid.normalizedFactors_one]
  simp [Finset.empty]

theorem native_unit_window (M : Real) (hM : 0 < M) :
    nativeDualPairWindow F hFpos hFgood 1 1 M = CubicGaussianUnit.unitPacket M := by
  have : forall i : ConcretePrimeRowBridge.primePool F, (i.val).IsMaximal :=
    fun i => ConcretePrimeRowBridge.primePool_maximal F hFpos i
  change dualPairWindow (fun i : ConcretePrimeRowBridge.primePool F => i.val)
    (ConcretePrimeRowBridge.primePool_good F hFgood)
    (ConcretePrimeRowBridge.idealSupport F 1) (ConcretePrimeRowBridge.idealSupport F 1) M = _
  rw [idealSupport_one]
  exact dualPairWindow_unit _ _ M hM

theorem native_unit_window_bound (M : Real) (hM : 1 <= M) :
    norm (nativeDualPairWindow F hFpos hFgood 1 1 M) <=
      EisensteinSchwartzPoisson.nonzeroLatticeEnvelopeConstant *
        CubicGaussianUnit.windowConstant / M := by
  rw [native_unit_window F hFpos hFgood M (by linarith)]
  exact CubicGaussianUnit.unitPacket_bound M hM

theorem native_compensated_unit_split {q : Nat} (chi : DirichletCharacter Complex q)
    (WA WB : Nat -> Complex) (c : Complex) (M : Real) (hM : 0 < M)
    (hOne : Membership.mem F (1 : Ideal Eis)) :
    let a : Ideal Eis -> Complex := fun I =>
      ShortDraftHeckeBridge.baseChangeWeight chi I *
        (WA (Ideal.absNorm I) - c * WB (Ideal.absNorm I))
    (tsum fun z : Eis => carrierProfile (norm (eisEmbedding z) ^ 2 / M) *
      ((norm (ConcretePrimeRowBridge.idealRowSum F hFpos hFgood chi WA z -
        c * ConcretePrimeRowBridge.idealRowSum F hFpos hFgood chi WB z) ^ 2 : Real) : Complex)) =
      star (a 1) * a 1 * CubicGaussianUnit.unitPacket M +
      (F.erase 1).sum (fun J =>
        star (a 1) * a J * nativeDualPairWindow F hFpos hFgood 1 J M +
        star (a J) * a 1 * nativeDualPairWindow F hFpos hFgood J 1 M) +
      (F.erase 1).sum (fun I => (F.erase 1).sum (fun J =>
        star (a I) * a J * nativeDualPairWindow F hFpos hFgood I J M)) := by
  dsimp only
  rw [native_compensated_window_transfer F hFpos hFgood chi WA WB c M hM]
  let a : Ideal Eis -> Complex := fun I =>
    ShortDraftHeckeBridge.baseChangeWeight chi I *
      (WA (Ideal.absNorm I) - c * WB (Ideal.absNorm I))
  let k : Ideal Eis -> Ideal Eis -> Complex := fun I J =>
    star (a I) * a J * nativeDualPairWindow F hFpos hFgood I J M
  have hs (f : Ideal Eis -> Complex) :
      F.sum f = (F.erase 1).sum f + f 1 :=
    (Finset.sum_erase_add F f hOne).symm
  have hSplit :
      F.sum (fun I => F.sum (fun J => k I J)) =
        k 1 1 +
        (F.erase 1).sum (fun J => k 1 J + k J 1) +
        (F.erase 1).sum (fun I => (F.erase 1).sum (fun J => k I J)) := by
    simp_rw [hs, Finset.sum_add_distrib]
    ring
  simpa only [k, a, native_unit_window F hFpos hFgood M hM] using hSplit

end PrimeFactorOscillations.CarmichaelMovingWindow
