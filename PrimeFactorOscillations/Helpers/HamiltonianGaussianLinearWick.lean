/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianGaussianPolynomialState

/-! # Mixed linear Gaussian moments with every contraction retained

The complete finite Wick recursion is derived from the polynomial Stein
identity. Contractions include repeated vertices and all off-diagonal
covariances; no independent term or compensation is discarded.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota Term : Type*} [Fintype Iota] [DecidableEq Iota]

theorem gaussianPolynomialState_one (z : Iota -> Complex) :
    gaussianPolynomialState z 1 = 1 := by
  change gaussianPolynomialState z (MvPolynomial.monomial 0 1) = 1
  rw [gaussianPolynomialState_monomial]
  simp [gaussianMonomialState, gaussianWickMonomial]

theorem gaussianPolynomialState_sum (z : Iota -> Complex)
    (S : Finset Term) (f : Term -> MvPolynomial Iota Complex) :
    gaussianPolynomialState z (Finset.sum S f) =
      Finset.sum S (fun t => gaussianPolynomialState z (f t)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, gaussianPolynomialState_zero]
  | @insert t S ht ih =>
    rw [Finset.sum_insert ht, gaussianPolynomialState_add, ih,
      Finset.sum_insert ht]

def gaussianLinearForm (a : Iota -> Complex) : MvPolynomial Iota Complex :=
  Finset.sum Finset.univ (fun i => MvPolynomial.C (a i) * MvPolynomial.X i)

def gaussianLinearCovariance (z a b : Iota -> Complex) : Complex :=
  Finset.sum Finset.univ (fun i => z i * a i * b i)

def gaussianDirectionalDerivative (z a : Iota -> Complex)
    (p : MvPolynomial Iota Complex) : MvPolynomial Iota Complex :=
  Finset.sum Finset.univ
    (fun i => MvPolynomial.C (z i * a i) * MvPolynomial.pderiv i p)

theorem gaussianLinearForm_pderiv (a : Iota -> Complex) (i : Iota) :
    MvPolynomial.pderiv i (gaussianLinearForm a) = MvPolynomial.C (a i) := by
  unfold gaussianLinearForm
  rw [map_sum]
  calc
    _ = MvPolynomial.pderiv i (MvPolynomial.C (a i) * MvPolynomial.X i) := by
      exact Finset.sum_eq_single i
        (fun j _ hji => by
          rw [MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X_of_ne hji, mul_zero])
        (fun hi => False.elim (hi (Finset.mem_univ i)))
    _ = MvPolynomial.C (a i) := by
      rw [MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X_self, mul_one]

theorem gaussianDirectionalDerivative_one (z a : Iota -> Complex) :
    gaussianDirectionalDerivative z a 1 = 0 := by
  unfold gaussianDirectionalDerivative
  apply Finset.sum_eq_zero
  intro i hi
  rw [MvPolynomial.pderiv_one, mul_zero]

theorem gaussianDirectionalDerivative_mul (z a : Iota -> Complex)
    (p q : MvPolynomial Iota Complex) :
    gaussianDirectionalDerivative z a (p * q) =
      gaussianDirectionalDerivative z a p * q +
        p * gaussianDirectionalDerivative z a q := by
  unfold gaussianDirectionalDerivative
  rw [Finset.sum_mul, Finset.mul_sum, <- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [MvPolynomial.pderiv_mul]
  ring

theorem gaussianDirectionalDerivative_linear (z a b : Iota -> Complex) :
    gaussianDirectionalDerivative z a (gaussianLinearForm b) =
      MvPolynomial.C (gaussianLinearCovariance z a b) := by
  unfold gaussianDirectionalDerivative gaussianLinearCovariance
  calc
    _ = Finset.sum Finset.univ (fun i => MvPolynomial.C (z i * a i * b i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [gaussianLinearForm_pderiv, <- map_mul]
    _ = _ := (map_sum MvPolynomial.C _ _).symm

theorem gaussianLinearForm_stein (z a : Iota -> Complex)
    (p : MvPolynomial Iota Complex) :
    gaussianPolynomialState z (gaussianLinearForm a * p) =
      gaussianPolynomialState z (gaussianDirectionalDerivative z a p) := by
  unfold gaussianLinearForm gaussianDirectionalDerivative
  rw [Finset.sum_mul, gaussianPolynomialState_sum, gaussianPolynomialState_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_assoc, gaussianPolynomialState_C_mul, gaussianPolynomialState_C_mul,
    gaussianPolynomialState_stein]
  ring

def gaussianLinearProduct : List (Iota -> Complex) -> MvPolynomial Iota Complex
  | [] => 1
  | a :: xs => gaussianLinearForm a * gaussianLinearProduct xs

theorem gaussianDirectionalDerivative_product (z a : Iota -> Complex)
    (xs : List (Iota -> Complex)) :
    gaussianDirectionalDerivative z a (gaussianLinearProduct xs) =
      Finset.sum (Finset.range xs.length) (fun k =>
        MvPolynomial.C (gaussianLinearCovariance z a (xs.getD k (fun _ => 0))) *
          gaussianLinearProduct (xs.eraseIdx k)) := by
  induction xs with
  | nil =>
    simp only [gaussianLinearProduct, gaussianDirectionalDerivative_one,
      List.length_nil, Finset.sum_range_zero]
  | cons b xs ih =>
    rw [gaussianLinearProduct, gaussianDirectionalDerivative_mul,
      gaussianDirectionalDerivative_linear, ih]
    have hTail :
        gaussianLinearForm b *
            Finset.sum (Finset.range xs.length) (fun k =>
              MvPolynomial.C (gaussianLinearCovariance z a
                (xs.getD k (fun _ => 0))) * gaussianLinearProduct (xs.eraseIdx k)) =
          Finset.sum (Finset.range xs.length) (fun k =>
            MvPolynomial.C (gaussianLinearCovariance z a
              (xs.getD k (fun _ => 0))) *
                gaussianLinearProduct (b :: xs.eraseIdx k)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [gaussianLinearProduct]
      ring
    rw [hTail, List.length_cons, Finset.sum_range_succ']
    have hZero : (b :: xs).getD 0 (fun _ => 0) = b := rfl
    have hEraseZero : (b :: xs).eraseIdx 0 = xs := rfl
    rw [hZero, hEraseZero, add_comm]
    apply congrArg (fun u => u +
      MvPolynomial.C (gaussianLinearCovariance z a b) * gaussianLinearProduct xs)
    apply Finset.sum_congr rfl
    intro k hk
    have hGet : (b :: xs).getD (k + 1) (fun _ => 0) =
        xs.getD k (fun _ => 0) := rfl
    have hErase : (b :: xs).eraseIdx (k + 1) = b :: xs.eraseIdx k := rfl
    rw [hGet, hErase]

def gaussianLinearWickValue (z : Iota -> Complex)
    (xs : List (Iota -> Complex)) : Complex :=
  gaussianPolynomialState z (gaussianLinearProduct xs)

theorem gaussianLinearWickValue_nil (z : Iota -> Complex) :
    gaussianLinearWickValue z [] = 1 :=
  gaussianPolynomialState_one z

theorem gaussianLinearWickValue_cons (z a : Iota -> Complex)
    (xs : List (Iota -> Complex)) :
    gaussianLinearWickValue z (a :: xs) =
      Finset.sum (Finset.range xs.length) (fun k =>
        gaussianLinearCovariance z a (xs.getD k (fun _ => 0)) *
          gaussianLinearWickValue z (xs.eraseIdx k)) := by
  unfold gaussianLinearWickValue
  rw [gaussianLinearProduct, gaussianLinearForm_stein,
    gaussianDirectionalDerivative_product, gaussianPolynomialState_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [gaussianPolynomialState_C_mul]

theorem gaussianLinearWickValue_integral (z w : Iota -> Complex)
    (hz : forall i, norm (z i) < 1)
    (hw : forall i, w i ^ 2 = z i / (1 + z i))
    (xs : List (Iota -> Complex)) :
    MeasureTheory.integral gaussianTensorMeasure
        (gaussianMvTiltKernel z w (gaussianLinearProduct xs)) /
        gaussianTensorTiltNormalizer z =
      gaussianLinearWickValue z xs :=
  gaussianMvTiltKernel_normalized z w hz hw (gaussianLinearProduct xs)

private theorem linearWick_getD_mem (xs : List (Iota -> Complex))
    (k : Nat) (hk : k < xs.length) :
    Membership.mem xs (xs.getD k (fun _ => 0)) := by
  induction xs generalizing k with
  | nil =>
    simp only [List.length_nil, Nat.not_lt_zero] at hk
  | cons a xs ih =>
    cases k with
    | zero => exact List.mem_cons_self
    | succ k =>
      change Membership.mem (a :: xs) (xs.getD k (fun _ => 0))
      exact List.mem_cons_of_mem a (ih k (by
        simpa only [List.length_cons] using Nat.lt_of_succ_lt_succ hk))

theorem gaussianLinearWickValue_norm_bound (z : Iota -> Complex)
    (c : Real) (hc : 0 <= c) (e : Nat) (xs : List (Iota -> Complex))
    (hLen : xs.length = 2 * e)
    (hCov : forall a, Membership.mem xs a ->
      forall b, Membership.mem xs b -> norm (gaussianLinearCovariance z a b) <= c) :
    norm (gaussianLinearWickValue z xs) <= (wickPairCount e : Real) * c ^ e := by
  induction e generalizing xs with
  | zero =>
    cases xs with
    | nil =>
      simp only [gaussianLinearWickValue_nil, wickPairCount, Nat.cast_one,
        pow_zero, mul_one, norm_one, le_refl]
    | cons a ys =>
      simp only [List.length_cons] at hLen
      omega
  | succ e ih =>
    cases xs with
    | nil =>
      simp only [List.length_nil] at hLen
      omega
    | cons a ys =>
      have hYs : ys.length = 2 * e + 1 := by
        simp only [List.length_cons] at hLen
        omega
      rw [gaussianLinearWickValue_cons]
      calc
        norm (Finset.sum (Finset.range ys.length) (fun k =>
            gaussianLinearCovariance z a (ys.getD k (fun _ => 0)) *
              gaussianLinearWickValue z (ys.eraseIdx k))) <=
          Finset.sum (Finset.range ys.length) (fun k =>
            norm (gaussianLinearCovariance z a (ys.getD k (fun _ => 0))) *
              norm (gaussianLinearWickValue z (ys.eraseIdx k))) := by
            simpa only [norm_mul] using
              (norm_sum_le (Finset.range ys.length) (fun k =>
                gaussianLinearCovariance z a (ys.getD k (fun _ => 0)) *
                  gaussianLinearWickValue z (ys.eraseIdx k)))
        _ <= Finset.sum (Finset.range ys.length)
            (fun _ => c * ((wickPairCount e : Real) * c ^ e)) := by
          apply Finset.sum_le_sum
          intro k hk
          have hkLt := Finset.mem_range.mp hk
          have hErase := List.length_eraseIdx_add_one hkLt
          have hEraseLen : (ys.eraseIdx k).length = 2 * e := by omega
          have hAllowed : forall u, Membership.mem (ys.eraseIdx k) u ->
              Membership.mem (a :: ys) u := by
            intro u hu
            exact List.mem_cons_of_mem a ((List.eraseIdx_sublist ys k).subset hu)
          have hCovRest : forall u, Membership.mem (ys.eraseIdx k) u ->
              forall v, Membership.mem (ys.eraseIdx k) v ->
                norm (gaussianLinearCovariance z u v) <= c := by
            intro u hu v hv
            exact hCov u (hAllowed u hu) v (hAllowed v hv)
          have hValue := ih (ys.eraseIdx k) hEraseLen hCovRest
          have hEntry : norm (gaussianLinearCovariance z a
              (ys.getD k (fun _ => 0))) <= c :=
            hCov a List.mem_cons_self _ (List.mem_cons_of_mem a
              (linearWick_getD_mem ys k hkLt))
          exact mul_le_mul hEntry hValue (norm_nonneg _) hc
        _ = (wickPairCount (e + 1) : Real) * c ^ (e + 1) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hYs,
            wickPairCount, pow_succ]
          push_cast
          ring

theorem gaussianLinearWickIntegral_norm_bound (z w : Iota -> Complex)
    (hz : forall i, norm (z i) < 1)
    (hw : forall i, w i ^ 2 = z i / (1 + z i))
    (c : Real) (hc : 0 <= c) (e : Nat) (xs : List (Iota -> Complex))
    (hLen : xs.length = 2 * e)
    (hCov : forall a, Membership.mem xs a ->
      forall b, Membership.mem xs b -> norm (gaussianLinearCovariance z a b) <= c) :
    norm (MeasureTheory.integral gaussianTensorMeasure
        (gaussianMvTiltKernel z w (gaussianLinearProduct xs)) /
        gaussianTensorTiltNormalizer z) <= (wickPairCount e : Real) * c ^ e := by
  rw [gaussianLinearWickValue_integral z w hz hw xs]
  exact gaussianLinearWickValue_norm_bound z c hc e xs hLen hCov

end PrimeFactorOscillations
