/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCompensatedJetTaylor

/-! # Full homogeneous Gaussian states and deformation order

All polynomial monomials are retained with their signed coefficients.
A covariance square dilation measures the actual amplitude degree.
Odd total degrees vanish, and degree 2e carries exactly the covariance
factor c^e. This makes every high homogeneous degree invisible below its
deformation order, without estimating its terms separately.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

theorem gaussianWickMonomial_scale_square (z u : Complex) (n : Nat) :
    gaussianWickMonomial (u ^ 2 * z) n = u ^ n * gaussianWickMonomial z n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp only [gaussianWickMonomial, pow_zero, mul_one]
    | succ n =>
      cases n with
      | zero => simp only [gaussianWickMonomial, mul_zero]
      | succ n =>
        change gaussianWickMonomial (u ^ 2 * z) (n + 2) =
          u ^ (n + 2) * gaussianWickMonomial z (n + 2)
        rw [gaussianWickMonomial, gaussianWickMonomial, ih n (by omega), pow_add]
        ring

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem gaussianMonomialState_scale_square (z : Iota -> Complex) (d : Iota -> Nat)
    (u : Complex) :
    gaussianMonomialState (fun j => u ^ 2 * z j) d =
      u ^ Finset.sum Finset.univ d * gaussianMonomialState z d := by
  unfold gaussianMonomialState
  simp_rw [gaussianWickMonomial_scale_square]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

theorem gaussianMonomialState_scale_even (z : Iota -> Complex) (d : Iota -> Nat)
    (c : Complex) (e : Nat) (hDegree : Finset.sum Finset.univ d = 2 * e) :
    gaussianMonomialState (fun j => c * z j) d =
      c ^ e * gaussianMonomialState z d := by
  have h := gaussianMonomialState_scale_square z d (complexGaussianSquareRoot c)
  rw [complexGaussianSquareRoot_sq, hDegree, pow_mul, complexGaussianSquareRoot_sq] at h
  exact h

theorem gaussianMonomialState_odd_degree (z : Iota -> Complex) (d : Iota -> Nat)
    (e : Nat) (hDegree : Finset.sum Finset.univ d = 2 * e + 1) :
    gaussianMonomialState z d = 0 := by
  have h := gaussianMonomialState_scale_square z d (-1)
  have hSquare : (-1 : Complex) ^ 2 = 1 := by norm_num
  have hSign : (-1 : Complex) ^ (2 * e + 1) = -1 := by
    rw [pow_add, pow_mul]
    norm_num
  rw [hSquare, hDegree, hSign] at h
  simp only [one_mul, neg_one_mul] at h
  have hTwo : (2 : Complex) * gaussianMonomialState z d = 0 := by
    calc
      _ = gaussianMonomialState z d + gaussianMonomialState z d := by ring
      _ = -gaussianMonomialState z d + gaussianMonomialState z d :=
        congrArg (fun a : Complex => a + gaussianMonomialState z d) h
      _ = 0 := neg_add_cancel _
  exact (mul_eq_zero.mp hTwo).resolve_left (by norm_num)

def gaussianStateDegree (d : Finsupp Iota Nat) : Nat :=
  Finset.sum Finset.univ (fun j => d j)

def gaussianPolynomialDegreeState (z : Iota -> Complex)
    (p : MvPolynomial Iota Complex) (k : Nat) : Complex :=
  Finset.sum (p.support.filter (fun d => gaussianStateDegree d = k))
    (fun d => p.coeff d * gaussianMonomialState z (fun j => d j))

def gaussianPolynomialDegreeBound (p : MvPolynomial Iota Complex) : Nat :=
  p.support.sup gaussianStateDegree

theorem gaussianPolynomialDegreeState_scale_square
    (z : Iota -> Complex) (p : MvPolynomial Iota Complex) (u : Complex) (k : Nat) :
    gaussianPolynomialDegreeState (fun j => u ^ 2 * z j) p k =
      u ^ k * gaussianPolynomialDegreeState z p k := by
  unfold gaussianPolynomialDegreeState
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hDegree := (Finset.mem_filter.mp hd).2
  rw [gaussianMonomialState_scale_square]
  change gaussianStateDegree d = k at hDegree
  rw [show Finset.sum Finset.univ (fun j => d j) = k from hDegree]
  ring

theorem gaussianPolynomialDegreeState_scale_even
    (z : Iota -> Complex) (p : MvPolynomial Iota Complex) (c : Complex) (e : Nat) :
    gaussianPolynomialDegreeState (fun j => c * z j) p (2 * e) =
      c ^ e * gaussianPolynomialDegreeState z p (2 * e) := by
  unfold gaussianPolynomialDegreeState
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hDegree := (Finset.mem_filter.mp hd).2
  rw [gaussianMonomialState_scale_even z (fun j => d j) c e hDegree]
  ring

theorem gaussianPolynomialDegreeState_odd (z : Iota -> Complex)
    (p : MvPolynomial Iota Complex) (e : Nat) :
    gaussianPolynomialDegreeState z p (2 * e + 1) = 0 := by
  unfold gaussianPolynomialDegreeState
  apply Finset.sum_eq_zero
  intro d hd
  have hDegree := (Finset.mem_filter.mp hd).2
  rw [gaussianMonomialState_odd_degree z (fun j => d j) e hDegree, mul_zero]

theorem gaussianPolynomialState_by_degree (z : Iota -> Complex)
    (p : MvPolynomial Iota Complex) :
    gaussianPolynomialState z p =
      Finset.sum (Finset.range (gaussianPolynomialDegreeBound p + 1))
        (gaussianPolynomialDegreeState z p) := by
  have hMap : forall d, Membership.mem p.support d ->
      Membership.mem (Finset.range (gaussianPolynomialDegreeBound p + 1))
        (gaussianStateDegree d) := by
    intro d hd
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le
      (Finset.le_sup (f := gaussianStateDegree) hd))
  have hGroup := Finset.sum_fiberwise_of_maps_to hMap
    (fun d => p.coeff d * gaussianMonomialState z (fun j => d j))
  change Finset.sum p.support (fun d => p.coeff d * gaussianMonomialState z (fun j => d j)) = _
  exact hGroup.symm

theorem gaussianPolynomialState_amplitude_decomposition
    (z : Iota -> Complex) (p : MvPolynomial Iota Complex) (u : Complex) :
    gaussianPolynomialState (fun j => u ^ 2 * z j) p =
      Finset.sum (Finset.range (gaussianPolynomialDegreeBound p + 1))
        (fun k => u ^ k * gaussianPolynomialDegreeState z p k) := by
  rw [gaussianPolynomialState_by_degree]
  apply Finset.sum_congr rfl
  intro k hk
  exact gaussianPolynomialDegreeState_scale_square z p u k

theorem gaussianPolynomialDegreeState_analyticAt
    (z : Complex -> Iota -> Complex) (s : Complex)
    (hz : forall j, AnalyticAt Complex (fun w => z w j) s)
    (p : MvPolynomial Iota Complex) (k : Nat) :
    AnalyticAt Complex (fun w => gaussianPolynomialDegreeState (z w) p k) s := by
  unfold gaussianPolynomialDegreeState
  apply Finset.analyticAt_fun_sum
  intro d hd
  exact analyticAt_const.mul (gaussianMonomialState_analyticAt z s hz (fun j => d j))

theorem gaussianPolynomialDegreeState_high_derivative_zero
    (z : Complex -> Iota -> Complex)
    (hz : forall j, AnalyticAt Complex (fun w => z w j) 0)
    (p : MvPolynomial Iota Complex) (e k : Nat) (hk : k < e) :
    iteratedDeriv k
      (fun w => gaussianPolynomialDegreeState (fun j => w * z w j) p (2 * e)) 0 = 0 := by
  let f := fun w : Complex =>
    gaussianPolynomialDegreeState (fun j => w * z w j) p (2 * e)
  let g := fun w : Complex => gaussianPolynomialDegreeState (z w) p (2 * e)
  have hf : AnalyticAt Complex f 0 :=
    gaussianPolynomialDegreeState_analyticAt (fun w j => w * z w j) 0
      (fun j => analyticAt_id.mul (hz j)) p (2 * e)
  have hg : AnalyticAt Complex g 0 :=
    gaussianPolynomialDegreeState_analyticAt z 0 hz p (2 * e)
  have hFactor : Filter.Eventually
      (fun w => f w = (w - 0) ^ e * g w) (nhds (0 : Complex)) :=
    Filter.Eventually.of_forall (fun w => by
      simpa only [sub_zero, f, g] using
        gaussianPolynomialDegreeState_scale_even (z w) p w e)
  have hOrder : (e : ENat) <= analyticOrderAt f 0 :=
    (natCast_le_analyticOrderAt hf).mpr
      (Exists.intro g (And.intro hg (by simpa only [smul_eq_mul] using hFactor)))
  exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf).mp hOrder k hk

end PrimeFactorOscillations
