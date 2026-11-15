/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Nat.Choose.Bounds
import PrimeFactorOscillations.Helpers.HamiltonianGaussianWickReadout

/-! # Complete finite Wick support and degree-profile coefficients

Every active vertex has degree at least three. All compositions and
all supports are summed, with the exact support binomial retained.
The support factorial is never replaced by an independent vertex choice.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota J : Type*} [Fintype Iota] [DecidableEq Iota]

def wickProfileList {k : Nat} (d : Composition k) (label : Fin d.length -> J) :
    List J :=
  (List.ofFn (fun i => List.replicate (d.blocksFun i) (label i))).flatten

theorem wickProfileList_length {k : Nat} (d : Composition k)
    (label : Fin d.length -> J) : (wickProfileList d label).length = k := by
  simp only [wickProfileList, List.length_flatten, List.map_ofFn,
    List.sum_ofFn, Function.comp_apply, List.length_replicate, d.sum_blocksFun]

def wickVertexProfiles (e v : Nat) : Finset (Composition (2 * e)) :=
  Finset.univ.filter (fun d =>
    And (d.length = v) (forall i, 3 <= d.blocksFun i))

theorem wickVertexProfiles_mem (e v : Nat) (d : Composition (2 * e)) :
    Membership.mem (wickVertexProfiles e v) d <->
      And (d.length = v) (forall i, 3 <= d.blocksFun i) := by
  simp only [wickVertexProfiles, Finset.mem_filter, Finset.mem_univ, true_and]

theorem wickVertexProfiles_card_le (e v : Nat) :
    (wickVertexProfiles e v).card <= 2 ^ (2 * e - 1) := by
  calc
    _ <= (Finset.univ : Finset (Composition (2 * e))).card := Finset.card_filter_le _ _
    _ = _ := by rw [Finset.card_univ, composition_card]

theorem wickVertexProfiles_support_bound (e v : Nat) (d : Composition (2 * e))
    (hd : Membership.mem (wickVertexProfiles e v) d) :
    3 * v <= 2 * e := by
  have hProfile := (wickVertexProfiles_mem e v d).mp hd
  have hSum : d.length * 3 <= 2 * e := by
    calc
      _ = Finset.sum (Finset.univ : Finset (Fin d.length)) (fun _ => (3 : Nat)) := by simp
      _ <= Finset.sum Finset.univ d.blocksFun :=
        Finset.sum_le_sum (fun i _ => hProfile.2 i)
      _ = 2 * e := d.sum_blocksFun
  rw [hProfile.1] at hSum
  omega

theorem wickVertexProfiles_empty_of_support (e v : Nat) (h : 2 * e < 3 * v) :
    wickVertexProfiles e v = EmptyCollection.emptyCollection := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro d hd
  have hBound := wickVertexProfiles_support_bound e v d hd
  omega

def gaussianWickProfile {k : Nat} (z : Iota -> Complex)
    (row : J -> Iota -> Complex) (d : Composition k) (label : Fin d.length -> J) :
    Complex :=
  Finset.prod Finset.univ (fun i => wickVertexCoefficient (d.blocksFun i)) *
    gaussianLinearWickValue z ((wickProfileList d label).map row)

theorem gaussianWickProfile_norm_bound
    (z : Iota -> Complex) (row : J -> Iota -> Complex)
    (c : Real) (hc : 0 <= c)
    (hCov : forall i j, norm (gaussianLinearCovariance z (row i) (row j)) <= c)
    (e : Nat) (d : Composition (2 * e)) (label : Fin d.length -> J) :
    norm (gaussianWickProfile z row d label) <= (wickPairCount e : Real) * c ^ e := by
  have hCoeffAll : forall S : Finset (Fin d.length),
      norm (Finset.prod S (fun i => wickVertexCoefficient (d.blocksFun i))) <= 1 := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
      rw [Finset.prod_insert hi, norm_mul]
      have hVertex := wickVertexCoefficient_norm_le_one (d.blocksFun i)
      nlinarith [norm_nonneg (wickVertexCoefficient (d.blocksFun i)),
        norm_nonneg (Finset.prod S (fun j => wickVertexCoefficient (d.blocksFun j)))]
  have hCoeff := hCoeffAll Finset.univ
  have hMoment : norm (gaussianLinearWickValue z ((wickProfileList d label).map row)) <=
      (wickPairCount e : Real) * c ^ e := by
    apply gaussianLinearWickValue_norm_bound z c hc e _
      (by rw [List.length_map, wickProfileList_length])
    intro a ha b hb
    cases List.mem_map.mp ha with
    | intro i hi =>
      cases hi with
      | intro hi hAi =>
        cases List.mem_map.mp hb with
        | intro j hj =>
          cases hj with
          | intro hj hBj =>
            rw [<- hAi, <- hBj]
            exact hCov i j
  unfold gaussianWickProfile
  rw [norm_mul]
  calc
    _ <= 1 * ((wickPairCount e : Real) * c ^ e) :=
      mul_le_mul hCoeff hMoment (norm_nonneg _) (by norm_num)
    _ = _ := one_mul _

variable [Fintype J] [DecidableEq J]

def wickSupportLabel (S : Finset J) (i : Fin S.card) : J :=
  ((Fintype.equivFin {j : J // Membership.mem S j}).symm
    (Fin.cast (by simp only [Fintype.card_coe]) i)).val

def gaussianWickSupportProfile (z : Iota -> Complex) (row : J -> Iota -> Complex)
    (e : Nat) (S : Finset J) (d : Composition (2 * e)) : Complex :=
  if h : d.length = S.card then
    gaussianWickProfile z row d
      (fun i => wickSupportLabel S (Fin.cast h i))
  else 0

def gaussianWickDiagramCoefficient (z : Iota -> Complex)
    (row : J -> Iota -> Complex) (e v : Nat) : Complex :=
  Finset.sum ((Finset.univ : Finset J).powersetCard v) (fun S =>
    Finset.sum (wickVertexProfiles e v) (fun d =>
      gaussianWickSupportProfile z row e S d))

theorem gaussianWickSupportProfile_norm_bound
    (z : Iota -> Complex) (row : J -> Iota -> Complex)
    (c : Real) (hc : 0 <= c)
    (hCov : forall i j, norm (gaussianLinearCovariance z (row i) (row j)) <= c)
    (e : Nat) (S : Finset J) (d : Composition (2 * e)) :
    norm (gaussianWickSupportProfile z row e S d) <=
      (wickPairCount e : Real) * c ^ e := by
  unfold gaussianWickSupportProfile
  split_ifs
  case pos h => exact gaussianWickProfile_norm_bound z row c hc hCov e d _
  case neg h =>
    rw [norm_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hc e)

theorem gaussianWickDiagramCoefficient_norm_bound
    (z : Iota -> Complex) (row : J -> Iota -> Complex)
    (c : Real) (hc : 0 <= c)
    (hCov : forall i j, norm (gaussianLinearCovariance z (row i) (row j)) <= c)
    (e v : Nat) :
    norm (gaussianWickDiagramCoefficient z row e v) <=
      ((Fintype.card J).choose v : Real) * (2 : Real) ^ (2 * e - 1) *
        ((wickPairCount e : Real) * c ^ e) := by
  let W : Real := (wickPairCount e : Real) * c ^ e
  have hW : 0 <= W := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hc e)
  have hCard : ((wickVertexProfiles e v).card : Real) <=
      (2 : Real) ^ (2 * e - 1) := by
    exact_mod_cast wickVertexProfiles_card_le e v
  unfold gaussianWickDiagramCoefficient
  calc
    _ <= Finset.sum ((Finset.univ : Finset J).powersetCard v)
        (fun S => norm (Finset.sum (wickVertexProfiles e v)
          (fun d => gaussianWickSupportProfile z row e S d))) := norm_sum_le _ _
    _ <= Finset.sum ((Finset.univ : Finset J).powersetCard v)
        (fun _ => ((wickVertexProfiles e v).card : Real) * W) := by
      apply Finset.sum_le_sum
      intro S hS
      calc
        _ <= Finset.sum (wickVertexProfiles e v)
            (fun d => norm (gaussianWickSupportProfile z row e S d)) := norm_sum_le _ _
        _ <= Finset.sum (wickVertexProfiles e v) (fun _ => W) :=
          Finset.sum_le_sum (fun d _ =>
            gaussianWickSupportProfile_norm_bound z row c hc hCov e S d)
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((Fintype.card J).choose v : Real) *
        ((wickVertexProfiles e v).card : Real) * W := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard, Finset.card_univ]
      ring
    _ <= _ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hCard (Nat.cast_nonneg _)) hW

theorem gaussianWickDiagramCoefficient_factorial_bound
    (z : Iota -> Complex) (row : J -> Iota -> Complex)
    (c : Real) (hc : 0 <= c)
    (hCov : forall i j, norm (gaussianLinearCovariance z (row i) (row j)) <= c)
    (e v : Nat) :
    norm (gaussianWickDiagramCoefficient z row e v) <=
      ((Fintype.card J : Real) ^ v / (v.factorial : Real)) *
        (2 : Real) ^ (2 * e - 1) * ((wickPairCount e : Real) * c ^ e) := by
  have hChoose : ((Fintype.card J).choose v : Real) <=
      (Fintype.card J : Real) ^ v / (v.factorial : Real) :=
    Nat.choose_le_pow_div v (Fintype.card J)
  exact le_trans (gaussianWickDiagramCoefficient_norm_bound z row c hc hCov e v)
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hChoose (pow_nonneg (by norm_num) _))
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hc e)))

theorem gaussianWickDiagramCoefficient_zero_of_support
    (z : Iota -> Complex) (row : J -> Iota -> Complex)
    (e v : Nat) (h : 2 * e < 3 * v) :
    gaussianWickDiagramCoefficient z row e v = 0 := by
  unfold gaussianWickDiagramCoefficient
  rw [wickVertexProfiles_empty_of_support e v h]
  simp only [Finset.sum_empty, Finset.sum_const_zero]


theorem wick_support_envelope_bound (n : Nat) (kappa : Real) (e v : Nat)
    (hn : 0 < n) (hKappa : 0 <= kappa) (he : 0 < e) (hVE : v <= e) :
    (((2 * (n : Real)) ^ v / (v.factorial : Real)) *
        (2 : Real) ^ (2 * e - 1) *
          ((wickPairCount e : Real) * (kappa / (n : Real)) ^ e)) <=
      (16 * kappa) ^ e * Real.exp (e : Real) *
        ((e : Real) / (n : Real)) ^ (e - v) := by
  have hn0 : Not ((n : Real) = 0) := ne_of_gt (Nat.cast_pos.mpr hn)
  have hf0 : Not ((v.factorial : Real) = 0) := by
    exact_mod_cast Nat.factorial_ne_zero v
  have hRatio : 0 <= (kappa / (n : Real)) ^ e :=
    pow_nonneg (div_nonneg hKappa (Nat.cast_nonneg n)) e
  have hEven : (2 : Real) ^ (2 * e - 1) <= (4 : Real) ^ e := by
    have hStep : 2 * e = (2 * e - 1) + 1 := by omega
    calc
      _ <= (2 : Real) ^ (2 * e - 1) * 2 := by
        nlinarith [pow_nonneg (by norm_num : (0 : Real) <= 2) (2 * e - 1)]
      _ = (2 : Real) ^ ((2 * e - 1) + 1) := (pow_succ _ _).symm
      _ = (2 : Real) ^ (2 * e) := congrArg (fun k : Nat => (2 : Real) ^ k) hStep.symm
      _ = (4 : Real) ^ e := by rw [pow_mul]; norm_num
  have hPairs : (wickPairCount e : Real) <= (2 * (e : Real)) ^ e := by
    exact_mod_cast wickPairCount_le_even_power e
  have hEpow : (e : Real) ^ e = (e : Real) ^ v * (e : Real) ^ (e - v) := by
    rw [<- pow_add, Nat.add_sub_of_le hVE]
  have hNpow : (n : Real) ^ e = (n : Real) ^ v * (n : Real) ^ (e - v) := by
    rw [<- pow_add, Nat.add_sub_of_le hVE]
  have hEight : (8 : Real) ^ e = (4 : Real) ^ e * (2 : Real) ^ e := by
    rw [<- mul_pow]
    norm_num
  have hAlgebra :
      ((2 * (n : Real)) ^ v / (v.factorial : Real)) * (4 : Real) ^ e *
          ((2 * (e : Real)) ^ e * (kappa / (n : Real)) ^ e) =
        (8 * kappa) ^ e *
          ((2 : Real) ^ v * ((e : Real) ^ v / (v.factorial : Real))) *
            ((e : Real) / (n : Real)) ^ (e - v) := by
    simp only [mul_pow, div_pow]
    rw [hEight, hEpow, hNpow]
    field_simp
  have hTwo : forall k : Nat, (1 : Real) <= (2 : Real) ^ k := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih => rw [pow_succ]; nlinarith
  have hTwoMono : (2 : Real) ^ v <= (2 : Real) ^ e := by
    have h := mul_le_mul_of_nonneg_left (hTwo (e - v))
      (pow_nonneg (by norm_num : (0 : Real) <= 2) v)
    rw [<- pow_add, Nat.add_sub_of_le hVE, mul_one] at h
    exact h
  have hExp : (e : Real) ^ v / (v.factorial : Real) <= Real.exp (e : Real) :=
    Real.pow_div_factorial_le_exp (e : Real) (Nat.cast_nonneg e) v
  have hJoint : (2 : Real) ^ v * ((e : Real) ^ v / (v.factorial : Real)) <=
      (2 : Real) ^ e * Real.exp (e : Real) :=
    mul_le_mul hTwoMono hExp
      (div_nonneg (pow_nonneg (Nat.cast_nonneg e) v) (Nat.cast_nonneg _))
      (pow_nonneg (by norm_num) e)
  have hConstant : (8 * kappa) ^ e * (2 : Real) ^ e = (16 * kappa) ^ e := by
    rw [<- mul_pow]
    congr 1
    ring
  calc
    _ <= ((2 * (n : Real)) ^ v / (v.factorial : Real)) * (4 : Real) ^ e *
        ((2 * (e : Real)) ^ e * (kappa / (n : Real)) ^ e) := by
      simp only [mul_assoc]
      apply mul_le_mul_of_nonneg_left
      exact mul_le_mul hEven (mul_le_mul_of_nonneg_right hPairs hRatio)
        (mul_nonneg (Nat.cast_nonneg _) hRatio) (pow_nonneg (by norm_num) e)
      exact div_nonneg (pow_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) v)
        (Nat.cast_nonneg _)
    _ = _ := hAlgebra
    _ <= (8 * kappa) ^ e * ((2 : Real) ^ e * Real.exp (e : Real)) *
        ((e : Real) / (n : Real)) ^ (e - v) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hJoint
          (pow_nonneg (mul_nonneg (by norm_num) hKappa) e))
        (pow_nonneg (div_nonneg (Nat.cast_nonneg e) (Nat.cast_nonneg n)) _)
    _ = _ := by rw [<- mul_assoc ((8 * kappa) ^ e), hConstant]

theorem gaussianWickDiagramCoefficient_support_envelope
    (z : Iota -> Complex) (row : J -> Iota -> Complex) (n : Nat)
    (kappa : Real) (e v : Nat)
    (hCard : Fintype.card J = 2 * n) (hn : 0 < n) (hKappa : 0 <= kappa)
    (he : 0 < e) (hVE : v <= e)
    (hCov : forall i j,
      norm (gaussianLinearCovariance z (row i) (row j)) <= kappa / (n : Real)) :
    norm (gaussianWickDiagramCoefficient z row e v) <=
      (16 * kappa) ^ e * Real.exp (e : Real) *
        ((e : Real) / (n : Real)) ^ (e - v) := by
  have hBase := gaussianWickDiagramCoefficient_factorial_bound z row
    (kappa / (n : Real)) (div_nonneg hKappa (Nat.cast_nonneg n)) hCov e v
  rw [hCard] at hBase
  push_cast at hBase
  exact le_trans hBase (wick_support_envelope_bound n kappa e v hn hKappa he hVE)

end PrimeFactorOscillations
