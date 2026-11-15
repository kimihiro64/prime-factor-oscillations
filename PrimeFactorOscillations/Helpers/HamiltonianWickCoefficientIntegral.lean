/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianWickProfileBijection

/-! # Actual Gaussian integrals of the complete scalar Wick coefficients

The auxiliary scalar degree is reindexed over every support and composition.
The resulting finite coefficient kernels are integrable for arbitrary complex
covariances. Their normalized integrals retain every signed Wick profile.
No exchange of an infinite Gaussian series with an integral is used.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota J : Type*} [Fintype Iota] [DecidableEq Iota]

theorem gaussianLinearProduct_map_prod (row : J -> Iota -> Complex) (xs : List J) :
    gaussianLinearProduct (xs.map row) =
      (xs.map (fun j => gaussianLinearForm (row j))).prod := by
  induction xs with
  | nil => rfl
  | cons j xs ih =>
    simp only [List.map_cons, gaussianLinearProduct, List.prod_cons, ih]

theorem gaussianLinearProduct_wickProfile {m : Nat}
    (row : J -> Iota -> Complex) (d : Composition m) (label : Fin d.length -> J) :
    gaussianLinearProduct ((wickProfileList d label).map row) =
      Finset.prod Finset.univ
        (fun i => gaussianLinearForm (row (label i)) ^ d.blocksFun i) := by
  rw [gaussianLinearProduct_map_prod]
  simp only [wickProfileList, List.map_flatten, List.map_map, Function.comp_def,
    List.map_ofFn, List.map_replicate, List.prod_flatten, List.prod_ofFn,
    List.prod_replicate]

def wickProfilePolynomial {m : Nat} (row : J -> Iota -> Complex)
    (d : Composition m) (label : Fin d.length -> J) : MvPolynomial Iota Complex :=
  MvPolynomial.C
      (Finset.prod Finset.univ (fun i => wickVertexCoefficient (d.blocksFun i))) *
    gaussianLinearProduct ((wickProfileList d label).map row)

def wickGaussianEvaluation (z : Iota -> Complex) (row : J -> Iota -> Complex)
    (x : Iota -> Real) (j : J) : Complex :=
  MvPolynomial.eval
    (fun i => complexGaussianSquareRoot (z i) * (x i : Complex))
    (gaussianLinearForm (row j))

def wickProfileScalarKernel {m : Nat} (z : Iota -> Complex)
    (row : J -> Iota -> Complex) (d : Composition m) (label : Fin d.length -> J)
    (x : Iota -> Real) : Complex :=
  Finset.prod Finset.univ (fun i =>
      wickVertexCoefficient (d.blocksFun i) *
        wickGaussianEvaluation z row x (label i) ^ d.blocksFun i) *
    standardGaussianPolynomialKernel z 1 x

theorem wickProfileScalarKernel_polynomial {m : Nat}
    (z : Iota -> Complex) (row : J -> Iota -> Complex)
    (d : Composition m) (label : Fin d.length -> J) :
    wickProfileScalarKernel z row d label =
      standardGaussianPolynomialKernel z (wickProfilePolynomial row d label) := by
  funext x
  simp only [wickProfileScalarKernel, wickProfilePolynomial,
    standardGaussianPolynomialKernel, gaussianMvTiltKernel,
    gaussianLinearProduct_wickProfile, wickGaussianEvaluation,
    map_mul, MvPolynomial.eval_C, map_prod, map_pow, map_one, one_mul,
    Finset.prod_mul_distrib]

theorem wickProfileScalarKernel_integrable {m : Nat}
    (z : Iota -> Complex) (row : J -> Iota -> Complex)
    (d : Composition m) (label : Fin d.length -> J) :
    MeasureTheory.Integrable (wickProfileScalarKernel z row d label)
      gaussianTensorMeasure := by
  rw [wickProfileScalarKernel_polynomial]
  exact standardGaussianPolynomialKernel_integrable z (wickProfilePolynomial row d label)

theorem wickProfileScalarKernel_normalized {m : Nat}
    (z : Iota -> Complex) (row : J -> Iota -> Complex)
    (d : Composition m) (label : Fin d.length -> J) :
    MeasureTheory.integral gaussianTensorMeasure (wickProfileScalarKernel z row d label) /
        gaussianTensorTiltNormalizer (fun _ : Iota => 0) =
      gaussianWickProfile z row d label := by
  rw [wickProfileScalarKernel_polynomial, standardGaussianPolynomial_normalized]
  unfold wickProfilePolynomial gaussianWickProfile gaussianLinearWickValue
  exact gaussianPolynomialState_C_mul z _ _

variable [Fintype J] [DecidableEq J]

def wickGaussianSupportKernel {m : Nat} (z : Iota -> Complex)
    (row : J -> Iota -> Complex) (p : Prod (Finset J) (Composition m))
    (x : Iota -> Real) : Complex :=
  wickScalarProfileContribution (wickGaussianEvaluation z row x) p *
    standardGaussianPolynomialKernel z 1 x

theorem wickGaussianSupportKernel_integrable (z : Iota -> Complex)
    (row : J -> Iota -> Complex) (e : Nat)
    (p : Prod (Finset J) (Composition (2 * e))) :
    MeasureTheory.Integrable (wickGaussianSupportKernel z row p) gaussianTensorMeasure := by
  unfold wickGaussianSupportKernel wickScalarProfileContribution
  by_cases hLen : p.snd.length = p.fst.card
  case pos =>
    simp only [dite_eq_left hLen]
    exact wickProfileScalarKernel_integrable z row p.snd
      (fun i => wickSupportLabel p.fst (Fin.cast hLen i))
  case neg =>
    simp only [dite_eq_right hLen, zero_mul]
    exact MeasureTheory.integrable_zero (Iota -> Real) Complex gaussianTensorMeasure

theorem wickGaussianSupportKernel_normalized (z : Iota -> Complex)
    (row : J -> Iota -> Complex) (e : Nat)
    (p : Prod (Finset J) (Composition (2 * e))) :
    MeasureTheory.integral gaussianTensorMeasure (wickGaussianSupportKernel z row p) /
        gaussianTensorTiltNormalizer (fun _ : Iota => 0) =
      gaussianWickSupportProfile z row e p.fst p.snd := by
  unfold wickGaussianSupportKernel wickScalarProfileContribution gaussianWickSupportProfile
  by_cases hLen : p.snd.length = p.fst.card
  case pos =>
    simp only [dite_eq_left hLen]
    exact wickProfileScalarKernel_normalized z row p.snd
      (fun i => wickSupportLabel p.fst (Fin.cast hLen i))
  case neg =>
    simp only [dite_eq_right hLen, zero_mul, MeasureTheory.integral_zero, zero_div]

def wickGaussianEvenCoefficientKernel (z : Iota -> Complex)
    (row : J -> Iota -> Complex) (e : Nat) (x : Iota -> Real) : Complex :=
  PowerSeries.coeff (2 * e)
      (Finset.prod Finset.univ
        (fun j => wickVertexScalarSeries (wickGaussianEvaluation z row x j))) *
    standardGaussianPolynomialKernel z 1 x

theorem wickGaussianEvenCoefficientKernel_sum (z : Iota -> Complex)
    (row : J -> Iota -> Complex) (e : Nat) :
    wickGaussianEvenCoefficientKernel z row e =
      (fun x => Finset.sum (wickProfileOwnerFinset (J := J) e)
        (fun p => wickGaussianSupportKernel z row p x)) := by
  funext x
  unfold wickGaussianEvenCoefficientKernel wickGaussianSupportKernel
  rw [wickVertexScalarProduct_coeff_profiles, Finset.sum_mul]

theorem wickGaussianEvenCoefficientKernel_integrable (z : Iota -> Complex)
    (row : J -> Iota -> Complex) (e : Nat) :
    MeasureTheory.Integrable (wickGaussianEvenCoefficientKernel z row e)
      gaussianTensorMeasure := by
  rw [wickGaussianEvenCoefficientKernel_sum]
  exact MeasureTheory.integrable_finsetSum (wickProfileOwnerFinset (J := J) e)
    (fun p _ => wickGaussianSupportKernel_integrable z row e p)

theorem wickGaussianEvenCoefficientKernel_normalized (z : Iota -> Complex)
    (row : J -> Iota -> Complex) (e : Nat) :
    MeasureTheory.integral gaussianTensorMeasure (wickGaussianEvenCoefficientKernel z row e) /
        gaussianTensorTiltNormalizer (fun _ : Iota => 0) =
      Finset.sum (wickProfileOwnerFinset (J := J) e)
        (fun p => gaussianWickSupportProfile z row e p.fst p.snd) := by
  rw [wickGaussianEvenCoefficientKernel_sum,
    MeasureTheory.integral_finsetSum (wickProfileOwnerFinset (J := J) e)
      (fun p _ => wickGaussianSupportKernel_integrable z row e p), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  exact wickGaussianSupportKernel_normalized z row e p

theorem wickProfileOwnerFinset_sum (e : Nat)
    (f : Prod (Finset J) (Composition (2 * e)) -> Complex) :
    Finset.sum (wickProfileOwnerFinset (J := J) e) f =
      Finset.sum (Finset.univ : Finset J).powerset (fun S =>
        Finset.sum (wickVertexProfiles e S.card) (fun d => f (Prod.mk S d))) := by
  have hDisjoint : Set.PairwiseDisjoint
      ((Finset.univ : Finset J).powerset : Set (Finset J))
      (fun S => (wickVertexProfiles e S.card).image (Prod.mk S)) := by
    intro S hS T hT hST
    apply Finset.disjoint_left.mpr
    intro p hpS hpT
    have hSimage := Finset.mem_image.mp hpS
    have hTimage := Finset.mem_image.mp hpT
    have hFstS : S = p.fst := congrArg Prod.fst hSimage.choose_spec.2
    have hFstT : T = p.fst := congrArg Prod.fst hTimage.choose_spec.2
    exact hST (hFstS.trans hFstT.symm)
  rw [wickProfileOwnerFinset, Finset.sum_biUnion hDisjoint]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.sum_image]
  intro d hd d' hd' h
  exact congrArg Prod.snd h

theorem wickGaussianSupport_sum_by_card (z : Iota -> Complex)
    (row : J -> Iota -> Complex) (e : Nat) :
    Finset.sum (wickProfileOwnerFinset (J := J) e)
        (fun p => gaussianWickSupportProfile z row e p.fst p.snd) =
      Finset.sum (Finset.range (Fintype.card J + 1))
        (fun v => gaussianWickDiagramCoefficient z row e v) := by
  rw [wickProfileOwnerFinset_sum]
  have hMap : forall S, Membership.mem (Finset.univ : Finset J).powerset S ->
      Membership.mem (Finset.range (Fintype.card J + 1)) S.card := by
    intro S hS
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Finset.card_le_univ S)
  have hGroup := Finset.sum_fiberwise_of_maps_to hMap
    (fun S => Finset.sum (wickVertexProfiles e S.card)
      (fun d => gaussianWickSupportProfile z row e S d))
  rw [<- hGroup]
  apply Finset.sum_congr rfl
  intro v hv
  have hFilter : (Finset.univ : Finset J).powerset.filter (fun S => S.card = v) =
      (Finset.univ : Finset J).powersetCard v := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
  rw [hFilter]
  unfold gaussianWickDiagramCoefficient
  apply Finset.sum_congr rfl
  intro S hS
  have hCard := (Finset.mem_powersetCard.mp hS).2
  rw [hCard]

theorem gaussianWickDiagramCoefficient_zero_of_card (z : Iota -> Complex)
    (row : J -> Iota -> Complex) (e v : Nat) (hv : Fintype.card J < v) :
    gaussianWickDiagramCoefficient z row e v = 0 := by
  unfold gaussianWickDiagramCoefficient
  apply Finset.sum_eq_zero
  intro S hS
  have hCard := (Finset.mem_powersetCard.mp hS).2
  have hLe := Finset.card_le_univ S
  omega

theorem wickGaussianSupport_sum_by_degree (z : Iota -> Complex)
    (row : J -> Iota -> Complex) (e : Nat) :
    Finset.sum (wickProfileOwnerFinset (J := J) e)
        (fun p => gaussianWickSupportProfile z row e p.fst p.snd) =
      Finset.sum (Finset.range (e + 1))
        (fun v => gaussianWickDiagramCoefficient z row e v) := by
  rw [wickGaussianSupport_sum_by_card]
  by_cases h : e <= Fintype.card J
  case pos =>
    symm
    apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right h 1))
    intro v hv hNot
    have hGe : e + 1 <= v :=
      Nat.le_of_not_gt (fun hLt => hNot (Finset.mem_range.mpr hLt))
    exact gaussianWickDiagramCoefficient_zero_of_support z row e v (by omega)
  case neg =>
    have hLe : Fintype.card J <= e := by omega
    apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hLe 1))
    intro v hv hNot
    have hGe : Fintype.card J + 1 <= v :=
      Nat.le_of_not_gt (fun hLt => hNot (Finset.mem_range.mpr hLt))
    exact gaussianWickDiagramCoefficient_zero_of_card z row e v (by omega)

theorem wickGaussianEvenCoefficientKernel_full_readout (z : Iota -> Complex)
    (row : J -> Iota -> Complex) (e : Nat) :
    MeasureTheory.integral gaussianTensorMeasure (wickGaussianEvenCoefficientKernel z row e) /
        gaussianTensorTiltNormalizer (fun _ : Iota => 0) =
      Finset.sum (Finset.range (e + 1))
        (fun v => gaussianWickDiagramCoefficient z row e v) := by
  rw [wickGaussianEvenCoefficientKernel_normalized, wickGaussianSupport_sum_by_degree]

end PrimeFactorOscillations
