/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianLowWickProfiles
import PrimeFactorOscillations.Helpers.HamiltonianWickPairSupports

/-! # Complete low Wick normal form with its diagonal compensation

Every low support and composition is classified before converting the
unordered degree-three pairs to the full ordered off-diagonal sum.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

variable {Iota J : Type*} [Fintype Iota] [DecidableEq Iota]

theorem gaussianWickProfile_two_triples
    (z : Iota -> Complex) (row : J -> Iota -> Complex) (label : Fin 2 -> J) :
    gaussianWickProfile z row wickTriplePairComposition label =
      (1 / 9 : Complex) * gaussianLinearWickValue z
        [row (label 0), row (label 0), row (label 0),
          row (label 1), row (label 1), row (label 1)] := by
  have hGet : forall i : Fin 2, ([3, 3] : List Nat).get i = 3 := by
    intro i
    have hi : i.val < 2 := i.isLt
    have hCases : Or (i.val = 0) (i.val = 1) := by omega
    cases hCases with
    | inl h =>
      have hIndex : i = (0 : Fin 2) := Fin.ext h
      rw [hIndex]
      rfl
    | inr h =>
      have hIndex : i = (1 : Fin 2) := Fin.ext h
      rw [hIndex]
      rfl
  change (Finset.prod (Finset.univ : Finset (Fin 2))
      (fun i => wickVertexCoefficient (([3, 3] : List Nat).get i))) *
    gaussianLinearWickValue z
      ((List.ofFn (fun i : Fin 2 =>
        List.replicate (([3, 3] : List Nat).get i) (label i))).flatten.map row) = _
  simp_rw [hGet]
  have hProd : Finset.prod (Finset.univ : Finset (Fin 2))
      (fun _ => wickVertexCoefficient 3) = (1 / 9 : Complex) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, wickVertexCoefficient_low.1]
    norm_num
  rw [hProd]
  simp [List.ofFn_succ]

theorem gaussianWickSupportProfile_two_triples [Fintype J] [DecidableEq J]
    (z : Iota -> Complex) (row : J -> Iota -> Complex)
    (i j : J) (hij : Not (i = j)) :
    gaussianWickSupportProfile z row 3 {i, j} wickTriplePairComposition =
      (1 / 9 : Complex) * gaussianLinearWickValue z
        [row i, row i, row i, row j, row j, row j] := by
  let S : Finset J := {i, j}
  have hCard : S.card = 2 := by dsimp only [S]; simp [hij]
  have hLength : wickTriplePairComposition.length = S.card := by
    change 2 = S.card
    exact hCard.symm
  let label : Fin 2 -> J := fun k => wickSupportLabel S (Fin.cast hLength k)
  have hMem0 : Or (label 0 = i) (label 0 = j) := by
    have h := wickSupportLabel_mem S (Fin.cast hLength (0 : Fin 2))
    simpa only [S, Finset.mem_insert, Finset.mem_singleton] using h
  have hMem1 : Or (label 1 = i) (label 1 = j) := by
    have h := wickSupportLabel_mem S (Fin.cast hLength (1 : Fin 2))
    simpa only [S, Finset.mem_insert, Finset.mem_singleton] using h
  have hNe : Not (label 0 = label 1) := by
    intro h
    have hIndex := wickSupportLabel_injective S h
    have hVal := congrArg Fin.val hIndex
    change (0 : Nat) = 1 at hVal
    omega
  unfold gaussianWickSupportProfile
  change (if h : wickTriplePairComposition.length = S.card then
    gaussianWickProfile z row wickTriplePairComposition
      (fun k => wickSupportLabel S (Fin.cast h k)) else 0) = _
  rw [dif_pos hLength]
  change gaussianWickProfile z row wickTriplePairComposition label = _
  refine (gaussianWickProfile_two_triples z row label).trans ?_
  cases hMem0 with
  | inl hi0 =>
    cases hMem1 with
    | inl hi1 => exact False.elim (hNe (hi0.trans hi1.symm))
    | inr hj1 => rw [hi0, hj1]
  | inr hj0 =>
    cases hMem1 with
    | inl hi1 =>
      rw [hj0, hi1, gaussianLinearWickValue_two_triples_comm z (row j) (row i)]
    | inr hj1 => exact False.elim (hNe (hj0.trans hj1.symm))

theorem gaussianWickDiagramCoefficient_two_triples [Fintype J] [DecidableEq J]
    (z : Iota -> Complex) (row : J -> Iota -> Complex) :
    gaussianWickDiagramCoefficient z row 3 2 =
      (1 / 18 : Complex) * Finset.sum Finset.univ (fun i =>
        Finset.sum Finset.univ (fun j => if i = j then 0 else
          gaussianLinearWickValue z [row i, row i, row i, row j, row j, row j])) := by
  let g : Finset J -> Complex := fun S =>
    gaussianWickSupportProfile z row 3 S wickTriplePairComposition
  have hDiagram : gaussianWickDiagramCoefficient z row 3 2 =
      Finset.sum ((Finset.univ : Finset J).powersetCard 2) g := by
    unfold gaussianWickDiagramCoefficient
    rw [wickVertexProfiles_low_two_triples]
    simp only [Finset.sum_singleton]
    rfl
  have hDouble := wick_two_support_sum_eq_ordered (Finset.univ : Finset J) g
  rw [<- hDiagram] at hDouble
  have hEach :
      Finset.sum Finset.univ (fun i => Finset.sum Finset.univ
        (fun j => if i = j then 0 else g {i, j})) =
      (1 / 9 : Complex) * Finset.sum Finset.univ (fun i =>
        Finset.sum Finset.univ (fun j => if i = j then 0 else
          gaussianLinearWickValue z [row i, row i, row i, row j, row j, row j])) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i = j
    case pos => simp only [hij, ite_true, mul_zero]
    case neg =>
      rw [if_neg hij, if_neg hij]
      exact gaussianWickSupportProfile_two_triples z row i j hij
  rw [hEach] at hDouble
  calc
    _ = (1 / 2 : Complex) * (2 * gaussianWickDiagramCoefficient z row 3 2) := by ring
    _ = _ := by rw [hDouble]; ring

theorem gaussianWickLowValue_eq_degreeSix [Fintype J] [DecidableEq J]
    (z : Iota -> Complex) (row : J -> Iota -> Complex) :
    gaussianWickLowValue z row = 1 + gaussianLinearDegreeSixValue z row := by
  rw [gaussianWickLowValue_three_profiles,
    gaussianWickDiagramCoefficient_single z row 2 (by omega),
    gaussianWickDiagramCoefficient_single z row 3 (by omega),
    gaussianWickDiagramCoefficient_two_triples]
  have hFour : wickVertexCoefficient (2 * 2) = -(1 / 4 : Complex) :=
    wickVertexCoefficient_low.2.1
  have hSix : wickVertexCoefficient (2 * 3) = -(1 / 9 : Complex) :=
    wickVertexCoefficient_low.2.2.2
  rw [hFour, hSix]
  unfold gaussianLinearDegreeSixValue
  simp only [List.map_cons, List.map_nil]
  change 1 + (-(1 / 4 : Complex)) *
      Finset.sum Finset.univ (fun i => gaussianLinearWickValue z
        [row i, row i, row i, row i]) +
    (-(1 / 9 : Complex)) *
      Finset.sum Finset.univ (fun i => gaussianLinearWickValue z
        [row i, row i, row i, row i, row i, row i]) +
    (1 / 18 : Complex) * Finset.sum Finset.univ (fun i =>
      Finset.sum Finset.univ (fun j => if i = j then 0 else
        gaussianLinearWickValue z [row i, row i, row i, row j, row j, row j])) = _
  ring

theorem realGaussianQuotientLowValue (M : Matrix Iota Iota Real)
    (hM : M.IsHermitian) (s : Real)
    (hAdd : forall j, Not (1 + s * hM.eigenvalues j = 0)) :
    gaussianWickLowValue
        (fun j => (s : Complex) * realGaussianEigenVariances M hM j /
          (1 + (s : Complex) * realGaussianEigenVariances M hM j))
        (realGaussianEigenRows M hM) =
      1 + ((covarianceCorrection (resolventCovariance (HSMul.hSMul s M)) -
        (5 / 2 : Real) * Finset.sum Finset.univ (fun i =>
          resolventCovariance (HSMul.hSMul s M) i i ^ 3) : Real) : Complex) := by
  rw [gaussianWickLowValue_eq_degreeSix, realGaussianQuotientDegreeSixValue M hM s hAdd]

end PrimeFactorOscillations
