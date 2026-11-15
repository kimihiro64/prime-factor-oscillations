/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianMinorFieldBudget
import PrimeFactorOscillations.Helpers.HamiltonianSignedBipartiteFunctional
import PrimeFactorOscillations.Helpers.HamiltonianSignedOccupancyBounds

/-! # The complete signed first-order correction

The signed coordinate readout is performed before estimating its
rank, diagonal, both off-diagonal orders and full field. The actual
stochastic consumer discharges every coordinate premise. No unsigned
determinant-mass amplification occurs in this main term.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

variable {Iota : Type*} [Fintype Iota] [DecidableEq Iota]

theorem hamiltonian_joint_signed_correction_bound
    (M G : Matrix Iota Iota Real) (v : Iota -> Real) (q p d : Real)
    (hq : 0 <= q) (hp : 1 <= p) (hNq : (Fintype.card Iota : Real) * q = 2)
    (hG : forall i j, abs (G i j) <= 2 * p * q)
    (hV : forall i, abs (v i) <= 19 * p ^ 2 * q)
    (hSingle : forall i, abs (hamiltonianCoordinateMinorMoment M i) <= 5 * abs d * p * q)
    (hPair : forall i j, Not (i = j) ->
      abs (hamiltonianCoordinatePairMinorMoment M i j) <= 50 * abs d * p ^ 2 * q ^ 2) :
    abs (hamiltonianSignedMinorFunctional M (hamiltonianSignedSupportCorrection G v q)) <=
      900 * abs d * p ^ 3 * q := by
  let m : Real := Fintype.card Iota
  let singles := Finset.univ.sum (fun i : Iota => hamiltonianCoordinateMinorMoment M i)
  let pairs := Finset.univ.sum (fun i : Iota => Finset.univ.sum (fun j : Iota =>
    if j = i then 0 else hamiltonianCoordinatePairMinorMoment M i j))
  let diagonal := Finset.univ.sum (fun i : Iota => G i i * hamiltonianCoordinateMinorMoment M i)
  let offDiagonal := Finset.univ.sum (fun i : Iota => Finset.univ.sum (fun j : Iota =>
    if j = i then 0 else G i j * hamiltonianCoordinatePairMinorMoment M i j))
  let field := Finset.univ.sum (fun i : Iota => v i * hamiltonianCoordinateMinorMoment M i)
  have hp0 : 0 <= p := le_trans (by norm_num) hp
  have hd : 0 <= abs d := abs_nonneg d
  have hNonneg (k l : Nat) : 0 <= abs d * p ^ k * q ^ l :=
    mul_nonneg (mul_nonneg hd (pow_nonneg hp0 k)) (pow_nonneg hq l)
  have hSum (f : Iota -> Real) (c : Real) (h : forall i, abs (f i) <= c) :
      abs (Finset.univ.sum f) <= m * c := by
    calc
      _ <= Finset.univ.sum (fun i => abs (f i)) := Finset.abs_sum_le_sum_abs _ _
      _ <= Finset.univ.sum (fun _ : Iota => c) := Finset.sum_le_sum (fun i _ => h i)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, m]
  have hMq : m * q = 2 := hNq
  have hSingles : abs singles <= 10 * abs d * p := by
    calc
      _ <= m * (5 * abs d * p * q) := hSum _ _ hSingle
      _ = 5 * abs d * p * (m * q) := by ring
      _ = _ := by rw [hMq]; ring
  have hPairs : abs pairs <= 200 * abs d * p ^ 2 := by
    have hTerm (i j : Iota) : abs (if j = i then 0 else
        hamiltonianCoordinatePairMinorMoment M i j) <= 50 * abs d * p ^ 2 * q ^ 2 := by
      by_cases h : j = i
      case pos =>
        simp only [if_pos h, abs_zero]
        nlinarith only [hNonneg 2 2]
      case neg =>
        simp only [if_neg h]
        exact hPair i j (Ne.symm h)
    calc
      _ <= m * (m * (50 * abs d * p ^ 2 * q ^ 2)) :=
        hSum _ _ (fun i => hSum _ _ (hTerm i))
      _ = 50 * abs d * p ^ 2 * (m * q) ^ 2 := by ring
      _ = _ := by rw [hMq]; ring
  have hDiag : abs diagonal <= 20 * abs d * p ^ 2 * q := by
    have hTerm (i : Iota) : abs (G i i * hamiltonianCoordinateMinorMoment M i) <=
        10 * abs d * p ^ 2 * q ^ 2 := by
      rw [abs_mul]
      have h := mul_le_mul (hG i i) (hSingle i) (abs_nonneg _)
        (mul_nonneg (mul_nonneg (by norm_num) hp0) hq)
      nlinarith only [h]
    calc
      _ <= m * (10 * abs d * p ^ 2 * q ^ 2) := hSum _ _ hTerm
      _ = 10 * abs d * p ^ 2 * q * (m * q) := by ring
      _ = _ := by rw [hMq]; ring
  have hOff : abs offDiagonal <= 400 * abs d * p ^ 3 * q := by
    have hTerm (i j : Iota) : abs (if j = i then 0 else
        G i j * hamiltonianCoordinatePairMinorMoment M i j) <=
          100 * abs d * p ^ 3 * q ^ 3 := by
      by_cases h : j = i
      case pos =>
        simp only [if_pos h, abs_zero]
        nlinarith only [hNonneg 3 3]
      case neg =>
        simp only [if_neg h, abs_mul]
        have hProduct := mul_le_mul (hG i j) (hPair i j (Ne.symm h)) (abs_nonneg _)
          (mul_nonneg (mul_nonneg (by norm_num) hp0) hq)
        nlinarith only [hProduct]
    calc
      _ <= m * (m * (100 * abs d * p ^ 3 * q ^ 3)) :=
        hSum _ _ (fun i => hSum _ _ (hTerm i))
      _ = 100 * abs d * p ^ 3 * q * (m * q) ^ 2 := by ring
      _ = _ := by rw [hMq]; ring
  have hField : abs field <= 190 * abs d * p ^ 3 * q := by
    have hTerm (i : Iota) : abs (v i * hamiltonianCoordinateMinorMoment M i) <=
        95 * abs d * p ^ 3 * q ^ 2 := by
      rw [abs_mul]
      have h := mul_le_mul (hV i) (hSingle i) (abs_nonneg _)
        (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg p)) hq)
      nlinarith only [h]
    calc
      _ <= m * (95 * abs d * p ^ 3 * q ^ 2) := hSum _ _ hTerm
      _ = 95 * abs d * p ^ 3 * q * (m * q) := by ring
      _ = _ := by rw [hMq]; ring
  have hp12 : p <= p ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hp hp0
    nlinarith only [h]
  have hp23 : p ^ 2 <= p ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hp (sq_nonneg p)
    nlinarith only [h]
  have hP12 := mul_le_mul_of_nonneg_left hp12 (mul_nonneg hd hq)
  have hP23 := mul_le_mul_of_nonneg_left hp23 (mul_nonneg hd hq)
  have hRank : abs (q / 4 * (pairs - singles)) <= 53 * abs d * p ^ 2 * q := by
    have hq4 : 0 <= q / 4 := div_nonneg hq (by norm_num)
    rw [abs_mul, abs_of_nonneg hq4]
    have hTriangle := mul_le_mul_of_nonneg_left
      (hamiltonian_abs_sub_bound pairs singles) hq4
    have hPairScaled := mul_le_mul_of_nonneg_left hPairs hq4
    have hSingleScaled := mul_le_mul_of_nonneg_left hSingles hq4
    nlinarith only [hTriangle, hPairScaled, hSingleScaled, hP12, hNonneg 2 1]
  have hReadout := hamiltonian_signed_minor_correction_readout M G v q
  change hamiltonianSignedMinorFunctional M (hamiltonianSignedSupportCorrection G v q) =
    q / 4 * (pairs - singles) + diagonal + offDiagonal + 2 * field at hReadout
  rw [hReadout]
  have h1 := abs_add_le (q / 4 * (pairs - singles)) diagonal
  have h2 := abs_add_le (q / 4 * (pairs - singles) + diagonal) offDiagonal
  have h3 := abs_add_le (q / 4 * (pairs - singles) + diagonal + offDiagonal) (2 * field)
  rw [abs_mul, abs_of_pos (by norm_num : (0 : Real) < 2)] at h3
  nlinarith only [h1, h2, h3, hRank, hDiag, hOff, hField, hP23, hNonneg 3 1]

variable [Nonempty Iota]

theorem stochastic_full_signed_first_correction
    (T : Matrix Iota Iota Real) (q a rho : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1) :
    let G := resolventCovariance (bipartiteLift (centeredKernel T q))
    abs (hamiltonianSignedMinorFunctional (bipartiteLift T)
      (hamiltonianSignedSupportCorrection G (hamiltonianMinorField T q) q)) <=
      900 * abs (Matrix.det ((1 : Matrix Iota Iota Real) -
        (centeredKernel T q).transpose * centeredKernel T q)) *
          (a / (1 - rho)) ^ 3 * q := by
  let g := 1 - rho
  let p := a / g
  let G := resolventCovariance (bipartiteLift (centeredKernel T q))
  let d := Matrix.det ((1 : Matrix Iota Iota Real) -
    (centeredKernel T q).transpose * centeredKernel T q)
  have hg : 0 < g := sub_pos.mpr hRho
  have hDen : Not (g = 0) := ne_of_gt hg
  have hgSq : 0 < g ^ 2 := sq_pos_of_pos hg
  have hRho0 : 0 <= rho := le_trans (norm_nonneg _) hNorm
  have hg1 : g <= 1 := by dsimp only [g]; linarith only [hRho0]
  have ha0 : 0 <= a := le_trans (by norm_num) ha
  have hp0 : 0 <= p := div_nonneg ha0 (le_of_lt hg)
  have hpClear : g * p = a := by dsimp only [p]; field_simp
  have hp : 1 <= p := by nlinarith only [hpClear, hg1, hp0, ha]
  have hSquare : g ^ 2 * p ^ 2 = a ^ 2 := by rw [<- mul_pow, hpClear]
  have hCard : 0 < (Fintype.card Iota : Real) := Nat.cast_pos.mpr Fintype.card_pos
  have hq0 : 0 <= q := by nlinarith only [hq, hCard]
  have hFull : (Fintype.card (Sum Iota Iota) : Real) * q = 2 := by
    simp only [Fintype.card_sum, Nat.cast_add]
    nlinarith only [hq]
  have hBounds := stochastic_root_occupancy_coefficient_bounds T q a rho hq ha
    hRow hCol hNonneg hUpper hNorm hRho
  have hG (i j : Sum Iota Iota) : abs (G i j) <= 2 * p * q := by
    apply le_of_mul_le_mul_left _ hg
    calc
      _ <= 2 * a * q := hBounds.1 i j
      _ = g * (2 * p * q) := by rw [<- hpClear]; ring
  have hV (i : Sum Iota Iota) : abs (hamiltonianMinorField T q i) <= 19 * p ^ 2 * q := by
    apply le_of_mul_le_mul_left _ hgSq
    calc
      _ <= 19 * a ^ 2 * q :=
        stochastic_minor_field_coordinate_bound T q a rho hq ha hRow hCol hNonneg hUpper hNorm hRho i
      _ = g ^ 2 * (19 * p ^ 2 * q) := by rw [<- hSquare]; ring
  have hSingle (i : Sum Iota Iota) :
      abs (hamiltonianCoordinateMinorMoment (bipartiteLift T) i) <= 5 * abs d * p * q := by
    apply le_of_mul_le_mul_left _ hg
    calc
      _ <= 5 * abs d * a * q :=
        stochastic_signed_coordinate_occupancy_bound T q a rho hq ha hRow hCol hNonneg hUpper hNorm hRho i
      _ = g * (5 * abs d * p * q) := by rw [<- hpClear]; ring
  have hPair (i j : Sum Iota Iota) (hIJ : Not (i = j)) :
      abs (hamiltonianCoordinatePairMinorMoment (bipartiteLift T) i j) <=
        50 * abs d * p ^ 2 * q ^ 2 := by
    apply le_of_mul_le_mul_left _ hgSq
    calc
      _ <= 50 * abs d * a ^ 2 * q ^ 2 :=
        stochastic_signed_coordinate_pair_occupancy_bound T q a rho hq ha
          hRow hCol hNonneg hUpper hNorm hRho i j hIJ
      _ = g ^ 2 * (50 * abs d * p ^ 2 * q ^ 2) := by rw [<- hSquare]; ring
  exact hamiltonian_joint_signed_correction_bound (bipartiteLift T) G
    (hamiltonianMinorField T q) q p d hq0 hp hFull hG hV hSingle hPair

def hamiltonianSignedMinorFirstOrderSum (T : Matrix Iota Iota Real) (q : Real) : Real :=
  -Finset.univ.sum (fun U : Finset Iota =>
    (-1 : Real) ^ U.card * (U.card : Real) *
      (Finset.univ.powersetCard U.card).sum (fun S =>
        rectangularMinorDet T S U ^ 2 * hamiltonianMinorFirstOrder T S U q))

theorem stochastic_signed_minor_first_order_sum_bound
    (T : Matrix Iota Iota Real) (q a rho : Real)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1) :
    abs (hamiltonianSignedMinorFirstOrderSum T q) <=
      900 * abs (Matrix.det ((1 : Matrix Iota Iota Real) -
        (centeredKernel T q).transpose * centeredKernel T q)) *
          (a / (1 - rho)) ^ 3 * q := by
  let G := resolventCovariance (bipartiteLift (centeredKernel T q))
  let f := hamiltonianSignedSupportCorrection G (hamiltonianMinorField T q) q
  have hReadout : hamiltonianSignedMinorFunctional (bipartiteLift T) f =
      hamiltonianSignedMinorFirstOrderSum T q := by
    rw [hamiltonian_signed_minor_bipartite]
    change -Finset.univ.sum (fun U : Finset Iota =>
      (-1 : Real) ^ U.card * (U.card : Real) *
        (Finset.univ.powersetCard U.card).sum (fun S =>
          rectangularMinorDet T S U ^ 2 * f (S.disjSum U))) = _
    unfold hamiltonianSignedMinorFirstOrderSum
    congr 1
    apply Finset.sum_congr rfl
    intro U hU
    congr 1
    apply Finset.sum_congr rfl
    intro S hS
    have hCard : S.card = U.card := (Finset.mem_powersetCard.mp hS).2
    rw [hamiltonian_minor_first_order_as_support_correction T S U hCard]
  rw [<- hReadout]
  exact stochastic_full_signed_first_correction T q a rho hq ha
    hRow hCol hNonneg hUpper hNorm hRho

end PrimeFactorOscillations
