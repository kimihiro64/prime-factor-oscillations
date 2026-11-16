/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCycleExponentialLower
import PrimeFactorOscillations.Helpers.HamiltonianInjectiveMatrixRestriction
import PrimeFactorOscillations.Helpers.HamiltonianMatrixGeometry
import PrimeFactorOscillations.Helpers.HamiltonianRepairedSquareExists

/-! # Independent positive cycle mass on the actual principal complement

The arbitrary row identification in square repair is undone before
counting cycles. The actual retained matrix is scaled on both sides;
its full scaling product, retained rank and spectral gap are kept.
-/

set_option autoImplicit false
set_option Elab.async false

open scoped Matrix.Norms.L2Operator

noncomputable section

namespace PrimeFactorOscillations

universe u
variable {Iota : Type u} [Fintype Iota] [DecidableEq Iota] [Nonempty Iota]

theorem stochastic_principal_repair_same_support_exists
    (T : Matrix Iota Iota Real) (D : Finset Iota) (q a rho : Real)
    (hN : 4 <= Fintype.card Iota)
    (hq : (Fintype.card Iota : Real) * q = 1) (ha : 1 <= a)
    (hRow : forall i, Finset.univ.sum (fun j => T i j) = 1)
    (hCol : forall j, Finset.univ.sum (fun i => T i j) = 1)
    (hNonneg : forall i j, 0 <= T i j) (hUpper : forall i j, T i j <= a * q)
    (hNorm : norm (centeredKernel T q) <= rho) (hRho : rho < 1)
    (hSmall : (D.card : Real) * (a / (1 - rho)) ^ 3 * q <= 1 / 10000) :
    let J : Finset Iota := Compl.compl D
    let M := T.submatrix (fun i : J => i.val) (fun i : J => i.val)
    let qNew := q / (1 - (D.card : Real) * q)
    2 <= Fintype.card J /\
      (Fintype.card J : Real) * qNew = 1 /\
      exists x y : J -> Real,
        (forall i, 0 < x i) /\ (forall i, 0 < y i) /\
        Finset.univ.sum (fun i => Real.log (x i)) +
          Finset.univ.sum (fun i => Real.log (y i)) <=
            40 * (D.card : Real) * a / (1 - rho) /\
        (forall i j, 0 <= hamiltonianCrossScaled M x y i j) /\
        ((forall i, Finset.univ.sum (fun j => hamiltonianCrossScaled M x y i j) = 1) /\
          (forall j, Finset.univ.sum (fun i => hamiltonianCrossScaled M x y i j) = 1)) /\
        (forall i j, hamiltonianCrossScaled M x y i j <= 2 * a * qNew) /\
        norm (centeredKernel (hamiltonianCrossScaled M x y) qNew) <=
          1 - (1 - rho) / 2 := by
  let J : Finset Iota := Compl.compl D
  let R : Finset (Sum Iota Iota) := Compl.compl (D.disjSum D)
  let M := T.submatrix (fun i : J => i.val) (fun i : J => i.val)
  let qNew := q / (1 - (D.card : Real) * q)
  have hRepair := stochastic_repaired_square_exists T D D rfl q a rho hN hq ha
    hRow hCol hNonneg hUpper hNorm hRho hSmall
  let z := hRepair.2.2.choose
  have hz := hRepair.2.2.choose_spec
  let e := hamiltonianComplementRowEquiv D D rfl
  let v := hamiltonianRepairedSquareEquiv D D rfl
  let A := hamiltonianRepairedSquareKernel T D D rfl z
  let x := fun i : J => 1 + z (v (Sum.inl (e.symm i)))
  let y := fun j : J => 1 + z (v (Sum.inr j))
  let N := hamiltonianCrossScaled M x y
  have hx (i : J) : 0 < x i := hz.2.2.1 _
  have hy (j : J) : 0 < y j := hz.2.2.1 _
  have hEq : N = A.submatrix e.symm id := by
    ext i j
    change (1 + z (v (Sum.inl (e.symm i)))) * T i.val j.val *
        (1 + z (v (Sum.inr j))) =
      (1 + z (v (Sum.inl (e.symm i)))) * T (e (e.symm i)).val j.val *
        (1 + z (v (Sum.inr j)))
    rw [e.apply_symm_apply]
  have hA0 (i j : J) : 0 <= A i j := hz.2.2.2.2.1 i j
  have hARow (i : J) : Finset.univ.sum (fun j => A i j) = 1 := hz.2.2.2.2.2.1.1 i
  have hACol (j : J) : Finset.univ.sum (fun i => A i j) = 1 := hz.2.2.2.2.2.1.2 j
  have hACap (i j : J) : A i j <= 2 * a * qNew := hz.2.2.2.2.2.2.1 i j
  have hAGap : norm (centeredKernel A qNew) <= 1 - (1 - rho) / 2 :=
    hz.2.2.2.2.2.2.2
  have hN0 (i j : J) : 0 <= N i j := by
    rw [hEq]
    exact hA0 (e.symm i) j
  have hNRow (i : J) : Finset.univ.sum (fun j => N i j) = 1 := by
    rw [hEq]
    exact hARow (e.symm i)
  have hNCol (j : J) : Finset.univ.sum (fun i => N i j) = 1 := by
    rw [hEq]
    change Finset.univ.sum (fun i : J => A (e.symm i) j) = 1
    rw [hamiltonian_sum_reindex e.symm (fun i => A i j)]
    exact hACol j
  have hNCap (i j : J) : N i j <= 2 * a * qNew := by
    rw [hEq]
    exact hACap (e.symm i) j
  have hCentered : centeredKernel N qNew = (centeredKernel A qNew).submatrix e.symm id := by
    rw [hEq]
    ext i j
    rfl
  have hNGap : norm (centeredKernel N qNew) <= 1 - (1 - rho) / 2 := by
    rw [hCentered]
    exact (hamiltonian_injective_rows_norm e.symm e.symm.injective _).trans hAGap
  let zeta := 20 * (D.card : Real) * a * q / (1 - rho)
  have hZ : norm z <= zeta := hz.1
  have hZ0 : 0 <= zeta := (norm_nonneg z).trans hZ
  have hPoint (i : R) : abs (z i) <= zeta := by
    have h := (pi_norm_le_iff_of_nonneg hZ0).mp hZ i
    simpa only [Real.norm_eq_abs] using h
  have hLogX (i : J) : Real.log (x i) <= zeta := by
    have h := (le_abs_self (z (v (Sum.inl (e.symm i))))).trans
      (hPoint (v (Sum.inl (e.symm i))))
    have hL := Real.log_le_sub_one_of_pos (hx i)
    dsimp only [x] at hL
    dsimp only [x]
    linarith only [hL, h]
  have hLogY (i : J) : Real.log (y i) <= zeta := by
    have h := (le_abs_self (z (v (Sum.inr i)))).trans (hPoint (v (Sum.inr i)))
    have hL := Real.log_le_sub_one_of_pos (hy i)
    dsimp only [y] at hL
    dsimp only [y]
    linarith only [hL, h]
  have hRank : Fintype.card J <= Fintype.card Iota :=
    Fintype.card_le_of_injective (fun i : J => i.val) Subtype.val_injective
  have hDim : 0 < (Fintype.card Iota : Real) := by exact_mod_cast Fintype.card_pos
  have hq0 : 0 <= q := by nlinarith only [hq, hDim]
  have hRetained : (Fintype.card J : Real) * q <= 1 := by
    have hRankReal : (Fintype.card J : Real) <= Fintype.card Iota := by exact_mod_cast hRank
    exact (mul_le_mul_of_nonneg_right hRankReal hq0).trans_eq hq
  have hB0 : 0 <= 40 * (D.card : Real) * a / (1 - rho) := by
    apply div_nonneg
    . exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
        (le_trans (by norm_num) ha)
    . exact (sub_pos.mpr hRho).le
  have hLog : Finset.univ.sum (fun i => Real.log (x i)) +
      Finset.univ.sum (fun i => Real.log (y i)) <=
        40 * (D.card : Real) * a / (1 - rho) := by
    have hX := Finset.sum_le_sum (s := (Finset.univ : Finset J)) (fun i hi => hLogX i)
    have hY := Finset.sum_le_sum (s := (Finset.univ : Finset J)) (fun i hi => hLogY i)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hX hY
    calc
      _ <= 2 * (Fintype.card J : Real) * zeta := by linarith only [hX, hY]
      _ = (40 * (D.card : Real) * a / (1 - rho)) *
          ((Fintype.card J : Real) * q) := by dsimp only [zeta]; ring
      _ <= (40 * (D.card : Real) * a / (1 - rho)) * 1 :=
        mul_le_mul_of_nonneg_left hRetained hB0
      _ = _ := mul_one _
  exact And.intro hRepair.1 (And.intro hRepair.2.1
    (Exists.intro x (Exists.intro y
      (And.intro hx (And.intro hy (And.intro hLog (And.intro hN0
        (And.intro (And.intro hNRow hNCol) (And.intro hNCap hNGap)))))))))

theorem stochastic_principal_deleted_cycle_exponential_lower_uniform
    (rho : Real) (hRho0 : 0 <= rho) (hRho1 : rho < 1) :
    exists N0 : Nat, 256 <= N0 /\
      forall (I : Type u) [Fintype I] [DecidableEq I] [Nonempty I]
        (T : Matrix I I Real) (D : Finset I) (q a : Real),
        4 <= Fintype.card I -> (Fintype.card I : Real) * q = 1 -> 1 <= a ->
        (forall i, Finset.univ.sum (fun j => T i j) = 1) ->
        (forall j, Finset.univ.sum (fun i => T i j) = 1) ->
        (forall i j, 0 <= T i j) -> (forall i j, T i j <= a * q) ->
        norm (centeredKernel T q) <= rho ->
        (D.card : Real) * (a / (1 - rho)) ^ 3 * q <= 1 / 10000 ->
        N0 <= Fintype.card (Compl.compl D : Finset I) ->
        (2 * a) ^ 2 <= hamiltonianAperiodicSublogDensity ((1 - rho) / 2) *
          Real.log (Fintype.card (Compl.compl D : Finset I) : Real) ->
        let J : Finset I := Compl.compl D
        let M := T.submatrix (fun i : J => i.val) (fun i : J => i.val)
        0 < hamiltonianCycleSum M /\
          Real.exp (-(Fintype.card J : Real) -
              ((2 * a - 1) + (2 * a - 1) / ((1 - rho) / 2)) -
              40 * (D.card : Real) * a / (1 - rho)) /
            (4 * (Fintype.card J : Real)) <= hamiltonianCycleSum M := by
  let delta := (1 - rho) / 2
  have hDelta : 0 < delta := by dsimp only [delta]; linarith only [hRho1]
  have hDelta1 : delta <= 1 := by dsimp only [delta]; linarith only [hRho0]
  choose N0 hN0 hCount using stochastic_aperiodic_cycle_exponential_lower_uniform.{u}
    delta hDelta hDelta1
  refine Exists.intro N0 (And.intro hN0 ?_)
  intro I instF instD instN T D q a hN hq ha hRow hCol hNonneg hUpper hNorm hSmall hCard hDensity
  let J : Finset I := Compl.compl D
  let M := T.submatrix (fun i : J => i.val) (fun i : J => i.val)
  let qNew := q / (1 - (D.card : Real) * q)
  have hRepair := stochastic_principal_repair_same_support_exists T D q a rho
    hN hq ha hRow hCol hNonneg hUpper hNorm hRho1 hSmall
  let x := hRepair.2.2.choose
  let y := hRepair.2.2.choose_spec.choose
  have hData := hRepair.2.2.choose_spec.choose_spec
  have hJPos : 0 < Fintype.card J := by
    change 0 < Fintype.card (Compl.compl D : Finset I)
    have h := hN0.trans hCard
    omega
  have : Nonempty J := Fintype.card_pos_iff.mp hJPos
  let N := hamiltonianCrossScaled M x y
  have hCountNew := hCount J hCard N qNew (2 * a) hRepair.2.1
    (by linarith only [ha]) hDensity hData.2.2.2.2.1.1 hData.2.2.2.2.1.2
    hData.2.2.2.1 hData.2.2.2.2.2.1 hData.2.2.2.2.2.2
  let B := 40 * (D.card : Real) * a / (1 - rho)
  let H := (2 * a - 1) + (2 * a - 1) / delta
  let m : Real := Fintype.card J
  have hUnscale := hamiltonian_cycle_unscale_lower M x y B
    (Real.exp (-m - H) / (4 * m))
    (fun i j => hNonneg i.val j.val) hData.1 hData.2.1 hData.2.2.1 hCountNew.2
  have hIdentity : Real.exp (-m - H - B) / (4 * m) =
      Real.exp (-B) * (Real.exp (-m - H) / (4 * m)) := by
    calc
      _ = Real.exp ((-B) + (-m - H)) / (4 * m) :=
        congrArg (fun t => Real.exp t / (4 * m)) (by ring)
      _ = _ := by rw [Real.exp_add]; ring
  rw [<- hIdentity] at hUnscale
  refine And.intro ?_ hUnscale
  have hm : 0 < m := by dsimp only [m]; exact_mod_cast hJPos
  exact (div_pos (Real.exp_pos _) (mul_pos (by norm_num) hm)).trans_le hUnscale

end PrimeFactorOscillations
