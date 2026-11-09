/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.Analysis.MeanInequalities.SeparatedGrid

/-! # Exact variance defects and concentration of every grid extremizer -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace Finset

theorem weightedVarianceNumerator_baseline_defect {Iota : Type*} (S : Finset Iota)
    (w x : Iota -> Real) (q c : Real) (hZero : Finset.sum S x = 0) :
    let r := (S.card : Real)
    let K := Finset.sum S w
    let C := Finset.sum S (fun i => (x i) ^ 2)
    weightedVarianceNumerator S w x - (q * K * C + q * r * (K - q * r) * c) =
      q * r * Finset.sum S (fun i => (w i - q) * ((x i) ^ 2 - c)) +
        weightedVarianceNumerator S (fun i => w i - q) x := by
  dsimp only
  let r := (S.card : Real)
  let K := Finset.sum S w
  let C := Finset.sum S (fun i => (x i) ^ 2)
  let b := fun i => w i - q
  let E := Finset.sum S b
  let R := Finset.sum S (fun i => b i * x i)
  let T := Finset.sum S (fun i => b i * (x i) ^ 2)
  have hE : E = K - q * r := by
    dsimp only [E, b, K, r]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  have hR : R = Finset.sum S (fun i => w i * x i) := by
    dsimp only [R, b]
    simp only [sub_mul, Finset.sum_sub_distrib, <- Finset.mul_sum, hZero,
      mul_zero, sub_zero]
  have hT : T = Finset.sum S (fun i => w i * (x i) ^ 2) - q * C := by
    dsimp only [T, b, C]
    simp only [sub_mul, Finset.sum_sub_distrib, <- Finset.mul_sum]
  have hDef : Finset.sum S (fun i => (w i - q) * ((x i) ^ 2 - c)) =
      T - c * E := by
    calc
      _ = Finset.sum S (fun i => b i * (x i) ^ 2 - c * b i) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [b]
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, <- Finset.mul_sum]
  change K * Finset.sum S (fun i => w i * (x i) ^ 2) -
      (Finset.sum S (fun i => w i * x i)) ^ 2 -
        (q * K * C + q * r * (K - q * r) * c) =
      q * r * Finset.sum S (fun i => (w i - q) * ((x i) ^ 2 - c)) +
        (E * T - R ^ 2)
  rw [hDef, hE, hT, hR]
  ring

theorem weightedVarianceNumerator_zero_pair {Iota : Type*} (S : Finset Iota)
    (w x : Iota -> Real) (hw : forall i, Membership.mem S i -> 0 <= w i)
    (hZero : weightedVarianceNumerator S w x = 0)
    (i j : Iota) (hi : Membership.mem S i) (hj : Membership.mem S j) :
    w i * w j * (x i - x j) ^ 2 = 0 := by
  classical
  have hTerm : forall a, Membership.mem S a -> forall b, Membership.mem S b ->
      0 <= w a * w b * (x a - x b) ^ 2 :=
    fun a ha b hb => mul_nonneg (mul_nonneg (hw a ha) (hw b hb))
      (sq_nonneg (x a - x b))
  have hInner : forall a, Membership.mem S a ->
      0 <= Finset.sum S (fun b => w a * w b * (x a - x b) ^ 2) :=
    fun a ha => Finset.sum_nonneg (hTerm a ha)
  have hTotal : Finset.sum S (fun a => Finset.sum S
      (fun b => w a * w b * (x a - x b) ^ 2)) = 0 := by
    rw [<- weightedVarianceNumerator_pairwise S w x, hZero, mul_zero]
  have h1 := Finset.single_le_sum (hTerm i hi) hj
  have h2 := Finset.single_le_sum hInner hi
  rw [hTotal] at h2
  exact le_antisymm (le_trans h1 h2) (hTerm i hi j hj)

theorem weighted_separatedGrid_equality_iff (r : Nat) (hr : 0 < r)
    (w : Fin r -> Real) (q : Real) (hq : 0 < q) (hw : forall i, q <= w i) :
    let K := Finset.sum Finset.univ w
    weightedVarianceNumerator Finset.univ w (separatedGridCoord r) =
      q * K * ((r : Real) * ((r : Real) ^ 2 - 1) / 12) +
        q * (r : Real) * (K - q * (r : Real)) * separatedGridParity r <->
      exists j : Fin r,
        And ((separatedGridCoord r j) ^ 2 = separatedGridParity r)
          (forall i, w i = separatedGridWeights r q K j i) := by
  classical
  dsimp only
  let K := Finset.sum Finset.univ w
  let b := fun i => w i - q
  let E := Finset.sum Finset.univ b
  have hb : forall i : Fin r, 0 <= b i := fun i => sub_nonneg.mpr (hw i)
  have hE : E = K - q * (r : Real) := by
    dsimp only [E, b, K]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
    ring
  have hE0 : 0 <= E := Finset.sum_nonneg (fun i _ => hb i)
  have hK : q * (r : Real) <= K := by linarith only [hE, hE0]
  change weightedVarianceNumerator Finset.univ w (separatedGridCoord r) =
      q * K * ((r : Real) * ((r : Real) ^ 2 - 1) / 12) +
        q * (r : Real) * (K - q * (r : Real)) * separatedGridParity r <->
      exists j : Fin r,
        And ((separatedGridCoord r j) ^ 2 = separatedGridParity r)
          (forall i, w i = separatedGridWeights r q K j i)
  constructor
  case mp =>
    intro hEq
    have hDef := weightedVarianceNumerator_baseline_defect Finset.univ w
      (separatedGridCoord r) q (separatedGridParity r) (separatedGridCoord_sum r)
    rw [separatedGridCoord_sum_sq, Finset.card_univ, Fintype.card_fin] at hDef
    dsimp only at hDef
    rw [hEq, sub_self] at hDef
    have hTerm : forall i : Fin r,
        0 <= b i * ((separatedGridCoord r i) ^ 2 - separatedGridParity r) :=
      fun i => mul_nonneg (hb i) (sub_nonneg.mpr (separatedGridParity_le_sq r i))
    have hTail : 0 <= Finset.sum Finset.univ
        (fun i => b i * ((separatedGridCoord r i) ^ 2 - separatedGridParity r)) :=
      Finset.sum_nonneg (fun i _ => hTerm i)
    have hNum := weightedVarianceNumerator_nonneg Finset.univ b
      (separatedGridCoord r) (fun i _ => hb i)
    have hrR : 0 < (r : Real) := by exact_mod_cast hr
    have hCoeff : 0 < q * (r : Real) := mul_pos hq hrR
    change 0 = q * (r : Real) * Finset.sum Finset.univ
      (fun i => b i * ((separatedGridCoord r i) ^ 2 - separatedGridParity r)) +
        weightedVarianceNumerator Finset.univ b (separatedGridCoord r) at hDef
    have hProduct := mul_nonneg hCoeff.le hTail
    have hNum0 : weightedVarianceNumerator Finset.univ b (separatedGridCoord r) = 0 := by
      linarith only [hDef, hProduct, hNum]
    have hTail0 : Finset.sum Finset.univ
        (fun i => b i * ((separatedGridCoord r i) ^ 2 - separatedGridParity r)) = 0 := by
      have hMul : q * (r : Real) * Finset.sum Finset.univ
          (fun i => b i * ((separatedGridCoord r i) ^ 2 - separatedGridParity r)) = 0 := by
        linarith only [hDef, hNum0]
      exact (mul_eq_zero.mp hMul).resolve_left (ne_of_gt hCoeff)
    by_cases hEmpty : E = 0
    case pos =>
      choose j hj using separatedGridParity_attained r hr
      refine Exists.intro j (And.intro hj ?_)
      have hK0 : K - q * (r : Real) = 0 := hE.symm.trans hEmpty
      intro i
      have hSingle := Finset.single_le_sum (fun a _ => hb a) (Finset.mem_univ i)
      change b i <= E at hSingle
      rw [hEmpty] at hSingle
      have hbi : b i = 0 := le_antisymm hSingle (hb i)
      simp only [separatedGridWeights, hK0, ite_self, add_zero]
      dsimp only [b] at hbi
      linarith only [hbi]
    case neg =>
      have hEpos : 0 < E := lt_of_le_of_ne hE0 (Ne.symm hEmpty)
      choose j hj hbj using (Finset.sum_pos_iff_of_nonneg (fun i _ => hb i)).mp hEpos
      have hOnly : forall i : Fin r, Not (i = j) -> b i = 0 := by
        intro i hij
        have hCoord : Not (separatedGridCoord r i = separatedGridCoord r j) := by
          intro heq
          have hVal : (i.val : Real) = (j.val : Real) := by
            dsimp only [separatedGridCoord] at heq
            linarith only [heq]
          have hNat : i.val = j.val := by exact_mod_cast hVal
          exact hij (Fin.ext hNat)
        have hSq : 0 < (separatedGridCoord r i - separatedGridCoord r j) ^ 2 :=
          sq_pos_of_ne_zero (sub_ne_zero.mpr hCoord)
        have hPos : 0 < b j * (separatedGridCoord r i - separatedGridCoord r j) ^ 2 :=
          mul_pos hbj hSq
        have hPair := weightedVarianceNumerator_zero_pair Finset.univ b
          (separatedGridCoord r) (fun a _ => hb a) hNum0 i j
            (Finset.mem_univ i) (Finset.mem_univ j)
        have hMul : b i * (b j *
            (separatedGridCoord r i - separatedGridCoord r j) ^ 2) = 0 := by
          rw [<- mul_assoc]
          exact hPair
        exact (mul_eq_zero.mp hMul).resolve_right (ne_of_gt hPos)
      have hMiddle : (separatedGridCoord r j) ^ 2 = separatedGridParity r := by
        have hSingle := Finset.single_le_sum (fun a _ => hTerm a) (Finset.mem_univ j)
        rw [hTail0] at hSingle
        have hMul : b j * ((separatedGridCoord r j) ^ 2 - separatedGridParity r) = 0 :=
          le_antisymm hSingle (hTerm j)
        have hSquare := (mul_eq_zero.mp hMul).resolve_left (ne_of_gt hbj)
        linarith only [hSquare]
      have hEj : E = b j := by
        calc
          _ = Finset.sum Finset.univ (fun i : Fin r => if i = j then b j else 0) := by
            apply Finset.sum_congr rfl
            intro i _
            by_cases hij : i = j
            case pos => subst i; simp
            case neg => simp only [ite_eq_right hij, hOnly i hij]
          _ = b j := by simp
      refine Exists.intro j (And.intro hMiddle ?_)
      intro i
      by_cases hij : i = j
      case pos =>
        subst i
        have hWeight : separatedGridWeights r q K j j =
            q + (K - q * (r : Real)) := by simp [separatedGridWeights]
        rw [hWeight]
        have hbjValue : w j - q = K - q * (r : Real) := by
          change b j = K - q * (r : Real)
          exact hEj.symm.trans hE
        linarith only [hbjValue]
      case neg =>
        have hWeight : separatedGridWeights r q K j i = q := by
          simp [separatedGridWeights, hij]
        rw [hWeight]
        have hbi := hOnly i hij
        dsimp only [b] at hbi
        linarith only [hbi]
  case mpr =>
    intro h
    choose j hj hwj using h
    have hFun : w = separatedGridWeights r q K j := funext hwj
    rw [hFun]
    exact separatedGridWeights_numerator r q K j hK hj

end Finset
