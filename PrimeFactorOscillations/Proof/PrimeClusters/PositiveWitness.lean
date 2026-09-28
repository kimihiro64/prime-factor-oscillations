import PrimeGapsTheory.Endgame.Main

set_option autoImplicit false

/-! # PositiveWitness in the quantitative prime-cluster count -/

namespace PrimeGaps

theorem exists_positive_smooth_margin_105 :
    exists theta : Real, 0 < theta /\ theta < 1 / 2 /\
    exists delta : Real, 0 < delta /\ delta < theta / 2 /\
    exists F : EuclideanSpace Real (Fin 105) -> Real,
    exists hF : ContDiff Real (Top.top : ENat) F,
    exists hsupp : Set.Subset (Function.support F)
      (EuclideanSpace.scaledStdSimplex 105 1),
      0 < (theta / 2 - delta) *
        Finset.univ.sum (fun m => J m ((MainProp.canonMemLp F hF hsupp).toLp F)) -
          norm ((MainProp.canonMemLp F hF hsupp).toLp F) ^ 2 := by
  have hMpos : 0 < M 105 := lt_trans (by norm_num) four_lt_M_verified
  have hMne : Not (M 105 = 0) := ne_of_gt hMpos
  let theta : Real := 1 / 4 + 1 / M 105
  have ht0 : 0 < theta := by dsimp [theta]; positivity
  have ht : theta < 1 / 2 := by
    have hrec := one_div_lt_one_div_of_lt (by norm_num : (0 : Real) < 4)
      four_lt_M_verified
    dsimp [theta]
    linarith
  have hx : 1 < theta * M 105 / 2 := by
    have heq : theta * M 105 / 2 = M 105 / 8 + 1 / 2 := by
      dsimp [theta]
      field_simp
      ring
    rw [heq]
    linarith [four_lt_M_verified]
  let epsilon := theta * M 105 / 2 - 1
  have heps : 0 < epsilon := by dsimp [epsilon]; linarith
  choose F hF htsupp hmem hI delta hd0 hineq using
    maynard_smooth_witness_ineq 105 (by norm_num) theta (And.intro ht0 (by linarith))
      epsilon heps 1 (by dsimp [epsilon]; ring)
  have hsum : 0 <= Finset.univ.sum (fun m => J m (hmem.toLp F)) := by
    apply Finset.sum_nonneg
    intro m hm
    rw [J_eq_normSq]
    positivity
  simp only [one_mul] at hineq
  have hd : delta < theta / 2 := by nlinarith
  have hsupp : Set.Subset (Function.support F)
      (EuclideanSpace.scaledStdSimplex 105 1) := (subset_tsupport F).trans htsupp
  refine Exists.intro theta (And.intro ht0 (And.intro ht ?_))
  refine Exists.intro delta (And.intro hd0 (And.intro hd ?_))
  refine Exists.intro F (Exists.intro hF (Exists.intro hsupp ?_))
  exact sub_pos.mpr hineq

end PrimeGaps
