import PrimeFactorOscillations.Proof.PrimeClusters.CountBridge
import PrimeFactorOscillations.Proof.PrimeClusters.ExcessLower
import PrimeGapsTheory.Sieve.Transforms.YmSubstituteSmooth

set_option autoImplicit false

/-! # ScaleCount in the quantitative prime-cluster count -/

namespace PrimeGaps

theorem exists_uniform_scale_count_bound {k : Nat} (hk : 2 <= k)
    (h : Fin k -> Nat) (hadm : GPYSieveS1.IsAdmissible h)
    (F : EuclideanSpace Real (Fin k) -> Real)
    (hF : ContDiff Real (Top.top : ENat) F)
    (hsupp : Set.Subset (Function.support F) (EuclideanSpace.scaledStdSimplex k 1))
    (theta delta : Real) (ht0 : 0 < theta) (ht : theta < 1 / 2)
    (hd0 : 0 < delta) (hd : delta < theta / 2)
    (hLD : Nat.HasLevelOfDistribution Set.univ theta 1)
    (hmargin : 0 <
      (theta / 2 - delta) *
        Finset.univ.sum (fun m => J m ((MainProp.canonMemLp F hF hsupp).toLp F)) -
          norm ((MainProp.canonMemLp F hF hsupp).toLp F) ^ 2) :
    exists C : Real, 0 < C /\ exists N0 : Real,
      forall N : Nat, N0 <= (N : Real) ->
      forall v : ZMod (sieveModulus N),
        (forall i, Int.gcd ((v.val : Int) + h i) (sieveModulus N) = 1) ->
      let R := sieveTruncation N delta theta
      mainScale k N R (sieveModulus N) *
        ((theta / 2 - delta) *
          Finset.univ.sum (fun m => J m ((MainProp.canonMemLp F hF hsupp).toLp F)) -
            norm ((MainProp.canonMemLp F hF hsupp).toLp F) ^ 2) / 2 <=
        (((Finset.Ioc N (2 * N)).filter (fun n =>
          2 <= (Finset.univ.filter (fun i : Fin k => Nat.Prime (n + h i))).card)).card :
            Real) *
          (((k : Real) - 1) *
            (C * (MaynardSmoothY.Fmax F + 1) * R * Real.log R ^ (2 * k)) ^ 2) := by
  classical
  choose C hC Nc hcount using exists_uniform_cluster_moment_count_bound hk theta delta
    (And.intro ht0 (by linarith)) (And.intro hd0 hd)
  choose Nl hlower using eventually_smooth_excess_lower hk h hadm F hF hsupp
    theta delta ht0 ht hd0 hd hLD hmargin
  refine Exists.intro C (And.intro hC (Exists.intro (max (max Nc Nl) 2) ?_))
  intro N hN v hv
  have hNc : Nc <= (N : Real) := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hNl : Nl <= (N : Real) := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN2 : (2 : Real) <= N := (le_max_right _ _).trans hN
  have hNpos : (0 : Real) < N := by linarith
  let R := sieveTruncation N delta theta
  let W := sieveModulus N
  let y := Finsupp.indicator (Finset.permissibleSupport k (Nat.floor R) W)
    (fun r _ => F (WithLp.toLp 2 (fun i => Real.log (r i) / Real.log R)))
  let lam := yToL y
  let s := (Finset.Ioc N (2 * N)).filter (fun n : Nat => (n : ZMod W) = v)
  let good := fun n : Nat =>
    2 <= (Finset.univ.filter (fun i : Fin k => Nat.Prime (n + h i))).card
  have hy : y.HasPermissibleSupport (Nat.floor R) W := Finsupp.support_indicator_subset ..
  have hlam : lam.HasPermissibleSupport (Nat.floor R) W := hy.yToL
  have hRpos : 0 < R := Real.rpow_pos_of_pos hNpos _
  have hlog : 0 <= Real.log R := by
    change 0 <= Real.log ((N : Real) ^ (theta / 2 - delta))
    rw [Real.log_rpow hNpos]
    exact mul_nonneg (by linarith) (Real.log_nonneg (by linarith))
  have hY : Finsupp.maxRealAbs (lToY lam) <= MaynardSmoothY.Fmax F :=
    MaynardSmoothY.maxRealAbs_lambda0_le_Fmax R W F hk hRpos hF hsupp
  have hY' : Finsupp.maxRealAbs (lToY lam) <= MaynardSmoothY.Fmax F + 1 := by linarith
  have hY0 : 0 <= Finsupp.maxRealAbs (lToY lam) := Finsupp.maxRealAbs_nonneg
  have hcoef0 : 0 <= C * Finsupp.maxRealAbs (lToY lam) * R *
      Real.log R ^ (2 * k) := by positivity
  have hcoef :
      C * Finsupp.maxRealAbs (lToY lam) * R * Real.log R ^ (2 * k) <=
        C * (MaynardSmoothY.Fmax F + 1) * R * Real.log R ^ (2 * k) := by
    gcongr
  have hsq :
      (C * Finsupp.maxRealAbs (lToY lam) * R * Real.log R ^ (2 * k)) ^ 2 <=
        (C * (MaynardSmoothY.Fmax F + 1) * R * Real.log R ^ (2 * k)) ^ 2 := by
    apply sq_le_sq.mpr
    rw [abs_of_nonneg hcoef0, abs_of_nonneg (hcoef0.trans hcoef)]
    exact hcoef
  have hkR : 0 <= (k : Real) - 1 := by
    have hk' : (2 : Real) <= k := by exact_mod_cast hk
    linarith
  have hcard : ((s.filter good).card : Real) <=
      (((Finset.Ioc N (2 * N)).filter good).card : Real) := by
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr
      (And.intro (Finset.mem_filter.mp hn'.1).1 hn'.2)
  have hmoment := hcount N hNc lam hlam h s
  have hlowerN := hlower N hNl v hv
  apply hlowerN.trans
  apply hmoment.trans
  exact (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hsq hkR) (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hcard (mul_nonneg hkR (sq_nonneg _)))

end PrimeGaps
