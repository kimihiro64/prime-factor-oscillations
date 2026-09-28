import PrimeGapsTheory.Endgame.MainProp

set_option autoImplicit false

/-! # ExcessLower in the quantitative prime-cluster count -/

namespace PrimeGaps

theorem eventually_smooth_excess_lower {k : Nat} (hk : 2 <= k)
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
    exists N0 : Real, forall N : Nat, N0 <= (N : Real) ->
      forall v : ZMod (sieveModulus N),
        (forall i, Int.gcd ((v.val : Int) + h i) (sieveModulus N) = 1) ->
      let R := sieveTruncation N delta theta
      let W := sieveModulus N
      let lam := yToL (Finsupp.indicator (Finset.permissibleSupport k (Nat.floor R) W)
        (fun r _ => F (WithLp.toLp 2 (fun i => Real.log (r i) / Real.log R))))
      let s := (Finset.Ioc N (2 * N)).filter (fun n : Nat => (n : ZMod W) = v)
      mainScale k N R W *
        ((theta / 2 - delta) *
          Finset.univ.sum (fun m => J m ((MainProp.canonMemLp F hF hsupp).toLp F)) -
            norm ((MainProp.canonMemLp F hF hsupp).toLp F) ^ 2) / 2 <=
        s.sum (fun n =>
          ((Finset.univ.filter (fun i : Fin k => Nat.Prime (n + h i))).card : Real) *
            weight h lam n) - s.sum (weight h lam) := by
  classical
  let gamma := (theta / 2 - delta) *
      Finset.univ.sum (fun m => J m ((MainProp.canonMemLp F hF hsupp).toLp F)) -
        norm ((MainProp.canonMemLp F hF hsupp).toLp F) ^ 2
  have hg : 0 < gamma := hmargin
  choose e he N0 hS using
    MainProp.lem_S_asymptotic hk h hadm F hF hsupp theta delta ht0 ht hd0 hd
      1 (by norm_num) hLD
  have hevent := he.eventually_lt_const (show 0 < gamma / 2 by linarith)
  choose K hK using Filter.eventually_atTop.mp hevent
  refine Exists.intro (max (max N0 (K : Real)) 2) ?_
  intro N hN v hv
  have hN0 : N0 <= (N : Real) := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hKN : (K : Real) <= (N : Real) :=
    (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN2 : (2 : Real) <= N := (le_max_right _ _).trans hN
  have heN : e N < gamma / 2 := hK N (by exact_mod_cast hKN)
  have hNpos : (0 : Real) < N := by linarith
  have hlog : 0 <= Real.log (sieveTruncation N delta theta) := by
    change 0 <= Real.log ((N : Real) ^ (theta / 2 - delta))
    rw [Real.log_rpow hNpos]
    exact mul_nonneg (by linarith) (Real.log_nonneg (by linarith))
  have hscale : 0 <= mainScale k N (sieveTruncation N delta theta) (sieveModulus N) := by
    unfold mainScale
    positivity
  have hs := hS N hN0 v hv
  simp only [one_mul] at hs
  have herror := mul_le_mul_of_nonneg_right (le_of_lt heN) hscale
  have hlower := (abs_le.mp hs).1
  let R := sieveTruncation N delta theta
  let W := sieveModulus N
  let lam := yToL (Finsupp.indicator (Finset.permissibleSupport k (Nat.floor R) W)
    (fun r _ => F (WithLp.toLp 2 (fun i => Real.log (r i) / Real.log R))))
  let s := (Finset.Ioc N (2 * N)).filter (fun n : Nat => (n : ZMod W) = v)
  have hlower' : -(e N * mainScale k N R W) <=
      s.sum (fun n =>
        ((Finset.univ.filter (fun i : Fin k => Nat.Prime (n + h i))).card : Real) *
          weight h lam n) - s.sum (weight h lam) - mainScale k N R W * gamma := hlower
  change mainScale k N R W * gamma / 2 <=
    s.sum (fun n =>
      ((Finset.univ.filter (fun i : Fin k => Nat.Prime (n + h i))).card : Real) *
        weight h lam n) - s.sum (weight h lam)
  linarith only [hlower', herror]

end PrimeGaps
