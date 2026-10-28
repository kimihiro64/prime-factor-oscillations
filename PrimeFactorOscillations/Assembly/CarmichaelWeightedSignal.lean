/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelWeightedResidue

/-!
# A noncancelling principal-zero signal for complex character weights

The full finite logarithmic-derivative packet retains every shared-zero
multiplicity. Nonnegative real parts of the character weights and principal
weight one force a nonzero residue at every principal zero off one.
No RH, zero-free-strip or simple-zero premise is used. Analytic correction
terms cannot remove that signal. This is detection, not zero exclusion.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace PrimeFactorOscillations.CarmichaelWeightedSignal

theorem L_factor_exists {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (rho : Complex) (hOne : Not (rho = 1)) :
    exists n : Nat, exists g : Complex -> Complex,
      AnalyticAt Complex g rho /\ Not (g rho = 0) /\
      Filter.Eventually (fun s => DirichletCharacter.LFunction chi s =
        (s - rho) ^ n * g s) (nhds rho) /\
      (DirichletCharacter.LFunction chi rho = 0 -> 0 < n) := by
  let L := DirichletCharacter.LFunction chi
  have ha := DirichletZeroReadout.analyticOnNhd_LFunction_off_one chi
  have har : AnalyticAt Complex L rho := ha rho (Set.mem_compl_singleton_iff.mpr hOne)
  have ha2 : AnalyticAt Complex L 2 :=
    ha 2 (Set.mem_compl_singleton_iff.mpr (by norm_num))
  have hn2 : Not (L 2 = 0) :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re chi (Or.inr (by norm_num)) (by norm_num)
  have hTwo : meromorphicOrderAt L 2 = 0 :=
    (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero ha2.meromorphicAt).mp
      (Exists.intro (L 2) (And.intro hn2
        (ha2.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)))
  have hNoTop : Not (meromorphicOrderAt L rho = Top.top) := by
    have hM : MeromorphicOn L (Set.compl {1}) := fun z hz => (ha z hz).meromorphicAt
    apply hM.meromorphicOrderAt_ne_top_of_isPreconnected (x := (2 : Complex))
      (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
    . exact Set.mem_compl_singleton_iff.mpr (by norm_num)
    . exact Set.mem_compl_singleton_iff.mpr hOne
    . rw [hTwo]
      simp
  have hNotZero : Not (Filter.Eventually (fun s => L s = 0) (nhds rho)) := by
    intro hz
    exact hNoTop (meromorphicOrderAt_eq_top_iff.mpr
      (hz.filter_mono nhdsWithin_le_nhds))
  have hFactor := har.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hNotZero
  choose n g hg hgn hEq using hFactor
  have hMul : Filter.Eventually (fun s => L s = (s - rho) ^ n * g s) (nhds rho) := by
    simpa only [smul_eq_mul] using hEq
  refine Exists.intro n (Exists.intro g (And.intro hg (And.intro hgn (And.intro hMul ?_))))
  intro hZero
  by_contra hNotPos
  have hn : n = 0 := Nat.eq_zero_of_not_pos hNotPos
  have hAt := Filter.EventuallyEq.eq_of_nhds hMul
  change L rho = (rho - rho) ^ n * g rho at hAt
  rw [hn, pow_zero, one_mul] at hAt
  apply hgn
  rw [<- hAt]
  exact hZero

def readout {iota : Type*} [Fintype iota]
    (F : iota -> Complex -> Complex) (k : iota -> Complex)
    (E : Complex -> Complex) (s : Complex) : Complex :=
  -(Finset.univ.sum (fun i : iota => k i * logDeriv (F i) s)) + E s

theorem weighted_limit {iota : Type*} [Fintype iota]
    (F g : iota -> Complex -> Complex) (k : iota -> Complex) (n : iota -> Nat)
    (rho : Complex)
    (hg : forall i, AnalyticAt Complex (g i) rho)
    (hgn : forall i, Not (g i rho = 0))
    (hEq : forall i, Filter.Eventually
      (fun s => F i s = (s - rho) ^ n i * g i s) (nhds rho))
    (E : Complex -> Complex) (hE : AnalyticAt Complex E rho) :
    Filter.Tendsto (fun s => (s - rho) * readout F k E s)
      (nhdsWithin rho (Set.compl {rho}))
      (nhds (-(Finset.univ.sum (fun i => k i * (n i : Complex))))) := by
  classical
  let l := nhdsWithin rho (Set.compl {rho})
  have ht (i : iota) := CarmichaelWeightedResidue.factor_logDeriv_limit
    (F i) (g i) rho (n i) (hg i) (hgn i) (hEq i)
  have hs (S : Finset iota) : Filter.Tendsto
      (fun s => S.sum (fun i => k i * ((s - rho) * logDeriv (F i) s))) l
      (nhds (S.sum (fun i => k i * (n i : Complex)))) := by
    induction S using Finset.induction_on with
    | empty =>
      simpa only [Finset.sum_empty] using (tendsto_const_nhds : Filter.Tendsto
        (fun _ : Complex => (0 : Complex)) l (nhds 0))
    | @insert i S hi ih =>
      simp only [Finset.sum_insert hi]
      exact (tendsto_const_nhds.mul (ht i)).add ih
  have hError : Filter.Tendsto (fun s : Complex => (s - rho) * E s) l (nhds 0) := by
    have hc : ContinuousAt (fun s : Complex => (s - rho) * E s) rho :=
      (continuousAt_id.sub continuousAt_const).mul hE.continuousAt
    simpa only [sub_self, zero_mul] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hFun : (fun s : Complex => (s - rho) * readout F k E s) =
      (fun s => -(Finset.univ.sum (fun i => k i * ((s - rho) * logDeriv (F i) s))) +
        (s - rho) * E s) := by
    funext s
    unfold readout
    rw [mul_add, mul_neg, Finset.mul_sum]
    congr 1
    apply congrArg Neg.neg
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hFun]
  simpa only [add_zero] using (hs Finset.univ).neg.add hError

theorem residue_re_bound {iota : Type*} [Fintype iota]
    (k : iota -> Complex) (n : iota -> Nat) (i0 : iota)
    (hk : forall i, 0 <= (k i).re) (hOne : k i0 = 1) :
    (n i0 : Real) <= (Finset.univ.sum (fun i => k i * (n i : Complex))).re := by
  classical
  have hTerm (i : iota) : (k i * (n i : Complex)).re = (k i).re * (n i : Real) := by
    have hn : (n i : Complex) = ((n i : Real) : Complex) := by simp
    rw [hn, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hNonneg (i : iota) : 0 <= (k i * (n i : Complex)).re := by
    rw [hTerm]
    exact mul_nonneg (hk i) (Nat.cast_nonneg _)
  have hSum (S : Finset iota) :
      (S.sum (fun i => k i * (n i : Complex))).re =
        S.sum (fun i => (k i * (n i : Complex)).re) := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih => simp only [Finset.sum_insert hi, Complex.add_re, ih]
  calc
    _ = (k i0 * (n i0 : Complex)).re := by rw [hTerm, hOne]; simp
    _ <= Finset.univ.sum (fun i => (k i * (n i : Complex)).re) :=
      Finset.single_le_sum (fun i _ => hNonneg i) (Finset.mem_univ i0)
    _ = _ := (hSum Finset.univ).symm

theorem principal_zero_scaled_residue {q : Nat} [NeZero q]
    (k : DirichletCharacter Complex q -> Complex)
    (hk : forall chi, 0 <= (k chi).re)
    (hPrincipal : k 1 = 1) (rho : Complex) (hOne : Not (rho = 1))
    (hZero : DirichletCharacter.LFunction (1 : DirichletCharacter Complex q) rho = 0)
    (E : Complex -> Complex) (hE : AnalyticAt Complex E rho) :
    exists A : Complex, 0 < A.re /\
      Filter.Tendsto
        (fun s => (s - rho) * readout (fun chi => DirichletCharacter.LFunction chi) k E s)
        (nhdsWithin rho (Set.compl {rho})) (nhds (-A)) := by
  classical
  choose n g hg hgn hEq hPos using
    (fun chi : DirichletCharacter Complex q => L_factor_exists chi rho hOne)
  let A := Finset.univ.sum (fun chi : DirichletCharacter Complex q => k chi * (n chi : Complex))
  have hnPos : 0 < n (1 : DirichletCharacter Complex q) := hPos 1 hZero
  have hA : 0 < A.re := lt_of_lt_of_le
    (show (0 : Real) < n (1 : DirichletCharacter Complex q) by exact_mod_cast hnPos)
    (residue_re_bound k n (1 : DirichletCharacter Complex q) hk hPrincipal)
  refine Exists.intro A (And.intro hA ?_)
  exact weighted_limit (fun chi => DirichletCharacter.LFunction chi) g k n rho hg hgn hEq E hE

theorem principal_zero_not_analytic {q : Nat} [NeZero q]
    (k : DirichletCharacter Complex q -> Complex)
    (hk : forall chi, 0 <= (k chi).re)
    (hPrincipal : k 1 = 1) (rho : Complex) (hOne : Not (rho = 1))
    (hZero : DirichletCharacter.LFunction (1 : DirichletCharacter Complex q) rho = 0)
    (E : Complex -> Complex) (hE : AnalyticAt Complex E rho) :
    Not (AnalyticAt Complex
      (readout (fun chi => DirichletCharacter.LFunction chi) k E) rho) := by
  choose A hA hT using principal_zero_scaled_residue k hk hPrincipal rho hOne hZero E hE
  intro ha
  have hc : ContinuousAt
      (fun s : Complex => (s - rho) *
        readout (fun chi => DirichletCharacter.LFunction chi) k E s) rho :=
    (continuousAt_id.sub continuousAt_const).mul ha.continuousAt
  have hZeroLimit : Filter.Tendsto
      (fun s : Complex => (s - rho) *
        readout (fun chi => DirichletCharacter.LFunction chi) k E s)
      (nhdsWithin rho (Set.compl {rho})) (nhds 0) := by
    simpa only [sub_self, zero_mul] using hc.tendsto.mono_left nhdsWithin_le_nhds
  haveI : Filter.NeBot (nhdsWithin rho (Set.compl {rho})) := by
    have h := PerfectSpace.univ_preperfect rho (Set.mem_univ rho)
    have he : Set.compl ({rho} : Set Complex) =
        Compl.compl ({rho} : Set Complex) := by rfl
    rw [he]
    simpa only [AccPt, Filter.principal_univ, inf_top_eq] using h
  have hNeg : -A = 0 := tendsto_nhds_unique hT hZeroLimit
  have hAZ : A = 0 := neg_eq_zero.mp hNeg
  rw [hAZ, Complex.zero_re] at hA
  exact (lt_irrefl (0 : Real)) hA

end PrimeFactorOscillations.CarmichaelWeightedSignal
