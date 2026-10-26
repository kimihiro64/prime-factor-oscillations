/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelIntegralSpectrum
import PrimeFactorOscillations.Helpers.DirichletZeroReadout

/-!
# Native Dirichlet products and shared-zero multiplicities

The integer spectrum defines an actual finite product of full L-functions.
All shared zeros add their orders. The original principal multiplicity
survives, and an analytic reconstruction error cannot conceal a supported
zero. Odd packets omit nonprincipal quadratic factors from the product.
-/


set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDirichletProduct

open CarmichaelIntegralSpectrum CarmichaelPermutationKernel

variable {q : Nat} [NeZero q]

def product (S : Finset Nat.Primes) : Complex -> Complex :=
  Finset.univ.prod (fun chi : DirichletCharacter Complex q =>
    (DirichletCharacter.LFunction chi) ^ multiplicity S chi)

theorem product_ne_zero_two (S : Finset Nat.Primes) :
    Not (product (q := q) S 2 = 0) := by
  classical
  rw [product, Finset.prod_apply]
  apply Finset.prod_ne_zero_iff.mpr
  intro chi _
  exact pow_ne_zero _ (DirichletCharacter.LFunction_ne_zero_of_one_le_re chi
    (Or.inr (by norm_num)) (by norm_num))

theorem analyticOnNhd_product_off_one (S : Finset Nat.Primes) :
    AnalyticOnNhd Complex (product (q := q) S) (Set.compl {1}) := by
  classical
  intro rho hRho
  have hA : forall T : Finset (DirichletCharacter Complex q),
      AnalyticAt Complex
        (T.prod (fun chi => (DirichletCharacter.LFunction chi) ^ multiplicity S chi)) rho := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty]
      change AnalyticAt Complex (fun _ : Complex => (1 : Complex)) rho
      exact analyticAt_const
    | @insert chi T hChi ih =>
      have hL := (DirichletZeroReadout.analyticOnNhd_LFunction_off_one chi) rho hRho
      simpa only [Finset.prod_insert hChi] using (hL.pow (multiplicity S chi)).mul ih
  exact hA Finset.univ

theorem product_zero_iff (S : Finset Nat.Primes) (rho : Complex) :
    product (q := q) S rho = 0 <->
      exists chi : DirichletCharacter Complex q,
        0 < multiplicity S chi /\ DirichletCharacter.LFunction chi rho = 0 := by
  classical
  rw [product, Finset.prod_apply, Finset.prod_eq_zero_iff]
  constructor
  . intro h
    choose chi hChi using h
    have hPow : (DirichletCharacter.LFunction chi rho) ^ multiplicity S chi = 0 := hChi.2
    have hMu : Not (multiplicity S chi = 0) := by
      intro hz
      rw [hz, pow_zero] at hPow
      exact one_ne_zero hPow
    exact Exists.intro chi (And.intro (Nat.pos_of_ne_zero hMu) ((pow_eq_zero_iff hMu).mp hPow))
  . intro h
    choose chi hChi using h
    exact Exists.intro chi (And.intro (Finset.mem_univ chi)
      ((pow_eq_zero_iff (Nat.ne_of_gt hChi.1)).mpr hChi.2))

theorem principal_zero_imp_product_zero (S : Finset Nat.Primes)
    (hDiv : forall p : S,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q))))
    (rho : Complex)
    (hZero : DirichletCharacter.LFunction (1 : DirichletCharacter Complex q) rho = 0) :
    product (q := q) S rho = 0 := by
  apply (product_zero_iff S rho).mpr
  apply Exists.intro (1 : DirichletCharacter Complex q)
  apply And.intro _ hZero
  rw [multiplicity_principal S hDiv]
  exact normalization_pos S hDiv

theorem product_order_formula (S : Finset Nat.Primes) (rho : Complex)
    (hOne : Not (rho = 1)) :
    meromorphicOrderAt (product (q := q) S) rho =
      Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
        (multiplicity S chi : WithTop Int) *
          meromorphicOrderAt (DirichletCharacter.LFunction chi) rho) := by
  classical
  have hL (chi : DirichletCharacter Complex q) :
      AnalyticAt Complex (DirichletCharacter.LFunction chi) rho :=
    (DirichletZeroReadout.analyticOnNhd_LFunction_off_one chi) rho
      (Set.mem_compl_singleton_iff.mpr hOne)
  rw [product, meromorphicOrderAt_prod (fun chi _ =>
    ((hL chi).pow (multiplicity S chi)).meromorphicAt)]
  apply Finset.sum_congr rfl
  intro chi _
  exact meromorphicOrderAt_pow (hL chi).meromorphicAt

theorem product_order_ne_top (S : Finset Nat.Primes) (rho : Complex)
    (hOne : Not (rho = 1)) :
    Not (meromorphicOrderAt (product (q := q) S) rho = Top.top) := by
  let F := product (q := q) S
  have ha := analyticOnNhd_product_off_one (q := q) S
  have haTwo : AnalyticAt Complex F 2 :=
    ha 2 (Set.mem_compl_singleton_iff.mpr (by norm_num))
  have hTwo : meromorphicOrderAt F 2 = 0 :=
    (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero haTwo.meromorphicAt).mp
      (Exists.intro (F 2) (And.intro (product_ne_zero_two S)
        (haTwo.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)))
  have hM : MeromorphicOn F (Set.compl {1}) := fun z hz => (ha z hz).meromorphicAt
  apply hM.meromorphicOrderAt_ne_top_of_isPreconnected (x := (2 : Complex))
    (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
  . exact Set.mem_compl_singleton_iff.mpr (by norm_num)
  . exact Set.mem_compl_singleton_iff.mpr hOne
  . rw [hTwo]
    simp


theorem principal_order_le_product_order (S : Finset Nat.Primes)
    (hDiv : forall p : S,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q))))
    (rho : Complex) (hOne : Not (rho = 1)) :
    (normalization (G := Units (ZMod q)) S : WithTop Int) *
      meromorphicOrderAt (DirichletCharacter.LFunction (1 : DirichletCharacter Complex q)) rho <=
    meromorphicOrderAt (product (q := q) S) rho := by
  classical
  have hNonneg (chi : DirichletCharacter Complex q) :
      0 <= (multiplicity S chi : WithTop Int) *
        meromorphicOrderAt (DirichletCharacter.LFunction chi) rho := by
    have ha := (DirichletZeroReadout.analyticOnNhd_LFunction_off_one chi) rho
      (Set.mem_compl_singleton_iff.mpr hOne)
    rw [<- meromorphicOrderAt_pow ha.meromorphicAt]
    exact (ha.pow (multiplicity S chi)).meromorphicOrderAt_nonneg
  rw [product_order_formula S rho hOne]
  have h := Finset.single_le_sum (fun chi _ => hNonneg chi)
    (Finset.mem_univ (1 : DirichletCharacter Complex q))
  simpa only [multiplicity_principal S hDiv] using h

theorem product_logDeriv_order (S : Finset Nat.Primes) (rho : Complex)
    (hOne : Not (rho = 1)) (hZero : product (q := q) S rho = 0) :
    meromorphicOrderAt (logDeriv (product (q := q) S)) rho = -1 := by
  have ha := (analyticOnNhd_product_off_one (q := q) S) rho
    (Set.mem_compl_singleton_iff.mpr hOne)
  have ht : Filter.Tendsto (product (q := q) S)
      (nhdsWithin rho (Set.compl {rho})) (nhds 0) := by
    simpa only [hZero] using ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hPos := (tendsto_zero_iff_meromorphicOrderAt_pos ha.meromorphicAt).mp ht
  exact meromorphicOrderAt_logDeriv_eq_neg_one ha.meromorphicAt
    (ne_of_gt hPos) (product_order_ne_top S rho hOne)

def readout (S : Finset Nat.Primes) (E : Complex -> Complex) (s : Complex) : Complex :=
  -logDeriv (product (q := q) S) s + E s

theorem readout_order_iff_product_zero (S : Finset Nat.Primes) (rho : Complex)
    (hOne : Not (rho = 1)) (E : Complex -> Complex) (hE : AnalyticAt Complex E rho) :
    meromorphicOrderAt (readout (q := q) S E) rho = -1 <-> product (q := q) S rho = 0 := by
  have ha := (analyticOnNhd_product_off_one (q := q) S) rho
    (Set.mem_compl_singleton_iff.mpr hOne)
  let negLog : Complex -> Complex := fun s => -logDeriv (product (q := q) S) s
  have hNeg : MeromorphicAt negLog rho := ha.meromorphicAt.logDeriv.neg
  constructor
  . intro hOrder
    by_contra hNonzero
    have hRegular : AnalyticAt Complex (readout (q := q) S E) rho := by
      have hFun : readout (q := q) S E =
          fun s => -(deriv (product (q := q) S) s / product (q := q) S s) + E s := by
        funext s
        rw [readout, logDeriv_apply]
      rw [hFun]
      exact (ha.deriv.div ha hNonzero).neg.add hE
    have hNonneg := hRegular.meromorphicOrderAt_nonneg
    rw [hOrder] at hNonneg
    have hLt : ((-1 : Int) : WithTop Int) < ((0 : Int) : WithTop Int) :=
      WithTop.coe_lt_coe.mpr (by norm_num)
    exact (not_lt_of_ge hNonneg) hLt
  . intro hZero
    have hOrder : meromorphicOrderAt negLog rho = -1 := by
      dsimp [negLog]
      rw [<- meromorphicOrderAt_fun_neg]
      exact product_logDeriv_order S rho hOne hZero
    have hEOrder := hE.meromorphicOrderAt_nonneg
    have hDifferent : Not (meromorphicOrderAt negLog rho = meromorphicOrderAt E rho) := by
      intro he
      rw [hOrder] at he
      rw [<- he] at hEOrder
      have hLt : ((-1 : Int) : WithTop Int) < ((0 : Int) : WithTop Int) :=
        WithTop.coe_lt_coe.mpr (by norm_num)
      exact (not_lt_of_ge hEOrder) hLt
    change meromorphicOrderAt (negLog + E) rho = -1
    rw [meromorphicOrderAt_add_of_ne hNeg hE.meromorphicAt hDifferent, hOrder, min_eq_left]
    exact le_of_lt (lt_of_lt_of_le
      (show ((-1 : Int) : WithTop Int) < ((0 : Int) : WithTop Int) from
        WithTop.coe_lt_coe.mpr (by norm_num)) hEOrder)

theorem readout_order_iff_supported_zero (S : Finset Nat.Primes) (rho : Complex)
    (hOne : Not (rho = 1)) (E : Complex -> Complex) (hE : AnalyticAt Complex E rho) :
    meromorphicOrderAt (readout (q := q) S E) rho = -1 <->
      exists chi : DirichletCharacter Complex q,
        0 < multiplicity S chi /\ DirichletCharacter.LFunction chi rho = 0 :=
  (readout_order_iff_product_zero S rho hOne E hE).trans (product_zero_iff S rho)

theorem principal_zero_readout_order (S : Finset Nat.Primes)
    (hDiv : forall p : S,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q))))
    (rho : Complex) (hOne : Not (rho = 1)) (E : Complex -> Complex)
    (hE : AnalyticAt Complex E rho)
    (hZero : DirichletCharacter.LFunction (1 : DirichletCharacter Complex q) rho = 0) :
    meromorphicOrderAt (readout (q := q) S E) rho = -1 :=
  (readout_order_iff_product_zero S rho hOne E hE).mpr
    (principal_zero_imp_product_zero S hDiv rho hZero)

def nonquadraticCharacters (q : Nat) : Finset (DirichletCharacter Complex q) := by
  classical
  exact Finset.univ.filter (fun chi => chi = 1 \/
    Not (forall u : Units (ZMod q), (chi (u : ZMod q)) ^ 2 = 1))

theorem odd_product_eq_nonquadratic (S : Finset Nat.Primes)
    (hDiv : forall p : S,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q))))
    (hOdd : forall p : S, Not ((p.val : Nat) = 2)) (s : Complex) :
    product (q := q) S s = (nonquadraticCharacters q).prod
      (fun chi => (DirichletCharacter.LFunction chi s) ^ multiplicity S chi) := by
  classical
  rw [product, Finset.prod_apply, nonquadraticCharacters, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro chi _
  by_cases h : chi = 1 \/
      Not (forall u : Units (ZMod q), (chi (u : ZMod q)) ^ 2 = 1)
  . rw [ite_eq_left h]
    rfl
  . have hChi : Not (chi = 1) := fun he => h (Or.inl he)
    have hSquare : forall u : Units (ZMod q), (chi (u : ZMod q)) ^ 2 = 1 := by
      by_contra he
      exact h (Or.inr he)
    rw [ite_eq_right h, odd_multiplicity_quadratic_zero S hDiv hOdd chi hChi hSquare, pow_zero]
    rfl

end PrimeFactorOscillations.CarmichaelDirichletProduct
