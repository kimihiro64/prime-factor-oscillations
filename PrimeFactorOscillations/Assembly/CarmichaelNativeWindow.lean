/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelInfiniteWindow

/-!
# Native infinite Carmichael window and full quartic zero signal

Identifies the convergent physical coefficient packet with the complete
positive-multiplicity Dirichlet product, including its principal factor.
The quartic reference retains its own Mellin multiplier and is regular in
the RH half-strip by the installed unconditional seven-eighths theorem.
No signed arithmetic moment bound or stronger zero-free region is asserted.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.CarmichaelNativeWindow
open MeasureTheory
open CarmichaelInfiniteWindow CubicInfiniteLaplace
open CarmichaelIntegralSpectrum CarmichaelCorrelationSpectrum

variable {q : Nat} [NeZero q]

def nativePacket (S : Finset Nat.Primes)
    (a : DirichletCharacter Complex q -> Nat -> Complex) (t : Real) : Complex :=
  Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
    (multiplicity S chi : Complex) * physicalPacket (a chi) t)

def nativeCorrection (S : Finset Nat.Primes)
    (a : DirichletCharacter Complex q -> Nat -> Complex) (s : Complex) : Complex :=
  Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
    (multiplicity S chi : Complex) * DirichletPacketMellin.correction chi (a chi) s)

theorem native_product_logDeriv (S : Finset Nat.Primes)
    (s : Complex) (hs : 1 < s.re) :
    logDeriv (CarmichaelDirichletProduct.product (q := q) S) s =
      Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
        (multiplicity S chi : Complex) * logDeriv (DirichletCharacter.LFunction chi) s) := by
  classical
  have hOne : Not (s = 1) := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hN (chi : DirichletCharacter Complex q) :
      Not (DirichletCharacter.LFunction chi s = 0) :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re chi (Or.inr hOne) hs.le
  have hD (chi : DirichletCharacter Complex q) :
      DifferentiableAt Complex (DirichletCharacter.LFunction chi) s :=
    (DirichletZeroReadout.analyticOnNhd_LFunction_off_one chi s
      (Set.mem_compl_singleton_iff.mpr hOne)).differentiableAt
  rw [CarmichaelDirichletProduct.product]
  have hProd := logDeriv_prod (s := Finset.univ)
    (f := fun chi : DirichletCharacter Complex q =>
      (DirichletCharacter.LFunction chi) ^ multiplicity S chi) (x := s)
    (fun chi _ => pow_ne_zero _ (hN chi))
    (fun chi _ => (hD chi).pow (multiplicity S chi))
  rw [hProd]
  apply Finset.sum_congr rfl
  intro chi hi
  exact logDeriv_fun_pow (hD chi) (multiplicity S chi)

theorem nativeCorrection_analyticAt (S : Finset Nat.Primes)
    (a : DirichletCharacter Complex q -> Nat -> Complex)
    (C : DirichletCharacter Complex q -> Real)
    (herror : forall chi : DirichletCharacter Complex q, forall n : Nat, Not (n = 0) ->
      norm (a chi n - DirichletPacketMellin.coefficient chi n) <= C chi / (n : Real))
    (rho : Complex) (hr : 0 < rho.re) :
    AnalyticAt Complex (nativeCorrection S a) rho := by
  classical
  have hA (T : Finset (DirichletCharacter Complex q)) :
      AnalyticAt Complex (fun s : Complex => T.sum (fun chi =>
        (multiplicity S chi : Complex) * DirichletPacketMellin.correction chi (a chi) s)) rho := by
    induction T using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact analyticAt_const
    | @insert chi T hChi ih =>
      have hE := DirichletPacketMellin.analyticOnNhd_correction chi (a chi)
        (C chi) (herror chi) rho hr
      have hc : AnalyticAt Complex (fun _ : Complex => (multiplicity S chi : Complex)) rho :=
        analyticAt_const
      have hTerm : AnalyticAt Complex (fun s : Complex =>
          (multiplicity S chi : Complex) * DirichletPacketMellin.correction chi (a chi) s) rho :=
        hc.mul hE
      have hSum : AnalyticAt Complex (fun s : Complex =>
          (multiplicity S chi : Complex) * DirichletPacketMellin.correction chi (a chi) s +
            T.sum (fun eta => (multiplicity S eta : Complex) *
              DirichletPacketMellin.correction eta (a eta) s)) rho := hTerm.add ih
      simpa only [Finset.sum_insert hChi] using hSum
  exact hA Finset.univ

theorem nativePacket_hasMellin (S : Finset Nat.Primes)
    (a : DirichletCharacter Complex q -> Nat -> Complex)
    (ha0 : forall chi : DirichletCharacter Complex q, a chi 0 = 0)
    (C : DirichletCharacter Complex q -> Real)
    (herror : forall chi : DirichletCharacter Complex q, forall n : Nat, Not (n = 0) ->
      norm (a chi n - DirichletPacketMellin.coefficient chi n) <= C chi / (n : Real))
    (s : Complex) (hs : 1 < s.re) :
    HasMellin (nativePacket S a) (-s)
      (nativeWindowReadout (q := q) S (nativeCorrection S a) s) := by
  classical
  have hFin (T : Finset (DirichletCharacter Complex q)) :
      HasMellin (fun t : Real => T.sum (fun chi =>
          (multiplicity S chi : Complex) * physicalPacket (a chi) t)) (-s)
        (T.sum (fun chi => (multiplicity S chi : Complex) * windowReadout chi (a chi) s)) := by
    induction T using Finset.induction_on with
    | empty =>
      simp [HasMellin, MellinConvergent, IntegrableOn, mellin]
    | @insert chi T hChi ih =>
      have hc := comparison_physical_hasMellin chi (a chi) (ha0 chi)
        (C chi) (herror chi) s hs
      have hw : HasMellin (fun t : Real =>
          (multiplicity S chi : Complex) * physicalPacket (a chi) t) (-s)
          ((multiplicity S chi : Complex) * windowReadout chi (a chi) s) := by
        have hh := hasMellin_const_smul hc.1 (multiplicity S chi : Complex)
        simpa only [smul_eq_mul, hc.2] using hh
      have hh := hasMellin_add hw.1 ih.1
      rw [hw.2, ih.2] at hh
      simpa only [Finset.sum_insert hChi] using hh
  have hValue :
      Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
        (multiplicity S chi : Complex) * windowReadout chi (a chi) s) =
      nativeWindowReadout (q := q) S (nativeCorrection S a) s := by
    unfold windowReadout nativeWindowReadout DirichletPacketMellin.continuation
      DirichletZeroReadout.readout CarmichaelDirichletProduct.readout nativeCorrection
    rw [native_product_logDeriv S s hs]
    conv_rhs =>
      rw [mul_add, <- Finset.sum_neg_distrib, Finset.mul_sum,
        Finset.mul_sum, <- Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro chi hi
    ring
  have hh := hFin Finset.univ
  have hFun : (fun t : Real => Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
      (multiplicity S chi : Complex) * physicalPacket (a chi) t)) = nativePacket S a := rfl
  rw [hFun, hValue] at hh
  exact hh

theorem nativePacket_hasSum (S : Finset Nat.Primes)
    (a : DirichletCharacter Complex q -> Nat -> Complex)
    (ha0 : forall chi : DirichletCharacter Complex q, a chi 0 = 0)
    (C : DirichletCharacter Complex q -> Real)
    (herror : forall chi : DirichletCharacter Complex q, forall n : Nat, Not (n = 0) ->
      norm (a chi n - DirichletPacketMellin.coefficient chi n) <= C chi / (n : Real))
    (t : Real) (ht : 0 < t) :
    HasSum (fun n : Nat => (Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
        (multiplicity S chi : Complex) * a chi n)) *
          CubicReciprocalGaussian.carrierProfile ((n : Real) / t)) (nativePacket S a t) := by
  classical
  have hFin (T : Finset (DirichletCharacter Complex q)) :
      HasSum (fun n : Nat => T.sum (fun chi =>
          (multiplicity S chi : Complex) *
            (a chi n * CubicReciprocalGaussian.carrierProfile ((n : Real) / t))))
        (T.sum (fun chi => (multiplicity S chi : Complex) * physicalPacket (a chi) t)) := by
    induction T using Finset.induction_on with
    | empty =>
      have hz : HasSum (fun _ : Nat => (0 : Complex)) 0 := hasSum_zero
      simpa only [Finset.sum_empty] using hz
    | @insert chi T hChi ih =>
      have ha2 := lseries_summable chi (a chi) (C chi) (herror chi) 2 (by norm_num)
      have hh := physicalPacket_hasSum (a chi) (ha0 chi) ha2 t ht
      simpa only [Finset.sum_insert hChi] using
        (hh.mul_left (multiplicity S chi : Complex)).add ih
  have he (n : Nat) :
      (Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
        (multiplicity S chi : Complex) * a chi n)) *
          CubicReciprocalGaussian.carrierProfile ((n : Real) / t) =
      Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
        (multiplicity S chi : Complex) *
          (a chi n * CubicReciprocalGaussian.carrierProfile ((n : Real) / t))) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro chi hi
    ring
  change HasSum (fun n : Nat => (Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
        (multiplicity S chi : Complex) * a chi n)) *
          CubicReciprocalGaussian.carrierProfile ((n : Real) / t))
    (Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
      (multiplicity S chi : Complex) * physicalPacket (a chi) t))
  simpa only [<- he] using hFin Finset.univ

theorem native_lambda_hasSum (S : Finset Nat.Primes)
    (hDiv : forall p : S,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q))))
    (t : Real) (ht : 0 < t) :
    HasSum (fun n : Nat =>
      (multiplicity S (1 : DirichletCharacter Complex q) : Complex) *
        (carmichaelPrimeWeight q S n : Complex) *
          (ArithmeticFunction.vonMangoldt n : Complex) *
            CubicReciprocalGaussian.carrierProfile ((n : Real) / t))
      (nativePacket (q := q) S (fun chi => DirichletPacketMellin.coefficient chi) t) := by
  have h0 (chi : DirichletCharacter Complex q) :
      DirichletPacketMellin.coefficient chi 0 = 0 := by
    simp [DirichletPacketMellin.coefficient]
  have hError (chi : DirichletCharacter Complex q) (n : Nat) (hn : Not (n = 0)) :
      norm (DirichletPacketMellin.coefficient chi n -
        DirichletPacketMellin.coefficient chi n) <= (0 : Real) / (n : Real) := by simp
  have hh := nativePacket_hasSum (q := q) S
    (fun chi => DirichletPacketMellin.coefficient chi)
    h0 (fun _ => 0) hError t ht
  have hCoeff (n : Nat) :
      (multiplicity S (1 : DirichletCharacter Complex q) : Complex) *
        (carmichaelPrimeWeight q S n : Complex) * (ArithmeticFunction.vonMangoldt n : Complex) =
      Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
        (multiplicity S chi : Complex) * DirichletPacketMellin.coefficient chi n) := by
    have h := CarmichaelPhysicalPacket.native_dirichlet_expansion (q := q) S hDiv {n}
      (fun k : Nat => (ArithmeticFunction.vonMangoldt k : Complex)) (0 : Complex)
    simpa [CarmichaelPhysicalPacket.dirichletPacket, DirichletPacketMellin.coefficient,
      mul_assoc] using h
  have he (n : Nat) :
      (multiplicity S (1 : DirichletCharacter Complex q) : Complex) *
        (carmichaelPrimeWeight q S n : Complex) * (ArithmeticFunction.vonMangoldt n : Complex) *
          CubicReciprocalGaussian.carrierProfile ((n : Real) / t) =
      (Finset.univ.sum (fun chi : DirichletCharacter Complex q =>
        (multiplicity S chi : Complex) * DirichletPacketMellin.coefficient chi n)) *
          CubicReciprocalGaussian.carrierProfile ((n : Real) / t) := by
    rw [hCoeff n]
  simpa only [<- he] using hh

theorem native_quartic_mellin (S : Finset Nat.Primes)
    (a : DirichletCharacter Complex q -> Nat -> Complex)
    (ha0 : forall chi : DirichletCharacter Complex q, a chi 0 = 0)
    (C : DirichletCharacter Complex q -> Real)
    (herror : forall chi : DirichletCharacter Complex q, forall n : Nat, Not (n = 0) ->
      norm (a chi n - DirichletPacketMellin.coefficient chi n) <= C chi / (n : Real))
    (s : Complex) (hs : 1 < s.re) :
    mellin (CarmichaelWindowTransfer.quarticPhysicalProbe (nativePacket S a)) (-s) =
      nativeWindowReadout (q := q) S (nativeCorrection S a) s -
        HSMul.hSMul ((4 : Real) ^ (-1 : Int))
          (nativeWindowReadout (q := q) S (nativeCorrection S a)
            (DirichletCompensatedProbe.quarticMap s)) := by
  have hq : 1 < (DirichletCompensatedProbe.quarticMap s).re := by
    dsimp [DirichletCompensatedProbe.quarticMap]
    simp only [Complex.div_ofNat_re, Complex.add_re]
    norm_num
    linarith
  have hMain := nativePacket_hasMellin S a ha0 C herror s hs
  have hRef := nativePacket_hasMellin S a ha0 C herror
    (DirichletCompensatedProbe.quarticMap s) hq
  have hh := CarmichaelWindowTransfer.quarticPhysicalProbe_mellin
    (nativePacket S a) s hMain.1 hRef.1
  rw [hMain.2, hRef.2] at hh
  exact hh

theorem native_observed_zero_readout (S : Finset Nat.Primes)
    (a : DirichletCharacter Complex q -> Nat -> Complex)
    (C : DirichletCharacter Complex q -> Real)
    (herror : forall chi : DirichletCharacter Complex q, forall n : Nat, Not (n = 0) ->
      norm (a chi n - DirichletPacketMellin.coefficient chi n) <= C chi / (n : Real))
    (rho : Complex) (hs : (1 / 2 : Real) < rho.re) (hs1 : rho.re < 1) :
    meromorphicOrderAt (nativeWindowReadout (q := q) S (nativeCorrection S a)) rho = -1 <->
      exists chi : DirichletCharacter Complex q,
        0 < multiplicity S chi /\ DirichletCharacter.LFunction chi rho = 0 := by
  have hOne : Not (rho = 1) := by
    intro h
    rw [h] at hs1
    norm_num at hs1
  have hr : 0 < rho.re := by linarith
  exact (nativeWindowReadout_order_iff_product_zero S (nativeCorrection S a) rho hs hs1
    (nativeCorrection_analyticAt S a C herror rho hr)).trans
      (CarmichaelDirichletProduct.product_zero_iff S rho)


def nativeCompensatedReadout (S : Finset Nat.Primes) (E : Complex -> Complex)
    (s : Complex) : Complex :=
  nativeWindowReadout (q := q) S E s -
    (1 / 4 : Complex) * nativeWindowReadout (q := q) S E
      (DirichletCompensatedProbe.quarticMap s)

theorem native_reference_analyticAt (S : Finset Nat.Primes)
    (E : Complex -> Complex) (hE : AnalyticOnNhd Complex E {s : Complex | 0 < s.re})
    (rho : Complex) (hs : (1 / 2 : Real) < rho.re) (hOne : Not (rho = 1)) :
    AnalyticAt Complex
      (fun s => (1 / 4 : Complex) * nativeWindowReadout (q := q) S E
        (DirichletCompensatedProbe.quarticMap s)) rho := by
  classical
  let r := DirichletCompensatedProbe.quarticMap rho
  have hr : (7 / 8 : Real) < r.re := by
    dsimp [r]
    rw [DirichletCompensatedProbe.quarticMap_re]
    linarith
  have hr0 : 0 < r.re := by linarith
  have hrOne : Not (r = 1) := by
    intro he
    apply hOne
    dsimp [r, DirichletCompensatedProbe.quarticMap] at he
    linear_combination 4 * he
  have hNonzero : Not (CarmichaelDirichletProduct.product (q := q) S r = 0) := by
    rw [CarmichaelDirichletProduct.product, Finset.prod_apply]
    apply Finset.prod_ne_zero_iff.mpr
    intro chi _
    apply pow_ne_zero
    exact QRH.dirichletL_ne_zero q chi r hr (fun h => hrOne h.2)
  have hProduct := CarmichaelDirichletProduct.analyticOnNhd_product_off_one
    (q := q) S r (Set.mem_compl_singleton_iff.mpr hrOne)
  have hRead : AnalyticAt Complex
      (CarmichaelDirichletProduct.readout (q := q) S E) r := by
    unfold CarmichaelDirichletProduct.readout
    simp only [logDeriv_apply]
    exact (hProduct.deriv.div hProduct hNonzero).neg.add (hE r hr0)
  have hWindow : AnalyticAt Complex (nativeWindowReadout (q := q) S E) r :=
    (CubicCarrierAnalytic.carrierMultiplier_analyticAt r hr0).mul hRead
  have hMap : AnalyticAt Complex DirichletCompensatedProbe.quarticMap rho := by
    change AnalyticAt Complex (fun s : Complex => (s + 3) / 4) rho
    exact (analyticAt_id.add analyticAt_const).div_const
  have hComp : AnalyticAt Complex
      (fun s => nativeWindowReadout (q := q) S E
        (DirichletCompensatedProbe.quarticMap s)) rho :=
    hWindow.comp (f := DirichletCompensatedProbe.quarticMap) hMap
  have hc : AnalyticAt Complex (fun _ : Complex => (1 / 4 : Complex)) rho :=
    analyticAt_const
  exact hc.mul hComp

theorem native_compensated_order_iff_product_zero (S : Finset Nat.Primes)
    (E : Complex -> Complex) (hE : AnalyticOnNhd Complex E {s : Complex | 0 < s.re})
    (rho : Complex) (hs : (1 / 2 : Real) < rho.re) (hs1 : rho.re < 1) :
    meromorphicOrderAt (nativeCompensatedReadout (q := q) S E) rho = -1 <->
      CarmichaelDirichletProduct.product (q := q) S rho = 0 := by
  have hr : 0 < rho.re := by linarith
  have hOne : Not (rho = 1) := by
    intro h
    rw [h] at hs1
    norm_num at hs1
  let F := nativeWindowReadout (q := q) S E
  let R : Complex -> Complex := fun s => -((1 / 4 : Complex) *
    nativeWindowReadout (q := q) S E (DirichletCompensatedProbe.quarticMap s))
  have hRef : AnalyticAt Complex R rho :=
    (native_reference_analyticAt S E hE rho hs hOne).neg
  have hProduct := CarmichaelDirichletProduct.analyticOnNhd_product_off_one
    (q := q) S rho (Set.mem_compl_singleton_iff.mpr hOne)
  have hMain : MeromorphicAt F rho :=
    (CubicCarrierAnalytic.carrierMultiplier_analyticAt rho hr).meromorphicAt.mul
      (hProduct.meromorphicAt.logDeriv.neg.add (hE rho hr).meromorphicAt)
  have hLt : ((-1 : Int) : WithTop Int) < ((0 : Int) : WithTop Int) :=
    WithTop.coe_lt_coe.mpr (by norm_num)
  constructor
  . intro hOrder
    by_contra hn
    have hRead : AnalyticAt Complex
        (CarmichaelDirichletProduct.readout (q := q) S E) rho := by
      unfold CarmichaelDirichletProduct.readout
      simp only [logDeriv_apply]
      exact (hProduct.deriv.div hProduct hn).neg.add (hE rho hr)
    have hF : AnalyticAt Complex F rho :=
      (CubicCarrierAnalytic.carrierMultiplier_analyticAt rho hr).mul hRead
    have hReg : AnalyticAt Complex (nativeCompensatedReadout (q := q) S E) rho := by
      change AnalyticAt Complex (fun s => F s + R s) rho
      exact hF.add hRef
    have hNonneg := hReg.meromorphicOrderAt_nonneg
    rw [hOrder] at hNonneg
    exact (not_lt_of_ge hNonneg) hLt
  . intro hz
    have hOrder : meromorphicOrderAt F rho = -1 :=
      (nativeWindowReadout_order_iff_product_zero S E rho hs hs1 (hE rho hr)).mpr hz
    have hNonneg := hRef.meromorphicOrderAt_nonneg
    have hDifferent : Not (meromorphicOrderAt F rho = meromorphicOrderAt R rho) := by
      intro he
      rw [hOrder] at he
      rw [<- he] at hNonneg
      exact (not_lt_of_ge hNonneg) hLt
    change meromorphicOrderAt (F + R) rho = -1
    rw [meromorphicOrderAt_add_of_ne hMain hRef.meromorphicAt hDifferent,
      hOrder, min_eq_left]
    exact le_trans hLt.le hNonneg

theorem native_compensated_observed_zero (S : Finset Nat.Primes)
    (a : DirichletCharacter Complex q -> Nat -> Complex)
    (C : DirichletCharacter Complex q -> Real)
    (herror : forall chi : DirichletCharacter Complex q, forall n : Nat, Not (n = 0) ->
      norm (a chi n - DirichletPacketMellin.coefficient chi n) <= C chi / (n : Real))
    (rho : Complex) (hs : (1 / 2 : Real) < rho.re) (hs1 : rho.re < 1) :
    meromorphicOrderAt
      (nativeCompensatedReadout (q := q) S (nativeCorrection S a)) rho = -1 <->
      exists chi : DirichletCharacter Complex q,
        0 < multiplicity S chi /\ DirichletCharacter.LFunction chi rho = 0 :=
  (native_compensated_order_iff_product_zero S (nativeCorrection S a)
    (fun z hz => nativeCorrection_analyticAt S a C herror z hz) rho hs hs1).trans
      (CarmichaelDirichletProduct.product_zero_iff S rho)

theorem native_compensated_principal_signal (S : Finset Nat.Primes)
    (hDiv : forall p : S,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q))))
    (E : Complex -> Complex) (hE : AnalyticOnNhd Complex E {s : Complex | 0 < s.re})
    (rho : Complex) (hs : (1 / 2 : Real) < rho.re) (hs1 : rho.re < 1)
    (hZero : DirichletCharacter.LFunction (1 : DirichletCharacter Complex q) rho = 0) :
    meromorphicOrderAt (nativeCompensatedReadout (q := q) S E) rho = -1 :=
  (native_compensated_order_iff_product_zero S E hE rho hs hs1).mpr
    (CarmichaelDirichletProduct.principal_zero_imp_product_zero S hDiv rho hZero)


theorem native_quartic_mellin_eq_compensated (S : Finset Nat.Primes)
    (a : DirichletCharacter Complex q -> Nat -> Complex)
    (ha0 : forall chi : DirichletCharacter Complex q, a chi 0 = 0)
    (C : DirichletCharacter Complex q -> Real)
    (herror : forall chi : DirichletCharacter Complex q, forall n : Nat, Not (n = 0) ->
      norm (a chi n - DirichletPacketMellin.coefficient chi n) <= C chi / (n : Real))
    (s : Complex) (hs : 1 < s.re) :
    mellin (CarmichaelWindowTransfer.quarticPhysicalProbe (nativePacket S a)) (-s) =
      nativeCompensatedReadout (q := q) S (nativeCorrection S a) s := by
  simpa [nativeCompensatedReadout, zpow_neg, Complex.real_smul] using
    native_quartic_mellin S a ha0 C herror s hs

end PrimeFactorOscillations.CarmichaelNativeWindow
