/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelDirichletProduct
import PrimeFactorOscillations.Assembly.CarmichaelPhysicalPacket
import PrimeFactorOscillations.Helpers.CubicInfiniteWindow

/-!
# Infinite physical window and native Dirichlet zero readout

Transfers the actual infinite coefficient packet and its quartic reference
with both Mellin factors retained. Existing coefficient comparisons discharge
initial convergence on Re(s)>1. The multiplier preserves individual and
native-product zero poles on 1/2<Re(s)<1 without RH. The signed arithmetic
Abel estimate and the prime-selected cubic paired-kernel adapter are separate.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.CarmichaelInfiniteWindow
open MeasureTheory
open CubicInfiniteLaplace CubicInfiniteWindow

def physicalPacket (a : Nat -> Complex) (t : Real) : Complex :=
  windowLaplace a (1 / t)

theorem physicalPacket_hasSum (a : Nat -> Complex) (ha0 : a 0 = 0)
    (ha2 : LSeriesSummable a 2) (t : Real) (ht : 0 < t) :
    HasSum (fun n : Nat => a n *
      CubicReciprocalGaussian.carrierProfile ((n : Real) / t)) (physicalPacket a t) := by
  simpa [physicalPacket, div_eq_mul_inv] using
    windowLaplace_hasSum a ha0 ha2 (1 / t) (one_div_pos.mpr ht)

theorem physicalPacket_hasMellin (a : Nat -> Complex) (ha0 : a 0 = 0)
    (ha2 : LSeriesSummable a 2) (s : Complex) (hs : 0 < s.re)
    (ha : LSeriesSummable a s) :
    HasMellin (physicalPacket a) (-s)
      (CubicCarrierMellin.carrierMultiplier s * LSeries a s) := by
  have hw := windowLaplace_hasMellin a ha0 ha2 s hs ha
  have hh := CarmichaelPhysicalPacket.scaledWindow_hasMellin
    (windowLaplace a) s _ hw 1 zero_lt_one
  change HasMellin (fun t : Real => windowLaplace a (1 / t)) (-s) _
  simpa using hh

theorem quartic_physical_mellin (a : Nat -> Complex) (ha0 : a 0 = 0)
    (ha2 : LSeriesSummable a 2) (s : Complex) (hs : 0 < s.re)
    (ha : LSeriesSummable a s)
    (haq : LSeriesSummable a (DirichletCompensatedProbe.quarticMap s)) :
    mellin (CarmichaelWindowTransfer.quarticPhysicalProbe (physicalPacket a)) (-s) =
      CubicCarrierMellin.carrierMultiplier s * LSeries a s -
        HSMul.hSMul ((4 : Real) ^ (-1 : Int))
          (CubicCarrierMellin.carrierMultiplier (DirichletCompensatedProbe.quarticMap s) *
            LSeries a (DirichletCompensatedProbe.quarticMap s)) := by
  have hq : 0 < (DirichletCompensatedProbe.quarticMap s).re := by
    dsimp [DirichletCompensatedProbe.quarticMap]
    simp only [Complex.div_ofNat_re, Complex.add_re]
    norm_num
    linarith
  have hMain := physicalPacket_hasMellin a ha0 ha2 s hs ha
  have hRef := physicalPacket_hasMellin a ha0 ha2
    (DirichletCompensatedProbe.quarticMap s) hq haq
  have hh := CarmichaelWindowTransfer.quarticPhysicalProbe_mellin
    (physicalPacket a) s hMain.1 hRef.1
  rw [hMain.2, hRef.2] at hh
  exact hh

variable {q : Nat} [NeZero q]

def windowReadout (chi : DirichletCharacter Complex q) (a : Nat -> Complex)
    (s : Complex) : Complex :=
  CubicCarrierMellin.carrierMultiplier s * DirichletPacketMellin.continuation chi a s

theorem comparison_physical_hasMellin (chi : DirichletCharacter Complex q)
    (a : Nat -> Complex) (ha0 : a 0 = 0) (C : Real)
    (herror : forall n : Nat, Not (n = 0) ->
      norm (a n - DirichletPacketMellin.coefficient chi n) <= C / (n : Real))
    (s : Complex) (hs : 1 < s.re) :
    HasMellin (physicalPacket a) (-s) (windowReadout chi a s) := by
  have ha2 := lseries_summable chi a C herror 2 (by norm_num)
  have ha := lseries_summable chi a C herror s hs
  unfold windowReadout
  rw [DirichletPacketMellin.continuation_eq_LSeries chi a C herror s hs]
  exact physicalPacket_hasMellin a ha0 ha2 s (by linarith) ha

theorem comparison_quartic_mellin (chi : DirichletCharacter Complex q)
    (a : Nat -> Complex) (ha0 : a 0 = 0) (C : Real)
    (herror : forall n : Nat, Not (n = 0) ->
      norm (a n - DirichletPacketMellin.coefficient chi n) <= C / (n : Real))
    (s : Complex) (hs : 1 < s.re) :
    mellin (CarmichaelWindowTransfer.quarticPhysicalProbe (physicalPacket a)) (-s) =
      windowReadout chi a s -
        HSMul.hSMul ((4 : Real) ^ (-1 : Int))
          (windowReadout chi a (DirichletCompensatedProbe.quarticMap s)) := by
  have hq : 1 < (DirichletCompensatedProbe.quarticMap s).re := by
    dsimp [DirichletCompensatedProbe.quarticMap]
    simp only [Complex.div_ofNat_re, Complex.add_re]
    norm_num
    linarith
  have ha2 := lseries_summable chi a C herror 2 (by norm_num)
  have ha := lseries_summable chi a C herror s hs
  have haq := lseries_summable chi a C herror (DirichletCompensatedProbe.quarticMap s) hq
  unfold windowReadout
  rw [DirichletPacketMellin.continuation_eq_LSeries chi a C herror s hs,
    DirichletPacketMellin.continuation_eq_LSeries chi a C herror
      (DirichletCompensatedProbe.quarticMap s) hq]
  exact quartic_physical_mellin a ha0 ha2 s (by linarith) ha haq

theorem windowReadout_order_iff_zero (chi : DirichletCharacter Complex q)
    (a : Nat -> Complex) (C : Real)
    (herror : forall n : Nat, Not (n = 0) ->
      norm (a n - DirichletPacketMellin.coefficient chi n) <= C / (n : Real))
    (rho : Complex) (hs : (1 / 2 : Real) < rho.re) (hs1 : rho.re < 1) :
    meromorphicOrderAt (windowReadout chi a) rho = -1 <->
      DirichletCharacter.LFunction chi rho = 0 := by
  have hOne : Not (rho = 1) := by
    intro h
    rw [h] at hs1
    norm_num at hs1
  have hL := DirichletZeroReadout.analyticOnNhd_LFunction_off_one chi rho
    (Set.mem_compl_singleton_iff.mpr hOne)
  have hr : 0 < rho.re := by linarith
  have hE := DirichletPacketMellin.analyticOnNhd_correction chi a C herror rho hr
  have hD : MeromorphicAt (DirichletPacketMellin.continuation chi a) rho := by
    change MeromorphicAt (fun s : Complex =>
      -logDeriv (DirichletCharacter.LFunction chi) s + DirichletPacketMellin.correction chi a s)
        rho
    exact hL.meromorphicAt.logDeriv.neg.add hE.meromorphicAt
  change meromorphicOrderAt (fun s : Complex =>
    CubicCarrierMellin.carrierMultiplier s * DirichletPacketMellin.continuation chi a s) rho =
      -1 <-> _
  rw [carrierMultiplier_order_mul _ rho hD hs hs1]
  exact DirichletPacketMellin.zero_readout chi a C herror rho hr hOne

def nativeWindowReadout (S : Finset Nat.Primes) (E : Complex -> Complex)
    (s : Complex) : Complex :=
  CubicCarrierMellin.carrierMultiplier s *
    CarmichaelDirichletProduct.readout (q := q) S E s

theorem nativeWindowReadout_order_iff_product_zero (S : Finset Nat.Primes)
    (E : Complex -> Complex) (rho : Complex)
    (hs : (1 / 2 : Real) < rho.re) (hs1 : rho.re < 1) (hE : AnalyticAt Complex E rho) :
    meromorphicOrderAt (nativeWindowReadout (q := q) S E) rho = -1 <->
      CarmichaelDirichletProduct.product (q := q) S rho = 0 := by
  have hOne : Not (rho = 1) := by
    intro h
    rw [h] at hs1
    norm_num at hs1
  have hL := CarmichaelDirichletProduct.analyticOnNhd_product_off_one (q := q) S rho
    (Set.mem_compl_singleton_iff.mpr hOne)
  have hD : MeromorphicAt (CarmichaelDirichletProduct.readout (q := q) S E) rho := by
    change MeromorphicAt (fun s : Complex =>
      -logDeriv (CarmichaelDirichletProduct.product (q := q) S) s + E s) rho
    exact hL.meromorphicAt.logDeriv.neg.add hE.meromorphicAt
  change meromorphicOrderAt (fun s : Complex =>
    CubicCarrierMellin.carrierMultiplier s *
      CarmichaelDirichletProduct.readout (q := q) S E s) rho = -1 <-> _
  rw [carrierMultiplier_order_mul _ rho hD hs hs1]
  exact CarmichaelDirichletProduct.readout_order_iff_product_zero S rho hOne E hE

theorem native_principal_zero_signal (S : Finset Nat.Primes)
    (hDiv : forall p : S,
      Dvd.dvd (p.val : Nat) (Monoid.exponent (Units (ZMod q))))
    (E : Complex -> Complex) (rho : Complex)
    (hs : (1 / 2 : Real) < rho.re) (hs1 : rho.re < 1) (hE : AnalyticAt Complex E rho)
    (hZero : DirichletCharacter.LFunction (1 : DirichletCharacter Complex q) rho = 0) :
    meromorphicOrderAt (nativeWindowReadout (q := q) S E) rho = -1 :=
  (nativeWindowReadout_order_iff_product_zero S E rho hs hs1 hE).mpr
    (CarmichaelDirichletProduct.principal_zero_imp_product_zero S hDiv rho hZero)

end PrimeFactorOscillations.CarmichaelInfiniteWindow
