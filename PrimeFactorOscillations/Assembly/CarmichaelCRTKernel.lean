/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelConductorAssembly

/-!
# Upper carrier compression through the actual prime-power CRT

Every prime-power coordinate, including inactive ones, is retained in
the global return predicate. Actual reduction maps compose before local
kernel descent is applied. This supplies the upper spectral-conductor
consumer for the already proved mixed-character lower construction.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelCRTKernel

open CarmichaelPrimePacket CarmichaelCorrelation CarmichaelCorrelationSpectrum
open CarmichaelDualCarrier CarmichaelConductorAssembly CarmichaelSpectralConductor

abbrev primaryLevel (q : Nat) (p : q.primeFactors) : Nat :=
  p.val ^ q.factorization p.val

local instance primaryNeZero (q : Nat) (p : q.primeFactors) :
    NeZero (primaryLevel q p) :=
  NeZero.mk (pow_ne_zero _ (Nat.mem_primeFactors.mp p.property).1.ne_zero)

def primaryUnitEquiv (q : Nat) [NeZero q] :
    MulEquiv (Units (ZMod q))
      ((p : q.primeFactors) -> Units (ZMod (primaryLevel q p))) :=
  (Units.mapEquiv (ZMod.equivPi q (NeZero.ne q)).toMulEquiv).trans MulEquiv.piUnits

theorem primaryLevel_dvd (q : Nat) (p : q.primeFactors) :
    Dvd.dvd (primaryLevel q p) q := Nat.ordProj_dvd q p.val

theorem coordinate_eq_actual_reduction (q : Nat) [NeZero q]
    (u : Units (ZMod q)) (p : q.primeFactors) :
    primaryUnitEquiv q u p = ZMod.unitsMap (primaryLevel_dvd q p) u := by
  apply Units.ext
  change ZMod.equivPi q (NeZero.ne q) (u : ZMod q) p =
    ZMod.castHom (primaryLevel_dvd q p) (ZMod (primaryLevel q p)) (u : ZMod q)
  calc
    _ = ZMod.equivPi q (NeZero.ne q) ((u : ZMod q).val : ZMod q) p :=
      congrArg (fun z : ZMod q => ZMod.equivPi q (NeZero.ne q) z p)
        (ZMod.natCast_zmod_val (u : ZMod q)).symm
    _ = ((u : ZMod q).val : ZMod (primaryLevel q p)) := by
      simp only [map_natCast]; rfl
    _ = ZMod.castHom (primaryLevel_dvd q p) (ZMod (primaryLevel q p))
        ((u : ZMod q).val : ZMod q) := by rw [map_natCast]
    _ = _ := by rw [ZMod.natCast_zmod_val]

theorem return_iff_all_primary_returns (q : Nat) [NeZero q]
    (u : Units (ZMod q)) (k : Nat) :
    u ^ k = 1 <->
      forall p : q.primeFactors, (ZMod.unitsMap (primaryLevel_dvd q p) u) ^ k = 1 := by
  constructor
  . intro h p
    simpa only [map_pow, map_one] using
      congrArg (ZMod.unitsMap (primaryLevel_dvd q p)) h
  . intro h
    apply (primaryUnitEquiv q).injective
    rw [map_pow, map_one]
    funext p
    change (primaryUnitEquiv q u p) ^ k = 1
    rw [coordinate_eq_actual_reduction]
    exact h p

theorem kernel_eq_iff_return_iff (q : Nat) [NeZero q] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (u v : Units (ZMod q)) :
    kernel (weight q l) u = kernel (weight q l) v <->
      (u ^ (Monoid.exponent (Units (ZMod q)) / (l : Nat)) = 1 <->
        v ^ (Monoid.exponent (Units (ZMod q)) / (l : Nat)) = 1) := by
  constructor
  . intro h
    rw [<- kernel_peak_iff_return q l hDiv u, <- kernel_peak_iff_return q l hDiv v, h]
  . intro h
    by_cases hu : u ^ (Monoid.exponent (Units (ZMod q)) / (l : Nat)) = 1
    . have hv := h.mp hu
      rw [kernel_closed q l hDiv u, kernel_closed q l hDiv v]
      simp [CarmichaelCorrelationLocal.returnBit, hu, hv]
    . have hv : Not (v ^ (Monoid.exponent (Units (ZMod q)) / (l : Nat)) = 1) :=
        fun hv => hu (h.mpr hv)
      rw [kernel_closed q l hDiv u, kernel_closed q l hDiv v]
      simp [CarmichaelCorrelationLocal.returnBit, hu, hv]

theorem reduction_fibers_compose (q M d f : Nat)
    (hM : Dvd.dvd M q) (hd : Dvd.dvd d q)
    (hFd : Dvd.dvd f d) (hFM : Dvd.dvd f M)
    (u v : Units (ZMod q))
    (hReduce : ZMod.unitsMap hM u = ZMod.unitsMap hM v) :
    ZMod.unitsMap hFd (ZMod.unitsMap hd u) =
      ZMod.unitsMap hFd (ZMod.unitsMap hd v) := by
  have h := congrArg (ZMod.unitsMap hFM) hReduce
  change ((ZMod.unitsMap hFM).comp (ZMod.unitsMap hM)) u =
    ((ZMod.unitsMap hFM).comp (ZMod.unitsMap hM)) v at h
  rw [ZMod.unitsMap_comp] at h
  change ((ZMod.unitsMap hFd).comp (ZMod.unitsMap hd)) u =
    ((ZMod.unitsMap hFd).comp (ZMod.unitsMap hd)) v
  rw [ZMod.unitsMap_comp]
  exact h

theorem kernel_reduction_of_active_local_reductions
    (q M : Nat) [NeZero q] [NeZero M] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (hM : Dvd.dvd M q)
    (f : q.primeFactors -> Nat) [forall p, NeZero (f p)]
    (hFd : forall p, Dvd.dvd (f p) (primaryLevel q p))
    (hFM : forall p : q.primeFactors,
      Not (Dvd.dvd (Monoid.exponent (Units (ZMod (primaryLevel q p))))
        (Monoid.exponent (Units (ZMod q)) / (l : Nat))) -> Dvd.dvd (f p) M)
    (hLocal : forall p : q.primeFactors,
      Not (Dvd.dvd (Monoid.exponent (Units (ZMod (primaryLevel q p))))
        (Monoid.exponent (Units (ZMod q)) / (l : Nat))) ->
      forall a b : Units (ZMod (primaryLevel q p)),
        ZMod.unitsMap (hFd p) a = ZMod.unitsMap (hFd p) b ->
          kernel (weight (primaryLevel q p) l) a = kernel (weight (primaryLevel q p) l) b) :
    forall u v : Units (ZMod q), ZMod.unitsMap hM u = ZMod.unitsMap hM v ->
      kernel (weight q l) u = kernel (weight q l) v := by
  intro u v hReduce
  apply (kernel_eq_iff_return_iff q l hDiv u v).mpr
  rw [return_iff_all_primary_returns q u, return_iff_all_primary_returns q v]
  apply forall_congr'
  intro p
  by_cases hInactive : Dvd.dvd (Monoid.exponent (Units (ZMod (primaryLevel q p))))
      (Monoid.exponent (Units (ZMod q)) / (l : Nat))
  . have hAll := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hInactive
    exact Iff.intro (fun _ => hAll _) (fun _ => hAll _)
  . have hEL := MonoidHom.exponent_dvd (f := ZMod.unitsMap (primaryLevel_dvd q p))
      (ZMod.unitsMap_surjective (primaryLevel_dvd q p))
    have hE : 0 < Monoid.exponent (Units (ZMod (primaryLevel q p))) :=
      Nat.pos_of_ne_zero (Monoid.exponent_ne_zero_of_finite
        (G := Units (ZMod (primaryLevel q p))))
    have hData := (active_period_iff _ _ l hE hEL hDiv).mp hInactive
    have hPeriod := (Nat.mul_div_cancel' hEL).symm
    have hCompat (x : Units (ZMod (primaryLevel q p))) :
        x ^ (Monoid.exponent (Units (ZMod q)) / (l : Nat)) = 1 <->
          x ^ (Monoid.exponent (Units (ZMod (primaryLevel q p))) / (l : Nat)) = 1 := by
      rw [hPeriod]
      exact inflated_period_return_iff x _ (l : Nat) _ hData.left
        (Monoid.pow_exponent_eq_one _) hData.right
    have hLocalEq := hLocal p hInactive
      (ZMod.unitsMap (primaryLevel_dvd q p) u) (ZMod.unitsMap (primaryLevel_dvd q p) v)
      (reduction_fibers_compose q M (primaryLevel q p) (f p)
        hM (primaryLevel_dvd q p) (hFd p) (hFM p hInactive) u v hReduce)
    have hNative := (kernel_eq_iff_return_iff (primaryLevel q p) l hData.left _ _).mp hLocalEq
    exact (hCompat _).trans (hNative.trans (hCompat _).symm)

theorem spectralConductor_dvd_of_active_local_reductions
    (q M : Nat) [NeZero q] [NeZero M] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (hM : Dvd.dvd M q)
    (f : q.primeFactors -> Nat) [forall p, NeZero (f p)]
    (hFd : forall p, Dvd.dvd (f p) (primaryLevel q p))
    (hFM : forall p : q.primeFactors,
      Not (Dvd.dvd (Monoid.exponent (Units (ZMod (primaryLevel q p))))
        (Monoid.exponent (Units (ZMod q)) / (l : Nat))) -> Dvd.dvd (f p) M)
    (hLocal : forall p : q.primeFactors,
      Not (Dvd.dvd (Monoid.exponent (Units (ZMod (primaryLevel q p))))
        (Monoid.exponent (Units (ZMod q)) / (l : Nat))) ->
      forall a b : Units (ZMod (primaryLevel q p)),
        ZMod.unitsMap (hFd p) a = ZMod.unitsMap (hFd p) b ->
          kernel (weight (primaryLevel q p) l) a = kernel (weight (primaryLevel q p) l) b) :
    Dvd.dvd (spectralConductor q l) M :=
  (kernel_reduction_iff_spectralConductor_dvd q M l hDiv hM).mp
    (kernel_reduction_of_active_local_reductions q M l hDiv hM f hFd hFM hLocal)

end PrimeFactorOscillations.CarmichaelCRTKernel
