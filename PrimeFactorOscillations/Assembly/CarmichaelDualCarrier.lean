/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelPrimePacket
import PrimeFactorOscillations.Helpers.CarmichaelAllCarrierReadout

/-!
# The same physical carriers in probability and additive spectra

The native kernel is tested on one actual CRT unit coordinate at a time.
A coordinate is invisible precisely when its prime period divides the
original shortened global exponent. These are exactly the physical
carriers already read from the full signed additive zero lattice.
The original global exponent and all native kernel normalizations remain.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDualCarrier

open CarmichaelPrimePacket CarmichaelCorrelation
open CarmichaelCarrierReadout CarmichaelAllCarrierReadout PrimeOrderReturnIndex

local instance factorNeZero (B : Nat) (p : B.primeFactors) : NeZero p.val :=
  NeZero.mk (Nat.mem_primeFactors.mp p.property).1.ne_zero

def coordinateUnit (B : Nat) [NeZero B] (hSq : Squarefree B)
    (p : B.primeFactors) (v : Units (ZMod p.val)) : Units (ZMod B) := by
  classical
  exact (squarefreeUnitEquiv B hSq).symm
    (Function.update (fun q : B.primeFactors => (1 : Units (ZMod q.val))) p v)

theorem coordinateUnit_apply (B : Nat) [NeZero B] (hSq : Squarefree B)
    (p : B.primeFactors) (v : Units (ZMod p.val)) :
    squarefreeUnitEquiv B hSq (coordinateUnit B hSq p v) p = v := by
  classical
  simp [coordinateUnit]

theorem coordinateUnit_power_iff (B : Nat) [NeZero B] (hSq : Squarefree B)
    (p : B.primeFactors) (v : Units (ZMod p.val)) (k : Nat) :
    coordinateUnit B hSq p v ^ k = 1 <-> v ^ k = 1 := by
  classical
  constructor
  . intro h
    have hc := congrArg (fun z : Units (ZMod B) => squarefreeUnitEquiv B hSq z p) h
    simpa only [map_pow, map_one, Pi.pow_apply, Pi.one_apply, coordinateUnit_apply] using hc
  . intro hv
    apply (squarefreeUnitEquiv B hSq).injective
    rw [map_pow, map_one]
    funext q
    simp only [Pi.pow_apply, Pi.one_apply, coordinateUnit, MulEquiv.apply_symm_apply]
    by_cases hq : q = p
    . subst q
      simpa using hv
    . simp only [Function.update_of_ne hq, one_pow]

theorem kernel_peak_iff_return (B : Nat) [NeZero B] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod B))))
    (u : Units (ZMod B)) :
    kernel (weight B l) u = kernel (weight B l) 1 <->
      u ^ (Monoid.exponent (Units (ZMod B)) / (l : Nat)) = 1 := by
  have hIndex := index_ge_two B l hDiv
  have hIndexReal : (2 : Real) <= (index B l : Real) := by exact_mod_cast hIndex
  have hDen : Not ((index B l : Real) - 1 = 0) := by linarith
  constructor
  . intro hEqual
    by_contra hNot
    rw [kernel_closed B l hDiv u, kernel_closed B l hDiv 1] at hEqual
    simp [CarmichaelCorrelationLocal.returnBit, hNot] at hEqual
    field_simp [hDen] at hEqual
    nlinarith
  . intro hReturn
    rw [kernel_closed B l hDiv u, kernel_closed B l hDiv 1]
    simp [CarmichaelCorrelationLocal.returnBit, hReturn]

theorem coordinate_kernel_flat_iff (B : Nat) [NeZero B] (hSq : Squarefree B)
    (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod B))))
    (p : B.primeFactors) :
    (forall v : Units (ZMod p.val),
      kernel (weight B l) (coordinateUnit B hSq p v) = kernel (weight B l) 1) <->
      Dvd.dvd (p.val - 1) (Monoid.exponent (Units (ZMod B)) / (l : Nat)) := by
  let r : Nat.Primes := Subtype.mk p.val (Nat.mem_primeFactors.mp p.property).1
  have hPeriod : Monoid.exponent (Units (ZMod p.val)) = p.val - 1 :=
    prime_unit_exponent r
  rw [<- hPeriod, Monoid.exponent_dvd_iff_forall_pow_eq_one]
  apply forall_congr'
  intro v
  exact (kernel_peak_iff_return B l hDiv (coordinateUnit B hSq p v)).trans
    (coordinateUnit_power_iff B hSq p v _)

theorem kernel_eq_of_active_coordinates (B : Nat) [NeZero B] (hSq : Squarefree B)
    (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod B))))
    (u v : Units (ZMod B))
    (hAgree : forall p : B.primeFactors,
      Not (Dvd.dvd (p.val - 1) (Monoid.exponent (Units (ZMod B)) / (l : Nat))) ->
        squarefreeUnitEquiv B hSq u p = squarefreeUnitEquiv B hSq v p) :
    kernel (weight B l) u = kernel (weight B l) v := by
  let k := Monoid.exponent (Units (ZMod B)) / (l : Nat)
  let e := squarefreeUnitEquiv B hSq
  have hPower (x y : Units (ZMod B))
      (hA : forall p : B.primeFactors, Not (Dvd.dvd (p.val - 1) k) ->
        e x p = e y p) (hx : x ^ k = 1) : y ^ k = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    funext p
    change (e y p) ^ k = 1
    by_cases hp : Dvd.dvd (p.val - 1) k
    . let r : Nat.Primes := Subtype.mk p.val (Nat.mem_primeFactors.mp p.property).1
      have hExp : Dvd.dvd (Monoid.exponent (Units (ZMod p.val))) k := by
        rw [prime_unit_exponent r]
        exact hp
      exact (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hExp) (e y p)
    . rw [<- hA p hp]
      have hc := congrArg (fun z : Units (ZMod B) => e z p) hx
      simpa only [map_pow, map_one, Pi.pow_apply, Pi.one_apply] using hc
  have hForward := hPower u v hAgree
  have hBack := hPower v u (fun p hp => (hAgree p hp).symm)
  by_cases hu : u ^ k = 1
  . have hv := hForward hu
    rw [kernel_closed B l hDiv u, kernel_closed B l hDiv v]
    simp [CarmichaelCorrelationLocal.returnBit, k, hu, hv]
  . have hv : Not (v ^ k = 1) := fun h => hu (hBack h)
    rw [kernel_closed B l hDiv u, kernel_closed B l hDiv v]
    simp [CarmichaelCorrelationLocal.returnBit, k, hu, hv]

theorem coordinate_support_iff (B : Nat) [NeZero B] (hSq : Squarefree B)
    (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod B))))
    (J : Finset B.primeFactors) :
    (forall u v : Units (ZMod B),
      (forall p : B.primeFactors, Membership.mem J p ->
        squarefreeUnitEquiv B hSq u p = squarefreeUnitEquiv B hSq v p) ->
          kernel (weight B l) u = kernel (weight B l) v) <->
      forall p : B.primeFactors,
        Not (Dvd.dvd (p.val - 1) (Monoid.exponent (Units (ZMod B)) / (l : Nat))) ->
          Membership.mem J p := by
  classical
  constructor
  . intro hFactor p hpActive
    apply Classical.byContradiction
    intro hpNot
    have hNotFlat : Not (forall v : Units (ZMod p.val),
        kernel (weight B l) (coordinateUnit B hSq p v) = kernel (weight B l) 1) :=
      (not_congr (coordinate_kernel_flat_iff B hSq l hDiv p)).mpr hpActive
    choose v hv using not_forall.mp hNotFlat
    apply hv
    apply hFactor (coordinateUnit B hSq p v) 1
    intro q hq
    have hqp : Not (q = p) := by
      intro h
      subst q
      exact hpNot hq
    simp [coordinateUnit, Function.update_of_ne hqp]
  . intro hSupport u v hAgree
    apply kernel_eq_of_active_coordinates B hSq l hDiv u v
    intro p hpActive
    exact hAgree p (hSupport p hpActive)

def kernelCarrierPrimes (B : Nat) [NeZero B] (hSq : Squarefree B)
    (l : Nat.Primes) : Finset Nat := by
  classical
  exact B.primeFactors.filter (fun p =>
    exists hp : Membership.mem B.primeFactors p,
      Not (forall v : Units (ZMod p),
        kernel (weight B l) (coordinateUnit B hSq (Subtype.mk p hp) v) =
          kernel (weight B l) 1))

def kernelCarrierProduct (B : Nat) [NeZero B] (hSq : Squarefree B)
    (l : Nat.Primes) : Nat := (kernelCarrierPrimes B hSq l).prod id

theorem kernelCarrierPrimes_eq (B : Nat) [NeZero B] (hSq : Squarefree B)
    (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod B)))) :
    kernelCarrierPrimes B hSq l =
      carrierPrimes B (Monoid.exponent (Units (ZMod B)) / (l : Nat)) := by
  classical
  ext p
  simp only [kernelCarrierPrimes, carrierPrimes, Finset.mem_filter]
  constructor
  . intro h
    choose hp hNot using h.right
    refine And.intro h.left ?_
    intro hPeriod
    exact hNot ((coordinate_kernel_flat_iff B hSq l hDiv (Subtype.mk p hp)).mpr hPeriod)
  . intro h
    refine And.intro h.left (Exists.intro h.left ?_)
    intro hFlat
    exact h.right
      ((coordinate_kernel_flat_iff B hSq l hDiv (Subtype.mk p h.left)).mp hFlat)

theorem kernelCarrierProduct_eq (B : Nat) [NeZero B] (hSq : Squarefree B)
    (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod B)))) :
    kernelCarrierProduct B hSq l =
      carrierProduct B (Monoid.exponent (Units (ZMod B)) / (l : Nat)) := by
  rw [kernelCarrierProduct, kernelCarrierPrimes_eq B hSq l hDiv]
  rfl

theorem additive_zero_iff_kernelCarrier_dvd (B : Nat) [NeZero B] (hSq : Squarefree B)
    (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod B)))) (h : Nat) :
    ModularReturnFourier.residueFourier B
      (centeredPower B (Monoid.exponent (Units (ZMod B)) / (l : Nat))) h = 0 <->
        Dvd.dvd (kernelCarrierProduct B hSq l) h := by
  rw [kernelCarrierProduct_eq B hSq l hDiv]
  exact all_carriers_intrinsic_readout B hSq _ h

theorem kernelCarrierProduct_pos (B : Nat) [NeZero B] (hSq : Squarefree B)
    (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod B)))) :
    0 < kernelCarrierProduct B hSq l := by
  rw [kernelCarrierProduct_eq B hSq l hDiv]
  exact carrier_product_pos B _

theorem first_positive_zero_kernelCarrier (B : Nat) [NeZero B] (hSq : Squarefree B)
    (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod B)))) :
    And (ModularReturnFourier.residueFourier B
      (centeredPower B (Monoid.exponent (Units (ZMod B)) / (l : Nat)))
        (kernelCarrierProduct B hSq l) = 0)
      (forall h : Nat, 0 < h -> h < kernelCarrierProduct B hSq l ->
        Not (ModularReturnFourier.residueFourier B
          (centeredPower B (Monoid.exponent (Units (ZMod B)) / (l : Nat))) h = 0)) := by
  rw [kernelCarrierProduct_eq B hSq l hDiv]
  exact first_positive_zero_all_carriers B hSq _

abbrev liftFactor (B d : Nat) [NeZero B] (hd : Dvd.dvd d B)
    (q : d.primeFactors) : B.primeFactors :=
  Subtype.mk q.val (Nat.mem_primeFactors.mpr
    (And.intro (Nat.mem_primeFactors.mp q.property).1
      (And.intro (dvd_trans (Nat.mem_primeFactors.mp q.property).2.1 hd) (NeZero.ne B))))

theorem coordinate_reduction_val (B d : Nat) [NeZero B] [NeZero d]
    (hSq : Squarefree B) (hSqd : Squarefree d) (hd : Dvd.dvd d B)
    (u : Units (ZMod B)) (q : d.primeFactors) :
    (squarefreeUnitEquiv d hSqd (ZMod.unitsMap hd u) q : ZMod q.val) =
      Units.val (squarefreeUnitEquiv B hSq u (liftFactor B d hd q)) := by
  calc
    _ = ModularReturnFourier.squarefreeResidueEquiv d hSqd
        (ZMod.unitsMap hd u : ZMod d) q :=
      squarefree_unit_coordinates d hSqd (ZMod.unitsMap hd u) q
    _ = ModularReturnFourier.squarefreeResidueEquiv d hSqd
        (ZMod.castHom hd (ZMod d) (u : ZMod B)) q := rfl
    _ = ModularReturnFourier.squarefreeResidueEquiv d hSqd
        (ZMod.castHom hd (ZMod d) ((u : ZMod B).val : ZMod B)) q :=
      congrArg (fun z : ZMod B => ModularReturnFourier.squarefreeResidueEquiv d hSqd
        (ZMod.castHom hd (ZMod d) z) q) (ZMod.natCast_zmod_val (u : ZMod B)).symm
    _ = ((u : ZMod B).val : ZMod q.val) := by simp only [map_natCast]; rfl
    _ = ModularReturnFourier.squarefreeResidueEquiv B hSq
        ((u : ZMod B).val : ZMod B) (liftFactor B d hd q) := by
      simp only [map_natCast] <;> rfl
    _ = ModularReturnFourier.squarefreeResidueEquiv B hSq
        (u : ZMod B) (liftFactor B d hd q) := by rw [ZMod.natCast_zmod_val]
    _ = _ := (squarefree_unit_coordinates B hSq u (liftFactor B d hd q)).symm

theorem reduction_eq_iff_prime_coordinates (B d : Nat) [NeZero B] [NeZero d]
    (hSq : Squarefree B) (hSqd : Squarefree d) (hd : Dvd.dvd d B)
    (u v : Units (ZMod B)) :
    ZMod.unitsMap hd u = ZMod.unitsMap hd v <->
      forall p : B.primeFactors, Dvd.dvd p.val d ->
        squarefreeUnitEquiv B hSq u p = squarefreeUnitEquiv B hSq v p := by
  constructor
  . intro h p hp
    let q : d.primeFactors := Subtype.mk p.val
      (Nat.mem_primeFactors.mpr (And.intro (Nat.mem_primeFactors.mp p.property).1
        (And.intro hp (NeZero.ne d))))
    apply Units.ext
    have hc := congrArg (fun z : Units (ZMod d) =>
      (squarefreeUnitEquiv d hSqd z q : ZMod q.val)) h
    rw [coordinate_reduction_val B d hSq hSqd hd u q,
      coordinate_reduction_val B d hSq hSqd hd v q] at hc
    change Units.val (squarefreeUnitEquiv B hSq u p) =
      Units.val (squarefreeUnitEquiv B hSq v p) at hc
    exact hc
  . intro h
    apply (squarefreeUnitEquiv d hSqd).injective
    funext q
    apply Units.ext
    rw [coordinate_reduction_val B d hSq hSqd hd u q,
      coordinate_reduction_val B d hSq hSqd hd v q]
    exact congrArg (fun z : Units (ZMod q.val) => (z : ZMod q.val))
      (h (liftFactor B d hd q) (Nat.mem_primeFactors.mp q.property).2.1)

theorem kernel_reduction_iff (B d : Nat) [NeZero B] [NeZero d]
    (hSq : Squarefree B) (hSqd : Squarefree d) (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod B))))
    (hd : Dvd.dvd d B) :
    (forall u v : Units (ZMod B), ZMod.unitsMap hd u = ZMod.unitsMap hd v ->
      kernel (weight B l) u = kernel (weight B l) v) <->
        Dvd.dvd (kernelCarrierProduct B hSq l) d := by
  classical
  let J : Finset B.primeFactors := Finset.univ.filter (fun p => Dvd.dvd p.val d)
  rw [kernelCarrierProduct_eq B hSq l hDiv]
  constructor
  . intro hFactor
    have hCoordinates : forall u v : Units (ZMod B),
        (forall p : B.primeFactors, Membership.mem J p ->
          squarefreeUnitEquiv B hSq u p = squarefreeUnitEquiv B hSq v p) ->
            kernel (weight B l) u = kernel (weight B l) v := by
      intro u v hAgree
      apply hFactor u v
      apply (reduction_eq_iff_prime_coordinates B d hSq hSqd hd u v).mpr
      intro p hp
      exact hAgree p (by simp [J, hp])
    have hAll := (coordinate_support_iff B hSq l hDiv J).mp hCoordinates
    apply (carrier_product_dvd_iff B
      (Monoid.exponent (Units (ZMod B)) / (l : Nat)) d).mpr
    intro p hp
    exact (Finset.mem_filter.mp (hAll p hp)).2
  . intro hProduct
    have hAll := (carrier_product_dvd_iff B
      (Monoid.exponent (Units (ZMod B)) / (l : Nat)) d).mp hProduct
    have hSelected : forall p : B.primeFactors,
        Not (Dvd.dvd (p.val - 1) (Monoid.exponent (Units (ZMod B)) / (l : Nat))) ->
          Membership.mem J p := by
      intro p hp
      simp [J, hAll p hp]
    have hFactor := (coordinate_support_iff B hSq l hDiv J).mpr hSelected
    intro u v hReduce
    apply hFactor u v
    intro p hp
    exact (reduction_eq_iff_prime_coordinates B d hSq hSqd hd u v).mp hReduce p
      (Finset.mem_filter.mp hp).2

theorem kernelCarrierProduct_dvd_level (B : Nat) [NeZero B] (hSq : Squarefree B)
    (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod B)))) :
    Dvd.dvd (kernelCarrierProduct B hSq l) B := by
  rw [kernelCarrierProduct_eq B hSq l hDiv]
  apply (carrier_product_dvd_iff B
    (Monoid.exponent (Units (ZMod B)) / (l : Nat)) B).mpr
  intro p _
  exact (Nat.mem_primeFactors.mp p.property).2.1

theorem kernelCarrierProduct_minimal (B : Nat) [NeZero B] (hSq : Squarefree B)
    (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod B)))) :
    And (forall u v : Units (ZMod B),
      ZMod.unitsMap (kernelCarrierProduct_dvd_level B hSq l hDiv) u =
        ZMod.unitsMap (kernelCarrierProduct_dvd_level B hSq l hDiv) v ->
          kernel (weight B l) u = kernel (weight B l) v)
      (forall {d : Nat} [NeZero d] (hd : Dvd.dvd d B),
        (forall u v : Units (ZMod B), ZMod.unitsMap hd u = ZMod.unitsMap hd v ->
          kernel (weight B l) u = kernel (weight B l) v) ->
            Dvd.dvd (kernelCarrierProduct B hSq l) d) := by
  let R := kernelCarrierProduct B hSq l
  have hPos : 0 < R := kernelCarrierProduct_pos B hSq l hDiv
  let : NeZero R := NeZero.mk (ne_of_gt hPos)
  have hDvd : Dvd.dvd R B := kernelCarrierProduct_dvd_level B hSq l hDiv
  refine And.intro ?_ ?_
  . have hSqR : Squarefree R := fun x hx => hSq x (dvd_trans hx hDvd)
    exact (kernel_reduction_iff B R hSq hSqR l hDiv hDvd).mpr (dvd_refl R)
  . intro d inst hd hFactor
    have hSqd : Squarefree d := fun x hx => hSq x (dvd_trans hx hd)
    exact (kernel_reduction_iff B d hSq hSqd l hDiv hd).mp hFactor

theorem exists_reduced_kernel_iff (B d : Nat) [NeZero B] [NeZero d]
    (hSq : Squarefree B) (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod B))))
    (hd : Dvd.dvd d B) :
    (exists f : Units (ZMod d) -> Real,
      forall u : Units (ZMod B), kernel (weight B l) u = f (ZMod.unitsMap hd u)) <->
        Dvd.dvd (kernelCarrierProduct B hSq l) d := by
  have hSqd : Squarefree d := fun x hx => hSq x (dvd_trans hx hd)
  constructor
  . intro h
    choose f hf using h
    apply (kernel_reduction_iff B d hSq hSqd l hDiv hd).mp
    intro u v hReduce
    rw [hf u, hf v, hReduce]
  . intro hProduct
    have hFiber := (kernel_reduction_iff B d hSq hSqd l hDiv hd).mpr hProduct
    let lift : Units (ZMod d) -> Units (ZMod B) :=
      fun v => Classical.choose (ZMod.unitsMap_surjective hd v)
    have hLift (v : Units (ZMod d)) : ZMod.unitsMap hd (lift v) = v :=
      Classical.choose_spec (ZMod.unitsMap_surjective hd v)
    refine Exists.intro (fun v => kernel (weight B l) (lift v)) ?_
    intro u
    exact hFiber u (lift (ZMod.unitsMap hd u)) (hLift (ZMod.unitsMap hd u)).symm

end PrimeFactorOscillations.CarmichaelDualCarrier
