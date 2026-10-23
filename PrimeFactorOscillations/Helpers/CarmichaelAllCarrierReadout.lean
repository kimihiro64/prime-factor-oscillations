/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.CarmichaelCarrierReadout
import PrimeFactorOscillations.Helpers.PrimeReturnFourier
import PrimeFactorOscillations.Helpers.RationalFourierOrbit

/-!
# Every physical carrier in the intrinsic power-return spectrum

The primary object is the difference of the complete return tensor and
the complete unit-mask tensor, with their actual global count factors.
Coprime frequency transport changes one coordinate without deleting
either centering product.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelAllCarrierReadout

open scoped BigOperators
open PrimeCarrierFourier PrimeReturnFourier ModularReturnFourier
open CarmichaelCarrierReadout PrimeOrderReturnIndex RationalFourierOrbit

local instance factorPrime (B : Nat) (p : B.primeFactors) :
    Fact (Nat.Prime (p.val : Nat)) :=
  Fact.mk (Nat.mem_primeFactors.mp p.property).1

theorem indicator_product {I : Type*} [Fintype I] (P : I -> Prop)
    [DecidablePred P] :
    Finset.univ.prod (fun i => if P i then (1 : Rat) else 0) =
      if forall i, P i then 1 else 0 := by
  classical
  by_cases hall : forall i, P i
  { rw [if_pos hall]
    apply Finset.prod_eq_one
    intro i _
    rw [if_pos (hall i)] }
  { rw [if_neg hall]
    choose i hi using not_forall.mp hall
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi) }

theorem unit_coefficient_eq_tensor (B : Nat) [NeZero B] (hSq : Squarefree B) :
    unitCoefficient B =
      residueTensor B hSq (fun p => unitWeight (p.val : Nat)) := by
  classical
  funext x
  have hc := isUnit_iff_nonzero_coordinates B hSq x
  have hw (p : B.primeFactors) :
      unitWeight (p.val : Nat) (squarefreeResidueEquiv B hSq x p) =
        if Not (squarefreeResidueEquiv B hSq x p = 0) then (1 : Rat) else 0 := by
    by_cases hz : squarefreeResidueEquiv B hSq x p = 0 <;> simp [unitWeight, hz]
  unfold unitCoefficient residueTensor
  simp_rw [hw]
  rw [indicator_product]
  simp only [hc]

theorem power_return_coordinates (B : Nat) [NeZero B] (hSq : Squarefree B)
    (k : Nat) (x : ZMod B) :
    (IsUnit x /\ x ^ k = 1) <->
      forall p : B.primeFactors,
        Not (squarefreeResidueEquiv B hSq x p = 0) /\
          (squarefreeResidueEquiv B hSq x p) ^ k = 1 := by
  let e := squarefreeResidueEquiv B hSq
  constructor
  { intro h p
    refine And.intro ((isUnit_iff_nonzero_coordinates B hSq x).mp h.1 p) ?_
    have he := congrArg (fun z : ZMod B => e z p) h.2
    simpa only [map_pow, map_one, Pi.pow_apply, Pi.one_apply] using he }
  { intro h
    refine And.intro ((isUnit_iff_nonzero_coordinates B hSq x).mpr (fun p => (h p).1)) ?_
    apply e.injective
    rw [map_pow, map_one]
    funext p
    exact (h p).2 }

theorem power_coefficient_eq_tensor (B : Nat) [NeZero B] (hSq : Squarefree B)
    (k : Nat) :
    powerCoefficient B k =
      residueTensor B hSq (fun p => returnWeight (p.val : Nat) k) := by
  classical
  funext x
  have hc := power_return_coordinates B hSq k x
  have hp : powerCoefficient B k x =
      if IsUnit x /\ x ^ k = 1 then (1 : Rat) else 0 := by
    by_cases hu : IsUnit x <;> by_cases hr : x ^ k = 1 <;>
      simp [powerCoefficient, hu, hr]
  have hw (p : B.primeFactors) :
      returnWeight (p.val : Nat) k (squarefreeResidueEquiv B hSq x p) =
        if Not (squarefreeResidueEquiv B hSq x p = 0) /\
            (squarefreeResidueEquiv B hSq x p) ^ k = 1 then (1 : Rat) else 0 := by
    by_cases hz : squarefreeResidueEquiv B hSq x p = 0 <;>
      by_cases hr : (squarefreeResidueEquiv B hSq x p) ^ k = 1 <;>
        simp [returnWeight, hz, hr]
  rw [hp]
  simp only [hc]
  unfold residueTensor
  simp_rw [hw]
  exact (indicator_product _).symm

def localFactor (B : Nat) [NeZero B] (hSq : Squarefree B) (h : Nat)
    (p : B.primeFactors) (f : ZMod (p.val : Nat) -> Rat) : Complex :=
  primeFourier (p.val : Nat)
    (localCharacter (fun p : B.primeFactors => (p.val : Nat)) (crtCharacter B hSq) h p) f

def powerFactor (B : Nat) [NeZero B] (hSq : Squarefree B)
    (k h : Nat) (p : B.primeFactors) : Complex :=
  localFactor B hSq h p (returnWeight (p.val : Nat) k)

def unitFactor (B : Nat) [NeZero B] (hSq : Squarefree B)
    (h : Nat) (p : B.primeFactors) : Complex :=
  localFactor B hSq h p (unitWeight (p.val : Nat))

theorem fourier_sub (B : Nat) [NeZero B] (f g : ZMod B -> Rat) (h : Nat) :
    residueFourier B (fun x => f x - g x) h =
      residueFourier B f h - residueFourier B g h := by
  simp only [residueFourier, Rat.cast_sub, sub_mul, Finset.sum_sub_distrib]

theorem complete_signed_factorization (B : Nat) [NeZero B] (hSq : Squarefree B)
    (k h : Nat) :
    residueFourier B (centeredPower B k) h =
      (unitCount B : Complex) * Finset.univ.prod (powerFactor B hSq k h) -
        (powerCount B k : Complex) * Finset.univ.prod (unitFactor B hSq h) := by
  change residueFourier B (fun x =>
    unitCount B * powerCoefficient B k x - powerCount B k * unitCoefficient B x) h = _
  rw [fourier_sub, fourier_const_mul, fourier_const_mul,
    power_coefficient_eq_tensor B hSq k, unit_coefficient_eq_tensor B hSq,
    residue_fourier_eq_tensor, residue_fourier_eq_tensor,
    tensor_fourier_factorization, tensor_fourier_factorization]
  rfl

theorem local_factor_nonzero (B : Nat) [NeZero B] (hSq : Squarefree B)
    (h : Nat) (p : B.primeFactors) (f : ZMod (p.val : Nat) -> Rat)
    (hmean : Not (Finset.univ.sum f = 0))
    (hnc : Not (forall x y, f x = f y)) :
    Not (localFactor B hSq h p f = 0) := by
  intro hz
  have hc := (local_fourier_zero_iff (fun p : B.primeFactors => (p.val : Nat))
    (crtCharacter B hSq) (crt_character_injective B hSq) p f h).mp hz
  rcases hc with hm | hn
  { exact hmean hm.2 }
  { exact hnc hn.2 }

theorem power_factor_nonzero (B : Nat) [NeZero B] (hSq : Squarefree B)
    (k h : Nat) (p : B.primeFactors) :
    Not (powerFactor B hSq k h p = 0) :=
  local_factor_nonzero B hSq h p _ (ne_of_gt (return_mass_pos (p.val : Nat) k))
    (return_weight_nonconstant (p.val : Nat) k)

theorem unit_factor_nonzero (B : Nat) [NeZero B] (hSq : Squarefree B)
    (h : Nat) (p : B.primeFactors) :
    Not (unitFactor B hSq h p = 0) :=
  local_factor_nonzero B hSq h p _ (ne_of_gt (unit_mass_pos (p.val : Nat)))
    (unit_weight_nonconstant (p.val : Nat))

theorem local_character_frequency_mul (B : Nat) [NeZero B] (hSq : Squarefree B)
    (h t : Nat) (p : B.primeFactors) (x : ZMod (p.val : Nat)) :
    localCharacter (fun p : B.primeFactors => (p.val : Nat)) (crtCharacter B hSq) (t * h) p x =
      localCharacter (fun p : B.primeFactors => (p.val : Nat)) (crtCharacter B hSq) h p
        ((t : ZMod (p.val : Nat)) * x) := by
  have hm : ((t * h : Nat) : ZMod (p.val : Nat)) * x =
      (h : ZMod (p.val : Nat)) * ((t : ZMod (p.val : Nat)) * x) := by
    rw [Nat.cast_mul]
    ring
  change (crtCharacter B hSq) (Pi.single p (((t * h : Nat) : ZMod (p.val : Nat)) * x)) =
    (crtCharacter B hSq) (Pi.single p ((h : ZMod (p.val : Nat)) *
      ((t : ZMod (p.val : Nat)) * x)))
  rw [hm]

theorem squarefree_unit_coordinates (B : Nat) [NeZero B] (hSq : Squarefree B)
    (u : Units (ZMod B)) (p : B.primeFactors) :
    ((squarefreeUnitEquiv B hSq u p) : ZMod (p.val : Nat)) =
      squarefreeResidueEquiv B hSq (u : ZMod B) p := by
  rfl

theorem exists_coprime_coordinate_dilation (B : Nat) [NeZero B] (hSq : Squarefree B)
    (q : B.primeFactors) (v : Units (ZMod (q.val : Nat))) :
    exists t : Nat, And (Nat.Coprime t B)
      (And ((t : ZMod (q.val : Nat)) = (v : ZMod (q.val : Nat)))
        (forall p : B.primeFactors, Not (p = q) -> (t : ZMod (p.val : Nat)) = 1)) := by
  classical
  let us : (p : B.primeFactors) -> Units (ZMod (p.val : Nat)) :=
    Function.update (fun p : B.primeFactors => (1 : Units (ZMod (p.val : Nat)))) q v
  let u := (squarefreeUnitEquiv B hSq).symm us
  let t := (u : ZMod B).val
  let e := squarefreeResidueEquiv B hSq
  have hcoord (p : B.primeFactors) : (t : ZMod (p.val : Nat)) = (us p : ZMod (p.val : Nat)) := by
    calc
      _ = e (t : ZMod B) p := by rw [map_natCast]; rfl
      _ = e (u : ZMod B) p := by
        change e (((u : ZMod B).val : ZMod B)) p = _
        rw [ZMod.natCast_zmod_val]
      _ = ((squarefreeUnitEquiv B hSq u p) : ZMod (p.val : Nat)) :=
        (squarefree_unit_coordinates B hSq u p).symm
      _ = _ := by
        have he := (squarefreeUnitEquiv B hSq).apply_symm_apply us
        exact congrArg (fun z => ((z p) : ZMod (p.val : Nat))) he
  refine Exists.intro t (And.intro (ZMod.val_coe_unit_coprime u) (And.intro ?_ ?_))
  { simpa [us] using hcoord q }
  { intro p hp
    simpa only [us, Function.update_of_ne hp, Units.val_one] using hcoord p }

theorem power_factor_dilation_eq (B : Nat) [NeZero B] (hSq : Squarefree B)
    (k h t : Nat) (p : B.primeFactors) (ht : (t : ZMod (p.val : Nat)) = 1) :
    powerFactor B hSq k (t * h) p = powerFactor B hSq k h p := by
  unfold powerFactor localFactor primeFourier
  simp_rw [local_character_frequency_mul, ht, one_mul]

theorem unit_factor_dilation_eq (B : Nat) [NeZero B] (hSq : Squarefree B)
    (h t : Nat) (p : B.primeFactors) (v : Units (ZMod (p.val : Nat)))
    (ht : (t : ZMod (p.val : Nat)) = (v : ZMod (p.val : Nat))) :
    unitFactor B hSq (t * h) p = unitFactor B hSq h p := by
  unfold unitFactor localFactor primeFourier
  simp_rw [local_character_frequency_mul, ht]
  exact unit_shift_eq (p.val : Nat)
    (localCharacter (fun p : B.primeFactors => (p.val : Nat)) (crtCharacter B hSq) h p) v

theorem power_factor_dilation_ne (B : Nat) [NeZero B] (hSq : Squarefree B)
    (k h t : Nat) (p : B.primeFactors) (hndiv : Not (Dvd.dvd (p.val : Nat) h))
    (v : Units (ZMod (p.val : Nat))) (hv : Not ((v : ZMod (p.val : Nat)) ^ k = 1))
    (ht : (t : ZMod (p.val : Nat)) = (v : ZMod (p.val : Nat))) :
    Not (powerFactor B hSq k (t * h) p = powerFactor B hSq k h p) := by
  unfold powerFactor localFactor primeFourier
  simp_rw [local_character_frequency_mul, ht]
  exact return_shift_ne (p.val : Nat) k
    (localCharacter (fun p : B.primeFactors => (p.val : Nat)) (crtCharacter B hSq) h p)
    (local_character_injective _ _ (crt_character_injective B hSq) h p hndiv) v hv

theorem zero_forces_each_carrier_dvd (B : Nat) [NeZero B] (hSq : Squarefree B)
    (k h : Nat) (hz : residueFourier B (centeredPower B k) h = 0)
    (q : B.primeFactors) (hq : Not (Dvd.dvd ((q.val : Nat) - 1) k)) :
    Dvd.dvd (q.val : Nat) h := by
  classical
  by_contra hndiv
  choose x hx using period_failure_witness (q.val : Nat) k hq
  let v : Units (ZMod (q.val : Nat)) := Units.mk0 x hx.1
  have hv : Not ((v : ZMod (q.val : Nat)) ^ k = 1) := hx.2
  choose t ht using exists_coprime_coordinate_dilation B hSq q v
  have hz1 := zero_of_coprime_frequency_dilation B (centeredPower B k) h t ht.1 hz
  have hU : Not ((unitCount B : Complex) = 0) := by
    exact_mod_cast ne_of_gt (unit_count_pos B)
  have hUnits : Finset.univ.prod (unitFactor B hSq (t * h)) =
      Finset.univ.prod (unitFactor B hSq h) := by
    apply Finset.prod_congr rfl
    intro p _
    by_cases hp : p = q
    { subst p
      exact unit_factor_dilation_eq B hSq h t q v ht.2.1 }
    { exact unit_factor_dilation_eq B hSq h t p 1 (ht.2.2 p hp) }
  let C : Complex := (Finset.univ.erase q).prod (powerFactor B hSq k h)
  have hC : Not (C = 0) :=
    Finset.prod_ne_zero_iff.mpr (fun p _ => power_factor_nonzero B hSq k h p)
  have hfac0 : Finset.univ.prod (powerFactor B hSq k h) =
      powerFactor B hSq k h q * C :=
    (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q)).symm
  have hfac1 : Finset.univ.prod (powerFactor B hSq k (t * h)) =
      powerFactor B hSq k (t * h) q * C := by
    calc
      _ = powerFactor B hSq k (t * h) q *
          (Finset.univ.erase q).prod (powerFactor B hSq k (t * h)) :=
        (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q)).symm
      _ = _ := by
        congr 1
        apply Finset.prod_congr rfl
        intro p hp
        exact power_factor_dilation_eq B hSq k h t p (ht.2.2 p (Finset.mem_erase.mp hp).1)
  have he0 := hz
  rw [complete_signed_factorization B hSq k h, hfac0] at he0
  rw [complete_signed_factorization B hSq k (t * h), hfac1, hUnits] at hz1
  have heq : (unitCount B : Complex) * (powerFactor B hSq k (t * h) q * C) =
      (unitCount B : Complex) * (powerFactor B hSq k h q * C) :=
    (sub_eq_zero.mp hz1).trans (sub_eq_zero.mp he0).symm
  have heq1 := (mul_eq_mul_left_iff.mp heq).resolve_right hU
  have heq2 := (mul_eq_mul_right_iff.mp heq1).resolve_right hC
  exact power_factor_dilation_ne B hSq k h t q hndiv v hv ht.2.1 heq2

theorem local_factor_at_divisible (B : Nat) [NeZero B] (hSq : Squarefree B)
    (h : Nat) (p : B.primeFactors) (hd : Dvd.dvd (p.val : Nat) h)
    (f : ZMod (p.val : Nat) -> Rat) :
    localFactor B hSq h p f = localFactor B hSq 0 p f := by
  unfold localFactor primeFourier
  simp_rw [local_character_trivial _ (crtCharacter B hSq) h p hd,
    local_character_trivial _ (crtCharacter B hSq) 0 p (dvd_zero _)]

theorem local_cross_balance (B : Nat) [NeZero B] (hSq : Squarefree B)
    (k h : Nat)
    (hall : forall p : B.primeFactors,
      Not (Dvd.dvd ((p.val : Nat) - 1) k) -> Dvd.dvd (p.val : Nat) h)
    (p : B.primeFactors) :
    powerFactor B hSq k h p * unitFactor B hSq 0 p =
      unitFactor B hSq h p * powerFactor B hSq k 0 p := by
  by_cases hd : Dvd.dvd (p.val : Nat) h
  { have hA := local_factor_at_divisible B hSq h p hd (returnWeight (p.val : Nat) k)
    have hB := local_factor_at_divisible B hSq h p hd (unitWeight (p.val : Nat))
    change localFactor B hSq h p (returnWeight (p.val : Nat) k) *
      localFactor B hSq 0 p (unitWeight (p.val : Nat)) =
      localFactor B hSq h p (unitWeight (p.val : Nat)) *
        localFactor B hSq 0 p (returnWeight (p.val : Nat) k)
    rw [hA, hB, mul_comm] }
  { have hper : Dvd.dvd ((p.val : Nat) - 1) k := by
      by_contra hp
      exact hd (hall p hp)
    have hr := return_weight_eq_unit_of_period_dvd (p.val : Nat) k hper
    simp only [powerFactor, unitFactor, hr] }

theorem centered_power_zero_frequency (B : Nat) [NeZero B] (k : Nat) :
    residueFourier B (centeredPower B k) 0 = 0 := by
  rw [fourier_zero_frequency]
  have hs : Finset.univ.sum (centeredPower B k) = 0 := by
    unfold centeredPower
    rw [Finset.sum_sub_distrib, <- Finset.mul_sum, <- Finset.mul_sum]
    change unitCount B * powerCount B k - powerCount B k * unitCount B = 0
    exact sub_eq_zero.mpr (mul_comm _ _)
  rw [hs, Rat.cast_zero]

theorem all_carriers_dvd_forces_zero (B : Nat) [NeZero B] (hSq : Squarefree B)
    (k h : Nat)
    (hall : forall p : B.primeFactors,
      Not (Dvd.dvd ((p.val : Nat) - 1) k) -> Dvd.dvd (p.val : Nat) h) :
    residueFourier B (centeredPower B k) h = 0 := by
  have hcross :
      Finset.univ.prod (powerFactor B hSq k h) * Finset.univ.prod (unitFactor B hSq 0) =
        Finset.univ.prod (unitFactor B hSq h) * Finset.univ.prod (powerFactor B hSq k 0) := by
    rw [<- Finset.prod_mul_distrib, <- Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p _
    exact local_cross_balance B hSq k h hall p
  have hV : Not (Finset.univ.prod (unitFactor B hSq 0) = 0) :=
    Finset.prod_ne_zero_iff.mpr (fun p _ => unit_factor_nonzero B hSq 0 p)
  have hz0 := centered_power_zero_frequency B k
  rw [complete_signed_factorization B hSq k 0] at hz0
  have hmain : residueFourier B (centeredPower B k) h *
      Finset.univ.prod (unitFactor B hSq 0) = 0 := by
    rw [complete_signed_factorization B hSq k h]
    calc
      _ = (unitCount B : Complex) *
          (Finset.univ.prod (powerFactor B hSq k h) * Finset.univ.prod (unitFactor B hSq 0)) -
          (powerCount B k : Complex) *
            (Finset.univ.prod (unitFactor B hSq h) * Finset.univ.prod (unitFactor B hSq 0)) := by ring
      _ = _ := by rw [hcross]
      _ = Finset.univ.prod (unitFactor B hSq h) *
          ((unitCount B : Complex) * Finset.univ.prod (powerFactor B hSq k 0) -
            (powerCount B k : Complex) * Finset.univ.prod (unitFactor B hSq 0)) := by ring
      _ = 0 := by rw [hz0, mul_zero]
  exact (mul_eq_zero.mp hmain).resolve_right hV

theorem intrinsic_zero_iff_all_carriers_dvd (B : Nat) [NeZero B] (hSq : Squarefree B)
    (k h : Nat) :
    residueFourier B (centeredPower B k) h = 0 <->
      forall p : B.primeFactors,
        Not (Dvd.dvd ((p.val : Nat) - 1) k) -> Dvd.dvd (p.val : Nat) h :=
  Iff.intro (fun hz p hp => zero_forces_each_carrier_dvd B hSq k h hz p hp)
    (all_carriers_dvd_forces_zero B hSq k h)

def carrierPrimes (B k : Nat) : Finset Nat :=
  B.primeFactors.filter (fun p => Not (Dvd.dvd (p - 1) k))

def carrierProduct (B k : Nat) : Nat := (carrierPrimes B k).prod id

theorem distinct_prime_product_dvd (s : Finset Nat)
    (hprime : forall p, Membership.mem s p -> Nat.Prime p) (n : Nat)
    (hdiv : forall p, Membership.mem s p -> Dvd.dvd p n) :
    Dvd.dvd (s.prod id) n := by
  classical
  revert hprime hdiv
  induction s using Finset.induction_on with
  | empty =>
      intro _ _
      simp only [Finset.prod_empty, one_dvd]
  | @insert p s hps ih =>
      intro hp hd
      have hpp : Nat.Prime p := hp p (Finset.mem_insert_self p s)
      have hsp : forall q, Membership.mem s q -> Nat.Prime q :=
        fun q hq => hp q (Finset.mem_insert_of_mem hq)
      have hc : Nat.Coprime p (s.prod id) := Nat.Coprime.prod_right (by
        intro q hq
        apply (Nat.coprime_primes hpp (hsp q hq)).mpr
        intro he
        subst q
        exact hps hq)
      rw [Finset.prod_insert hps]
      exact hc.mul_dvd_of_dvd_of_dvd (hd p (Finset.mem_insert_self p s))
        (ih hsp (fun q hq => hd q (Finset.mem_insert_of_mem hq)))

theorem carrier_product_dvd_iff (B k h : Nat) :
    Dvd.dvd (carrierProduct B k) h <->
      forall p : B.primeFactors,
        Not (Dvd.dvd ((p.val : Nat) - 1) k) -> Dvd.dvd (p.val : Nat) h := by
  constructor
  { intro hd p hp
    have hm : Membership.mem (carrierPrimes B k) (p.val : Nat) :=
      Finset.mem_filter.mpr (And.intro p.property hp)
    exact dvd_trans (Finset.dvd_prod_of_mem id hm) hd }
  { intro hall
    exact distinct_prime_product_dvd (carrierPrimes B k)
      (fun p hp => (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1) h
      (fun p hp => hall (Subtype.mk p (Finset.mem_filter.mp hp).1) (Finset.mem_filter.mp hp).2) }

theorem all_carriers_intrinsic_readout (B : Nat) [NeZero B] (hSq : Squarefree B)
    (k h : Nat) :
    residueFourier B (centeredPower B k) h = 0 <-> Dvd.dvd (carrierProduct B k) h :=
  (intrinsic_zero_iff_all_carriers_dvd B hSq k h).trans (carrier_product_dvd_iff B k h).symm

theorem carrier_product_pos (B k : Nat) : 0 < carrierProduct B k := by
  unfold carrierProduct
  apply Finset.prod_pos
  intro p hp
  exact (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1.pos

theorem first_positive_zero_all_carriers (B : Nat) [NeZero B] (hSq : Squarefree B)
    (k : Nat) :
    And (residueFourier B (centeredPower B k) (carrierProduct B k) = 0)
      (forall h : Nat, 0 < h -> h < carrierProduct B k ->
        Not (residueFourier B (centeredPower B k) h = 0)) := by
  constructor
  { exact (all_carriers_intrinsic_readout B hSq k _).mpr (dvd_refl _) }
  { intro h hh hlt hz
    have hd := (all_carriers_intrinsic_readout B hSq k h).mp hz
    exact (Nat.not_le.mpr hlt) (Nat.le_of_dvd hh hd) }

end PrimeFactorOscillations.CarmichaelAllCarrierReadout
