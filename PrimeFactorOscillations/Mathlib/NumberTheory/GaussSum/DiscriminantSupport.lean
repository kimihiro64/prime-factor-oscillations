/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.GaussSum.StationaryPhase

/-!
# Deep discriminant support for quadratic cusp packets

Principal units in odd finite residue-local rings have square roots.
Quadratic Gauss factors therefore depend only on unit residue classes.
Exact Fourier translation identities then force the joint cusp packet onto
the annihilator of the residue kernel. The prime-power specialization retains
both inner and outer weights and includes the zero-discriminant case.

No bound on the surviving exceptional values or incomplete sums is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

namespace RingHom

variable {R S : Type*} [CommRing R] [Fintype R] [CommRing S]

/-- In a finite residue-local ring of odd residue characteristic, principal units are squares. -/
theorem exists_sq_eq_of_residue_one (rho : RingHom R S)
    (hunit : forall x : R, Not (rho x = 0) -> IsUnit x)
    (h2 : Not ((2 : S) = 0)) (u : R) (hu : rho u = 1) :
    exists v : R, And (rho v = 1) (v ^ 2 = u) := by
  classical
  let P := {x : R // rho x = 1}
  let square : P -> P := fun x =>
    Subtype.mk (x.val ^ 2) (by simp only [map_pow, x.property, one_pow])
  have hinj : Function.Injective square := by
    intro x y hxy
    have hs : x.val ^ 2 = y.val ^ 2 := congrArg Subtype.val hxy
    have hadd : IsUnit (x.val + y.val) := by
      apply hunit
      simpa only [map_add, x.property, y.property, one_add_one_eq_two] using h2
    have hprod : (x.val - y.val) * (x.val + y.val) = 0 := by
      calc
        _ = x.val ^ 2 - y.val ^ 2 := by ring
        _ = 0 := sub_eq_zero.mpr hs
    apply Subtype.ext
    exact sub_eq_zero.mp (hadd.mul_left_eq_zero.mp hprod)
  have hsurj : Function.Surjective square := Finite.surjective_of_injective hinj
  let target : P := Subtype.mk u hu
  let v := Classical.choose (hsurj target)
  have hv := Classical.choose_spec (hsurj target)
  exact Exists.intro v.val (And.intro v.property (congrArg Subtype.val hv))

end RingHom

namespace ZMod

/-- A residue modulo a prime power is a unit exactly when its reduction modulo p is nonzero. -/
theorem primePower_isUnit_iff_residue_ne_zero (p a : Nat) [Fact (Nat.Prime p)]
    (x : ZMod (p ^ (a + 2))) :
    IsUnit x <-> Not (primePowerResidue p a x = 0) := by
  have hp : Nat.Prime p := Fact.out
  constructor
  . intro hx
    exact (hx.map (primePowerResidue p a)).ne_zero
  . intro hx
    have hmap : primePowerResidue p a x = (x.val : ZMod p) := by
      calc
        _ = primePowerResidue p a (x.val : ZMod (p ^ (a + 2))) :=
          congrArg (primePowerResidue p a) (ZMod.natCast_zmod_val x).symm
        _ = _ := map_natCast _ _
    have hn : Not (Dvd.dvd p x.val) := by
      simpa only [hmap, ZMod.natCast_eq_zero_iff] using hx
    have hc : Nat.Coprime x.val p := (hp.coprime_iff_not_dvd.mpr hn).symm
    have hu := (ZMod.isUnit_iff_coprime x.val (p ^ (a + 2))).mpr (hc.pow_right (a + 2))
    simpa only [ZMod.natCast_zmod_val] using hu

/-- Every principal unit at an odd prime-power modulus has a principal square root. -/
theorem primePower_exists_principal_sq (p a : Nat) [Fact (Nat.Prime p)]
    (hodd : Odd p) (u : ZMod (p ^ (a + 2))) (hu : primePowerResidue p a u = 1) :
    exists v : ZMod (p ^ (a + 2)),
      And (primePowerResidue p a v = 1) (v ^ 2 = u) := by
  have h2R : IsUnit (2 : ZMod (p ^ (a + 2))) :=
    (ZMod.isUnit_iff_coprime 2 _).mpr ((Nat.coprime_two_left.mpr hodd).pow_right (a + 2))
  have h2 : Not ((2 : ZMod p) = 0) := by
    simpa only [map_ofNat] using (h2R.map (primePowerResidue p a)).ne_zero
  exact RingHom.exists_sq_eq_of_residue_one (primePowerResidue p a)
    (fun x hx => (primePower_isUnit_iff_residue_ne_zero p a x).mpr hx) h2 u hu

end ZMod

namespace AddChar

variable {R S : Type*} [CommRing R] [Fintype R] [Field S]

/-- Quadratic Gauss sums are constant on unit residue classes over an odd finite local ring. -/
theorem sum_quadraticPhase_eq_of_residue_eq
    (rho : RingHom R S) (hunit : forall x : R, Not (rho x = 0) -> IsUnit x)
    (h2 : Not ((2 : S) = 0)) (psi : AddChar R Complex)
    (a b : Units R) (hab : rho a = rho b) :
    Finset.sum Finset.univ (fun r : R => psi ((a : R) * r ^ 2)) =
      Finset.sum Finset.univ (fun r : R => psi ((b : R) * r ^ 2)) := by
  classical
  have hratio : rho ((a : R) * (Units.val (Inv.inv b))) = 1 := by
    rw [map_mul, hab, <- map_mul]
    simp
  have hex := RingHom.exists_sq_eq_of_residue_one rho hunit h2
    ((a : R) * (Units.val (Inv.inv b))) hratio
  let v := Classical.choose hex
  have hv := Classical.choose_spec hex
  have huv : IsUnit v := hunit v (by rw [hv.1]; exact one_ne_zero)
  let w : Units R := huv.unit
  have hw : (w : R) = v := IsUnit.unit_spec huv
  have ha : (a : R) = (b : R) * (w : R) ^ 2 := by
    rw [hw, hv.2]
    simp [mul_left_comm]
  calc
    _ = Finset.sum Finset.univ (fun r : R => psi ((b : R) * ((w : R) * r) ^ 2)) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [ha]
      congr 1
      ring
    _ = _ := Fintype.sum_bijective _ w.mulLeft_bijective _ _ (fun _ => rfl)

/-- An inflated Fourier coefficient vanishes outside the annihilator of the residue kernel. -/
theorem sum_inflatedPhase_eq_zero
    (psi : AddChar R Complex) (hpsi : psi.IsPrimitive)
    (rho : RingHom R S) (weight : S -> Complex) (d A : R)
    (hd : rho d = 0) (hA : Not (A * d = 0)) :
    Finset.sum Finset.univ (fun x : R => weight (rho x) * psi (A * x)) = 0 := by
  classical
  let T := Finset.sum Finset.univ (fun x : R => weight (rho x) * psi (A * x))
  have hshift (y : R) : T = T * psi (y * (A * d)) := by
    calc
      _ = Finset.sum Finset.univ (fun x : R =>
          weight (rho (x + d * y)) * psi (A * (x + d * y))) := by
        exact (Fintype.sum_equiv (Equiv.addRight (d * y)) _ _ (fun _ => rfl)).symm
      _ = _ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        rw [rho.map_add, rho.map_mul, hd, zero_mul, add_zero,
          mul_add, AddChar.map_add_eq_mul]
        have hphase : A * (d * y) = y * (A * d) := by ring
        rw [hphase, mul_assoc]
  have hc : (Fintype.card R : Complex) * T = 0 := by
    calc
      _ = Finset.sum Finset.univ (fun _ : R => T) := by simp [Finset.sum_const, nsmul_eq_mul]
      _ = Finset.sum Finset.univ (fun y : R => T * psi (y * (A * d))) := by
        apply Finset.sum_congr rfl
        intro y _
        exact hshift y
      _ = _ := by rw [<- Finset.mul_sum, sum_mulShift _ hpsi]; simp [hA]
  have hcard : Not ((Fintype.card R : Complex) = 0) := by exact_mod_cast Fintype.card_ne_zero
  exact (mul_eq_zero.mp hc).resolve_left hcard

/-- Unit-supported residue-invariant Fourier sums retain their full annihilator support. -/
theorem sum_unitResiduePhase_eq_zero [Fintype (Units R)]
    (psi : AddChar R Complex) (hpsi : psi.IsPrimitive)
    (rho : RingHom R S) (hunit : forall x : R, Not (rho x = 0) -> IsUnit x)
    (coeff : Units R -> Complex)
    (hcoeff : forall x y : Units R, rho x = rho y -> coeff x = coeff y)
    (d A : R) (hd : rho d = 0) (hA : Not (A * d = 0)) :
    Finset.sum Finset.univ (fun x : Units R => coeff x * psi (A * (x : R))) = 0 := by
  classical
  have hshiftUnit (y : R) (x : Units R) : IsUnit ((x : R) + d * y) := by
    apply hunit
    simpa only [map_add, map_mul, hd, zero_mul, add_zero] using (x.isUnit.map rho).ne_zero
  let shift (y : R) (x : Units R) := (hshiftUnit y x).unit
  have hval (y : R) (x : Units R) : (shift y x : R) = (x : R) + d * y :=
    IsUnit.unit_spec (hshiftUnit y x)
  have hbij (y : R) : Function.Bijective (shift y) := by
    constructor
    . intro x z hxz
      have hv := congrArg Units.val hxz
      simp only [hval] at hv
      exact Units.ext (add_right_cancel hv)
    . intro x
      apply Exists.intro (shift (-y) x)
      apply Units.ext
      simp only [hval]
      ring
  let T := Finset.sum Finset.univ (fun x : Units R => coeff x * psi (A * (x : R)))
  have hshift (y : R) : T = T * psi (y * (A * d)) := by
    calc
      _ = Finset.sum Finset.univ (fun x : Units R =>
          coeff (shift y x) * psi (A * (shift y x : R))) :=
        (Fintype.sum_bijective (shift y) (hbij y) _ _ (fun _ => rfl)).symm
      _ = _ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        have hc : coeff (shift y x) = coeff x := by
          apply hcoeff
          rw [hval, rho.map_add, rho.map_mul, hd, zero_mul, add_zero]
        rw [hc, hval, mul_add, AddChar.map_add_eq_mul]
        have hp : A * (d * y) = y * (A * d) := by ring
        rw [hp, mul_assoc]
  have hc : (Fintype.card R : Complex) * T = 0 := by
    calc
      _ = Finset.sum Finset.univ (fun _ : R => T) := by simp [Finset.sum_const, nsmul_eq_mul]
      _ = Finset.sum Finset.univ (fun y : R => T * psi (y * (A * d))) := by
        apply Finset.sum_congr rfl
        intro y _
        exact hshift y
      _ = _ := by rw [<- Finset.mul_sum, sum_mulShift _ hpsi]; simp [hA]
  have hcard : Not ((Fintype.card R : Complex) = 0) := by exact_mod_cast Fintype.card_ne_zero
  exact (mul_eq_zero.mp hc).resolve_left hcard

/-- Complete the quadratic phase over a ring with an explicit inverse of two. -/
theorem sum_quadraticCusp_completeSquare
    (psi : AddChar R Complex) (b : R) (hb : 2 * b = 1)
    (h : Units R) (t nu : R) :
    Finset.sum Finset.univ (fun r : R =>
      psi ((h : R) * r ^ 2 + t * r + nu * Units.val (Inv.inv h))) =
      (Finset.sum Finset.univ (fun r : R => psi ((h : R) * r ^ 2))) *
        psi ((nu - (b * t) ^ 2) * Units.val (Inv.inv h)) := by
  classical
  let r0 : R := -(Units.val (Inv.inv h) * (b * t))
  have hr : (h : R) * r0 = -(b * t) := by simp [r0, <- mul_assoc]
  have hr0 : 2 * (h : R) * r0 + t = 0 := by
    calc
      _ = 2 * ((h : R) * r0) + t := by ring
      _ = -(2 * b) * t + t := by rw [hr]; ring
      _ = 0 := by rw [hb]; ring
  have hconst : ((h : R) * r0) ^ 2 * Units.val (Inv.inv h) = (h : R) * r0 ^ 2 := by
    calc
      _ = (h : R) * r0 ^ 2 * ((h : R) * Units.val (Inv.inv h)) := by ring
      _ = _ := by simp
  have hphase (r : R) : (h : R) * (r + r0) ^ 2 + t * (r + r0) +
      nu * Units.val (Inv.inv h) =
      (h : R) * r ^ 2 + (nu - (b * t) ^ 2) * Units.val (Inv.inv h) := by
    calc
      _ = (h : R) * r ^ 2 + (r + r0) * (2 * (h : R) * r0 + t) -
          (h : R) * r0 ^ 2 + nu * Units.val (Inv.inv h) := by ring
      _ = (h : R) * r ^ 2 + (nu - ((h : R) * r0) ^ 2) * Units.val (Inv.inv h) := by
        rw [hr0, mul_zero, add_zero, sub_mul, hconst]
        ring
      _ = _ := by rw [hr]; ring
  calc
    _ = Finset.sum Finset.univ (fun r : R =>
        psi ((h : R) * (r + r0) ^ 2 + t * (r + r0) + nu * Units.val (Inv.inv h))) :=
      (Fintype.sum_equiv (Equiv.addRight r0) _ _ (fun _ => rfl)).symm
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      rw [hphase, AddChar.map_add_eq_mul]

/-- The full quadratic cusp packet has discriminant support in the residue-kernel annihilator. -/
theorem sum_quadraticCusp_eq_zero_of_discriminant
    [Fintype (Units R)] (psi : AddChar R Complex) (hpsi : psi.IsPrimitive)
    (rho : RingHom R S) (hunit : forall x : R, Not (rho x = 0) -> IsUnit x)
    (h2 : Not ((2 : S) = 0)) (weight : S -> Complex)
    (b : R) (hb : 2 * b = 1) (t nu d : R)
    (hd : rho d = 0) (hA : Not ((nu - (b * t) ^ 2) * d = 0)) :
    Finset.sum Finset.univ (fun h : Units R =>
      Finset.sum Finset.univ (fun r : R => weight (rho h) *
        psi ((h : R) * r ^ 2 + t * r + nu * Units.val (Inv.inv h)))) = 0 := by
  classical
  let G (h : Units R) := Finset.sum Finset.univ (fun r : R => psi ((h : R) * r ^ 2))
  let coeff (h : Units R) := weight (rho (Inv.inv h : Units R)) * G (Inv.inv h)
  have hperiod : forall x y : Units R, rho x = rho y -> coeff x = coeff y := by
    intro x y hxy
    have hinv : rho (Inv.inv x : Units R) = rho (Inv.inv y : Units R) := by
      apply (x.isUnit.map rho).mul_right_cancel
      calc
        rho (Inv.inv x : Units R) * rho x = (1 : S) := by rw [<- rho.map_mul]; simp
        _ = rho (Inv.inv y : Units R) * rho x := by rw [hxy, <- rho.map_mul]; simp
    dsimp only [coeff, G]
    rw [hinv, sum_quadraticPhase_eq_of_residue_eq rho hunit h2 psi _ _ hinv]
  have hzero := sum_unitResiduePhase_eq_zero psi hpsi rho hunit coeff hperiod
    d (nu - (b * t) ^ 2) hd hA
  calc
    _ = Finset.sum Finset.univ (fun h : Units R =>
        weight (rho h) * G h * psi ((nu - (b * t) ^ 2) * Units.val (Inv.inv h))) := by
      apply Finset.sum_congr rfl
      intro h _
      rw [<- Finset.mul_sum, sum_quadraticCusp_completeSquare psi b hb]
      simp only [G, mul_assoc]
    _ = Finset.sum Finset.univ (fun h : Units R =>
        coeff h * psi ((nu - (b * t) ^ 2) * (h : R))) := by
      apply (Fintype.sum_bijective (fun h : Units R => Inv.inv h)
        inv_involutive.bijective _ _ ?_).symm
      intro h
      simp only [coeff, inv_inv]
    _ = 0 := hzero

end AddChar

namespace ZMod

/-- The annihilator condition is exactly divisibility by the penultimate prime power. -/
theorem primePower_mul_prime_eq_zero_iff (p a : Nat) [Fact (Nat.Prime p)]
    (x : ZMod (p ^ (a + 2))) :
    x * (p : ZMod (p ^ (a + 2))) = 0 <-> Dvd.dvd (p ^ (a + 1)) x.val := by
  have hp : Nat.Prime p := Fact.out
  have hcast : x * (p : ZMod (p ^ (a + 2))) = ((x.val * p : Nat) : ZMod (p ^ (a + 2))) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [hcast, ZMod.natCast_eq_zero_iff]
  change Dvd.dvd (p ^ (a + 1) * p) (x.val * p) <-> Dvd.dvd (p ^ (a + 1)) x.val
  exact Nat.mul_dvd_mul_iff_right hp.pos

/-- Cusp packets with any residue weight vanish away from deep discriminant congruences. -/
theorem quadraticCusp_eq_zero_of_primePower_discriminant (p a : Nat) [Fact (Nat.Prime p)]
    (hodd : Odd p) (psi : AddChar (ZMod (p ^ (a + 2))) Complex) (hpsi : psi.IsPrimitive)
    (weight : ZMod p -> Complex) (t nu : ZMod (p ^ (a + 2)))
    (hdisc : Not (Dvd.dvd (p ^ (a + 1)) (4 * nu - t ^ 2).val)) :
    Finset.sum Finset.univ (fun h : Units (ZMod (p ^ (a + 2))) =>
      Finset.sum Finset.univ (fun r : ZMod (p ^ (a + 2)) =>
        weight (primePowerResidue p a h) *
          psi ((h : ZMod (p ^ (a + 2))) * r ^ 2 + t * r + nu * Units.val (Inv.inv h)))) = 0 := by
  classical
  let rho := primePowerResidue p a
  have h2R : IsUnit (2 : ZMod (p ^ (a + 2))) :=
    (ZMod.isUnit_iff_coprime 2 _).mpr ((Nat.coprime_two_left.mpr hodd).pow_right (a + 2))
  let b : ZMod (p ^ (a + 2)) := Units.val (Inv.inv h2R.unit)
  have hb : 2 * b = 1 := by
    have hh : (h2R.unit : ZMod (p ^ (a + 2))) * Units.val (Inv.inv h2R.unit) = 1 := by simp
    simpa only [IsUnit.unit_spec] using hh
  have h2 : Not ((2 : ZMod p) = 0) := by
    simpa only [map_ofNat] using (h2R.map rho).ne_zero
  have hd : rho (p : ZMod (p ^ (a + 2))) = 0 := by simp only [map_natCast, ZMod.natCast_self]
  have hA : Not ((nu - (b * t) ^ 2) * (p : ZMod (p ^ (a + 2))) = 0) := by
    intro hAz
    apply hdisc
    apply (primePower_mul_prime_eq_zero_iff p a _).mp
    have hb4 : 4 * b ^ 2 = 1 := by
      calc
        _ = (2 * b) ^ 2 := by ring
        _ = 1 := by rw [hb]; ring
    have heq : 4 * (nu - (b * t) ^ 2) = 4 * nu - t ^ 2 := by
      calc
        _ = 4 * nu - (4 * b ^ 2) * t ^ 2 := by ring
        _ = _ := by rw [hb4]; ring
    rw [<- heq, mul_assoc, hAz, mul_zero]
  exact AddChar.sum_quadraticCusp_eq_zero_of_discriminant psi hpsi rho
    (fun x hx => (primePower_isUnit_iff_residue_ne_zero p a x).mpr hx)
    h2 weight b hb t nu (p : ZMod (p ^ (a + 2))) hd hA

/-- The full two-weight joint packet has the same deep discriminant support. -/
theorem jointCusp_eq_zero_of_primePower_discriminant (p a : Nat) [Fact (Nat.Prime p)]
    (hodd : Odd p) (psi : AddChar (ZMod (p ^ (a + 2))) Complex) (hpsi : psi.IsPrimitive)
    (inner outer : ZMod p -> Complex) (t nu : ZMod (p ^ (a + 2)))
    (hdisc : Not (Dvd.dvd (p ^ (a + 1)) (4 * nu - t ^ 2).val)) :
    Finset.sum Finset.univ (fun h : Units (ZMod (p ^ (a + 2))) =>
      Finset.sum Finset.univ (fun r : ZMod (p ^ (a + 2)) =>
        inner (primePowerResidue p a r) * outer (primePowerResidue p a h) *
          psi ((h : ZMod (p ^ (a + 2))) * r ^ 2 + t * r + nu * Units.val (Inv.inv h)))) = 0 := by
  classical
  let rho := primePowerResidue p a
  let weight (s : ZMod p) := inner (-rho t / (2 * s)) * outer s
  have hrow (h : Units (ZMod (p ^ (a + 2)))) :
      Finset.sum Finset.univ (fun r : ZMod (p ^ (a + 2)) =>
        inner (rho r) * outer (rho h) *
          psi ((h : ZMod (p ^ (a + 2))) * r ^ 2 + t * r + nu * Units.val (Inv.inv h))) =
      Finset.sum Finset.univ (fun r : ZMod (p ^ (a + 2)) =>
        weight (rho h) *
          psi ((h : ZMod (p ^ (a + 2))) * r ^ 2 + t * r + nu * Units.val (Inv.inv h))) := by
    have heval := sum_quadraticPhase_primePower_residueValue p a hodd psi hpsi inner h t
    have hc := congrArg (fun z : Complex => outer (rho h) * z * psi (nu * Units.val (Inv.inv h))) heval
    simpa only [rho, weight, Finset.mul_sum, Finset.sum_mul, AddChar.map_add_eq_mul,
      mul_assoc, mul_left_comm, mul_comm] using hc
  dsimp only [rho] at hrow
  simp_rw [hrow]
  exact quadraticCusp_eq_zero_of_primePower_discriminant p a hodd psi hpsi weight t nu hdisc

end ZMod
