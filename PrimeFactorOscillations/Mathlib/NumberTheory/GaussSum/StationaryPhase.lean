/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.GaussSum.FiniteRingEnergy

/-!
# Stationary phase for inflated prime-power weights

Averaging translations by a square-zero direction projects a complete
quadratic sum onto its stationary residue classes. Prime-power annihilator
identities discharge the projection hypotheses for ZMod at every exponent
at least two. Inflated multiplicative characters then have an exact shared
cusp energy, including the vanishing case for zero linear residue.

No incomplete-sum or global mean-square estimate is assumed.
-/

set_option autoImplicit false
set_option Elab.async false

namespace AddChar

variable {R S : Type*} [CommRing R] [Fintype R] [CommRing S]

/-- Translation by a square-zero direction removes every nonstationary residue. -/
theorem sum_quadraticPhase_stationary [DecidableEq R]
    (psi : AddChar R Complex) (hpsi : psi.IsPrimitive)
    (rho : RingHom R S) (e : R) (he : e ^ 2 = 0) (hrhoe : rho e = 0)
    (weight : S -> Complex) (h t : R) :
    Finset.sum Finset.univ (fun r : R => weight (rho r) * psi (h * r ^ 2 + t * r)) =
      Finset.sum Finset.univ (fun r : R =>
        if e * (2 * h * r + t) = 0 then weight (rho r) * psi (h * r ^ 2 + t * r) else 0) := by
  classical
  let f (r : R) := weight (rho r) * psi (h * r ^ 2 + t * r)
  have hshift (y : R) :
      Finset.sum Finset.univ f =
      Finset.sum Finset.univ (fun r : R => f r * psi (y * (e * (2 * h * r + t)))) := by
    have hphase (r : R) : h * (r + e * y) ^ 2 + t * (r + e * y) =
        (h * r ^ 2 + t * r) + y * (e * (2 * h * r + t)) := by
      calc
        _ = (h * r ^ 2 + t * r) + y * (e * (2 * h * r + t)) + h * e ^ 2 * y ^ 2 := by ring
        _ = _ := by rw [he]; ring
    apply (Fintype.sum_equiv (Equiv.addRight (e * y)) _ _ ?_).symm
    intro r
    change (weight (rho r) * psi (h * r ^ 2 + t * r)) *
      psi (y * (e * (2 * h * r + t))) =
        weight (rho (r + e * y)) * psi (h * (r + e * y) ^ 2 + t * (r + e * y))
    rw [hphase, rho.map_add r (e * y), rho.map_mul e y, hrhoe,
      zero_mul, add_zero,
      psi.map_add_eq_mul (h * r ^ 2 + t * r) (y * (e * (2 * h * r + t)))]
    ring
  have hc : (Fintype.card R : Complex) * Finset.sum Finset.univ f =
      (Fintype.card R : Complex) * Finset.sum Finset.univ (fun r : R =>
        if e * (2 * h * r + t) = 0 then f r else 0) := by
    calc
      _ = Finset.sum Finset.univ (fun y : R => Finset.sum Finset.univ f) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ = Finset.sum Finset.univ (fun y : R =>
          Finset.sum Finset.univ (fun r : R => f r * psi (y * (e * (2 * h * r + t))))) := by
        apply Finset.sum_congr rfl
        intro y _
        exact hshift y
      _ = _ := by
        rw [Finset.sum_comm]
        simp_rw [<- Finset.mul_sum, AddChar.sum_mulShift _ hpsi]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        simp [mul_comm]
  have hcard : Not ((Fintype.card R : Complex) = 0) := by exact_mod_cast Fintype.card_ne_zero
  exact (isUnit_iff_ne_zero.mpr hcard).mul_left_cancel hc

/-- An inflated residue weight evaluates at the unique stationary residue class. -/
theorem sum_quadraticPhase_residueEvaluation
    (psi : AddChar R Complex) (hpsi : psi.IsPrimitive)
    (rho : RingHom R S) (e : R) (he : e ^ 2 = 0) (hrhoe : rho e = 0)
    (hann : forall x : R, e * x = 0 <-> rho x = 0)
    (weight : S -> Complex) (h t r0 : R) (hu : IsUnit (2 * h))
    (hr0 : 2 * h * r0 + t = 0) :
    Finset.sum Finset.univ (fun r : R => weight (rho r) * psi (h * r ^ 2 + t * r)) =
      weight (rho r0) * Finset.sum Finset.univ (fun r : R => psi (h * r ^ 2 + t * r)) := by
  classical
  have hclass (r : R) : e * (2 * h * r + t) = 0 <-> rho r = rho r0 := by
    have hd : 2 * h * r + t = (2 * h) * (r - r0) := by
      calc
        _ = (2 * h) * (r - r0) + (2 * h * r0 + t) := by ring
        _ = _ := by rw [hr0, add_zero]
    rw [hann, hd, rho.map_mul, rho.map_sub,
      (hu.map rho).mul_right_eq_zero, sub_eq_zero]
  have hplain : Finset.sum Finset.univ (fun r : R => psi (h * r ^ 2 + t * r)) =
      Finset.sum Finset.univ (fun r : R =>
        if e * (2 * h * r + t) = 0 then psi (h * r ^ 2 + t * r) else 0) := by
    simpa only [one_mul] using sum_quadraticPhase_stationary psi hpsi rho e he hrhoe
      (fun _ : S => (1 : Complex)) h t
  rw [sum_quadraticPhase_stationary psi hpsi rho e he hrhoe weight h t,
    hplain, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : e * (2 * h * r + t) = 0
  case pos => simp [hr, hclass r |>.mp hr]
  case neg => simp [hr]

end AddChar

namespace ZMod

/-- Reduction from a prime-power modulus of exponent at least two. -/
noncomputable def primePowerResidue (p a : Nat) :
    RingHom (ZMod (p ^ (a + 2))) (ZMod p) :=
  ZMod.castHom (dvd_pow_self p (by omega : Not (a + 2 = 0))) (ZMod p)

/-- The last residue digit is square-zero. -/
theorem primePower_lastDigit_sq (p a : Nat) :
    (((p ^ (a + 1) : Nat) : ZMod (p ^ (a + 2)))) ^ 2 = 0 := by
  rw [<- Nat.cast_pow, <- pow_mul, ZMod.natCast_eq_zero_iff]
  exact Nat.pow_dvd_pow p (by omega)

/-- The last residue digit is invisible after reduction modulo p. -/
theorem primePowerResidue_lastDigit (p a : Nat) :
    primePowerResidue p a ((p ^ (a + 1) : Nat) : ZMod (p ^ (a + 2))) = 0 := by
  rw [map_natCast, ZMod.natCast_eq_zero_iff]
  exact dvd_pow_self p (by omega)

/-- Multiplication by the last digit has exactly the residue-map kernel. -/
theorem primePower_lastDigit_annihilator (p a : Nat) [Fact (Nat.Prime p)]
    (x : ZMod (p ^ (a + 2))) :
    ((p ^ (a + 1) : Nat) : ZMod (p ^ (a + 2))) * x = 0 <->
      primePowerResidue p a x = 0 := by
  have hp : Nat.Prime p := Fact.out
  have hmap : primePowerResidue p a x = (x.val : ZMod p) := by
    calc
      _ = primePowerResidue p a (x.val : ZMod (p ^ (a + 2))) :=
        congrArg (primePowerResidue p a) (ZMod.natCast_zmod_val x).symm
      _ = _ := map_natCast _ _
  have hcast : ((p ^ (a + 1) : Nat) : ZMod (p ^ (a + 2))) * x =
      ((p ^ (a + 1) * x.val : Nat) : ZMod (p ^ (a + 2))) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [hcast, hmap, ZMod.natCast_eq_zero_iff, ZMod.natCast_eq_zero_iff]
  change Dvd.dvd (p ^ (a + 1) * p) (p ^ (a + 1) * x.val) <-> Dvd.dvd p x.val
  exact Nat.mul_dvd_mul_iff_left (pow_pos hp.pos _)

/-- Inflated weights at every odd prime-power level evaluate at the stationary residue. -/
theorem sum_quadraticPhase_primePower_residueValue (p a : Nat) [Fact (Nat.Prime p)]
    (hodd : Odd p) (psi : AddChar (ZMod (p ^ (a + 2))) Complex)
    (hpsi : psi.IsPrimitive) (weight : ZMod p -> Complex)
    (h : Units (ZMod (p ^ (a + 2)))) (t : ZMod (p ^ (a + 2))) :
    Finset.sum Finset.univ (fun r : ZMod (p ^ (a + 2)) =>
      weight (primePowerResidue p a r) * psi ((h : ZMod (p ^ (a + 2))) * r ^ 2 + t * r)) =
      weight (-primePowerResidue p a t / (2 * primePowerResidue p a h)) *
        Finset.sum Finset.univ (fun r : ZMod (p ^ (a + 2)) =>
          psi ((h : ZMod (p ^ (a + 2))) * r ^ 2 + t * r)) := by
  classical
  let rho := primePowerResidue p a
  have h2 : IsUnit (2 : ZMod (p ^ (a + 2))) :=
    (ZMod.isUnit_iff_coprime 2 _).mpr ((Nat.coprime_two_left.mpr hodd).pow_right (a + 2))
  let u : Units (ZMod (p ^ (a + 2))) := h2.unit * h
  let r0 : ZMod (p ^ (a + 2)) := -(Units.val (Inv.inv u) * t)
  have hu : (u : ZMod (p ^ (a + 2))) = 2 * (h : ZMod (p ^ (a + 2))) := by
    simp only [u, Units.val_mul, IsUnit.unit_spec]
  have hr0 : 2 * (h : ZMod (p ^ (a + 2))) * r0 + t = 0 := by
    rw [<- hu]
    simp [r0, <- mul_assoc]
  have hc : IsUnit (2 * rho h) := by
    simpa only [map_mul, map_ofNat] using (h2.mul h.isUnit).map rho
  have hrF : (2 * rho h) * rho r0 + rho t = 0 := by
    have hr := congrArg rho hr0
    simpa only [map_add, map_mul, map_ofNat, map_zero] using hr
  have hroot : rho r0 = -rho t / (2 * rho h) := by
    apply (eq_div_iff hc.ne_zero).mpr
    rw [mul_comm]
    exact eq_neg_of_add_eq_zero_left hrF
  have hv := AddChar.sum_quadraticPhase_residueEvaluation psi hpsi rho
    ((p ^ (a + 1) : Nat) : ZMod (p ^ (a + 2)))
    (primePower_lastDigit_sq p a) (primePowerResidue_lastDigit p a)
    (primePower_lastDigit_annihilator p a) weight (h : ZMod (p ^ (a + 2))) t r0
    (h2.mul h.isUnit) hr0
  rw [hroot] at hv
  exact hv

/-- Exact inner-row energy, including vanishing when the linear coefficient reduces to zero. -/
theorem normSq_quadraticPhase_primePower_inflated (p a : Nat) [Fact (Nat.Prime p)]
    (hodd : Odd p) (chi : MulChar (ZMod p) Complex)
    (psi : AddChar (ZMod (p ^ (a + 2))) Complex) (hpsi : psi.IsPrimitive)
    (h : Units (ZMod (p ^ (a + 2)))) (t : ZMod (p ^ (a + 2))) :
    Complex.normSq (Finset.sum Finset.univ (fun r : ZMod (p ^ (a + 2)) =>
      chi (primePowerResidue p a r) * psi ((h : ZMod (p ^ (a + 2))) * r ^ 2 + t * r))) =
      if primePowerResidue p a t = 0 then 0 else (p ^ (a + 2) : Real) := by
  classical
  have h2 : IsUnit (2 : ZMod (p ^ (a + 2))) :=
    (ZMod.isUnit_iff_coprime 2 _).mpr ((Nat.coprime_two_left.mpr hodd).pow_right (a + 2))
  rw [sum_quadraticPhase_primePower_residueValue p a hodd psi hpsi chi h t]
  by_cases ht : primePowerResidue p a t = 0
  case pos => simp [ht, MulChar.map_zero]
  case neg =>
    have hc : IsUnit (2 * primePowerResidue p a h) := by
      simpa only [map_mul, map_ofNat] using (h2.mul h.isUnit).map (primePowerResidue p a)
    have harg : Not (-primePowerResidue p a t / (2 * primePowerResidue p a h) = 0) :=
      div_ne_zero (neg_ne_zero.mpr ht) hc.ne_zero
    have hw : Complex.normSq (chi (-primePowerResidue p a t / (2 * primePowerResidue p a h))) = 1 :=
      MulChar.normSq_apply_unit chi (Units.mk0 _ harg)
    rw [ite_eq_right ht, map_mul, hw,
      AddChar.normSq_quadraticPhase_unit psi hpsi h2 h t, one_mul, ZMod.card, Nat.cast_pow]

/-- Exact complete energy for the shared-prime packet with both inflated character factors. -/
theorem sum_normSq_primePower_inflatedCusp (p a : Nat) [Fact (Nat.Prime p)]
    (hodd : Odd p) (chi : MulChar (ZMod p) Complex)
    (psi : AddChar (ZMod (p ^ (a + 2))) Complex) (hpsi : psi.IsPrimitive)
    (t : ZMod (p ^ (a + 2))) :
    Finset.sum Finset.univ (fun nu : ZMod (p ^ (a + 2)) =>
      Complex.normSq (Finset.sum Finset.univ (fun h : Units (ZMod (p ^ (a + 2))) =>
        Finset.sum Finset.univ (fun r : ZMod (p ^ (a + 2)) =>
          chi (primePowerResidue p a r) * (Inv.inv chi) (primePowerResidue p a h) *
            psi ((h : ZMod (p ^ (a + 2))) * r ^ 2 + t * r +
              nu * ((Inv.inv h : Units (ZMod (p ^ (a + 2)))) : ZMod (p ^ (a + 2)))))))) =
      if primePowerResidue p a t = 0 then 0 else
        (p ^ (a + 2) : Real) ^ 2 * (Fintype.card (Units (ZMod (p ^ (a + 2)))) : Real) := by
  classical
  let rho := primePowerResidue p a
  let q (h : Units (ZMod (p ^ (a + 2)))) :=
    Finset.sum Finset.univ (fun r : ZMod (p ^ (a + 2)) =>
      chi (rho r) * psi ((h : ZMod (p ^ (a + 2))) * r ^ 2 + t * r))
  have hrow (h : Units (ZMod (p ^ (a + 2)))) (nu : ZMod (p ^ (a + 2))) :
      Finset.sum Finset.univ (fun r : ZMod (p ^ (a + 2)) =>
        chi (rho r) * (Inv.inv chi) (rho h) *
          psi ((h : ZMod (p ^ (a + 2))) * r ^ 2 + t * r +
            nu * ((Inv.inv h : Units (ZMod (p ^ (a + 2)))) : ZMod (p ^ (a + 2))))) =
      ((Inv.inv chi) (rho h) * q h) *
        psi (nu * ((Inv.inv h : Units (ZMod (p ^ (a + 2)))) : ZMod (p ^ (a + 2)))) := by
    dsimp only [q]
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r _
    rw [AddChar.map_add_eq_mul]
    ring
  have hinj : Function.Injective (fun h : Units (ZMod (p ^ (a + 2))) =>
      ((Inv.inv h : Units (ZMod (p ^ (a + 2)))) : ZMod (p ^ (a + 2)))) := by
    intro x y hxy
    exact inv_injective (Units.ext hxy)
  have hw (h : Units (ZMod (p ^ (a + 2)))) :
      Complex.normSq ((Inv.inv chi) (rho h)) = 1 := by
    simpa only [IsUnit.unit_spec] using
      MulChar.normSq_apply_unit (Inv.inv chi) (h.isUnit.map rho).unit
  change Finset.sum Finset.univ (fun nu : ZMod (p ^ (a + 2)) =>
      Complex.normSq (Finset.sum Finset.univ (fun h : Units (ZMod (p ^ (a + 2))) =>
        Finset.sum Finset.univ (fun r : ZMod (p ^ (a + 2)) =>
          chi (rho r) * (Inv.inv chi) (rho h) *
            psi ((h : ZMod (p ^ (a + 2))) * r ^ 2 + t * r +
              nu * ((Inv.inv h : Units (ZMod (p ^ (a + 2)))) : ZMod (p ^ (a + 2)))))))) = _
  simp_rw [hrow]
  rw [AddChar.sum_normSq_fourier_injective psi hpsi _ hinj]
  simp_rw [map_mul, hw, one_mul, q, rho,
    normSq_quadraticPhase_primePower_inflated p a hodd chi psi hpsi]
  by_cases ht : primePowerResidue p a t = 0
  case pos => simp [ht]
  case neg =>
    simp only [ht, ite_false, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ZMod.card, Nat.cast_pow]
    ring

/-- The normalized shared-prime average is zero off unit linear coefficients and 1 - 1/p on them. -/
theorem mean_normSq_primePower_inflatedCusp (p a : Nat) [Fact (Nat.Prime p)]
    (hodd : Odd p) (chi : MulChar (ZMod p) Complex)
    (psi : AddChar (ZMod (p ^ (a + 2))) Complex) (hpsi : psi.IsPrimitive)
    (t : ZMod (p ^ (a + 2))) :
    (Finset.sum Finset.univ (fun nu : ZMod (p ^ (a + 2)) =>
      Complex.normSq ((Finset.sum Finset.univ (fun h : Units (ZMod (p ^ (a + 2))) =>
        Finset.sum Finset.univ (fun r : ZMod (p ^ (a + 2)) =>
          chi (primePowerResidue p a r) * (Inv.inv chi) (primePowerResidue p a h) *
            psi ((h : ZMod (p ^ (a + 2))) * r ^ 2 + t * r +
              nu * ((Inv.inv h : Units (ZMod (p ^ (a + 2)))) : ZMod (p ^ (a + 2))))))) /
                (p ^ (a + 2) : Complex)))) / (p ^ (a + 2) : Real) =
      if primePowerResidue p a t = 0 then 0 else 1 - 1 / (p : Real) := by
  classical
  have hp : Nat.Prime p := Fact.out
  have hp0 : Not ((p : Real) = 0) := by exact_mod_cast hp.ne_zero
  simp only [Complex.normSq_div, map_pow, Complex.normSq_natCast]
  rw [<- Finset.sum_div, sum_normSq_primePower_inflatedCusp p a hodd chi psi hpsi]
  by_cases ht : primePowerResidue p a t = 0
  case pos => simp [ht]
  case neg =>
    simp only [ht, ite_false]
    rw [ZMod.card_units_eq_totient]
    have htot : (p ^ (a + 2)).totient = p ^ (a + 1) * (p - 1) :=
      Nat.totient_prime_pow_succ hp (a + 1)
    rw [htot]
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hp.one_le, Nat.cast_one]
    have hpow : (p : Real) ^ (a + 2) = (p : Real) ^ (a + 1) * p := by rw [<- pow_succ]
    rw [hpow]
    field_simp [hp0]
    ring

end ZMod
