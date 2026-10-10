/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Mathlib.NumberTheory.GaussSum.SquareClasses

/-!
# The original shared cusp packet at odd prime powers

The full two-variable packet, including both multiplicative character weights
and the reciprocal phase, equals its joint Fourier transform. Stationary
projection and completing the square retain the zero mask exactly, even when
the stationary residue is zero. The inverse-unit change of variables retains
the same quadratic Gauss factor.

These identities apply to ZMod at odd prime-power depth at least two.
They assume neither a bound on the transformed sum nor a Gaussian quotient
identification. Such identifications and incomplete-sum estimates are separate.
-/

set_option autoImplicit false
set_option Elab.async false

namespace AddChar

variable {R : Type*} [CommRing R] [Fintype R]

/-- Inverting a unit coefficient does not change a complete quadratic sum. -/
theorem sum_quadraticPhase_inv_unit (psi : AddChar R Complex) (h : Units R) :
    Finset.sum Finset.univ (fun r : R => psi ((Inv.inv h : Units R) * r ^ 2)) =
      Finset.sum Finset.univ (fun r : R => psi ((h : R) * r ^ 2)) := by
  have hh : h * (Inv.inv h) ^ 2 = Inv.inv h := by simp [pow_two, <- mul_assoc]
  simpa only [hh] using sum_quadraticPhase_mul_unit_sq psi h (Inv.inv h)

end AddChar

namespace MulChar

variable {F : Type*} [Field F]

/-- The two stationary character weights combine without removing their zero mask. -/
theorem quartic_stationaryWeight (chi : MulChar F Complex) (hfour : chi ^ 4 = 1)
    (b s t : F) (hb : 2 * b = 1) :
    chi (-t / (2 * s)) * (Inv.inv chi) s = chi (-(b * t)) * (chi ^ 2) s := by
  by_cases hs : s = 0
  . simp [hs]
  have h2 : Not ((2 : F) = 0) := by
    intro h
    have he := hb
    rw [h, zero_mul] at he
    exact zero_ne_one he
  have hb' : b = 1 / (2 : F) := by
    apply (eq_div_iff h2).mpr
    simpa only [mul_comm] using hb
  have harg : -t / (2 * s) = -(b * t) * Inv.inv s := by
    rw [hb']
    field_simp [h2, hs]
  have hinv : Inv.inv (chi ^ 2) = chi ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    calc
      chi ^ 2 * chi ^ 2 = chi ^ (2 + 2) := (pow_add chi 2 2).symm
      _ = 1 := hfour
  have hchar : (Inv.inv chi) ^ 2 = chi ^ 2 := by rw [inv_pow, hinv]
  rw [harg, map_mul, <- MulChar.inv_apply']
  calc
    _ = chi (-(b * t)) * ((Inv.inv chi) ^ 2) s := by
      rw [MulChar.pow_apply' (Inv.inv chi) (by decide : Not ((2 : Nat) = 0))]
      ring
    _ = _ := by rw [hchar]

end MulChar

namespace ZMod

/-- The original shared prime-power cusp packet equals its joint Fourier transform. -/
theorem quartic_primePower_jointCusp_to_jointFourier
    (p a : Nat) [Fact (Nat.Prime p)] (hodd : Odd p)
    (chi : MulChar (ZMod p) Complex) (hfour : chi ^ 4 = 1)
    (psi : AddChar (ZMod (p ^ (a + 2))) Complex) (hpsi : psi.IsPrimitive)
    (b t nu : ZMod (p ^ (a + 2))) (hb : 2 * b = 1) :
    Finset.sum Finset.univ (fun h : Units (ZMod (p ^ (a + 2))) =>
      Finset.sum Finset.univ (fun r : ZMod (p ^ (a + 2)) =>
        chi (primePowerResidue p a r) * (Inv.inv chi) (primePowerResidue p a h) *
          psi ((h : ZMod (p ^ (a + 2))) * r ^ 2 + t * r + nu * Units.val (Inv.inv h)))) =
      chi (-(primePowerResidue p a b * primePowerResidue p a t)) *
        Finset.sum Finset.univ (fun h : Units (ZMod (p ^ (a + 2))) =>
          (chi ^ 2) (primePowerResidue p a h) *
            (Finset.sum Finset.univ (fun r : ZMod (p ^ (a + 2)) =>
              psi ((h : ZMod (p ^ (a + 2))) * r ^ 2))) *
            psi ((nu - (b * t) ^ 2) * (h : ZMod (p ^ (a + 2))))) := by
  classical
  let rho := primePowerResidue p a
  let G (h : Units (ZMod (p ^ (a + 2)))) :=
    Finset.sum Finset.univ (fun r : ZMod (p ^ (a + 2)) => psi ((h : ZMod (p ^ (a + 2))) * r ^ 2))
  have hbF : (2 : ZMod p) * rho b = 1 := by
    simpa only [map_mul, map_ofNat, map_one] using congrArg rho hb
  have hinv : Inv.inv (chi ^ 2) = chi ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    calc
      chi ^ 2 * chi ^ 2 = chi ^ (2 + 2) := (pow_add chi 2 2).symm
      _ = 1 := hfour
  have hrow (h : Units (ZMod (p ^ (a + 2)))) :
      Finset.sum Finset.univ (fun r : ZMod (p ^ (a + 2)) =>
        chi (rho r) * (Inv.inv chi) (rho h) *
          psi ((h : ZMod (p ^ (a + 2))) * r ^ 2 + t * r + nu * Units.val (Inv.inv h))) =
        chi (-(rho b * rho t)) * (chi ^ 2) (rho h) * G h *
          psi ((nu - (b * t) ^ 2) * Units.val (Inv.inv h)) := by
    have heval := sum_quadraticPhase_primePower_residueValue p a hodd psi hpsi chi h t
    have hc := congrArg (fun z : Complex =>
      (Inv.inv chi) (rho h) * z * psi (nu * Units.val (Inv.inv h))) heval
    have hc' :
        Finset.sum Finset.univ (fun r : ZMod (p ^ (a + 2)) =>
          chi (rho r) * (Inv.inv chi) (rho h) *
            psi ((h : ZMod (p ^ (a + 2))) * r ^ 2 + t * r + nu * Units.val (Inv.inv h))) =
        (chi (-rho t / (2 * rho h)) * (Inv.inv chi) (rho h)) *
          Finset.sum Finset.univ (fun r : ZMod (p ^ (a + 2)) =>
            psi ((h : ZMod (p ^ (a + 2))) * r ^ 2 + t * r + nu * Units.val (Inv.inv h))) := by
      simpa only [rho, Finset.mul_sum, Finset.sum_mul, AddChar.map_add_eq_mul,
        mul_assoc, mul_left_comm, mul_comm] using hc
    rw [hc', MulChar.quartic_stationaryWeight chi hfour (rho b) (rho h) (rho t) hbF,
      AddChar.sum_quadraticCusp_completeSquare psi b hb]
    simp only [G, mul_assoc]
  change Finset.sum Finset.univ (fun h : Units (ZMod (p ^ (a + 2))) =>
      Finset.sum Finset.univ (fun r : ZMod (p ^ (a + 2)) =>
        chi (rho r) * (Inv.inv chi) (rho h) *
          psi ((h : ZMod (p ^ (a + 2))) * r ^ 2 + t * r + nu * Units.val (Inv.inv h)))) =
    chi (-(rho b * rho t)) * Finset.sum Finset.univ (fun h : Units (ZMod (p ^ (a + 2))) =>
      (chi ^ 2) (rho h) * G h * psi ((nu - (b * t) ^ 2) * (h : ZMod (p ^ (a + 2)))))
  simp_rw [hrow]
  rw [Finset.mul_sum]
  apply (Fintype.sum_bijective
    (fun h : Units (ZMod (p ^ (a + 2))) => Inv.inv h)
    inv_involutive.bijective _ _ ?_).symm
  intro h
  have hrho : rho (Inv.inv h : Units (ZMod (p ^ (a + 2)))) = Inv.inv (rho h) := by
    change Units.val ((Units.map rho.toMonoidHom) (Inv.inv h)) = _
    rw [map_inv, Units.val_inv_eq_inv_val]
    rfl
  have hG : G (Inv.inv h) = G h := AddChar.sum_quadraticPhase_inv_unit psi h
  simp only [inv_inv, hrho, hG, <- MulChar.inv_apply', hinv]
  ring

end ZMod
