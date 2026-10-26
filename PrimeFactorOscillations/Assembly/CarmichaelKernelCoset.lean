/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelCorrelationSpectrum
import PrimeFactorOscillations.Helpers.ReturnPacketPowerSupport

/-!
# Exact coset averaging of a native correlation kernel

A complete subgroup average kills every surviving nonprincipal restriction
that is nontrivial on that subgroup. The original principal coefficient is
retained exactly; no absolute values or omitted Fourier phases are used.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelKernelCoset

open CarmichaelCorrelation CarmichaelCorrelationSpectrum

variable {q : Nat} [NeZero q]

theorem restriction_sum_zero
    (H : Subgroup (Units (ZMod q))) [Fintype H]
    (chi : DirichletCharacter Complex q)
    (hNot : Not (forall h : H, unitCharacter chi h.val = 1)) :
    Finset.univ.sum (fun h : H => unitCharacter chi h.val) = 0 := by
  classical
  let eta : MonoidHom H Complex := (unitCharacter chi).comp H.subtype
  have hPower : Not (forall h : H, (eta h) ^ 1 = 1) := by
    intro h
    apply hNot
    intro v
    have hv := h v
    change (unitCharacter chi v.val) ^ 1 = 1 at hv
    simpa only [pow_one] using hv
  have hEmpty (p : (Finset.empty : Finset Nat.Primes)) : False :=
    Finset.notMem_empty p.val p.property
  change Finset.univ.sum (fun h : H => eta h) = 0
  simpa only [one_mul] using
    ReturnPacketPowerSupport.packet_sum_eq_zero_of_not_power
      (Monoid.exponent H) 1 Finset.empty
      (fun p => (hEmpty p).elim) (fun p => (hEmpty p).elim)
      (fun h => Monoid.pow_exponent_eq_one h) eta hPower (fun _ => 1)

theorem inverse_restriction_sum_zero
    (H : Subgroup (Units (ZMod q))) [Fintype H]
    (chi : DirichletCharacter Complex q)
    (hNot : Not (forall h : H, unitCharacter chi h.val = 1)) :
    Finset.univ.sum (fun h : H => unitCharacter chi (Inv.inv h.val)) = 0 := by
  calc
    _ = Finset.univ.sum (fun h : H => unitCharacter chi h.val) :=
      Equiv.sum_comp (Equiv.inv H) (fun h : H => unitCharacter chi h.val)
    _ = 0 := restriction_sum_zero H chi hNot

theorem coset_character_sum_zero
    (H : Subgroup (Units (ZMod q))) [Fintype H]
    (chi : DirichletCharacter Complex q)
    (hNot : Not (forall h : H, unitCharacter chi h.val = 1))
    (u : Units (ZMod q)) :
    Finset.univ.sum (fun h : H => unitCharacter chi (Inv.inv (u * h.val))) = 0 := by
  calc
    _ = unitCharacter chi (Inv.inv u) *
        Finset.univ.sum (fun h : H => unitCharacter chi (Inv.inv h.val)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      rw [mul_inv_rev, map_mul]
      ring
    _ = 0 := by rw [inverse_restriction_sum_zero H chi hNot, mul_zero]

theorem kernel_coset_sum
    (w : Units (ZMod q) -> Real) (hw : 0 < weightSum w)
    (H : Subgroup (Units (ZMod q))) [Fintype H]
    (hSupport : forall chi : DirichletCharacter Complex q,
      Not (coefficient w chi = 0) -> Not (chi = 1) ->
        Not (forall h : H, unitCharacter chi h.val = 1))
    (u : Units (ZMod q)) :
    Finset.univ.sum (fun h : H => kernel w (u * h.val)) = (Fintype.card H : Real) := by
  classical
  have hComplex :
      Finset.univ.sum (fun h : H => (kernel w (u * h.val) : Complex)) =
        (Fintype.card H : Complex) := by
    simp_rw [kernel_expansion]
    rw [Finset.sum_comm]
    calc
      _ = Finset.univ.sum (fun h : H =>
          (coefficient w (1 : DirichletCharacter Complex q) : Complex) *
            unitCharacter (1 : DirichletCharacter Complex q) (Inv.inv (u * h.val))) := by
        apply Finset.sum_eq_single (1 : DirichletCharacter Complex q)
        . intro chi _ hChi
          by_cases hZero : coefficient w chi = 0
          . simp only [hZero, Complex.ofReal_zero, zero_mul, Finset.sum_const_zero]
          . rw [<- Finset.mul_sum,
              coset_character_sum_zero H chi (hSupport chi hZero hChi) u, mul_zero]
        . intro h
          exact False.elim (h (Finset.mem_univ 1))
      _ = _ := by simp [coefficient_principal w hw, unitCharacter_one]
  exact_mod_cast hComplex

end PrimeFactorOscillations.CarmichaelKernelCoset
