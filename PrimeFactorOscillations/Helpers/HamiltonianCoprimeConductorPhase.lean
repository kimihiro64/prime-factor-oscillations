/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianCoprimeCubicKernel
import PrimeFactorOscillations.Helpers.HamiltonianCoprimeCubicPacket
import PrimeFactorOscillations.Helpers.HamiltonianCoprimeDeterminant

/-! # Full conductor phases and a uniform native three-step supply

Primitive unit parameters describe each exact conductor fiber.
Their complete phase sum is retained, including the prime-two row.
The positive cubic arithmetic packet is then read on the actual
coprime transition matrix with its full dimension normalization.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations

def hamiltonianCoprimeFrequencyLift (g t : Nat) [NeZero t]
    (u : Units (ZMod t)) : ZMod (g * t) :=
  ((g * (u : ZMod t).val : Nat) : ZMod (g * t))

theorem hamiltonian_coprime_frequency_lift_val (g t : Nat) [NeZero g] [NeZero t]
    (u : Units (ZMod t)) :
    (hamiltonianCoprimeFrequencyLift g t u).val = g * (u : ZMod t).val := by
  exact ZMod.val_natCast_of_lt
    (Nat.mul_lt_mul_of_pos_left (u : ZMod t).val_lt (NeZero.pos g))

theorem hamiltonian_coprime_frequency_lift_conductor (g t : Nat) [NeZero g] [NeZero t]
    (u : Units (ZMod t)) :
    hamiltonianCoprimeConductor (hamiltonianCoprimeFrequencyLift g t u) = t := by
  unfold hamiltonianCoprimeConductor
  rw [hamiltonian_coprime_frequency_lift_val, Nat.gcd_mul_left,
    (ZMod.val_coe_unit_coprime u).symm.gcd_eq_one, mul_one]
  exact Nat.mul_div_cancel_left t (NeZero.pos g)

theorem hamiltonian_coprime_conductor_phase_product
    (g t h : Nat) [NeZero g] [NeZero t] :
    (Finset.univ.filter (fun k : ZMod (g * t) => hamiltonianCoprimeConductor k = t)).sum
        (fun k => ZMod.stdAddChar ((h : ZMod (g * t)) * k)) =
      LPF.lpfRamanujanSum (q := t) h := by
  symm
  unfold LPF.lpfRamanujanSum
  apply Finset.sum_bij (fun (u : Units (ZMod t)) _ => hamiltonianCoprimeFrequencyLift g t u)
  next =>
    intro u hu
    exact Finset.mem_filter.mpr (And.intro (Finset.mem_univ _)
      (hamiltonian_coprime_frequency_lift_conductor g t u))
  next =>
    intro u hu v hv hEq
    have hVal := congrArg (fun k : ZMod (g * t) => k.val) hEq
    rw [hamiltonian_coprime_frequency_lift_val,
      hamiltonian_coprime_frequency_lift_val] at hVal
    apply Units.ext
    exact ZMod.val_injective t (Nat.eq_of_mul_eq_mul_left (NeZero.pos g) hVal)
  next =>
    intro k hk
    have hCond := (Finset.mem_filter.mp hk).2
    have hData := hamiltonian_coprime_frequency_factorization k
    have hGcd : Nat.gcd (g * t) k.val = g := by
      apply Nat.eq_of_mul_eq_mul_right (NeZero.pos t)
      simpa only [hCond] using hData.2.2.1
    let b := k.val / g
    have hFactor : g * b = k.val := by
      simpa only [b, hGcd] using hData.2.2.2.1
    have hCop : Nat.Coprime b t := by
      simpa only [b, hGcd, hCond] using hData.2.2.2.2
    have hBLt : b < t := by
      by_contra hNot
      have hLe : t <= b := le_of_not_gt hNot
      have hMul := Nat.mul_le_mul_left g hLe
      rw [hFactor] at hMul
      exact (Nat.not_le_of_gt k.val_lt) hMul
    have hUnit : IsUnit (b : ZMod t) := (ZMod.isUnit_iff_coprime b t).mpr hCop
    let u := hUnit.unit
    have hUVal : (u : ZMod t).val = b := by
      dsimp only [u]
      rw [hUnit.unit_spec, ZMod.val_natCast_of_lt hBLt]
    refine Exists.intro u (Exists.intro (Finset.mem_univ _) ?_)
    unfold hamiltonianCoprimeFrequencyLift
    rw [hUVal, hFactor, ZMod.natCast_zmod_val]
  next =>
    intro u hu
    symm
    calc
      _ = ZMod.stdAddChar (N := g * t)
          ((g * ((u : ZMod t).val * h) : Nat) : ZMod (g * t)) := by
        congr 1
        unfold hamiltonianCoprimeFrequencyLift
        simp only [Nat.cast_mul]
        ring
      _ = ZMod.stdAddChar (N := t)
          (((u : ZMod t).val * h : Nat) : ZMod t) :=
        hamiltonian_scaled_standard_character g t _
      _ = _ := by rw [Nat.cast_mul, ZMod.natCast_zmod_val]

theorem hamiltonian_coprime_conductor_phase_divisor
    (n t h : Nat) [NeZero n] (ht : Dvd.dvd t n) :
    (Finset.univ.filter (fun k : ZMod n => hamiltonianCoprimeConductor k = t)).sum
        (fun k => ZMod.stdAddChar ((h : ZMod n) * k)) =
      LPF.lpfRamanujanFunction h t := by
  choose g hDim using ht
  have hEq : n = g * t := hDim.trans (Nat.mul_comm t g)
  clear hDim
  subst n
  have hProd : Not (g * t = 0) := NeZero.ne (g * t)
  haveI : NeZero g := NeZero.mk (fun hg => hProd (by rw [hg, zero_mul]))
  haveI : NeZero t := NeZero.mk (fun ht => hProd (by rw [ht, mul_zero]))
  rw [LPF.lpfRamanujanFunction_eq_sum]
  exact hamiltonian_coprime_conductor_phase_product g t h

theorem hamiltonian_coprime_conductor_phase_sum
    (n h : Nat) [NeZero n] (w : Nat -> Complex) :
    Finset.univ.sum (fun k : ZMod n =>
        w (hamiltonianCoprimeConductor k) * ZMod.stdAddChar ((h : ZMod n) * k)) =
      n.divisors.sum (fun t => w t * LPF.lpfRamanujanFunction h t) := by
  have hMaps : forall k, Membership.mem (Finset.univ : Finset (ZMod n)) k ->
      Membership.mem n.divisors (hamiltonianCoprimeConductor k) := by
    intro k hk
    exact hamiltonian_coprime_conductor_mem_divisors k
  calc
    _ = n.divisors.sum (fun t =>
        (Finset.univ.filter (fun k : ZMod n => hamiltonianCoprimeConductor k = t)).sum
          (fun k => w (hamiltonianCoprimeConductor k) *
            ZMod.stdAddChar ((h : ZMod n) * k))) :=
      (Finset.sum_fiberwise_of_maps_to hMaps
        (fun k : ZMod n => w (hamiltonianCoprimeConductor k) *
          ZMod.stdAddChar ((h : ZMod n) * k))).symm
    _ = n.divisors.sum (fun t => w t *
        (Finset.univ.filter (fun k : ZMod n => hamiltonianCoprimeConductor k = t)).sum
          (fun k => ZMod.stdAddChar ((h : ZMod n) * k))) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [(Finset.mem_filter.mp hk).2]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [hamiltonian_coprime_conductor_phase_divisor n t h (Nat.dvd_of_mem_divisors ht)]

theorem hamiltonian_coprime_three_step_packet
    (n : Nat) [NeZero n] (a b : ZMod n) :
    (n : Complex) * Complex.ofReal (hamiltonianCoprimeThreeStepKernel a b) =
      hamiltonianCoprimeCubicSum (-(a - b)).val n := by
  let h := (-(a - b)).val
  let F := fun k : ZMod n => hamiltonianCoprimeFourierSymbol k / (n.totient : Complex)
  have hPhase (k : ZMod n) :
      ZMod.stdAddChar ((a - b) * -k) = ZMod.stdAddChar ((h : ZMod n) * k) := by
    congr 1
    dsimp only [h]
    rw [ZMod.natCast_zmod_val]
    ring
  have hRatio (k : ZMod n) :
      F k = (ArithmeticFunction.moebius (hamiltonianCoprimeConductor k) : Complex) /
        ((hamiltonianCoprimeConductor k).totient : Complex) := by
    simpa only [F, hamiltonianCoprimeFourierSymbol] using
      hamiltonian_coprime_full_frequency_ratio k
  have hGroup := hamiltonian_coprime_conductor_phase_sum n h
    (fun t => ((ArithmeticFunction.moebius t : Complex) / (t.totient : Complex)) ^ 3)
  have hSum : Finset.univ.sum (fun k : ZMod n =>
      F k ^ 3 * ZMod.stdAddChar ((h : ZMod n) * k)) =
        hamiltonianCoprimeCubicSum h n := by
    simp_rw [hRatio]
    rw [hGroup, hamiltonian_coprime_cubic_sum_apply]
    apply Finset.sum_congr rfl
    intro t ht
    exact (hamiltonian_coprime_cubic_weight_apply h t).symm
  have hN : Not ((n : Complex) = 0) := by exact_mod_cast NeZero.ne n
  rw [<- hamiltonian_coprime_cubic_inverse a b]
  change (n : Complex) * LPF.lpfCyclicInverse (fun k => F k ^ 3) (a - b) = _
  unfold LPF.lpfCyclicInverse
  simp only [zpow_neg_one]
  simp_rw [hPhase]
  rw [hSum]
  dsimp only [h]
  field_simp [hN]

theorem hamiltonian_coprime_three_step_lower
    (n : Nat) [NeZero n] (a b : ZMod n)
    (hParity : Odd n \/ Odd (-(a - b)).val) :
    (1 : Real) / (2 * (n : Real)) <= hamiltonianCoprimeThreeStepKernel a b := by
  have hLower := hamiltonian_coprime_cubic_packet_lower n (-(a - b)).val hParity
  have hReadout := hamiltonian_coprime_three_step_packet n a b
  have hCast : Complex.ofReal ((n : Real) * hamiltonianCoprimeThreeStepKernel a b) =
      hamiltonianCoprimeCubicSum (-(a - b)).val n := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_natCast] using hReadout
  have hReal : (n : Real) * hamiltonianCoprimeThreeStepKernel a b =
      (hamiltonianCoprimeCubicSum (-(a - b)).val n).re := by
    simpa only [Complex.ofReal_re] using congrArg Complex.re hCast
  have hN : 0 < (n : Real) := by exact_mod_cast NeZero.pos n
  have hTwoN : 0 < 2 * (n : Real) := mul_pos (by norm_num) hN
  have hScale : (2 * (n : Real)) * (1 / (2 * (n : Real))) = 1 := by
    field_simp [ne_of_gt hN]
  have hScaled : (2 * (n : Real)) * (1 / (2 * (n : Real))) <=
      (2 * (n : Real)) * hamiltonianCoprimeThreeStepKernel a b := by
    rw [hScale]
    nlinarith only [hLower, hReal]
  exact le_of_mul_le_mul_left hScaled hTwoN

end PrimeFactorOscillations
