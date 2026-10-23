/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.PrimePowerIntrinsicBridge
import PrimeFactorOscillations.Helpers.PrimePowerTameImage

/-!
# Full compensated transport under actual root lifting

Both the return trace and unit-reference trace are pushed forward with
their own exact fiber masses. The complete signed difference scales by
a positive product of those masses. No main-term absolute bound occurs.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CyclicConductorReduction

open scoped BigOperators

def compensatedTrace {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) (w : G -> Complex) : Complex :=
  letI : Fintype H := Fintype.ofFinite H
  (Nat.card G : Complex) * Finset.univ.sum (fun u : H => w u.val) -
    (Nat.card H : Complex) * Finset.univ.sum w

theorem compensated_trace_pushforward {G Q : Type*} [Group G] [Group Q]
    [Fintype G] [Fintype Q] (f : MonoidHom G Q)
    (hf : Function.Surjective f) (H : Subgroup G) (w : Q -> Complex) :
    compensatedTrace H (fun u => w (f u)) =
      (Nat.card f.ker : Complex) *
        (Nat.card (f.subgroupMap H).ker : Complex) *
          compensatedTrace (H.map f) w := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  letI : Fintype (H.map f) := Fintype.ofFinite _
  let g := f.subgroupMap H
  have hG : (Nat.card G : Complex) =
      (Nat.card f.ker : Complex) * (Nat.card Q : Complex) := by
    have hs := sum_comp_surjective_hom f hf (fun _ => (1 : Complex))
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Nat.card_eq_fintype_card] using hs
  have hH : (Nat.card H : Complex) =
      (Nat.card g.ker : Complex) * (Nat.card (H.map f) : Complex) := by
    have hs := sum_comp_surjective_hom g (f.subgroupMap_surjective H)
      (fun _ => (1 : Complex))
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Nat.card_eq_fintype_card] using hs
  have hT : Finset.univ.sum (fun u : H => w (f u.val)) =
      (Nat.card g.ker : Complex) *
        Finset.univ.sum (fun v : H.map f => w v.val) :=
    sum_comp_surjective_hom g (f.subgroupMap_surjective H)
      (fun v : H.map f => w v.val)
  have hU := sum_comp_surjective_hom f hf w
  unfold compensatedTrace
  dsimp only []
  rw [hG, hH, hT, hU]
  ring

end PrimeFactorOscillations.CyclicConductorReduction

namespace PrimeFactorOscillations.PrimePowerReturnSpectrum

open scoped BigOperators
open CyclicConductorReduction

theorem native_centered_as_compensated (n k h : Nat) [NeZero n] :
    centeredTransform n k h = compensatedTrace (powerKernel n k)
      (fun u : Units (ZMod n) =>
        ZMod.stdAddChar ((h : ZMod n) * (u : ZMod n))) := by
  classical
  simp only [centeredTransform, compensatedTrace, returnTransform,
    LPF.lpfRamanujanSum, Nat.card_eq_fintype_card, mul_comm]

theorem centered_conductor_reduction (N B m k j : Nat)
    [NeZero N] [NeZero B] [NeZero m] (hd : Dvd.dvd B N)
    (hnm : N = m * B)
    (hi : (powerKernel N k).map (ZMod.unitsMap hd) = powerKernel B k) :
    centeredTransform N k (m * j) =
      (Nat.card (ZMod.unitsMap hd).ker : Complex) *
        (Nat.card ((ZMod.unitsMap hd).subgroupMap (powerKernel N k)).ker : Complex) *
          centeredTransform B k j := by
  classical
  let w : Units (ZMod B) -> Complex :=
    fun u => ZMod.stdAddChar ((j : ZMod B) * (u : ZMod B))
  have hs := compensated_trace_pushforward (ZMod.unitsMap hd)
    (ZMod.unitsMap_surjective hd) (powerKernel N k) w
  have hci := congrArg
    (fun J : Subgroup (Units (ZMod B)) => compensatedTrace J w) hi
  rw [hci] at hs
  rw [native_centered_as_compensated N k (m * j), native_centered_as_compensated B k j]
  calc
    _ = compensatedTrace (powerKernel N k)
        (fun u : Units (ZMod N) => w (ZMod.unitsMap hd u)) := by
      apply congrArg (compensatedTrace (powerKernel N k))
      funext u
      change ZMod.stdAddChar (((m * j : Nat) : ZMod N) * (u : ZMod N)) =
        ZMod.stdAddChar ((j : ZMod B) * ZMod.castHom hd (ZMod B) (u : ZMod N))
      have hc := standard_character_reduce N B m hd hnm
        ((j : ZMod N) * (u : ZMod N))
      simpa only [Nat.cast_mul, mul_assoc, map_mul, map_natCast] using hc
    _ = _ := hs

theorem centered_conductor_reduction_zero_iff (N B m k j : Nat)
    [NeZero N] [NeZero B] [NeZero m] (hd : Dvd.dvd B N)
    (hnm : N = m * B)
    (hi : (powerKernel N k).map (ZMod.unitsMap hd) = powerKernel B k) :
    centeredTransform N k (m * j) = 0 <-> centeredTransform B k j = 0 := by
  have hq : Not ((Nat.card (ZMod.unitsMap hd).ker : Complex) = 0) := by
    exact_mod_cast (Nat.card_pos.ne' : Not (Nat.card (ZMod.unitsMap hd).ker = 0))
  have hr : Not ((Nat.card ((ZMod.unitsMap hd).subgroupMap (powerKernel N k)).ker : Complex) = 0) := by
    exact_mod_cast (Nat.card_pos.ne' :
      Not (Nat.card ((ZMod.unitsMap hd).subgroupMap (powerKernel N k)).ker = 0))
  rw [centered_conductor_reduction N B m k j hd hnm hi]
  constructor
  { intro hz
    exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero hq hr) }
  { intro hz
    rw [hz, mul_zero] }

theorem intrinsic_conductor_reduction_zero_iff (N B m k j : Nat)
    [NeZero N] [NeZero B] [NeZero m] (hd : Dvd.dvd B N)
    (hnm : N = m * B)
    (hi : (powerKernel N k).map (ZMod.unitsMap hd) = powerKernel B k) :
    ModularReturnFourier.residueFourier N (CarmichaelCarrierReadout.centeredPower N k) (m * j) = 0 <->
      ModularReturnFourier.residueFourier B (CarmichaelCarrierReadout.centeredPower B k) j = 0 := by
  rw [intrinsic_eq_native N k (m * j), intrinsic_eq_native B k j]
  exact centered_conductor_reduction_zero_iff N B m k j hd hnm hi

theorem prime_power_centered_reduction (p s k h : Nat) [NeZero p]
    (hp : Nat.Prime p) (hp2 : Not (p = 2)) :
    centeredTransform (p ^ (s + 1)) k (p ^ s * h) =
      (p ^ s : Complex) * (Nat.gcd k (p ^ s) : Complex) *
        centeredTransform (p ^ (0 + 1)) k h := by
  letI : IsCyclic (Units (ZMod (p ^ (s + 1)))) :=
    ZMod.isCyclic_units_of_prime_pow p hp hp2 (s + 1)
  let f := conductorMap p s 0
  let H := powerKernel (p ^ (s + 1)) k
  have hk : (f.subgroupMap H).ker = f.ker.subgroupOf H := by
    apply Subgroup.ext
    intro u
    change (f.subgroupMap H u = 1) <-> (f u.val = 1)
    constructor
    { intro hu
      exact congrArg Subtype.val hu }
    { intro hu
      exact Subtype.ext hu }
  have hr : Nat.card (f.subgroupMap H).ker = Nat.gcd k (p ^ s) := by
    rw [hk, cyclic_restricted_kernel_card H f, conductor_kernel_card p s 0 hp]
    exact (root_kernel_mass_factors p s k hp hp2).right.left
  have hs := centered_conductor_reduction (p ^ (s + 1)) (p ^ (0 + 1)) (p ^ s) k h
    (conductor_dvd p s 0) (conductor_product p s 0)
    (prime_power_tame_image p s k hp hp2)
  change centeredTransform (p ^ (s + 1)) k (p ^ s * h) =
    (Nat.card f.ker : Complex) * (Nat.card (f.subgroupMap H).ker : Complex) *
      centeredTransform (p ^ (0 + 1)) k h at hs
  rw [conductor_kernel_card p s 0 hp, hr, Nat.cast_pow] at hs
  exact hs

/-- Explicit dependent transport for the prime-conductor normalization. -/
theorem centered_prime_conductor_normalization (p k h : Nat) [NeZero p] :
    centeredTransform (p ^ (0 + 1)) k h = centeredTransform p k h := by
  have transport (n : Nat) [NeZero n] (hn : n = p) :
      centeredTransform n k h = centeredTransform p k h := by
    subst n
    rfl
  exact transport (p ^ (0 + 1)) (by simp only [Nat.zero_add, pow_one])

theorem prime_power_centered_reduction_at_prime (p s k h : Nat) [NeZero p]
    (hp : Nat.Prime p) (hp2 : Not (p = 2)) :
    centeredTransform (p ^ (s + 1)) k (p ^ s * h) =
      (p ^ s : Complex) * (Nat.gcd k (p ^ s) : Complex) *
        centeredTransform p k h := by
  have hs := prime_power_centered_reduction p s k h hp hp2
  rw [centered_prime_conductor_normalization] at hs
  exact hs

theorem prime_power_intrinsic_reduction (p s k h : Nat) [NeZero p]
    (hp : Nat.Prime p) (hp2 : Not (p = 2)) :
    ModularReturnFourier.residueFourier (p ^ (s + 1))
        (CarmichaelCarrierReadout.centeredPower (p ^ (s + 1)) k) (p ^ s * h) =
      (p ^ s : Complex) * (Nat.gcd k (p ^ s) : Complex) *
        ModularReturnFourier.residueFourier p
          (CarmichaelCarrierReadout.centeredPower p k) h := by
  rw [intrinsic_eq_native, intrinsic_eq_native]
  exact prime_power_centered_reduction_at_prime p s k h hp hp2

end PrimeFactorOscillations.PrimePowerReturnSpectrum
