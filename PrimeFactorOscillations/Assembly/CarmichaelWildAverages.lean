/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelKernelCoset
import PrimeFactorOscillations.Assembly.CarmichaelWildConductor
import PrimeFactorOscillations.Helpers.PrimeSquareProgressionFiber

/-!
# Exact coarse residue averages of original native prime-power kernels

Every nonprincipal survivor is nontrivial on the kernel of actual reduction
to the residue prime. The complete original kernel therefore averages to one
on every coarse unit fiber, for all primes, including the two-power exceptions.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelWildAverages

open CarmichaelPrimePacket CarmichaelCorrelation CarmichaelCorrelationSpectrum
open CarmichaelKernelCoset PrimePowerReturnSpectrum PrimePowerWildCharacterConductor

local instance primeLabelNeZero (l : Nat.Primes) : NeZero (l : Nat) :=
  NeZero.mk l.property.ne_zero

abbrev coarseKernel (l : Nat.Primes) (a : Nat) :=
  (conductorMap (l : Nat) (a + 1) 0).ker

local instance coarseFintype (l : Nat.Primes) (a : Nat) :
    Fintype (coarseKernel l a) := Fintype.ofFinite _

theorem coarse_kernel_card (l : Nat.Primes) (a : Nat) :
    Nat.card (coarseKernel l a) = (l : Nat) ^ (a + 1) :=
  conductor_kernel_card (l : Nat) (a + 1) 0 l.property

theorem native_nonprincipal_coarse_nontrivial (l : Nat.Primes) (a : Nat)
    (chi : DirichletCharacter Complex ((l : Nat) ^ (a + 2)))
    (hNonzero : Not (coefficient (weight ((l : Nat) ^ (a + 2)) l) chi = 0))
    (hChi : Not (chi = 1)) :
    Not (forall h : coarseKernel l a, unitCharacter chi h.val = 1) := by
  intro hTrivial
  have hFactor : chi.FactorsThrough ((l : Nat) ^ 1) := by
    apply (DirichletCharacter.factorsThrough_iff_ker_unitsMap
      (conductor_dvd (l : Nat) (a + 1) 0)).mpr
    intro v hv
    change chi.toUnitHom v = 1
    apply Units.ext
    have hValue := hTrivial (Subtype.mk v hv)
    change chi (Units.val v) = 1 at hValue
    simpa only [MulChar.coe_toUnitHom, Units.val_one] using hValue
  have hPrimeFactor : chi.FactorsThrough (l : Nat) :=
    Eq.mp (congrArg (fun d : Nat => chi.FactorsThrough d) (pow_one (l : Nat))) hFactor
  have hPower := CarmichaelPrimePacketSpectrum.nonzero_coefficient_prime_power
    ((l : Nat) ^ (a + 2)) l (prime_dvd_exponent (l : Nat) a l.property) chi hNonzero
  exact nonprincipal_not_factorsThrough_prime (l : Nat) a l.property
    chi hPower hChi hPrimeFactor

theorem native_coarse_sum (l : Nat.Primes) (a : Nat)
    (u : Units (ZMod ((l : Nat) ^ (a + 2)))) :
    Finset.univ.sum (fun h : coarseKernel l a =>
      kernel (weight ((l : Nat) ^ (a + 2)) l) (u * h.val)) =
        (((l : Nat) ^ (a + 1) : Nat) : Real) := by
  have hSum := weightSum_pos ((l : Nat) ^ (a + 2)) l
    (prime_dvd_exponent (l : Nat) a l.property)
  have h := kernel_coset_sum (weight ((l : Nat) ^ (a + 2)) l) hSum
    (coarseKernel l a) (native_nonprincipal_coarse_nontrivial l a) u
  have hCard : Fintype.card (coarseKernel l a) = (l : Nat) ^ (a + 1) := by
    rw [<- Nat.card_eq_fintype_card]
    exact coarse_kernel_card l a
  simpa only [hCard] using h

theorem native_coarse_average (l : Nat.Primes) (a : Nat)
    (u : Units (ZMod ((l : Nat) ^ (a + 2)))) :
    (Finset.univ.sum (fun h : coarseKernel l a =>
      kernel (weight ((l : Nat) ^ (a + 2)) l) (u * h.val))) /
        (((l : Nat) ^ (a + 1) : Nat) : Real) = 1 := by
  rw [native_coarse_sum]
  apply div_self
  exact_mod_cast pow_ne_zero (a + 1) l.property.ne_zero

theorem native_signed_coarse_sum (l : Nat.Primes) (a : Nat)
    (u : Units (ZMod ((l : Nat) ^ (a + 2)))) (B : Real) :
    Finset.univ.sum (fun h : coarseKernel l a =>
      kernel (weight ((l : Nat) ^ (a + 2)) l) (u * h.val) * B) =
        (((l : Nat) ^ (a + 1) : Nat) : Real) * B := by
  rw [<- Finset.sum_mul]
  change (Finset.univ.sum (fun h : coarseKernel l a =>
    kernel (weight ((l : Nat) ^ (a + 2)) l) (u * h.val))) * B = _
  rw [native_coarse_sum]

theorem native_coarse_probability_mass (l : Nat.Primes) (a : Nat)
    (u : Units (ZMod ((l : Nat) ^ (a + 2)))) :
    (Finset.univ.sum (fun h : coarseKernel l a =>
      kernel (weight ((l : Nat) ^ (a + 2)) l) (u * h.val))) /
        (Fintype.card (Units (ZMod ((l : Nat) ^ (a + 2)))) : Real) =
          1 / (((l : Nat) - 1 : Nat) : Real) := by
  have hCard : Fintype.card (Units (ZMod ((l : Nat) ^ (a + 2)))) =
      (l : Nat) ^ (a + 1) * ((l : Nat) - 1) := by
    rw [ZMod.card_units_eq_totient]
    exact Nat.totient_prime_pow_succ l.property (a + 1)
  rw [native_coarse_sum, hCard, Nat.cast_mul]
  have hPow : Not ((((l : Nat) ^ (a + 1) : Nat) : Real) = 0) := by
    exact_mod_cast pow_ne_zero (a + 1) l.property.ne_zero
  have hMinus : Not ((((l : Nat) - 1 : Nat) : Real) = 0) := by
    exact_mod_cast (show Not ((l : Nat) - 1 = 0) by have h := l.property.one_lt; omega)
  field_simp [hPow, hMinus]

def squareLift (l : Nat.Primes) (a : Nat) (v : Units (ZMod ((l : Nat) ^ 2))) :
    Units (ZMod ((l : Nat) ^ (a + 2))) :=
  Classical.choose (ZMod.unitsMap_surjective (primeSquare_dvd_level (l : Nat) a) v)

theorem squareLift_spec (l : Nat.Primes) (a : Nat)
    (v : Units (ZMod ((l : Nat) ^ 2))) :
    conductorMap (l : Nat) a 1 (squareLift l a v) = v :=
  Classical.choose_spec (ZMod.unitsMap_surjective (primeSquare_dvd_level (l : Nat) a) v)

def reducedKernel (l : Nat.Primes) (a : Nat) (v : Units (ZMod ((l : Nat) ^ 2))) : Real :=
  kernel (weight ((l : Nat) ^ (a + 2)) l) (squareLift l a v)

theorem kernel_eq_reducedKernel (l : Nat.Primes) (a : Nat)
    (hTwo : Not ((l : Nat) = 2)) (u : Units (ZMod ((l : Nat) ^ (a + 2)))) :
    kernel (weight ((l : Nat) ^ (a + 2)) l) u =
      reducedKernel l a (conductorMap (l : Nat) a 1 u) := by
  exact CarmichaelWildConductor.wild_kernel_eq_of_reduction_eq l a hTwo u
    (squareLift l a (conductorMap (l : Nat) a 1 u))
    (squareLift_spec l a (conductorMap (l : Nat) a 1 u)).symm

theorem coarse_reduction_comp (l : Nat.Primes) (a : Nat) :
    (conductorMap (l : Nat) 1 0).comp (conductorMap (l : Nat) a 1) =
      conductorMap (l : Nat) (a + 1) 0 := by
  change (ZMod.unitsMap (conductor_dvd (l : Nat) 1 0)).comp
    (ZMod.unitsMap (conductor_dvd (l : Nat) a 1)) =
      ZMod.unitsMap (conductor_dvd (l : Nat) (a + 1) 0)
  exact ZMod.unitsMap_comp _ _

theorem coarseKernel_map_square (l : Nat.Primes) (a : Nat) :
    (coarseKernel l a).map (conductorMap (l : Nat) a 1) = coarseKernel l 0 := by
  apply Subgroup.ext
  intro v
  constructor
  . intro hv
    choose u hu hImage using hv
    change conductorMap (l : Nat) 1 0 v = 1
    rw [<- hImage]
    have hComp :
        conductorMap (l : Nat) 1 0 (conductorMap (l : Nat) a 1 u) =
          conductorMap (l : Nat) (a + 1) 0 u :=
      congrArg (fun f => f u) (coarse_reduction_comp l a)
    rw [hComp]
    exact hu
  . intro hv
    choose u hu using ZMod.unitsMap_surjective (conductor_dvd (l : Nat) a 1) v
    have hImage : conductorMap (l : Nat) a 1 u = v := hu
    refine Exists.intro u (And.intro ?_ hImage)
    change conductorMap (l : Nat) (a + 1) 0 u = 1
    have hComp :
        conductorMap (l : Nat) 1 0 (conductorMap (l : Nat) a 1 u) =
          conductorMap (l : Nat) (a + 1) 0 u :=
      congrArg (fun f => f u) (coarse_reduction_comp l a)
    rw [<- hComp, hImage]
    exact hv

theorem reduced_kernel_coarse_sum (l : Nat.Primes) (a : Nat)
    (hTwo : Not ((l : Nat) = 2)) (v : Units (ZMod ((l : Nat) ^ 2))) :
    Finset.univ.sum (fun h : coarseKernel l 0 =>
      reducedKernel l a (v * h.val)) = ((l : Nat) : Real) := by
  classical
  let : IsCyclic (Units (ZMod ((l : Nat) ^ (a + 2)))) :=
    ZMod.isCyclic_units_of_prime_pow (l : Nat) l.property hTwo (a + 2)
  have hPush := CyclicConductorReduction.cyclic_subgroup_sum_pushforward
    (coarseKernel l a) (conductorMap (l : Nat) a 1)
    (fun x : Units (ZMod ((l : Nat) ^ 2)) => (reducedKernel l a (v * x) : Complex))
  rw [coarseKernel_map_square, coarse_kernel_card,
    conductor_kernel_card (l : Nat) a 1 l.property,
    Nat.gcd_eq_right (pow_dvd_pow (l : Nat) (by omega : a <= a + 1))] at hPush
  have hPoint (h : coarseKernel l a) :
      kernel (weight ((l : Nat) ^ (a + 2)) l) (squareLift l a v * h.val) =
        reducedKernel l a (v * conductorMap (l : Nat) a 1 h.val) := by
    rw [kernel_eq_reducedKernel l a hTwo, map_mul, squareLift_spec]
  have hOriginal :
      Finset.univ.sum (fun h : coarseKernel l a =>
        (kernel (weight ((l : Nat) ^ (a + 2)) l) (squareLift l a v * h.val) : Complex)) =
          ((((l : Nat) ^ (a + 1) : Nat)) : Complex) := by
    exact_mod_cast native_coarse_sum l a (squareLift l a v)
  simp_rw [hPoint] at hOriginal
  have hScale :
      ((((l : Nat) ^ a : Nat)) : Complex) *
        Finset.univ.sum (fun h : coarseKernel l 0 => (reducedKernel l a (v * h.val) : Complex)) =
      ((((l : Nat) ^ a : Nat)) : Complex) * ((l : Nat) : Complex) := by
    rw [<- hPush]
    simpa only [hPoint, Nat.pow_succ, Nat.cast_mul] using hOriginal
  have hPow : Not (((((l : Nat) ^ a : Nat)) : Complex) = 0) := by
    exact_mod_cast pow_ne_zero a l.property.ne_zero
  have hDiff :
      ((((l : Nat) ^ a : Nat)) : Complex) *
        (Finset.univ.sum (fun h : coarseKernel l 0 =>
          (reducedKernel l a (v * h.val) : Complex)) - ((l : Nat) : Complex)) = 0 := by
    rw [mul_sub, hScale, sub_self]
  have hSum := sub_eq_zero.mp ((mul_eq_zero.mp hDiff).resolve_left hPow)
  exact_mod_cast hSum

def nativePositionUnit (l : Nat.Primes) (a n t j : Nat)
    (hn : Nat.Coprime n (l : Nat)) : Units (ZMod ((l : Nat) ^ (a + 2))) :=
  ZMod.unitOfCoprime (n + j * (l : Nat) * t)
    ((PrimeSquareProgressionFiber.position_coprime l n t j hn).pow_right (a + 2))

theorem nativePositionUnit_reduction (l : Nat.Primes) (a n t j : Nat)
    (hn : Nat.Coprime n (l : Nat)) :
    conductorMap (l : Nat) a 1 (nativePositionUnit l a n t j hn) =
      PrimeSquareProgressionFiber.positionUnit l n t j hn := by
  apply Units.ext
  change ZMod.castHom (conductor_dvd (l : Nat) a 1) _
    ((n + j * (l : Nat) * t : Nat) : ZMod ((l : Nat) ^ (a + 2))) =
      ((n + j * (l : Nat) * t : Nat) : ZMod ((l : Nat) ^ 2))
  exact map_natCast _ _

theorem native_progression_sum (l : Nat.Primes) (a : Nat)
    (hTwo : Not ((l : Nat) = 2)) (n t : Nat)
    (hn : Nat.Coprime n (l : Nat)) (ht : Nat.Coprime t (l : Nat))
    (c : Units (ZMod ((l : Nat) ^ (a + 2)))) :
    Finset.univ.sum (fun i : Fin (l : Nat) =>
      kernel (weight ((l : Nat) ^ (a + 2)) l) (c * nativePositionUnit l a n t i.val hn)) =
        ((l : Nat) : Real) := by
  classical
  calc
    _ = Finset.univ.sum (fun i : Fin (l : Nat) =>
        reducedKernel l a (conductorMap (l : Nat) a 1 c *
          PrimeSquareProgressionFiber.positionUnit l n t i.val hn)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [kernel_eq_reducedKernel l a hTwo, map_mul, nativePositionUnit_reduction]
    _ = Finset.univ.sum (fun h : coarseKernel l 0 =>
        reducedKernel l a ((conductorMap (l : Nat) a 1 c *
          PrimeSquareProgressionFiber.baseUnit l n hn) * h.val)) :=
      PrimeSquareProgressionFiber.progression_sum_eq_coset l n t hn ht
        (reducedKernel l a) (conductorMap (l : Nat) a 1 c)
    _ = ((l : Nat) : Real) := reduced_kernel_coarse_sum l a hTwo _

theorem native_progression_average (l : Nat.Primes) (a : Nat)
    (hTwo : Not ((l : Nat) = 2)) (n t : Nat)
    (hn : Nat.Coprime n (l : Nat)) (ht : Nat.Coprime t (l : Nat))
    (c : Units (ZMod ((l : Nat) ^ (a + 2)))) :
    (Finset.univ.sum (fun i : Fin (l : Nat) =>
      kernel (weight ((l : Nat) ^ (a + 2)) l) (c * nativePositionUnit l a n t i.val hn))) /
        ((l : Nat) : Real) = 1 := by
  rw [native_progression_sum l a hTwo n t hn ht c]
  apply div_self
  exact_mod_cast l.property.ne_zero

theorem native_signed_progression_sum (l : Nat.Primes) (a : Nat)
    (hTwo : Not ((l : Nat) = 2)) (n t : Nat)
    (hn : Nat.Coprime n (l : Nat)) (ht : Nat.Coprime t (l : Nat))
    (c : Units (ZMod ((l : Nat) ^ (a + 2)))) (B : Real) :
    Finset.univ.sum (fun i : Fin (l : Nat) =>
      kernel (weight ((l : Nat) ^ (a + 2)) l) (c * nativePositionUnit l a n t i.val hn) * B) =
        ((l : Nat) : Real) * B := by
  rw [<- Finset.sum_mul, native_progression_sum l a hTwo n t hn ht c]

end PrimeFactorOscillations.CarmichaelWildAverages
