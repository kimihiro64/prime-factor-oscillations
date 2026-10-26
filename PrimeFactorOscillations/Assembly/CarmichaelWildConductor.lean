/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelPrimePacketSpectrum
import PrimeFactorOscillations.Helpers.PrimeOrderReturnIndex
import PrimeFactorOscillations.Helpers.PrimePowerWildCharacterConductor

/-!
# Native odd-wild prime-square spectral rigidity

The return label is the odd residue prime itself. Admissibility and the
exact image index are proved, every nonprincipal surviving mode has
conductor p^2, and the full original kernel descends to that square.
All Fourier phases, the flat coefficient, and the positive weight bounds
are retained. No analytic principal-wave estimate is asserted.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelWildConductor

open CarmichaelPrimePacket CarmichaelCorrelation CarmichaelCorrelationSpectrum
open CarmichaelPrimePacketSpectrum PrimeOrderReturnLaw
open PrimePowerWildCharacterConductor

local instance primeLabelNeZero (l : Nat.Primes) : NeZero (l : Nat) :=
  NeZero.mk l.property.ne_zero

theorem wild_index_eq_label (l : Nat.Primes) (a : Nat)
    (hTwo : Not ((l : Nat) = 2)) :
    index ((l : Nat) ^ (a + 2)) l = (l : Nat) := by
  let G := Units (ZMod ((l : Nat) ^ (a + 2)))
  let : IsCyclic G :=
    ZMod.isCyclic_units_of_prime_pow (l : Nat) l.property hTwo (a + 2)
  let n := Fintype.card G
  have hn : 0 < n := Fintype.card_pos
  have hDiv : Dvd.dvd (l : Nat) n := by
    have h := prime_dvd_exponent (l : Nat) a l.property
    rw [IsCyclic.exponent_eq_card, Nat.card_eq_fintype_card] at h
    exact h
  have hNot : Not (Dvd.dvd n (n / (l : Nat))) := by
    intro h
    have hPos : 0 < n / (l : Nat) :=
      Nat.div_pos (Nat.le_of_dvd hn hDiv) l.property.pos
    have hLe := Nat.le_of_dvd hPos h
    exact (not_le_of_gt (Nat.div_lt_self hn l.property.one_lt)) hLe
  change returnIndex (G := G) (Monoid.exponent G) (l : Nat) = (l : Nat)
  rw [PrimeOrderReturnIndex.returnIndex_cyclic, IsCyclic.exponent_eq_card,
    Nat.card_eq_fintype_card]
  change n / Nat.gcd n (n / (l : Nat)) = (l : Nat)
  rw [PrimeOrderReturnIndex.local_period_ratio n n l hn (dvd_refl n) hDiv,
    ite_eq_right hNot]

theorem wild_kernel_closed (l : Nat.Primes) (a : Nat)
    (hTwo : Not ((l : Nat) = 2))
    (u : Units (ZMod ((l : Nat) ^ (a + 2)))) :
    kernel (weight ((l : Nat) ^ (a + 2)) l) u =
      1 + ((if CarmichaelCorrelationLocal.returnBit
          (Monoid.exponent (Units (ZMod ((l : Nat) ^ (a + 2)))))
          (l : Nat) u then ((l : Nat) : Real) else 0) - 1) /
        (((l : Nat) : Real) - 1) ^ 2 := by
  rw [kernel_closed _ l (prime_dvd_exponent (l : Nat) a l.property) u,
    wild_index_eq_label l a hTwo]

theorem wild_survivor_factorsThrough (l : Nat.Primes) (a : Nat)
    (hTwo : Not ((l : Nat) = 2))
    (chi : DirichletCharacter Complex ((l : Nat) ^ (a + 2)))
    (hNonzero : Not (coefficient (weight ((l : Nat) ^ (a + 2)) l) chi = 0)) :
    chi.FactorsThrough ((l : Nat) ^ 2) :=
  odd_wild_factorsThrough (l : Nat) a l.property hTwo chi
    (nonzero_coefficient_prime_power _ l
      (prime_dvd_exponent (l : Nat) a l.property) chi hNonzero)

theorem wild_nonprincipal_survivor_conductor (l : Nat.Primes) (a : Nat)
    (hTwo : Not ((l : Nat) = 2))
    (chi : DirichletCharacter Complex ((l : Nat) ^ (a + 2)))
    (hNonzero : Not (coefficient (weight ((l : Nat) ^ (a + 2)) l) chi = 0))
    (hChi : Not (chi = 1)) :
    chi.conductor = (l : Nat) ^ 2 :=
  odd_wild_nonprincipal_conductor (l : Nat) a l.property hTwo chi
    (nonzero_coefficient_prime_power _ l
      (prime_dvd_exponent (l : Nat) a l.property) chi hNonzero) hChi

theorem wild_kernel_eq_of_reduction_eq (l : Nat.Primes) (a : Nat)
    (hTwo : Not ((l : Nat) = 2))
    (u v : Units (ZMod ((l : Nat) ^ (a + 2))))
    (hReduce : ZMod.unitsMap (primeSquare_dvd_level (l : Nat) a) u =
      ZMod.unitsMap (primeSquare_dvd_level (l : Nat) a) v) :
    kernel (weight ((l : Nat) ^ (a + 2)) l) u =
      kernel (weight ((l : Nat) ^ (a + 2)) l) v := by
  classical
  apply Complex.ofReal_injective
  rw [kernel_expansion, kernel_expansion]
  apply Finset.sum_congr rfl
  intro chi _
  by_cases hZero : coefficient (weight ((l : Nat) ^ (a + 2)) l) chi = 0
  . simp only [hZero, Complex.ofReal_zero, zero_mul]
  . apply congrArg (fun z : Complex =>
      (coefficient (weight ((l : Nat) ^ (a + 2)) l) chi : Complex) * z)
    choose hd psi hEquality using wild_survivor_factorsThrough l a hTwo chi hZero
    have hInv : ZMod.unitsMap hd (Inv.inv u) = ZMod.unitsMap hd (Inv.inv v) := by
      simpa only [map_inv] using
        congrArg (fun z : Units (ZMod ((l : Nat) ^ 2)) => Inv.inv z) hReduce
    have hUnits : chi.toUnitHom (Inv.inv u) = chi.toUnitHom (Inv.inv v) := by
      rw [hEquality, DirichletCharacter.changeLevel_toUnitHom]
      exact congrArg psi.toUnitHom hInv
    have hValues := congrArg (fun z : Units Complex => (z : Complex)) hUnits
    change chi (Units.val (Inv.inv u)) = chi (Units.val (Inv.inv v))
    simpa only [MulChar.coe_toUnitHom] using hValues

theorem wild_kernel_descends_to_primeSquare (l : Nat.Primes) (a : Nat)
    (hTwo : Not ((l : Nat) = 2)) :
    exists k : Units (ZMod ((l : Nat) ^ 2)) -> Real,
      forall u : Units (ZMod ((l : Nat) ^ (a + 2))),
        kernel (weight ((l : Nat) ^ (a + 2)) l) u =
          k (ZMod.unitsMap (primeSquare_dvd_level (l : Nat) a) u) := by
  let lift : Units (ZMod ((l : Nat) ^ 2)) ->
      Units (ZMod ((l : Nat) ^ (a + 2))) :=
    fun v => Classical.choose
      (ZMod.unitsMap_surjective (primeSquare_dvd_level (l : Nat) a) v)
  have hLift (v : Units (ZMod ((l : Nat) ^ 2))) :
      ZMod.unitsMap (primeSquare_dvd_level (l : Nat) a) (lift v) = v :=
    Classical.choose_spec
      (ZMod.unitsMap_surjective (primeSquare_dvd_level (l : Nat) a) v)
  refine Exists.intro
    (fun v => kernel (weight ((l : Nat) ^ (a + 2)) l) (lift v)) ?_
  intro u
  exact wild_kernel_eq_of_reduction_eq l a hTwo u
    (lift (ZMod.unitsMap (primeSquare_dvd_level (l : Nat) a) u))
    (hLift (ZMod.unitsMap (primeSquare_dvd_level (l : Nat) a) u)).symm

theorem exists_wild_primeSquare_conductor_survivor (l : Nat.Primes) (a : Nat)
    (hTwo : Not ((l : Nat) = 2)) :
    exists chi : DirichletCharacter Complex ((l : Nat) ^ (a + 2)),
      Not (chi = 1) /\ chi.conductor = (l : Nat) ^ 2 /\
        coefficient (weight ((l : Nat) ^ (a + 2)) l) chi =
          1 / (((l : Nat) : Real) - 1) ^ 2 := by
  choose chi hChi hPower hCoefficient using
    exists_nonprincipal_prime_character ((l : Nat) ^ (a + 2)) l
      (prime_dvd_exponent (l : Nat) a l.property)
  refine Exists.intro chi (And.intro hChi (And.intro
    (odd_wild_nonprincipal_conductor (l : Nat) a l.property hTwo chi hPower hChi) ?_))
  simpa only [wild_index_eq_label l a hTwo] using hCoefficient

theorem wild_native_weight_bounds (l : Nat.Primes) (a : Nat)
    (hTwo : Not ((l : Nat) = 2))
    (u : Units (ZMod ((l : Nat) ^ (a + 2)))) :
    And ((3 / 4 : Real) <= kernel (weight ((l : Nat) ^ (a + 2)) l) u)
      (kernel (weight ((l : Nat) ^ (a + 2)) l) u <= 3 / 2) := by
  have hIndex : 3 <= index ((l : Nat) ^ (a + 2)) l := by
    rw [wild_index_eq_label l a hTwo]
    have h := l.property.two_le
    omega
  exact kernel_bounds_of_index_ge_three _ l
    (prime_dvd_exponent (l : Nat) a l.property) hIndex u

end PrimeFactorOscillations.CarmichaelWildConductor
