/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelCRTKernel
import PrimeFactorOscillations.Assembly.CarmichaelLocalSharpness

/-!
# A genuine character attains the entire native spectral conductor

The full prime-power CRT upper compression is matched to the actual
mixed-character lower construction. Every admissible native kernel has
a nonprincipal survivor whose conductor is the least simultaneous kernel
modulus. The global coefficient is the original flat coefficient.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelMaximalConductor

open CarmichaelPrimePacket CarmichaelCorrelation CarmichaelCorrelationSpectrum
open CarmichaelConductorAssembly CarmichaelSpectralConductor CarmichaelCRTKernel
open CarmichaelLocalSharpness

local instance primaryNeZero (q : Nat) (p : q.primeFactors) :
    NeZero (primaryLevel q p) :=
  NeZero.mk (pow_ne_zero _ (Nat.mem_primeFactors.mp p.property).1.ne_zero)

theorem primary_conductors_coprime (q : Nat) [NeZero q]
    (p r : q.primeFactors) (hNe : Not (p = r))
    (chi : DirichletCharacter Complex (primaryLevel q p))
    (psi : DirichletCharacter Complex (primaryLevel q r)) :
    Nat.Coprime chi.conductor psi.conductor := by
  have hBase : Nat.Coprime (primaryLevel q p) (primaryLevel q r) :=
    @Nat.pairwise_coprime_pow_primeFactors_factorization q p r hNe
  exact Nat.Coprime.of_dvd_left chi.conductor_dvd_level
    (Nat.Coprime.of_dvd_right psi.conductor_dvd_level hBase)

theorem primary_has_sharp_mode (q : Nat) [NeZero q]
    (l : Nat.Primes) (p : q.primeFactors)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod (primaryLevel q p))))) :
    exists chi : DirichletCharacter Complex (primaryLevel q p),
      Not (chi = 1) /\ Not (coefficient (weight (primaryLevel q p) l) chi = 0) /\
        chi.conductor = spectralConductor (primaryLevel q p) l := by
  have hPrime := (Nat.mem_primeFactors.mp p.property).1
  let r : Nat.Primes := Subtype.mk p.val hPrime
  letI : NeZero p.val := NeZero.mk hPrime.ne_zero
  have hPos : 0 < q.factorization p.val :=
    hPrime.factorization_pos_of_dvd (NeZero.ne q)
      (Nat.mem_primeFactors.mp p.property).2.1
  have hEq : q.factorization p.val = (q.factorization p.val - 1) + 1 := by omega
  let P : Nat -> Prop := fun e =>
    Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod (p.val ^ e)))) ->
      exists chi : DirichletCharacter Complex (p.val ^ e),
        Not (chi = 1) /\ Not (coefficient (weight (p.val ^ e) l) chi = 0) /\
          chi.conductor = spectralConductor (p.val ^ e) l
  have hP : P ((q.factorization p.val - 1) + 1) := by
    intro h
    exact prime_power_has_sharp_mode r l (q.factorization p.val - 1) h
  have hAt : P (q.factorization p.val) := Eq.mp (congrArg P hEq.symm) hP
  exact hAt hDiv

theorem conductor_product_and_sharp_mode
    (q : Nat) [NeZero q] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q)))) :
    And (spectralConductor q l =
      (Finset.univ.filter (fun p : q.primeFactors =>
        Not (Dvd.dvd (Monoid.exponent (Units (ZMod (primaryLevel q p))))
          (Monoid.exponent (Units (ZMod q)) / (l : Nat))))).prod
        (fun p => spectralConductor (primaryLevel q p) l))
      (exists chi : DirichletCharacter Complex q,
        Not (chi = 1) /\ Not (coefficient (weight q l) chi = 0) /\
          chi.conductor = spectralConductor q l /\
            coefficient (weight q l) chi = 1 / ((index q l : Real) - 1) ^ 2) := by
  classical
  let S : Finset q.primeFactors := Finset.univ.filter (fun p =>
    Not (Dvd.dvd (Monoid.exponent (Units (ZMod (primaryLevel q p))))
      (Monoid.exponent (Units (ZMod q)) / (l : Nat))))
  have hS (p : q.primeFactors) :
      Membership.mem S p <->
        Not (Dvd.dvd (Monoid.exponent (Units (ZMod (primaryLevel q p))))
          (Monoid.exponent (Units (ZMod q)) / (l : Nat))) := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  have hDivLocal (p : q.primeFactors)
      (hActive : Not (Dvd.dvd (Monoid.exponent (Units (ZMod (primaryLevel q p))))
        (Monoid.exponent (Units (ZMod q)) / (l : Nat)))) :
      Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod (primaryLevel q p)))) := by
    have hEL := MonoidHom.exponent_dvd (f := ZMod.unitsMap (primaryLevel_dvd q p))
      (ZMod.unitsMap_surjective (primaryLevel_dvd q p))
    have hE : 0 < Monoid.exponent (Units (ZMod (primaryLevel q p))) :=
      Nat.pos_of_ne_zero (Monoid.exponent_ne_zero_of_finite
        (G := Units (ZMod (primaryLevel q p))))
    exact ((active_period_iff _ _ l hE hEL hDiv).mp hActive).left
  have hEach (p : q.primeFactors) :
      exists chi : DirichletCharacter Complex (primaryLevel q p),
        Not (Dvd.dvd (Monoid.exponent (Units (ZMod (primaryLevel q p))))
          (Monoid.exponent (Units (ZMod q)) / (l : Nat))) ->
          And (Not (coefficient (weight (primaryLevel q p) l) chi = 0))
            (chi.conductor = spectralConductor (primaryLevel q p) l) := by
    by_cases hActive : Not (Dvd.dvd (Monoid.exponent (Units (ZMod (primaryLevel q p))))
        (Monoid.exponent (Units (ZMod q)) / (l : Nat)))
    . choose chi hChi hNonzero hCond using primary_has_sharp_mode q l p (hDivLocal p hActive)
      exact Exists.intro chi (fun _ => And.intro hNonzero hCond)
    . exact Exists.intro 1 (fun h => (hActive h).elim)
  choose chi hChi using hEach
  let Phi := S.prod (fun p => DirichletCharacter.changeLevel (primaryLevel_dvd q p) (chi p))
  let M := S.prod (fun p => (chi p).conductor)
  have hPair : forall p, Membership.mem S p -> forall r, Membership.mem S r ->
      Not (p = r) -> Nat.Coprime (chi p).conductor (chi r).conductor := by
    intro p _ r _ hNe
    exact primary_conductors_coprime q p r hNe (chi p) (chi r)
  have hSurvive : forall p, Membership.mem S p ->
      Not (coefficient (weight (primaryLevel q p) l) (chi p) = 0) := by
    intro p hp
    exact (hChi p ((hS p).mp hp)).left
  have hData := active_divisor_product q l hDiv S (primaryLevel q) (primaryLevel_dvd q)
    chi (fun p hp => (hS p).mp hp) hSurvive hPair
  have hAlive : Not (coefficient (weight q l) Phi = 0) := hData.left
  have hCond : Phi.conductor = M := hData.right.left
  have hMLevel : Dvd.dvd M q := by
    have h := Phi.conductor_dvd_level
    rwa [hCond] at h
  have hMNonzero : Not (M = 0) := by
    intro h
    exact Phi.conductor_ne_zero (hCond.trans h)
  letI : NeZero M := NeZero.mk hMNonzero
  letI : forall p : q.primeFactors, NeZero ((chi p).conductor) :=
    fun p => NeZero.mk (chi p).conductor_ne_zero
  have hFM (p : q.primeFactors)
      (hActive : Not (Dvd.dvd (Monoid.exponent (Units (ZMod (primaryLevel q p))))
        (Monoid.exponent (Units (ZMod q)) / (l : Nat)))) :
      Dvd.dvd (chi p).conductor M :=
    Finset.dvd_prod_of_mem (fun r => (chi r).conductor) ((hS p).mpr hActive)
  have hLocal : forall p : q.primeFactors,
      Not (Dvd.dvd (Monoid.exponent (Units (ZMod (primaryLevel q p))))
        (Monoid.exponent (Units (ZMod q)) / (l : Nat))) ->
      forall a b : Units (ZMod (primaryLevel q p)),
        ZMod.unitsMap (chi p).conductor_dvd_level a =
          ZMod.unitsMap (chi p).conductor_dvd_level b ->
            kernel (weight (primaryLevel q p) l) a =
              kernel (weight (primaryLevel q p) l) b := by
    intro p hActive a b hReduce
    have hAll : forall psi : DirichletCharacter Complex (primaryLevel q p),
        Not (coefficient (weight (primaryLevel q p) l) psi = 0) ->
          Dvd.dvd psi.conductor (chi p).conductor := by
      intro psi hPsi
      rw [(hChi p hActive).right]
      exact (spectralConductor_dvd_iff (primaryLevel q p) l
        (spectralConductor (primaryLevel q p) l)).mp (dvd_refl _) psi hPsi
    exact (kernel_reduction_iff_survivor_conductors (primaryLevel q p) (chi p).conductor
      l (hDivLocal p hActive) (chi p).conductor_dvd_level).mpr hAll a b hReduce
  have hUpper : Dvd.dvd (spectralConductor q l) M :=
    spectralConductor_dvd_of_active_local_reductions q M l hDiv hMLevel
      (fun p => (chi p).conductor) (fun p => (chi p).conductor_dvd_level) hFM hLocal
  have hLower : Dvd.dvd M (spectralConductor q l) :=
    active_product_conductor_dvd_spectral q l hDiv S (primaryLevel q) (primaryLevel_dvd q)
      chi (fun p hp => (hS p).mp hp) hSurvive hPair
  have hEqual : spectralConductor q l = M := Nat.dvd_antisymm hUpper hLower
  have hNotOne : Not (M = 1) := by
    intro h
    exact spectralConductor_ne_one q l hDiv (hEqual.trans h)
  have hNotPrincipal : Not (Phi = 1) := by
    intro h
    apply hNotOne
    rw [<- hCond, h, DirichletCharacter.conductor_one]
  have hProduct : spectralConductor q l =
      S.prod (fun p => spectralConductor (primaryLevel q p) l) := by
    calc
      _ = M := hEqual
      _ = _ := Finset.prod_congr rfl (fun p hp => (hChi p ((hS p).mp hp)).right)
  exact And.intro hProduct (Exists.intro Phi (And.intro hNotPrincipal
    (And.intro hAlive (And.intro (hCond.trans hEqual.symm) (hData.right.right hNotOne)))))

theorem spectralConductor_eq_active_primary_product
    (q : Nat) [NeZero q] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q)))) :
    spectralConductor q l =
      (Finset.univ.filter (fun p : q.primeFactors =>
        Not (Dvd.dvd (Monoid.exponent (Units (ZMod (primaryLevel q p))))
          (Monoid.exponent (Units (ZMod q)) / (l : Nat))))).prod
        (fun p => spectralConductor (primaryLevel q p) l) :=
  (conductor_product_and_sharp_mode q l hDiv).left

theorem exists_maximal_conductor_survivor
    (q : Nat) [NeZero q] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q)))) :
    exists chi : DirichletCharacter Complex q,
      Not (chi = 1) /\ Not (coefficient (weight q l) chi = 0) /\
        chi.conductor = spectralConductor q l /\
          coefficient (weight q l) chi = 1 / ((index q l : Real) - 1) ^ 2 :=
  (conductor_product_and_sharp_mode q l hDiv).right

end PrimeFactorOscillations.CarmichaelMaximalConductor
