/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import Mathlib.Data.Nat.GCD.BigOperators
import PrimeFactorOscillations.Assembly.CarmichaelSpectralConductor
import PrimeFactorOscillations.Assembly.CarmichaelTwoPowerConductor

/-!
# Sharp composition of actual native character modes

Local survivors lift through an original global period when the period
inflation is coprime to the return label. Arbitrarily many such modes
combine without losing survival. Pairwise coprime true conductors multiply
exactly; the resulting coefficient uses the global index, not a product
of local coefficients. The exceptional modulus-eight sharp witness is
constructed from the previously proved modulus-sixteen mode.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelConductorAssembly

open CarmichaelPrimePacket CarmichaelCorrelation CarmichaelCorrelationSpectrum
open CarmichaelPrimePacketSpectrum CarmichaelTwoPowerConductor

theorem conductor_dvd_product_conductor (q : Nat) [NeZero q]
    (chi psi : DirichletCharacter Complex q)
    (hCop : Nat.Coprime chi.conductor psi.conductor) :
    Dvd.dvd chi.conductor (chi * psi).conductor := by
  have h := DirichletCharacter.conductor_mul_dvd_lcm_conductor (chi * psi) (Inv.inv psi)
  rw [mul_inv_cancel_right, DirichletCharacter.conductor_inv] at h
  exact hCop.dvd_of_dvd_mul_right (dvd_trans h (Nat.lcm_dvd_mul _ _))

theorem conductor_mul_eq_mul (q : Nat) [NeZero q]
    (chi psi : DirichletCharacter Complex q)
    (hCop : Nat.Coprime chi.conductor psi.conductor) :
    (chi * psi).conductor = chi.conductor * psi.conductor := by
  apply Nat.dvd_antisymm
  . rw [<- hCop.lcm_eq_mul]
    exact DirichletCharacter.conductor_mul_dvd_lcm_conductor chi psi
  . apply hCop.mul_dvd_of_dvd_of_dvd
    . exact conductor_dvd_product_conductor q chi psi hCop
    . simpa only [mul_comm] using conductor_dvd_product_conductor q psi chi hCop.symm

theorem conductor_finset_prod {I : Type*} (q : Nat) [NeZero q]
    (S : Finset I) (chi : I -> DirichletCharacter Complex q)
    (hPair : forall i, Membership.mem S i -> forall j, Membership.mem S j ->
      Not (i = j) -> Nat.Coprime (chi i).conductor (chi j).conductor) :
    (S.prod chi).conductor = S.prod (fun i => (chi i).conductor) := by
  classical
  revert hPair
  induction S using Finset.induction_on with
  | empty =>
    intro _
    simp only [Finset.prod_empty, DirichletCharacter.conductor_one]
  | @insert a S ha ih =>
    intro hPair
    have hPairS : forall i, Membership.mem S i -> forall j, Membership.mem S j ->
        Not (i = j) -> Nat.Coprime (chi i).conductor (chi j).conductor := by
      intro i hi j hj hNe
      exact hPair i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hNe
    have hCond := ih hPairS
    have hCop : Nat.Coprime (chi a).conductor (S.prod chi).conductor := by
      rw [hCond]
      apply Nat.Coprime.prod_right
      intro b hb
      apply hPair a (Finset.mem_insert_self a S) b (Finset.mem_insert_of_mem hb)
      intro h
      subst b
      exact ha hb
    rw [Finset.prod_insert ha, conductor_mul_eq_mul q _ _ hCop,
      hCond, Finset.prod_insert ha]

theorem coprime_power_preserves_return {G : Type*} [Group G]
    (u : G) (E l m : Nat) (hDiv : Dvd.dvd l E)
    (hAnn : u ^ E = 1) (hCop : Nat.Coprime m l) :
    u ^ ((E / l) * m) = 1 <-> u ^ (E / l) = 1 := by
  constructor
  . intro h
    let v := u ^ (E / l)
    have hM : v ^ m = 1 := by
      rw [<- pow_mul]
      exact h
    have hL : v ^ l = 1 := by
      change (u ^ (E / l)) ^ l = 1
      rw [<- pow_mul, Nat.div_mul_cancel hDiv, hAnn]
    have hOrder : Dvd.dvd (orderOf v) 1 := by
      have hBoth := Nat.dvd_gcd
        (orderOf_dvd_iff_pow_eq_one.mpr hM)
        (orderOf_dvd_iff_pow_eq_one.mpr hL)
      rwa [hCop.gcd_eq_one] at hBoth
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hOrder)
  . intro h
    rw [pow_mul, h, one_pow]

theorem inflated_period_return_iff {G : Type*} [Group G]
    (u : G) (E l m : Nat) (hDiv : Dvd.dvd l E)
    (hAnn : u ^ E = 1) (hCop : Nat.Coprime m l) :
    u ^ ((E * m) / l) = 1 <-> u ^ (E / l) = 1 := by
  have hQuot : (E * m) / l = (E / l) * m := by
    rw [Nat.mul_comm E m, Nat.mul_div_assoc m hDiv, Nat.mul_comm m (E / l)]
  rw [hQuot]
  exact coprime_power_preserves_return u E l m hDiv hAnn hCop

theorem active_period_iff (E L : Nat) (l : Nat.Primes)
    (hE : 0 < E) (hEL : Dvd.dvd E L) (hDiv : Dvd.dvd (l : Nat) L) :
    Not (Dvd.dvd E (L / (l : Nat))) <->
      And (Dvd.dvd (l : Nat) E) (Nat.Coprime (L / E) (l : Nat)) := by
  have hL : L = E * (L / E) := (Nat.mul_div_cancel' hEL).symm
  constructor
  . intro hActive
    have hNotDiv : Not (Dvd.dvd (l : Nat) (L / E)) := by
      intro h
      apply hActive
      rw [hL, Nat.mul_div_assoc E h]
      exact dvd_mul_right E _
    have hCop : Nat.Coprime (L / E) (l : Nat) :=
      ((l.property.coprime_iff_not_dvd).mpr hNotDiv).symm
    have hProduct : Dvd.dvd (l : Nat) (E * (L / E)) := by
      rw [<- hL]
      exact hDiv
    exact And.intro ((l.property.dvd_mul.mp hProduct).resolve_right hNotDiv) hCop
  . intro h hRet
    choose t ht using hRet
    have hScaled : Dvd.dvd (E * (l : Nat)) L := by
      refine Exists.intro t ?_
      calc
        L = (L / (l : Nat)) * (l : Nat) := (Nat.div_mul_cancel hDiv).symm
        _ = (E * t) * (l : Nat) := by rw [ht]
        _ = (E * (l : Nat)) * t := by ring
    rw [hL] at hScaled
    have hLabel : Dvd.dvd (l : Nat) (L / E) :=
      Nat.dvd_of_mul_dvd_mul_left hE hScaled
    have hOne : Dvd.dvd (l : Nat) 1 := by
      have hBoth := Nat.dvd_gcd hLabel (dvd_refl (l : Nat))
      rwa [h.right.gcd_eq_one] at hBoth
    exact l.property.ne_one (Nat.dvd_one.mp hOne)


theorem active_lift_survives (q d m : Nat) [NeZero q] [NeZero d]
    (l : Nat.Primes)
    (hDivQ : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (hDivD : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod d))))
    (hd : Dvd.dvd d q)
    (hPeriod : Monoid.exponent (Units (ZMod q)) =
      Monoid.exponent (Units (ZMod d)) * m)
    (hCop : Nat.Coprime m (l : Nat))
    (chi : DirichletCharacter Complex d)
    (hNonzero : Not (coefficient (weight d l) chi = 0)) :
    Not (coefficient (weight q l) (DirichletCharacter.changeLevel hd chi) = 0) := by
  apply (coefficient_nonzero_iff_trivial_return q l hDivQ _).mpr
  intro u hReturn
  have hMapped : (ZMod.unitsMap hd u) ^
      (Monoid.exponent (Units (ZMod q)) / (l : Nat)) = 1 := by
    simpa only [map_pow, map_one] using congrArg (ZMod.unitsMap hd) hReturn
  rw [hPeriod] at hMapped
  have hLocal := (inflated_period_return_iff (ZMod.unitsMap hd u)
    (Monoid.exponent (Units (ZMod d))) (l : Nat) m hDivD
      (Monoid.pow_exponent_eq_one _) hCop).mp hMapped
  have hValue := (coefficient_nonzero_iff_trivial_return d l hDivD chi).mp
    hNonzero (ZMod.unitsMap hd u) hLocal
  have hUnits : (DirichletCharacter.changeLevel hd chi).toUnitHom u = 1 := by
    rw [DirichletCharacter.changeLevel_toUnitHom]
    change chi.toUnitHom (ZMod.unitsMap hd u) = 1
    apply Units.ext
    exact hValue
  have h := congrArg (fun z : Units Complex => (z : Complex)) hUnits
  simpa only [MulChar.coe_toUnitHom, Units.val_one] using h

theorem active_divisor_lift_survives (q d : Nat) [NeZero q] [NeZero d]
    (l : Nat.Primes)
    (hDivQ : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (hd : Dvd.dvd d q)
    (hActive : Not (Dvd.dvd (Monoid.exponent (Units (ZMod d)))
      (Monoid.exponent (Units (ZMod q)) / (l : Nat))))
    (chi : DirichletCharacter Complex d)
    (hNonzero : Not (coefficient (weight d l) chi = 0)) :
    Not (coefficient (weight q l) (DirichletCharacter.changeLevel hd chi) = 0) := by
  have hEL := MonoidHom.exponent_dvd (f := ZMod.unitsMap hd) (ZMod.unitsMap_surjective hd)
  have hE : 0 < Monoid.exponent (Units (ZMod d)) :=
    Nat.pos_of_ne_zero (Monoid.exponent_ne_zero_of_finite (G := Units (ZMod d)))
  have hData := (active_period_iff _ _ l hE hEL hDivQ).mp hActive
  exact active_lift_survives q d
    (Monoid.exponent (Units (ZMod q)) / Monoid.exponent (Units (ZMod d)))
    l hDivQ hData.left hd (Nat.mul_div_cancel' hEL).symm hData.right chi hNonzero


theorem multiply_survivors (q : Nat) [NeZero q] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (chi psi : DirichletCharacter Complex q)
    (hChi : Not (coefficient (weight q l) chi = 0))
    (hPsi : Not (coefficient (weight q l) psi = 0)) :
    Not (coefficient (weight q l) (chi * psi) = 0) := by
  apply (coefficient_nonzero_iff_trivial_return q l hDiv _).mpr
  intro u hu
  change chi (u : ZMod q) * psi (u : ZMod q) = 1
  rw [(coefficient_nonzero_iff_trivial_return q l hDiv chi).mp hChi u hu,
    (coefficient_nonzero_iff_trivial_return q l hDiv psi).mp hPsi u hu, one_mul]

theorem prod_survives {I : Type*} (q : Nat) [NeZero q] (l : Nat.Primes)
    (hDiv : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (S : Finset I) (chi : I -> DirichletCharacter Complex q)
    (hS : forall i, Membership.mem S i -> Not (coefficient (weight q l) (chi i) = 0)) :
    Not (coefficient (weight q l) (S.prod chi) = 0) := by
  classical
  revert hS
  induction S using Finset.induction_on with
  | empty =>
    intro _
    rw [Finset.prod_empty, coefficient_principal _ (weightSum_pos q l hDiv)]
    norm_num
  | @insert a S ha ih =>
    intro hS
    rw [Finset.prod_insert ha]
    exact multiply_survivors q l hDiv (chi a) (S.prod chi)
      (hS a (Finset.mem_insert_self a S))
      (ih (fun i hi => hS i (Finset.mem_insert_of_mem hi)))

theorem active_local_product {I : Type*}
    (q : Nat) [NeZero q] (l : Nat.Primes)
    (hDivQ : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (S : Finset I) (d m : I -> Nat) [forall i, NeZero (d i)]
    (hd : forall i, Dvd.dvd (d i) q)
    (chi : forall i, DirichletCharacter Complex (d i))
    (hDivD : forall i, Membership.mem S i ->
      Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod (d i)))))
    (hPeriod : forall i, Membership.mem S i ->
      Monoid.exponent (Units (ZMod q)) = Monoid.exponent (Units (ZMod (d i))) * m i)
    (hCop : forall i, Membership.mem S i -> Nat.Coprime (m i) (l : Nat))
    (hSurvive : forall i, Membership.mem S i ->
      Not (coefficient (weight (d i) l) (chi i) = 0))
    (hPair : forall i, Membership.mem S i -> forall j, Membership.mem S j ->
      Not (i = j) -> Nat.Coprime (chi i).conductor (chi j).conductor) :
    let psi := S.prod (fun i => DirichletCharacter.changeLevel (hd i) (chi i))
    And (Not (coefficient (weight q l) psi = 0))
      (And (psi.conductor = S.prod (fun i => (chi i).conductor))
        (Not (S.prod (fun i => (chi i).conductor) = 1) ->
          coefficient (weight q l) psi = 1 / ((index q l : Real) - 1) ^ 2)) := by
  classical
  dsimp only
  let psi := S.prod (fun i => DirichletCharacter.changeLevel (hd i) (chi i))
  have hAlive : Not (coefficient (weight q l) psi = 0) := by
    apply prod_survives q l hDivQ
    intro i hi
    exact active_lift_survives q (d i) (m i) l hDivQ
      (hDivD i hi) (hd i) (hPeriod i hi) (hCop i hi) (chi i) (hSurvive i hi)
  have hCond : psi.conductor = S.prod (fun i => (chi i).conductor) := by
    calc
      _ = S.prod (fun i => (DirichletCharacter.changeLevel (hd i) (chi i)).conductor) := by
        apply conductor_finset_prod q
        intro i hi j hj hNe
        simpa only [DirichletCharacter.conductor_changeLevel] using hPair i hi j hj hNe
      _ = _ := Finset.prod_congr rfl (fun i _ => DirichletCharacter.conductor_changeLevel _ _)
  refine And.intro hAlive (And.intro hCond ?_)
  intro hNotOne
  have hNotPrincipal : Not (psi = 1) := by
    intro h
    apply hNotOne
    rw [<- hCond, h, DirichletCharacter.conductor_one]
  exact coefficient_of_trivial_return q l hDivQ psi hNotPrincipal
    ((coefficient_nonzero_iff_trivial_return q l hDivQ psi).mp hAlive)

theorem active_divisor_product {I : Type*}
    (q : Nat) [NeZero q] (l : Nat.Primes)
    (hDivQ : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (S : Finset I) (d : I -> Nat) [forall i, NeZero (d i)]
    (hd : forall i, Dvd.dvd (d i) q)
    (chi : forall i, DirichletCharacter Complex (d i))
    (hActive : forall i, Membership.mem S i ->
      Not (Dvd.dvd (Monoid.exponent (Units (ZMod (d i))))
        (Monoid.exponent (Units (ZMod q)) / (l : Nat))))
    (hSurvive : forall i, Membership.mem S i ->
      Not (coefficient (weight (d i) l) (chi i) = 0))
    (hPair : forall i, Membership.mem S i -> forall j, Membership.mem S j ->
      Not (i = j) -> Nat.Coprime (chi i).conductor (chi j).conductor) :
    let psi := S.prod (fun i => DirichletCharacter.changeLevel (hd i) (chi i))
    And (Not (coefficient (weight q l) psi = 0))
      (And (psi.conductor = S.prod (fun i => (chi i).conductor))
        (Not (S.prod (fun i => (chi i).conductor) = 1) ->
          coefficient (weight q l) psi = 1 / ((index q l : Real) - 1) ^ 2)) := by
  have hData (i : I) (hi : Membership.mem S i) :
      And (Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod (d i)))))
        (Nat.Coprime (Monoid.exponent (Units (ZMod q)) /
          Monoid.exponent (Units (ZMod (d i)))) (l : Nat)) := by
    have hEL := MonoidHom.exponent_dvd (f := ZMod.unitsMap (hd i))
      (ZMod.unitsMap_surjective (hd i))
    have hE : 0 < Monoid.exponent (Units (ZMod (d i))) :=
      Nat.pos_of_ne_zero (Monoid.exponent_ne_zero_of_finite (G := Units (ZMod (d i))))
    exact (active_period_iff _ _ l hE hEL hDivQ).mp (hActive i hi)
  exact active_local_product q l hDivQ S d
    (fun i => Monoid.exponent (Units (ZMod q)) / Monoid.exponent (Units (ZMod (d i))))
    hd chi (fun i hi => (hData i hi).left)
    (fun i _ => (Nat.mul_div_cancel'
      (MonoidHom.exponent_dvd (f := ZMod.unitsMap (hd i))
        (ZMod.unitsMap_surjective (hd i)))).symm)
    (fun i hi => (hData i hi).right) hSurvive hPair


theorem active_product_conductor_dvd_spectral {I : Type*}
    (q : Nat) [NeZero q] (l : Nat.Primes)
    (hDivQ : Dvd.dvd (l : Nat) (Monoid.exponent (Units (ZMod q))))
    (S : Finset I) (d : I -> Nat) [forall i, NeZero (d i)]
    (hd : forall i, Dvd.dvd (d i) q)
    (chi : forall i, DirichletCharacter Complex (d i))
    (hActive : forall i, Membership.mem S i ->
      Not (Dvd.dvd (Monoid.exponent (Units (ZMod (d i))))
        (Monoid.exponent (Units (ZMod q)) / (l : Nat))))
    (hSurvive : forall i, Membership.mem S i ->
      Not (coefficient (weight (d i) l) (chi i) = 0))
    (hPair : forall i, Membership.mem S i -> forall j, Membership.mem S j ->
      Not (i = j) -> Nat.Coprime (chi i).conductor (chi j).conductor) :
    Dvd.dvd (S.prod (fun i => (chi i).conductor))
      (CarmichaelSpectralConductor.spectralConductor q l) := by
  let psi := S.prod (fun i => DirichletCharacter.changeLevel (hd i) (chi i))
  have hWitness := active_divisor_product q l hDivQ S d hd chi hActive hSurvive hPair
  have hCond : psi.conductor = S.prod (fun i => (chi i).conductor) := hWitness.right.left
  have hDiv := (CarmichaelSpectralConductor.spectralConductor_dvd_iff q l
    (CarmichaelSpectralConductor.spectralConductor q l)).mp (dvd_refl _) psi hWitness.left
  rwa [hCond] at hDiv


theorem level_eight_nonprincipal_coefficient
    (chi : DirichletCharacter Complex 8) (hChi : Not (chi = 1)) :
    coefficient (weight 8 labelTwo) chi = 1 / 9 := by
  have hQuot : Monoid.exponent (Units (ZMod 8)) / 2 = 1 := by
    change Monoid.exponent (Units (ZMod (2 ^ (0 + 3)))) / 2 = 1
    rw [TwoPowerCharacterConductor.unit_exponent 0]
    decide
  have hTrivial : forall u : Units (ZMod 8),
      u ^ (Monoid.exponent (Units (ZMod 8)) / 2) = 1 ->
        chi (u : ZMod 8) = 1 := by
    intro u hu
    rw [hQuot, pow_one] at hu
    subst u
    simp
  rw [coefficient_of_trivial_return 8 labelTwo (two_divides_exponent 0)
    chi hChi hTrivial, level_eight_index]
  norm_num

theorem exists_level_eight_conductor_eight_survivor :
    exists chi : DirichletCharacter Complex 8,
      Not (chi = 1) /\ chi.conductor = 8 /\
        coefficient (weight 8 labelTwo) chi = 1 / 9 := by
  choose chi hChi hCond hCoefficient using exists_large_conductor_eight_survivor 0
  have hNonzero : Not (coefficient (weight (2 ^ (0 + 4)) labelTwo) chi = 0) := by
    rw [hCoefficient]
    norm_num
  choose hd psi hLift using large_survivor_factorsThrough_eight 0 chi hNonzero
  have hPsiCond : psi.conductor = 8 := by
    have h := DirichletCharacter.conductor_changeLevel psi hd
    rw [<- hLift, hCond] at h
    exact h.symm
  have hPsi : Not (psi = 1) := by
    intro h
    rw [h, DirichletCharacter.conductor_one] at hPsiCond
    norm_num at hPsiCond
  exact Exists.intro psi (And.intro hPsi
    (And.intro hPsiCond (level_eight_nonprincipal_coefficient psi hPsi)))

end PrimeFactorOscillations.CarmichaelConductorAssembly
