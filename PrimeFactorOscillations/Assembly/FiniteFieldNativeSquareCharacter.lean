/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativePrincipalMean

/-!
# Positive numerator characters and their square classes

The classical character fact is supporting arithmetic for the explicit
native agreement classifier. All characters retain their complete modulus.
Square multipliers preserve nonprincipality by the proved prime means,
their exact eventual square-factor identity, and positive band mass.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace PrimeFactorOscillations.FiniteFieldIntegerSignature
open Filter IntegerQuadraticCharacter
open FiniteFieldIntegerWindowTransfer

theorem numerator_character_square_mul_ne_one (a : Nat) (ha : 0 < a)
    (D : Int) (hD : Not (D = 0)) (hchi : Not (numeratorCharacter D hD = 1))
    (hAD : Not ((a : Int) ^ 2 * D = 0)) :
    Not (numeratorCharacter ((a : Int) ^ 2 * D) hAD = 1) := by
  intro hprincipal
  have hmass := principal_prime_correlation_eventually_eq_mass
    ((a : Int) ^ 2 * D) hAD hprincipal
  have hsquare := prime_correlation_square_factor_eventually a ha D
  have heps : (0 : Real) < Real.log 2 / 4 := by positivity
  have hsmall := (fixed_nonprincipal_prime_correlation_tendsto_zero D hD hchi).eventually
    (Iio_mem_nhds heps)
  have hpositive := precise_core_tendsto_atTop.eventually
    eventually_reciprocal_square_band_positive
  choose U hU using (hmass.and (hsquare.and (hsmall.and hpositive))).exists
  have hEq := hU.1
  have hSquare := hU.2.1
  have hSmall := hU.2.2.1
  have hMass := hU.2.2.2
  rw [hEq] at hSquare
  have hlog : 0 < Real.log 2 := by positivity
  linarith only [hSquare, hSmall, hMass, hlog]

theorem squarefree_numerator_character_ne_one (d : Nat) (hd : 1 < d)
    (hsf : Squarefree d) (hD : Not ((d : Int) = 0)) :
    Not (numeratorCharacter (d : Int) hD = 1) := by
  by_cases hd2 : d = 2
  . subst d
    apply character_ne_one_of_neg_one (numeratorCharacter (2 : Int) hD)
      (3 : ZMod (4 * (2 : Int).natAbs))
    have hodd := numerator_character_odd (2 : Int) hD 3 (by decide)
    norm_num only [Nat.cast_ofNat] at hodd
    rw [hodd]
    have hv : jacobiSym (2 : Int) 3 = -1 := by
      rw [jacobiSym.at_two (by decide)]
      decide
    simp only [hv, Int.cast_neg, Int.cast_one]
  . have hex : exists P : Nat, And (Nat.Prime P)
        (And (2 < P) (Dvd.dvd P d)) := by
      choose P hP hPd using Nat.exists_prime_and_dvd (by omega : Not (d = 1))
      by_cases hP2 : P = 2
      . subst P
        choose c hdc using hPd
        have hsf2 : Squarefree (2 * c) := by
          rw [<- hdc]
          exact hsf
        have hcop2c := (Nat.squarefree_mul_iff.mp hsf2).1
        have hc1 : Not (c = 1) := by
          intro hz
          apply hd2
          simpa only [hz, Nat.mul_one] using hdc
        choose P hP hPc using Nat.exists_prime_and_dvd hc1
        have hn2 : Not (Dvd.dvd 2 c) := Nat.prime_two.coprime_iff_not_dvd.mp hcop2c
        have hP2 : Not (P = 2) := by
          intro he
          apply hn2
          simpa only [he] using hPc
        have hPgt : 2 < P := by
          have ht := hP.two_le
          omega
        refine Exists.intro P (And.intro hP (And.intro hPgt ?_))
        choose v hcv using hPc
        refine Exists.intro (2 * v) ?_
        rw [hdc, hcv]
        ring
      . have hPgt : 2 < P := by
          have ht := hP.two_le
          omega
        exact Exists.intro P (And.intro hP (And.intro hPgt hPd))
    choose P hP hPgt hPd using hex
    choose a hda using hPd
    have hsfP : Squarefree (P * a) := by
      rw [<- hda]
      exact hsf
    have hcop : Nat.Coprime P a := (Nat.squarefree_mul_iff.mp hsfP).1
    have ha : 0 < a := by
      by_contra hna
      have hz : a = 0 := by omega
      rw [hz, Nat.mul_zero] at hda
      omega
    have hSign : (d : Int) = (a : Int) * (P : Int) := by
      exact_mod_cast (hda.trans (Nat.mul_comm P a))
    exact numerator_character_ne_one_of_coprime_prime_factor
      a P ha hP hPgt hcop (d : Int) hD (Or.inl hSign)

theorem square_numerator_character_eq_one (a : Nat)
    (hD : Not ((a : Int) ^ 2 = 0)) :
    numeratorCharacter ((a : Int) ^ 2) hD = 1 := by
  let : NeZero (4 * ((a : Int) ^ 2).natAbs) := NeZero.mk (by
    have hd := Int.natAbs_pos.mpr hD
    omega)
  apply MulChar.ext'
  intro x
  by_cases hx : IsUnit x
  . have hcop : Nat.Coprime x.val (4 * ((a : Int) ^ 2).natAbs) := by
      apply (ZMod.isUnit_iff_coprime x.val (4 * ((a : Int) ^ 2).natAbs)).mp
      simpa only [ZMod.natCast_zmod_val] using hx
    have htwo : Dvd.dvd 2 (4 * ((a : Int) ^ 2).natAbs) := by
      refine Exists.intro (2 * ((a : Int) ^ 2).natAbs) ?_
      ring
    have hodd : Odd x.val :=
      Nat.coprime_two_right.mp (Nat.Coprime.of_dvd_right htwo hcop)
    have ha : Dvd.dvd a (4 * ((a : Int) ^ 2).natAbs) := by
      simp only [Int.natAbs_pow, Int.natAbs_natCast]
      refine Exists.intro (4 * a) ?_
      ring
    have hroot : Nat.Coprime a x.val := (Nat.Coprime.of_dvd_right ha hcop).symm
    have hg : (a : Int).gcd (x.val : Int) = 1 := by
      simpa only [Int.gcd_natCast_natCast] using hroot
    have hj : jacobiSym ((a : Int) ^ 2) x.val = 1 := jacobiSym.sq_one' hg
    change numeratorKernel ((a : Int) ^ 2) x.val =
      (1 : DirichletCharacter Complex (4 * ((a : Int) ^ 2).natAbs)) x
    rw [MulChar.one_apply hx]
    simp only [numeratorKernel, ite_eq_left hodd, hj, Int.cast_one]
  . exact ((numeratorCharacter ((a : Int) ^ 2) hD).map_nonunit hx).trans
      ((1 : DirichletCharacter Complex (4 * ((a : Int) ^ 2).natAbs)).map_nonunit hx).symm

theorem numerator_character_nat_eq_one_iff_isSquare (N : Nat) (hN : 0 < N)
    (hD : Not ((N : Int) = 0)) :
    (numeratorCharacter (N : Int) hD = 1) <-> IsSquare N := by
  have htransport (E F : Int) (hEF : E = F)
      (hE : Not (E = 0)) (hF : Not (F = 0)) :
      (numeratorCharacter E hE = 1) <-> (numeratorCharacter F hF = 1) := by
    subst F
    rfl
  constructor
  . intro hprincipal
    choose d s hd hs hEq hsf using Nat.sq_mul_squarefree_of_pos hN
    by_cases hd1 : d = 1
    . refine Exists.intro s ?_
      simpa only [hd1, Nat.mul_one, pow_two] using hEq.symm
    . have hdgt : 1 < d := by omega
      have hdNZ : Not ((d : Int) = 0) := by exact_mod_cast (ne_of_gt hd)
      have hdchi := squarefree_numerator_character_ne_one d hdgt hsf hdNZ
      have hInt : (N : Int) = (s : Int) ^ 2 * (d : Int) := by
        exact_mod_cast hEq.symm
      have hnew : Not ((s : Int) ^ 2 * (d : Int) = 0) := by
        rw [<- hInt]
        exact hD
      have hchi := numerator_character_square_mul_ne_one s hs (d : Int) hdNZ hdchi hnew
      apply False.elim
      apply hchi
      exact (htransport (N : Int) ((s : Int) ^ 2 * (d : Int)) hInt hD hnew).mp hprincipal
  . intro hsquare
    choose a ha using hsquare
    have hInt : (N : Int) = (a : Int) ^ 2 := by
      exact_mod_cast (ha.trans (pow_two a).symm)
    have hroot : Not ((a : Int) ^ 2 = 0) := by
      rw [<- hInt]
      exact hD
    exact (htransport (N : Int) ((a : Int) ^ 2) hInt hD hroot).mpr
      (square_numerator_character_eq_one a hroot)

theorem numerator_principal_indicator_nat_eq_square (N : Nat) (hN : 0 < N) :
    numeratorPrincipalIndicator (N : Int) = if IsSquare N then (1 : Real) else 0 := by
  classical
  have hD : Not ((N : Int) = 0) := by exact_mod_cast (ne_of_gt hN)
  have hiff := numerator_character_nat_eq_one_iff_isSquare N hN hD
  by_cases hs : IsSquare N
  . have hc := hiff.mpr hs
    simp only [numeratorPrincipalIndicator, dite_eq_right hD,
      ite_eq_left hc, ite_eq_left hs]
  . have hc : Not (numeratorCharacter (N : Int) hD = 1) := fun h => hs (hiff.mp h)
    simp only [numeratorPrincipalIndicator, dite_eq_right hD,
      ite_eq_right hc, ite_eq_right hs]

end PrimeFactorOscillations.FiniteFieldIntegerSignature
