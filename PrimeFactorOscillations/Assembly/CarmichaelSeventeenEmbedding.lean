/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelEqualityOrders
import PrimeFactorOscillations.Assembly.CarmichaelSeventeenRows

/-!
# The forced seventeen-point embedding

The branches forced by a common weak fifth-order atom embed the entire
seventeen-point geometry in every sharp equality configuration.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness.ReflectedSpectrum

open DirichletCompensatedProbe CarmichaelWeightedSignal

variable {I : Type*} [Fintype I]

def equalitySeventeenIndex (S : ReflectedSpectrum I (7 / 8)) (i : I)
    (k : Fin 17) : I :=
  let a := S.mirror (S.referenceIndex 2 i)
  let b := S.mirror (S.referenceIndex 4 i)
  let c := S.mirror (S.referenceIndex 2 a)
  match k.val with
  | 0 => i
  | 1 => a
  | 2 => S.referenceIndex 2 i
  | 3 => b
  | 4 => S.referenceIndex 4 i
  | 5 => c
  | 6 => S.referenceIndex 2 a
  | 7 => S.mirror (S.referenceIndex 4 a)
  | 8 => S.referenceIndex 4 a
  | 9 => S.mirror (S.referenceIndex 2 b)
  | 10 => S.referenceIndex 2 b
  | 11 => S.mirror (S.referenceIndex 4 b)
  | 12 => S.referenceIndex 4 b
  | 13 => S.mirror (S.referenceIndex 2 c)
  | 14 => S.referenceIndex 2 c
  | 15 => S.mirror (S.referenceIndex 4 c)
  | _ => S.referenceIndex 4 c

theorem equalitySeventeenIndex_point (S : ReflectedSpectrum I (7 / 8))
    (hEq : S.carrierMass =
      39 * S.weakUnitMass + S.weakRepeatedUnitMass + 4 * S.weakFifthUnitMass)
    (i : I) (hi : Membership.mem S.weakIndices i) (hFive : 5 <= S.mult i)
    (k : Fin 17) :
    S.point (S.equalitySeventeenIndex i k) = seventeenPoint (S.point i).im k := by
  let H := (S.point i).im
  have hH : 0 < H := S.im_pos i
  let a := S.mirror (S.referenceIndex 2 i)
  let b := S.mirror (S.referenceIndex 4 i)
  let c := S.mirror (S.referenceIndex 2 a)
  have ha : Membership.mem S.weakIndices a :=
    S.fifth_equality_weak_fifth_two_mirror hEq i hi hFive
  have hb : Membership.mem S.weakIndices b :=
    S.fifth_equality_weak_fifth_four_mirror hEq i hi hFive
  have hThree : S.mult a = 3 := by
    dsimp only [a]
    rw [S.mult_mirror]
    exact S.fifth_equality_weak_fifth_two_order hEq i hi hFive
  have hc : Membership.mem S.weakIndices c :=
    S.fifth_equality_weak_three_two_mirror hEq a ha hThree
  have hTwo (j : I) (hj : Membership.mem S.weakIndices j) (u v : Fin 17)
      (hp : S.point j = seventeenPoint H u)
      (ht : seventeenTwoTarget u = some v) :
      S.point (S.referenceIndex 2 j) = seventeenPoint H v := by
    have hw := (Finset.mem_filter.mp hj).2.1
    rw [S.point_referenceIndex 2 j hw, hp]
    exact seventeenPoint_two_of_target H u v ht
  have hFour (j : I) (hj : Membership.mem S.weakIndices j) (u v : Fin 17)
      (hp : S.point j = seventeenPoint H u)
      (ht : seventeenFourTarget u = some v) :
      S.point (S.referenceIndex 4 j) = seventeenPoint H v := by
    have hw := (Finset.mem_filter.mp hj).2.2
    rw [S.point_referenceIndex 4 j hw, hp]
    exact seventeenPoint_four_of_target H u v ht
  have hMirror (j : I) (u : Fin 17) (hp : S.point j = seventeenPoint H u) :
      S.point (S.mirror j) = seventeenPoint H (seventeenMirror u) := by
    rw [S.point_mirror j, hp]
    exact ((seventeenSpectrum H hH).point_mirror u).symm
  have p0 : S.point i = seventeenPoint H 0 := by
    apply Complex.ext
    . change (S.point i).re = 32 / 64
      rw [S.fifth_equality_high_central hEq i hFive]
      norm_num
    . simp [seventeenPoint, seventeenHeightDenominator, H]
  have p2 := hTwo i hi 0 2 p0 rfl
  have p1 : S.point a = seventeenPoint H 1 := hMirror _ 2 p2
  have p4 := hFour i hi 0 4 p0 rfl
  have p3 : S.point b = seventeenPoint H 3 := hMirror _ 4 p4
  have p6 := hTwo a ha 1 6 p1 rfl
  have p5 : S.point c = seventeenPoint H 5 := hMirror _ 6 p6
  have p8 := hFour a ha 1 8 p1 rfl
  have p7 := hMirror _ 8 p8
  have p10 := hTwo b hb 3 10 p3 rfl
  have p9 := hMirror _ 10 p10
  have p12 := hFour b hb 3 12 p3 rfl
  have p11 := hMirror _ 12 p12
  have p14 := hTwo c hc 5 14 p5 rfl
  have p13 := hMirror _ 14 p14
  have p16 := hFour c hc 5 16 p5 rfl
  have p15 := hMirror _ 16 p16
  fin_cases k <;> first
    | exact p0
    | exact p1
    | exact p2
    | exact p3
    | exact p4
    | exact p5
    | exact p6
    | exact p7
    | exact p8
    | exact p9
    | exact p10
    | exact p11
    | exact p12
    | exact p13
    | exact p14
    | exact p15
    | exact p16

theorem equalitySeventeenIndex_injective (S : ReflectedSpectrum I (7 / 8))
    (hEq : S.carrierMass =
      39 * S.weakUnitMass + S.weakRepeatedUnitMass + 4 * S.weakFifthUnitMass)
    (i : I) (hi : Membership.mem S.weakIndices i) (hFive : 5 <= S.mult i) :
    Function.Injective (S.equalitySeventeenIndex i) := by
  intro k l h
  apply seventeenPoint_injective (S.point i).im
  rw [<- S.equalitySeventeenIndex_point hEq i hi hFive k,
    <- S.equalitySeventeenIndex_point hEq i hi hFive l, h]

theorem weak_fifth_exists_of_mass_pos (S : ReflectedSpectrum I (7 / 8))
    (hPos : 0 < S.weakFifthUnitMass) :
    exists i, Membership.mem S.weakIndices i /\ 5 <= S.mult i := by
  classical
  by_contra h
  have hSmall : forall i, Membership.mem S.weakIndices i -> S.mult i <= 4 := by
    intro i hi
    by_contra hn
    exact h (Exists.intro i (And.intro hi (by omega)))
  have hz := S.weakFifthUnitMass_eq_zero_iff.mpr hSmall
  linarith

theorem fifth_equality_card_minimum (S : ReflectedSpectrum I (7 / 8))
    (hEq : S.carrierMass =
      39 * S.weakUnitMass + S.weakRepeatedUnitMass + 4 * S.weakFifthUnitMass)
    (hPos : 0 < S.weakFifthUnitMass) :
    17 <= Fintype.card I := by
  choose i hi hFive using S.weak_fifth_exists_of_mass_pos hPos
  have hCard := Fintype.card_le_of_injective _
    (S.equalitySeventeenIndex_injective hEq i hi hFive)
  simpa using hCard

end PrimeFactorOscillations.CarmichaelDyadicSharpness.ReflectedSpectrum

