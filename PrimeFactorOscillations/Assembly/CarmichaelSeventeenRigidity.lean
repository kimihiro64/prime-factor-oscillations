/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.CarmichaelRootMultiplicity
import PrimeFactorOscillations.Assembly.CarmichaelSeventeenEmbedding

/-!
# Classification of the smallest sharp fifth-tail configurations

At support size seventeen the forced embedding is surjective. The terminal
left nodes cannot be weak, which forces every terminal reference order to be
one and leaves only the two central orders five and six.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace PrimeFactorOscillations.CarmichaelDyadicSharpness.ReflectedSpectrum

open DirichletCompensatedProbe CarmichaelTraceSharpness

variable {I : Type*} [Fintype I]

theorem equalitySeventeenIndex_surjective (S : ReflectedSpectrum I (7 / 8))
    (hEq : S.carrierMass =
      39 * S.weakUnitMass + S.weakRepeatedUnitMass + 4 * S.weakFifthUnitMass)
    (i : I) (hi : Membership.mem S.weakIndices i) (hFive : 5 <= S.mult i)
    (hCard : Fintype.card I = 17) :
    Function.Surjective (S.equalitySeventeenIndex i) := by
  classical
  let f := S.equalitySeventeenIndex i
  have hinj : Function.Injective f := S.equalitySeventeenIndex_injective hEq i hi hFive
  have hRange : Finset.univ.image f = (Finset.univ : Finset I) := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_image_of_injective _ hinj]
    simp [hCard]
  intro j
  have hj : Membership.mem (Finset.univ.image f) j := by rw [hRange]; exact Finset.mem_univ j
  choose k hk he using Finset.mem_image.mp hj
  exact Exists.intro k he

theorem equality_terminal_not_weak (S : ReflectedSpectrum I (7 / 8))
    (hEq : S.carrierMass =
      39 * S.weakUnitMass + S.weakRepeatedUnitMass + 4 * S.weakFifthUnitMass)
    (i : I) (hi : Membership.mem S.weakIndices i) (hFive : 5 <= S.mult i)
    (hCard : Fintype.card I = 17) (k : Fin 17)
    (hAbsent : seventeenTwoTarget k = none) :
    Not (Membership.mem S.weakIndices (S.equalitySeventeenIndex i k)) := by
  intro hk
  have hw := (Finset.mem_filter.mp hk).2.1
  choose l hl using S.equalitySeventeenIndex_surjective hEq i hi hFive hCard
    (S.referenceIndex 2 (S.equalitySeventeenIndex i k))
  have ht : seventeenPoint (S.point i).im l =
      powerMap 2 (seventeenPoint (S.point i).im k) := by
    rw [<- S.equalitySeventeenIndex_point hEq i hi hFive l, hl,
      S.point_referenceIndex 2 _ hw, S.equalitySeventeenIndex_point hEq i hi hFive k]
  exact seventeenPoint_two_absent (S.point i).im k hAbsent l ht

theorem right_order_one_of_floor_and_not_mirror_weak (S : ReflectedSpectrum I (7 / 8))
    (j : I) (hRight : 1 / 2 < (S.point j).re)
    (hFloor : S.multiplicitySupportWeight j = S.unitMass j)
    (hMirror : Not (Membership.mem S.weakIndices (S.mirror j))) :
    S.mult j = 1 := by
  have hMass := S.right_weight_eq_mass_of_not_mirror_weak j hRight hMirror
  rw [hMass] at hFloor
  by_contra h
  have hTwo : 2 <= S.mult j := by have hp := S.mult_pos j; omega
  have hTwoReal : (2 : Real) <= (S.mult j : Real) := by exact_mod_cast hTwo
  have hLower := mul_le_mul_of_nonneg_right hTwoReal (S.unitMass_nonneg j)
  rw [<- S.equality_mass_eq_mult_unit j, hFloor] at hLower
  linarith [S.equality_unitMass_pos j]

theorem fifth_equality_terminal_two_order (S : ReflectedSpectrum I (7 / 8))
    (hEq : S.carrierMass =
      39 * S.weakUnitMass + S.weakRepeatedUnitMass + 4 * S.weakFifthUnitMass)
    (j : I) (hj : Membership.mem S.weakIndices j) (hSmall : S.mult j <= 4)
    (hMirror : Not (Membership.mem S.weakIndices (S.mirror (S.referenceIndex 2 j)))) :
    S.mult (S.referenceIndex 2 j) = 1 := by
  have hw := (Finset.mem_filter.mp hj).2.1
  have hu := S.reference_unit_mass_eq 2 (by norm_num) j hw
  norm_num at hu
  have hf := S.fifth_equality_two_weight hEq j hj
  have hNot : Not (5 <= S.mult j) := by omega
  simp only [fifthUnitAt, if_neg hNot, mul_zero, add_zero] at hf
  apply S.right_order_one_of_floor_and_not_mirror_weak (S.referenceIndex 2 j)
    (S.weak_reference_two_bounds j hj).1 _ hMirror
  rw [hf, hu]

theorem fifth_equality_terminal_four_order (S : ReflectedSpectrum I (7 / 8))
    (hEq : S.carrierMass =
      39 * S.weakUnitMass + S.weakRepeatedUnitMass + 4 * S.weakFifthUnitMass)
    (j : I) (hj : Membership.mem S.weakIndices j)
    (hMirror : Not (Membership.mem S.weakIndices (S.mirror (S.referenceIndex 4 j)))) :
    S.mult (S.referenceIndex 4 j) = 1 := by
  have hw := (Finset.mem_filter.mp hj).2.2
  have hu := S.reference_unit_mass_eq 4 (by norm_num) j hw
  norm_num at hu
  have hr := S.weak_reference_four_lower j hj
  apply S.right_order_one_of_floor_and_not_mirror_weak (S.referenceIndex 4 j)
    (by linarith) _ hMirror
  rw [S.fifth_equality_four_weight hEq j hj, hu]

theorem equalitySeventeenIndex_multiplicity (S : ReflectedSpectrum I (7 / 8))
    (hEq : S.carrierMass =
      39 * S.weakUnitMass + S.weakRepeatedUnitMass + 4 * S.weakFifthUnitMass)
    (i : I) (hi : Membership.mem S.weakIndices i) (hFive : 5 <= S.mult i)
    (hCard : Fintype.card I = 17) (k : Fin 17) :
    S.mult (S.equalitySeventeenIndex i k) = seventeenRootMultiplicity (S.mult i) k := by
  let a := S.mirror (S.referenceIndex 2 i)
  let b := S.mirror (S.referenceIndex 4 i)
  let c := S.mirror (S.referenceIndex 2 a)
  have ha : Membership.mem S.weakIndices a :=
    S.fifth_equality_weak_fifth_two_mirror hEq i hi hFive
  have hb : Membership.mem S.weakIndices b :=
    S.fifth_equality_weak_fifth_four_mirror hEq i hi hFive
  have h2 := S.fifth_equality_weak_fifth_two_order hEq i hi hFive
  have h4 := S.fifth_equality_weak_fifth_four_order hEq i hi hFive
  have hA : S.mult a = 3 := by dsimp only [a]; rw [S.mult_mirror, h2]
  have hB : S.mult b = 2 := by dsimp only [b]; rw [S.mult_mirror, h4]
  have hc : Membership.mem S.weakIndices c :=
    S.fifth_equality_weak_three_two_mirror hEq a ha hA
  have h6 := S.fifth_equality_weak_three_two_order hEq a ha hA
  have hC : S.mult c = 2 := by dsimp only [c]; rw [S.mult_mirror, h6]
  have h7 := S.equality_terminal_not_weak hEq i hi hFive hCard 7 rfl
  have h9 := S.equality_terminal_not_weak hEq i hi hFive hCard 9 rfl
  have h11 := S.equality_terminal_not_weak hEq i hi hFive hCard 11 rfl
  have h13 := S.equality_terminal_not_weak hEq i hi hFive hCard 13 rfl
  have h15 := S.equality_terminal_not_weak hEq i hi hFive hCard 15 rfl
  have h8 : S.mult (S.referenceIndex 4 a) = 1 :=
    S.fifth_equality_terminal_four_order hEq a ha h7
  have h10 : S.mult (S.referenceIndex 2 b) = 1 :=
    S.fifth_equality_terminal_two_order hEq b hb (by omega) h9
  have h12 : S.mult (S.referenceIndex 4 b) = 1 :=
    S.fifth_equality_terminal_four_order hEq b hb h11
  have h14 : S.mult (S.referenceIndex 2 c) = 1 :=
    S.fifth_equality_terminal_two_order hEq c hc (by omega) h13
  have h16 : S.mult (S.referenceIndex 4 c) = 1 :=
    S.fifth_equality_terminal_four_order hEq c hc h15
  fin_cases k <;>
    simp [equalitySeventeenIndex, seventeenRootMultiplicity, seventeenMultiplicity,
      S.mult_mirror, h2, h4, h6, h8, h10, h12, h14, h16, a, b, c] at *

theorem fifth_minimal_configuration_classification (S : ReflectedSpectrum I (7 / 8))
    (hEq : S.carrierMass =
      39 * S.weakUnitMass + S.weakRepeatedUnitMass + 4 * S.weakFifthUnitMass)
    (hPos : 0 < S.weakFifthUnitMass) (hCard : Fintype.card I = 17) :
    exists H : Real, 0 < H /\ exists M : Nat, (M = 5 \/ M = 6) /\
      exists e : Equiv (Fin 17) I,
        (forall k, S.point (e k) = seventeenPoint H k) /\
        (forall k, S.mult (e k) = seventeenRootMultiplicity M k) := by
  choose i hi hFive using S.weak_fifth_exists_of_mass_pos hPos
  let e : Equiv (Fin 17) I := Equiv.ofBijective (S.equalitySeventeenIndex i)
    (And.intro (S.equalitySeventeenIndex_injective hEq i hi hFive)
      (S.equalitySeventeenIndex_surjective hEq i hi hFive hCard))
  refine Exists.intro (S.point i).im (And.intro (S.im_pos i)
    (Exists.intro (S.mult i) (And.intro (S.fifth_equality_weak_root_order hEq i hi hFive)
      (Exists.intro e (And.intro ?_ ?_)))))
  . exact S.equalitySeventeenIndex_point hEq i hi hFive
  . exact S.equalitySeventeenIndex_multiplicity hEq i hi hFive hCard

end PrimeFactorOscillations.CarmichaelDyadicSharpness.ReflectedSpectrum

