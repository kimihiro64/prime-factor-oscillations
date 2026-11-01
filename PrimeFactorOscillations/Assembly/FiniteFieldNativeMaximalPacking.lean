/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeArithmeticAgreement
import PrimeFactorOscillations.Mathlib.Data.Nat.IsSquareTrans

/-!
# Sharp deficit control for maximal native packings

The two positive square-class rows allow at most two members of a flat
family to conflict with one anchor. A three-label actual prime family
certifies that the resulting maximal-packing deficit factor is sharp.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

/-- Three actual prime-pair labels realize the path with two conflicting
edges and a compatible outer pair. These include one long positive gap. -/
theorem native_maximal_packing_sharp_rates :
    nativeAgreementRate 11 2 11 8 = 1 / 2 /\
    nativeAgreementRate 11 2 5 8 = 1 / 2 /\
    nativeAgreementRate 11 8 5 8 = 3 / 8 := by
  have habL : IsSquare (2 * 8 * 11 * 11 : Nat) := Exists.intro 44 (by norm_num)
  have habU : Not (IsSquare (2 * 8 * (11 + 2) * (11 + 8) : Nat)) := by
    intro hs
    choose r hr using hs
    have he : (3952 : Nat) = r * r := hr
    by_cases hroot : r <= 62
    . have hb : r * r <= 62 * 62 := Nat.mul_le_mul hroot hroot
      omega
    . have hrLow : 63 <= r := by omega
      have hb : 63 * 63 <= r * r := Nat.mul_le_mul hrLow hrLow
      omega
  have hacL : Not (IsSquare (2 * 8 * 11 * 5 : Nat)) := by
    intro hs
    choose r hr using hs
    have he : (880 : Nat) = r * r := hr
    by_cases hroot : r <= 29
    . have hb : r * r <= 29 * 29 := Nat.mul_le_mul hroot hroot
      omega
    . have hrLow : 30 <= r := by omega
      have hb : 30 * 30 <= r * r := Nat.mul_le_mul hrLow hrLow
      omega
  have hacU : IsSquare (2 * 8 * (11 + 2) * (5 + 8) : Nat) :=
    Exists.intro 52 (by norm_num)
  have hbcL : Not (IsSquare (8 * 8 * 11 * 5 : Nat)) := by
    intro hs
    choose r hr using hs
    have he : (3520 : Nat) = r * r := hr
    by_cases hroot : r <= 59
    . have hb : r * r <= 59 * 59 := Nat.mul_le_mul hroot hroot
      omega
    . have hrLow : 60 <= r := by omega
      have hb : 60 * 60 <= r * r := Nat.mul_le_mul hrLow hrLow
      omega
  have hbcU : Not (IsSquare (8 * 8 * (11 + 8) * (5 + 8) : Nat)) := by
    intro hs
    choose r hr using hs
    have he : (15808 : Nat) = r * r := hr
    by_cases hroot : r <= 125
    . have hb : r * r <= 125 * 125 := Nat.mul_le_mul hroot hroot
      omega
    . have hrLow : 126 <= r := by omega
      have hb : 126 * 126 <= r * r := Nat.mul_le_mul hrLow hrLow
      omega
  refine And.intro ?_ (And.intro ?_ ?_)
  . rw [native_agreement_rate_eq_square_test 11 2 11 8
      (by decide) (by decide) (by decide) (by decide)]
    rw [ite_eq_left habL, ite_eq_right habU]
    norm_num
  . rw [native_agreement_rate_eq_square_test 11 2 5 8
      (by decide) (by decide) (by decide) (by decide)]
    rw [ite_eq_right hacL, ite_eq_left hacU]
    norm_num
  . rw [native_agreement_rate_eq_square_test 11 8 5 8
      (by decide) (by decide) (by decide) (by decide)]
    rw [ite_eq_right hbcL, ite_eq_right hbcU]
    norm_num

/-- In a flat actual prime-pair family, each square-class row meets an
arbitrary positive anchor in at most one member. -/
theorem native_flat_square_row_conflicts_card_le_one
    (M : Finset (Prod Nat Nat))
    (hGeometry : forall a : Prod Nat Nat, Membership.mem M a ->
      Nat.Prime a.1 /\ Nat.Prime (a.1 + a.2) /\ 0 < a.2)
    (hFlat : forall a : Prod Nat Nat, Membership.mem M a ->
      forall b : Prod Nat Nat, Membership.mem M b -> Not (a = b) ->
        nativeAgreementRate a.1 a.2 b.1 b.2 = 3 / 8)
    (n h : Nat) (hn : 0 < n) (hh : 0 < h) :
    (M.filter (fun a => IsSquare ((h * n) * (a.2 * a.1)))).card <= 1 /\
    (M.filter (fun a => IsSquare ((h * (n + h)) * (a.2 * (a.1 + a.2))))).card <= 1 := by
  classical
  have hSeparated (a : Prod Nat Nat) (ha : Membership.mem M a)
      (b : Prod Nat Nat) (hb : Membership.mem M b) (hab : Not (a = b)) :
      Not (IsSquare ((a.2 * a.1) * (b.2 * b.1))) /\
      Not (IsSquare ((a.2 * (a.1 + a.2)) * (b.2 * (b.1 + b.2)))) := by
    have ga := hGeometry a ha
    have gb := hGeometry b hb
    have hneq : Not (And (a.1 = b.1) (a.2 = b.2)) := by
      intro he
      exact hab (Prod.ext he.1 he.2)
    have hRows := (native_agreement_arithmetic_classification
      a.1 a.2 b.1 b.2 ga.1 ga.2.1 gb.1 gb.2.1 ga.2.2 gb.2.2 hneq).2.mp
        (hFlat a ha b hb hab)
    refine And.intro ?_ ?_
    . intro hs
      apply hRows.1
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hs
    . intro hs
      apply hRows.2
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hs
  refine And.intro ?_ ?_
  . apply Finset.card_le_one.mpr
    intro a ha b hb
    by_contra hab
    have hA := Finset.mem_filter.mp ha
    have hB := Finset.mem_filter.mp hb
    have hLeft : IsSquare ((a.2 * a.1) * (h * n)) := by
      simpa only [mul_comm] using hA.2
    have hAB : IsSquare ((a.2 * a.1) * (b.2 * b.1)) :=
      Nat.isSquare_mul_trans_of_pos (Nat.mul_pos hh hn) hLeft hB.2
    exact (hSeparated a hA.1 b hB.1 hab).1 hAB
  . apply Finset.card_le_one.mpr
    intro a ha b hb
    by_contra hab
    have hA := Finset.mem_filter.mp ha
    have hB := Finset.mem_filter.mp hb
    have hUpper : 0 < n + h := by omega
    have hLeft : IsSquare ((a.2 * (a.1 + a.2)) * (h * (n + h))) := by
      simpa only [mul_comm] using hA.2
    have hAB : IsSquare ((a.2 * (a.1 + a.2)) * (b.2 * (b.1 + b.2))) :=
      Nat.isSquare_mul_trans_of_pos (Nat.mul_pos hh hUpper) hLeft hB.2
    exact (hSeparated a hA.1 b hB.1 hab).2 hAB

/-- Both complete native square rows together block at most two members
of any flat actual prime-pair family. -/
theorem native_flat_square_conflicts_card_le_two
    (M : Finset (Prod Nat Nat))
    (hGeometry : forall a : Prod Nat Nat, Membership.mem M a ->
      Nat.Prime a.1 /\ Nat.Prime (a.1 + a.2) /\ 0 < a.2)
    (hFlat : forall a : Prod Nat Nat, Membership.mem M a ->
      forall b : Prod Nat Nat, Membership.mem M b -> Not (a = b) ->
        nativeAgreementRate a.1 a.2 b.1 b.2 = 3 / 8)
    (n h : Nat) (hn : 0 < n) (hh : 0 < h) :
    (M.filter (fun a =>
      Or (IsSquare ((h * n) * (a.2 * a.1)))
        (IsSquare ((h * (n + h)) * (a.2 * (a.1 + a.2)))))).card <= 2 := by
  classical
  let L := M.filter (fun a => IsSquare ((h * n) * (a.2 * a.1)))
  let U := M.filter (fun a => IsSquare ((h * (n + h)) * (a.2 * (a.1 + a.2))))
  let D := M.filter (fun a =>
    Or (IsSquare ((h * n) * (a.2 * a.1)))
      (IsSquare ((h * (n + h)) * (a.2 * (a.1 + a.2)))))
  have hRows := native_flat_square_row_conflicts_card_le_one M hGeometry hFlat n h hn hh
  have hL : L.card <= 1 := hRows.1
  have hU : U.card <= 1 := hRows.2
  have hSub : D <= Union.union L U := by
    intro a ha
    have hm : Membership.mem M a := (Finset.mem_filter.mp ha).1
    have hCases :
        Or (IsSquare ((h * n) * (a.2 * a.1)))
          (IsSquare ((h * (n + h)) * (a.2 * (a.1 + a.2)))) :=
      (Finset.mem_filter.mp ha).2
    rcases hCases with hl | hu
    . exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr (And.intro hm hl)))
    . exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr (And.intro hm hu)))
  have hCover : D.card <= (Union.union L U).card := Finset.card_le_card hSub
  have hUnion : (Union.union L U).card + (Inter.inter L U).card = L.card + U.card :=
    Finset.card_union_add_card_inter L U
  change D.card <= 2
  omega

/-- A square-row dominating selection has deletion deficit at most twice
that of any flat comparison family, on the exact common finite support. -/
theorem native_dominating_selection_flat_deficit
    (S G M : Finset (Prod Nat Nat))
    (hGeometry : forall a : Prod Nat Nat, Membership.mem S a ->
      Nat.Prime a.1 /\ Nat.Prime (a.1 + a.2) /\ 0 < a.2)
    (hGS : G <= S) (hMS : M <= S)
    (hFlat : forall a : Prod Nat Nat, Membership.mem M a ->
      forall b : Prod Nat Nat, Membership.mem M b -> Not (a = b) ->
        nativeAgreementRate a.1 a.2 b.1 b.2 = 3 / 8)
    (hDom : forall a : Prod Nat Nat, Membership.mem S a -> Not (Membership.mem G a) ->
      exists g : Prod Nat Nat, Membership.mem G g /\
        Or (IsSquare ((a.2 * a.1) * (g.2 * g.1)))
          (IsSquare ((a.2 * (a.1 + a.2)) * (g.2 * (g.1 + g.2))))) :
    (S \ G).card <= 2 * (S \ M).card := by
  classical
  let A := M \ G
  let B := G \ M
  let F := fun g : Prod Nat Nat => M.filter (fun a =>
    Or (IsSquare ((g.2 * g.1) * (a.2 * a.1)))
      (IsSquare ((g.2 * (g.1 + g.2)) * (a.2 * (a.1 + a.2)))))
  have hMGeometry (a : Prod Nat Nat) (ha : Membership.mem M a) :
      Nat.Prime a.1 /\ Nat.Prime (a.1 + a.2) /\ 0 < a.2 := hGeometry a (hMS ha)
  have hFibers (g : Prod Nat Nat) (hg : Membership.mem B g) : (F g).card <= 2 := by
    have hgG : Membership.mem G g := (Finset.mem_sdiff.mp hg).1
    have hh := hGeometry g (hGS hgG)
    exact native_flat_square_conflicts_card_le_two M hMGeometry hFlat
      g.1 g.2 hh.1.pos hh.2.2
  have hCover : A <= B.biUnion F := by
    intro a ha
    have hInfo : Membership.mem M a /\ Not (Membership.mem G a) := Finset.mem_sdiff.mp ha
    choose g hg hCollision using hDom a (hMS hInfo.1) hInfo.2
    have hgNotM : Not (Membership.mem M g) := by
      intro hgM
      have hneq : Not (a = g) := by
        intro he
        apply hInfo.2
        rw [he]
        exact hg
      have ga := hMGeometry a hInfo.1
      have gg := hMGeometry g hgM
      have hpair : Not (And (a.1 = g.1) (a.2 = g.2)) := by
        intro he
        exact hneq (Prod.ext he.1 he.2)
      have hRows := (native_agreement_arithmetic_classification
        a.1 a.2 g.1 g.2 ga.1 ga.2.1 gg.1 gg.2.1 ga.2.2 gg.2.2 hpair).2.mp
          (hFlat a hInfo.1 g hgM hneq)
      rcases hCollision with hl | hu
      . apply hRows.1
        simpa only [mul_assoc, mul_comm, mul_left_comm] using hl
      . apply hRows.2
        simpa only [mul_assoc, mul_comm, mul_left_comm] using hu
    apply Finset.mem_biUnion.mpr
    refine Exists.intro g (And.intro (Finset.mem_sdiff.mpr (And.intro hg hgNotM)) ?_)
    apply Finset.mem_filter.mpr
    refine And.intro hInfo.1 ?_
    simpa only [mul_comm] using hCollision
  have hCharge : A.card <= B.card * 2 :=
    (Finset.card_le_card hCover).trans (Finset.card_biUnion_le_card_mul B F 2 hFibers)
  have hBSub : B <= S \ M := by
    intro g hg
    have hi : Membership.mem G g /\ Not (Membership.mem M g) := Finset.mem_sdiff.mp hg
    exact Finset.mem_sdiff.mpr (And.intro (hGS hi.1) hi.2)
  have hBLe : B.card <= (S \ M).card := Finset.card_le_card hBSub
  have hGM : B.card + M.card = (Union.union G M).card := Finset.card_sdiff_add_card G M
  have hMG : A.card + G.card = (Union.union G M).card := by
    calc
      A.card + G.card = (Union.union M G).card := Finset.card_sdiff_add_card M G
      _ = (Union.union G M).card := congrArg Finset.card (Finset.union_comm M G)
  have hSG : (S \ G).card + G.card = S.card := Finset.card_sdiff_add_card_eq_card hGS
  have hSM : (S \ M).card + M.card = S.card := Finset.card_sdiff_add_card_eq_card hMS
  omega

/-- The deficit factor two is attained on three genuine prime-pair labels:
the singleton middle selection is flat and dominating, while the two outer
labels form a flat comparison family. -/
theorem native_dominating_selection_flat_deficit_sharp :
    exists S G M : Finset (Prod Nat Nat),
      (forall a : Prod Nat Nat, Membership.mem S a ->
        Nat.Prime a.1 /\ Nat.Prime (a.1 + a.2) /\ 0 < a.2) /\
      G <= S /\ M <= S /\
      (forall a : Prod Nat Nat, Membership.mem G a ->
        forall b : Prod Nat Nat, Membership.mem G b -> Not (a = b) ->
          nativeAgreementRate a.1 a.2 b.1 b.2 = 3 / 8) /\
      (forall a : Prod Nat Nat, Membership.mem M a ->
        forall b : Prod Nat Nat, Membership.mem M b -> Not (a = b) ->
          nativeAgreementRate a.1 a.2 b.1 b.2 = 3 / 8) /\
      (forall a : Prod Nat Nat, Membership.mem S a -> Not (Membership.mem G a) ->
        exists g : Prod Nat Nat, Membership.mem G g /\
          Or (IsSquare ((a.2 * a.1) * (g.2 * g.1)))
            (IsSquare ((a.2 * (a.1 + a.2)) * (g.2 * (g.1 + g.2))))) /\
      (S \ G).card = 2 /\ (S \ M).card = 1 := by
  classical
  let a : Prod Nat Nat := (11, 2)
  let b : Prod Nat Nat := (11, 8)
  let c : Prod Nat Nat := (5, 8)
  let S : Finset (Prod Nat Nat) := {a, b, c}
  let G : Finset (Prod Nat Nat) := {a}
  let M : Finset (Prod Nat Nat) := {b, c}
  have hRates := native_maximal_packing_sharp_rates
  have hReverse : nativeAgreementRate 5 8 11 8 = 3 / 8 := by
    have he : nativeAgreementRate 5 8 11 8 = nativeAgreementRate 11 8 5 8 := by
      simp only [nativeAgreementRate, mul_assoc, mul_comm, mul_left_comm]
    exact he.trans hRates.2.2
  refine Exists.intro S (Exists.intro G (Exists.intro M ?_))
  refine And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro ?_
    (And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))))))
  . intro u hu
    have hc : u = a \/ u = b \/ u = c := by
      simpa only [S, Finset.mem_insert, Finset.mem_singleton] using hu
    rcases hc with rfl | rfl | rfl <;> norm_num [a, b, c]
  . intro u hu
    have he : u = a := Finset.mem_singleton.mp hu
    rw [he]
    simp only [S, Finset.mem_insert, true_or]
  . intro u hu
    have hc : u = b \/ u = c := by
      simpa only [M, Finset.mem_insert, Finset.mem_singleton] using hu
    rcases hc with rfl | rfl <;> simp [S]
  . intro u hu v hv hne
    have huA : u = a := Finset.mem_singleton.mp hu
    have hvA : v = a := Finset.mem_singleton.mp hv
    exact False.elim (hne (huA.trans hvA.symm))
  . intro u hu v hv hne
    have huC : u = b \/ u = c := by
      simpa only [M, Finset.mem_insert, Finset.mem_singleton] using hu
    have hvC : v = b \/ v = c := by
      simpa only [M, Finset.mem_insert, Finset.mem_singleton] using hv
    rcases huC with rfl | rfl <;> rcases hvC with rfl | rfl
    . exact False.elim (hne rfl)
    . exact hRates.2.2
    . exact hReverse
    . exact False.elim (hne rfl)
  . intro u hu hNot
    have huC : u = a \/ u = b \/ u = c := by
      simpa only [S, Finset.mem_insert, Finset.mem_singleton] using hu
    rcases huC with rfl | rfl | rfl
    . exact False.elim (hNot (Finset.mem_singleton_self a))
    . refine Exists.intro a (And.intro (Finset.mem_singleton_self a) ?_)
      have hRows := (native_agreement_arithmetic_classification 11 2 11 8
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by decide) (by decide) (by decide)).1.mp hRates.1
      simpa only [a, b, mul_assoc, mul_comm, mul_left_comm] using hRows
    . refine Exists.intro a (And.intro (Finset.mem_singleton_self a) ?_)
      have hRows := (native_agreement_arithmetic_classification 11 2 5 8
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by decide) (by decide) (by decide)).1.mp hRates.2.1
      simpa only [a, c, mul_assoc, mul_comm, mul_left_comm] using hRows
  . change ({(11, 2), (11, 8), (5, 8)} \ {(11, 2)} : Finset (Prod Nat Nat)).card = 2
    decide
  . norm_num [S, M, a, b, c]

end PrimeFactorOscillations.FiniteFieldIntegerSignature
